{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneDeriving #-}

-- | Transform the blocks from a parsed text to TFF form.
-- This code is a bit fragile since it was written mainly
-- by checking that a ton of examples work and not focussing
-- on correctness by design. Therefore we made the concious
-- decision to add many calls to 'error'. This ensures that
-- this transformation is indeed faithful to the Naproche text.

-- TODO: Introduce an error monad for errors that are strictly
-- user errors and not a fault of the translation like duplicate 
-- variables, etc.

module SAD.Core.Transform
 ( convert, convertBlock
 ) where

import Data.Text (Text)
import qualified Data.Text as Text
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Functor.Const
import Data.Functor.Identity
import qualified Data.List as List
import Data.Maybe (fromMaybe)
import Control.Applicative

import SAD.Data.Formula (Formula, Tag(..))
import qualified SAD.Data.Formula as F
import SAD.Data.VarName
import SAD.Data.Text.Decl
import SAD.Data.Terms
import SAD.Core.SourcePos (noSourcePos)
import SAD.Data.Text.Block (ProofText(..), Block(..))
import qualified SAD.Data.Text.Block as Block
import SAD.Core.Pretty (Pretty(..))

import SAD.Core.Typed
import SAD.Core.Coerce

import Debug.Trace
import GHC.Stack

-- | If you encounter a weird error, this may help
-- with debugging it. You need to import Debug.Trace
traceReprId :: Pretty a => a -> a
traceReprId a = a -- trace (Text.unpack (pretty a)) a

data Context = Context
  { typings :: Map TermName Type
    -- ^ a type for each resolved name
  , resolved :: Map TermName (Set TermName)
    -- ^ resolve functions into names, e.g. + into add_nat 
    -- and and_rat if + was defined twice.
  , nextName :: Maybe Text
    -- ^ the resolved name of the next definition,
    -- if given by an instruction
  , coercions :: Coercions TermName TermName
  , preBoundVars :: Map VarName InType
    -- ^ variables bound by a previous choose statement or in the claim.
  } deriving (Eq, Ord, Show)

-- | Danger: Costly in second argument due to coercions
instance Semigroup Context where
  (<>) (Context t1 r1 n1 c1 p1) (Context t2 r2 n2 c2 p2) = Context (t1 <> t2) (r1 <> r2) (n1 <> n2) (c1 <> c2) (p1 <> p2)

instance Monoid Context where
  mempty = Context mempty mempty mempty mempty mempty

-- | Parse a formula into a term while ignoring all type information.
-- This will only check that no variable overlap and that all de-bruijn
-- indices have a binder. We will subsequently use the variable names at
-- the binders instead of indices since this leads to nicer output.
parseFormula :: Formula -> Term (Const ()) Tag
parseFormula = go []
  where 
    go vars = \case
      F.All (Decl v _ _) f -> Forall v (Const ()) $ go (addVar v vars) f
      F.Exi (Decl v _ _) f -> Exists v (Const ()) $ go (addVar v vars) f
      F.Iff f1 f2 -> App Iff [go vars f1, go vars f2]
      F.Imp f1 f2 -> App Imp [go vars f1, go vars f2]
      F.And f1 f2 -> App And [go vars f1, go vars f2]
      F.Or  f1 f2 -> App Or  [go vars f1, go vars f2]
      F.Tag t f   -> Tag t $ go vars f
      F.Not f -> App Not [go vars f]
      F.Top -> App Top []
      F.Bot -> App Bot []
      F.Trm TermEquality [f1, f2] _ _ -> App Eq [go vars f1, go vars f2]
      F.Trm TermLess _ _ _ -> error $ "Old style induction using -<- is not supported any longer!"
        ++ " See the manual for the new approach."
      F.Trm name args _ _ -> App (OpTrm name) $ map (go vars) args
      F.Var v _ _ -> Var v
      F.Ind i _ ->
        if length vars > i then Var $ vars !! i
        else error $ "Unbound index: " ++ show i
      f -> error $  "Unexpected formula: " ++ show f

    addVar v vars = v:vars

-- | Bind free variables by forall quantifiers.
bindFree :: Term (Const ()) t -> Term (Const ()) t
bindFree t = bind (Set.toList $ fvToVarSet $ free t) t
  where
    bind vars tr = foldr (\v t -> Forall v (Const ()) t) tr vars

    free = \case
      Forall v (Const ()) t -> bindVar v $ free t
      Exists v (Const ()) t -> bindVar v $ free t
      App _ args -> mconcat $ free <$> args
      Tag _ t -> free t
      Var v -> unitFV v noSourcePos

-- | Bind free variables by exists quantifiers.
bindExists :: [VarName] -> Term (Const ()) t -> Term (Const ()) t
bindExists vs tr = foldr (\v -> Exists v (Const ())) tr vs

-- | Given a list of defined sorts and a TermName,
-- decide if this is a sort.
parseType :: Context -> TermName -> Maybe InType
parseType ctx = \case 
  (TermNotion "Object") -> Just Object
  t@(TermNotion _) -> case Map.lookup t (typings ctx) of
    Just Sort -> Just $ Signature t
    _ -> Nothing
  _ -> Nothing

-- | Transform type predicates into types.
-- This needs to be seperate from finding types, since
-- the type predicates need to be deleted from the terms
-- and it is not allowed for a variable to have more than
-- one sort (which we check here).
extractGivenTypes :: Context -> Term (Const ()) t -> Term Identity t
extractGivenTypes ctx = snd . go
  where
    duplicateType a b = error $ 
      "A variable has been defined with multiple types: " ++ show a ++ " and " ++ show b

    go :: Term (Const ()) t -> (Map VarName InType, Term Identity t)
    go = \case
      Forall v (Const ()) t ->
        let (typings, t') = go t
        in (typings, Forall v (Identity $ Map.findWithDefault Object v typings) t')
      Exists v (Const ()) t ->
        let (typings, t') = go t
        in (typings, Exists v (Identity $ Map.findWithDefault Object v typings) t')
      App (OpTrm name) [Var v] -> case parseType ctx name of
        Just t -> (Map.insert v t mempty, App Top [])
        Nothing -> (mempty, App (OpTrm name) [Var v])
      App op args ->
        let res = map go args
            typings = Map.unionsWith duplicateType $ map fst res
            args' = map snd res
        in (typings, App op args')
      Tag tag t -> Tag tag <$> go t
      Var v -> (mempty, Var v)

coercibleInto :: Type -> Type -> Coercions TermName TermName -> Bool
coercibleInto smaller bigger coe = case (smaller, bigger) of
  (Sort, Sort) -> True
  (Pred is o, Pred is' o') ->
    let lenOk = length is == length is'
        outOk = case (o, o') of
          (Prop, Prop) -> True 
          (InType i, InType i') -> coercibleInto' i' i coe -- contravariant
          _ -> False
        inOk = all id $ zipWith (\a b -> coercibleInto' a b coe) is is'
    in lenOk && outOk && inOk
  _ -> False

coercibleInto' :: InType -> InType -> Coercions TermName TermName -> Bool
coercibleInto' smaller bigger coe = case (smaller, bigger) of
  (_, Object) -> True
  (Object, _) -> False -- because bigger != object
  (Signature s, Signature s') -> coercibleTo s s' coe

resolve :: HasCallStack => Context -> TermName -> Type -> (TermName, Type)
resolve (Context idents res _ coe _) name typ =
  let resolvedNames = Set.map (\a -> (a, idents Map.! a)) $ res Map.! name
      feasibleNames = Set.filter (\t -> coercibleInto typ (snd t) coe) resolvedNames
  in case Set.toList feasibleNames of
    [] -> error $ Text.unpack $ "Resolve failed: " <> pretty name <> " of type " <> pretty typ
    [x] -> x
    xs -> leastGeneral xs
  where
    leastGeneral [] = error "won't happen"
    leastGeneral [x] = x
    leastGeneral (x:y:xs) = if coercibleInto (snd x) (snd y) coe then leastGeneral (x:xs) else
      if coercibleInto (snd y) (snd x) coe then leastGeneral (y:xs) else
        error $ Text.unpack $ "Resolve ambigous: " <> pretty name <> " of type " <> pretty typ
          <> " can be resolved as " <> pretty x <> " or " <> pretty y <> "\n"
          <> "and none of them is more general than the other."

-- | Gather the possible types for variables.
-- We will store the explicit typings in the maybe and all implicit
-- typings from applications in the set. We assume all terms to be known
-- and applications to have the correct number of arguments 
-- (except for HeadTerms of course).
gatherTypes :: Context -> Term Identity Tag -> Term Identity Tag
gatherTypes c = snd . go Prop (preBoundVars c) 0
  where
    -- The context is the type that the surrounding context expects.
    -- It is defined in every case but equality statements where we
    -- use Nothing. Therefore Nothing => InType.
    -- The return type of functions needs a special variable here,
    -- numbered by d
    go context typings d = \case
      Forall v (Identity m) t -> case context of
        Prop -> Forall v (Identity m) <$> go Prop (Map.insert v m typings) d t
        _ -> error $ "Found a forall term where an object was expected"
      Exists v (Identity m) t -> case context of
        Prop -> Exists v (Identity m) <$> go Prop (Map.insert v m typings) d t
        _ -> error $ "Found an exists term where an object was expected"
      -- If we use a sort as a predicate aSort(x), we instead use ∃[v : aSort] v = x
      -- and add the coercion later.
      App (OpTrm name@(TermNotion _)) [arg] -> go Prop typings (d+1) 
        (Exists (VarF d) (Identity $ Signature name) (App Eq [Var (VarF d), arg]))
      App (OpTrm (TermNotion _)) _ -> error $ "Internal: we don't support THF yet."
      App (OpTrm name) args ->
        let (argtypes, args') = unzip $ map (go (InType Object) typings d) args
            argintypes = flip map argtypes $ \t -> case t of
              Prop -> error "An truth value cannot be passed to a function!"
              InType t' -> t'
        in case resolve c name (Pred argintypes context) of
              (name', Sort) -> 
                error $ "Illegal use of sort as predicate: " ++ show (App (OpTrm name') args') 
                  ++ " where an object was expected."
              (name', Pred _ t) -> (t, App (OpTrm name') args')
      App Eq [a, b] -> let res = map (go (InType Object) typings d) [a, b] 
        in (Prop, App Eq $ map snd res)
      App op args -> let res = map (go Prop typings d) args
        in (Prop, App op $ map snd res)
      -- predicate defintions: check that all args are variables
      Tag HeadTerm (App (OpTrm name) args) ->
        (context, Tag HeadTerm $ App (OpTrm name) 
          (map (\case Var v -> Var v; x -> error $ "Expected variable in definition but got: " ++ show x) args))
      -- function definitions; check that all args are variables
      Tag HeadTerm (App Eq [Var v0, App (OpTrm name) args]) ->
        (context, Tag HeadTerm $ App Eq [Var v0, App (OpTrm name) 
          (map (\case Var v -> Var v; x -> error $ "Expected variable in definition but got: " ++ show x) args)])
      Tag tag t -> Tag tag <$> go context typings d t
      Var v -> case context of
        Prop -> error $ "A variable " ++ show v ++ " may not appear as a proposition."
        InType Object -> case Map.lookup v typings of
          Nothing -> error $ "Unbound variable: " ++ show v
          Just t -> (InType t, Var v)
        InType _ -> error "Internal: We pass only Prop and InType Object as context."

coercionName :: TermName -> TermName -> TermName
coercionName (TermNotion n1) (TermNotion n2) = TermName $ n1 <> "_to_" <> n2
coercionName _ _ = error $ "Coercions only between notions"

-- | Extract definitions from a typed term.
-- This will find HeadTerms and add them as definitions,
-- as well as delete all HeadTerm Tags.
extractDefinitions :: HasCallStack => Term Identity Tag -> ([Stmt Identity ()], Term Identity Tag)
extractDefinitions = go mempty
  where
    go types = \case
      Forall v (Identity m) t -> simp <$> Forall v (Identity m) <$> go (Map.insert v m types) t
      Exists v (Identity m) t -> simp <$> Exists v (Identity m) <$> go (Map.insert v m types) t
      App op args -> let res = map (go types) args
        in (concatMap fst res, simp $ App op $ map snd res)
      -- sorts and predicate definitions
      Tag HeadTerm trm@(App (OpTrm name) args) -> case (name, args) of
        (TermNotion _, [Var v]) -> let t = case Map.lookup v types of
                                        (Just (Signature t')) -> [Coercion (coercionName name t') name t']
                                        _ -> []
           in ([IntroSort name] ++ t, App Top [])
        _ -> let ts = map (\case Var v -> types Map.! v; _ -> undefined) args
          in ([Predicate name ts Prop], simp $ trm)
      -- function definitions
      Tag HeadTerm trm@(App Eq [Var v0, App (OpTrm name) args]) ->
        let ts = map (\case Var v -> types Map.! v; _ -> undefined) args
        in ([Predicate name ts (InType $ types Map.! v0)], trm)
      Tag tag t -> Tag tag <$> simp <$> go types t
      Var v -> ([], Var v)

-- | Make sure that there are no tags left.
noTags :: Term Identity Tag -> Term Identity ()
noTags = go
  where
    go = \case
      Forall v m t -> Forall v m (go t)
      Exists v m t -> Exists v m (go t)
      App op args -> App op (go <$> args)
      Tag EqualityChain t -> go t
      Tag tag _ -> error $ "Remaining tag: " ++ show tag
      Var v -> Var v

-- | The full pipeline from formula to a terms.
typecheck :: Context -> Term (Const ()) Tag -> Term Identity Tag
typecheck ctx
  = traceReprId . gatherTypes ctx 
  . traceReprId . extractGivenTypes ctx 

-- | Convert a single line of a proof.
subClaim :: Context -> Block -> Proof
subClaim ctx (Block f b _ _ n l p _) = Located n p $
  let mainF = typecheck ctx $ parseFormula f 
  in Subclaim (noTags $ mainF) l (convertProof ctx b)

subClaims :: Context -> [Block] -> Maybe (Proof, [Block])
subClaims _ [] = Nothing
subClaims ctx (b:bs) = Just (subClaim ctx b, bs)

byContradiction :: Context -> [Block] -> Maybe (Proof, [Block])
byContradiction _ [] = Nothing
byContradiction ctx (b:bs) = case formula b of
  F.Not (F.Trm TermThesis [] _ _) ->
    let p = convertProof ctx (map ProofTextBlock bs)
    in Just (Located (name b) (position b) $ ByContradiction p, [])
  _ -> Nothing

preBind :: Map VarName InType -> Context -> Context
preBind vs ctx = ctx { preBoundVars = vs <> preBoundVars ctx }

chooses :: Context -> [Block] -> Maybe (Proof, [Block])
chooses _ [] = Nothing
chooses ctx (b:bs) = case kind b of
  Block.Selection ->
    let l = position b; n = name b
        vs = Set.map declName $ declaredVariables b
        f = noTags $ typecheck ctx
          $ bindExists (Set.toList vs) $ parseFormula (formula b)
        boundVs = Map.fromList $ concat $ flip List.unfoldr f $ \case
            Forall _ (Identity _) t -> Just ([], t)
            Exists v (Identity typ) t
              | v `Set.member` vs -> Just ([(v, typ)], t)
              | otherwise -> Just ([], t)
            _ -> Nothing
        p = convertProof (preBind boundVs ctx) (map ProofTextBlock bs)
    in Just $ (Located n l $ Choose (Map.toList boundVs) f (link b) p, [])
  _ -> Nothing

cases :: Context -> [Block] -> Maybe (Proof, [Block])
cases ctx = go Nothing
  where
    go _ [] = Nothing
    go m (b:bs) = case formula b of
      F.Imp (F.Tag CaseHypothesisTag c) (F.Trm TermThesis [] _ _) ->
        let c' = noTags $ typecheck ctx $ parseFormula c
            p' = convertProof ctx (body b)
            l' = (position b)
        in case m of
          Nothing -> go (Just (l', [(c', p')])) bs
          Just (l, ms) -> go (Just (l, (c', p'):ms)) bs
      _ -> case m of
        Nothing -> Nothing
        Just (l, ms) -> Just (Located "Cases" l $ Cases ms, b:bs)

-- | Convert a Proof. ... end. part
convertProof :: Context -> [ProofText] -> [Proof]
convertProof ctx = go . concatMap (\case ProofTextBlock b -> [b]; _ -> [])
  where
    go bs = flip List.unfoldr bs $ \bs -> 
      cases ctx bs <|> chooses ctx bs 
      <|> byContradiction ctx bs <|> subClaims ctx bs

-- | Get the blocks in a Prooftext.
getBlocks :: ProofText -> [Block]
getBlocks (ProofTextBlock b) = [b]
getBlocks (ProofTextRoot ts) = concatMap getBlocks ts
getBlocks p = error $ "Internal error: getBlocks received: " ++ show p

-- | Convert a block into a statement.
convertBlock :: Context -> Block -> [Statement]
convertBlock ctx bl@(Block f b _ _ n l p _) = Located n p <$>
  case f of
    -- top-level blocks:
    (F.Var (VarHole _) _ _) ->
      let (main:assms) = reverse $ concatMap getBlocks b
          mainF = foldr (F.Imp) (formula main) (formula <$> assms)
          (defs, mainT) = traceReprId $ extractDefinitions 
            $ typecheck ctx $ bindFree $ parseFormula mainF
          boundVars = Map.fromList $ flip List.unfoldr mainT $ \case
              Forall v (Identity typ) t -> Just ((v, typ), t)
              _ -> Nothing
      in case Block.needsProof bl of
        True -> if not (null defs)
          then error $ "Definitions in claim!"
          else [Claim (noTags mainT) l (convertProof (preBind boundVars ctx) (body main))]
        False -> case defs of
          -- (x:y:_) -> error $ "Multiple definitions: " ++ show [x, y]
          _ -> defs ++ if mainT == App Top [] then [] else [Axiom (noTags mainT)]
    _ -> error "convertBlock should not be applied to proofs!"

convert :: [ProofText] -> [Statement]
convert = go mempty . concatMap (\case ProofTextBlock bl -> [bl]; _ -> [])
  where
    go _ [] = []
    go c (b:bs) =
      let stmts = convertBlock c b
      in stmts ++ go (List.foldl' addStmt c stmts) bs

    addStmt (Context idents res nn coe pbv) (Located _ _ s) = case s of
      IntroSort n ->
        let n' = newName n res_n 
            res_n = Map.lookup n res
            res_n' = fromMaybe mempty res_n
        in Context (Map.insert n' Sort idents) (Map.insert n (Set.insert n' res_n') res) nn coe pbv
      Predicate n is o ->
        let n' = newName n res_n 
            res_n = Map.lookup n res
            res_n' = fromMaybe mempty res_n
        in Context (Map.insert n' (Pred is o) idents) (Map.insert n (Set.insert n' res_n') res) nn coe pbv
      Coercion n from to -> Context idents res nn (add (from, to) n coe) pbv
      _ -> Context idents res nn coe pbv