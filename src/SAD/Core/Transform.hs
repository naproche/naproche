{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ViewPatterns #-}

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
import Data.Bifunctor (bimap)

import SAD.Data.Formula (Formula, Tag(..))
import qualified SAD.Data.Formula as F
import SAD.Data.VarName
import SAD.Data.Text.Decl
import SAD.Data.Terms
import SAD.Core.SourcePos (noSourcePos)
import SAD.Data.Text.Block (ProofText(..), Block(..), position)
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
      F.Class (Decl v _ _) f -> Class v (Const ()) $ go (addVar v vars) f
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

-- | Bind free variables by forall quantifiers
-- and turn all bound variables into 'TermVar's.
bindFree :: Set VarName -> Term (Const ()) t -> Term (Const ()) t
bindFree bound t = bind $ findFree bound t
  where
    bind (vars, tr) = foldr (\v t -> Forall v (Const ()) t) tr $ Set.toList $ fvToVarSet $ vars

termify :: Set VarName -> Term f t -> Term f t
termify bound = snd . findFree bound

findFree :: Set VarName -> Term f t -> (FV VarName, Term f t)
findFree bound = free
  where
    free = \case
      Forall v f t -> bimap (bindVar v) (Forall v f) $ free t
      Exists v f t -> bimap (bindVar v) (Exists v f) $ free t
      Class  v f t -> bimap (bindVar v) (Class  v f) $ free t
      App op args -> bimap mconcat (App op) $ unzip $ free <$> args
      Tag tag t -> Tag tag <$> free t
      Var v -> if v `Set.member` bound 
        then (mempty, App (OpTrm (TermVar v)) [])
        else (unitFV v noSourcePos, Var v)

-- | Bind free variables by exists quantifiers.
bindExists :: [VarName] -> Term (Const ()) t -> Term (Const ()) t
bindExists vs tr = foldr (\v -> Exists v (Const ())) tr vs

-- | Given a list of defined sorts and a TermName,
-- decide if this is a sort.
parseType :: Context -> TermName -> Maybe InType
parseType ctx = \case 
  (TermNotion "Obj") -> Just Object
  t@(TermNotion _) -> case Map.lookup t (typings ctx) of
    Just Sort -> Just $ Signature t
    _ -> Nothing
  _ -> Nothing

-- | Transform type predicates into types.
-- This needs to be seperate from finding types, since
-- the type predicates need to be deleted from the terms
-- and it is not allowed for a variable to have more than
-- one sort (which we check here).
extractGivenTypes :: Context -> Term (Const ()) Tag -> Term Identity Tag
extractGivenTypes ctx = snd . go
  where
    -- TODO: This is not always evaluated to WHNF
    -- and so the error is sometimes not reported.
    duplicateType a b =
      if coercibleInto' a b (coercions ctx) then a else
      if coercibleInto' b a (coercions ctx) then b else
      error $ "A variable has been defined with multiple types: " ++ show a ++ " and " ++ show b

    go :: Term (Const ()) Tag -> (Map VarName InType, Term Identity Tag)
    go = \case
      Forall v (Const ()) t ->
        let (typings, t') = go t
        in (typings, Forall v (Identity $ Map.findWithDefault Object v typings) t')
      Exists v (Const ()) t ->
        let (typings, t') = go t
        in (typings, Exists v (Identity $ Map.findWithDefault Object v typings) t')
      Class v (Const ()) t ->
        let (typings, t') = go t
        in (typings, Class v (Identity $ Map.findWithDefault Object v typings) t')
      -- this hack allows for new coercions in a lemma or axiom
      -- if it is of the form "Let s be a from. Then s is a to."
      App Imp [App (OpTrm (parseType ctx -> Just from)) [Var v0], App (OpTrm name@(parseType ctx -> Just _)) [Var v1]]
        | v0 == v1 -> (Map.singleton v0 from, Tag CoercionTag $ App (OpTrm name) [Var v0])
      App (OpTrm name) [Var v] -> case parseType ctx name of
        Just t -> (Map.singleton v t, App Top [])
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
      Class v (Identity m) t -> case context of
        InType _ -> (InType $ Signature (TermNotion "Class"), Class v (Identity m) 
          $ snd $ go Prop (Map.insert v m typings) d t)
        Prop -> error $ "Found a class where a proposition was expected."
      -- If we use a sort as a predicate aSort(x), we instead use ∃[v : aSort] v = x
      -- and add the coercion later.
      App (OpTrm name@(TermNotion _)) [arg] -> go Prop typings (d+1) 
        (Exists (VarF d) (Identity $ Signature name) (App Eq [Var (VarF d), arg]))
      App (OpTrm name@(TermVar v)) args -> case (Map.lookup v typings, args) of
        (Nothing, _) -> error "Internal: Variable bound as term in a proof was not registered."
        (_, (_:_)) -> error "Internal: Variable bound as term can't be applied."
        (Just t, []) -> (InType t, App (OpTrm name) [])
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
      Class v (Identity m) t -> simp <$> Class v (Identity m) <$> go (Map.insert v m types) t
      App op args -> let res = map (go types) args
        in (concatMap fst res, simp $ App op $ map snd res)
      -- coercion definitions
      Tag CoercionTag trm@(Exists _ (Identity (Signature to)) (App Eq [_, Var v0])) -> case Map.lookup v0 types of
        (Just (Signature from)) -> ([Coercion (coercionName from to) from to], App Top [])
        _ -> ([], trm)
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
      Class v m t -> Class v m (go t)
      App op args -> App op (go <$> args)
      Tag Replacement t -> go t
      Tag EqualityChain t -> go t
      Tag tag _ -> error $ "Remaining tag: " ++ show tag
      Var v -> Var v

-- | The full pipeline from formula to a terms.
typecheck :: Context -> Term (Const ()) Tag -> Term Identity Tag
typecheck ctx
  = traceReprId . gatherTypes ctx 
  . traceReprId . extractGivenTypes ctx 

-- | A tactic takes the goal, the current context and a number of proof lines (Block)
-- and may translate some lines and give a new goal.
type Tactic = (Term Identity (), Context, [Block]) -> Maybe (Proof, (Term Identity (), Context, [Block]))

preBind :: Map VarName InType -> Context -> Context
preBind vs ctx = ctx { preBoundVars = vs <> preBoundVars ctx }

-- | Introduce top-level forall-bound variables in the term
-- and the conditions of if-terms as a tactic.
autoIntroAssume :: Tactic
autoIntroAssume (_, _, []) = Nothing
autoIntroAssume (goal, ctx, (b:bs)) = case goal of
    Forall v (Identity typ) t -> Just ((Located "intro" (position b) (Intro v typ)), (t, preBind (Map.singleton v typ) ctx, b:bs))
    App Imp [ass, goal'] -> Just ((Located "intro" (position b) (Assume $ termify (Map.keysSet $ preBoundVars ctx) ass)), (goal', ctx, b:bs))
    _ -> Nothing

-- | Convert a single line of a proof.
subClaim :: Context -> Block -> Proof
subClaim ctx bl@(Block f b _ _ n l _) = Located n (position bl) $
  let mainF = noTags $ typecheck ctx $ bindFree (Map.keysSet $ preBoundVars ctx) $ parseFormula f
  in Subclaim mainF (convertProof mainF l ctx b)

subClaims :: Tactic
subClaims (_, _, []) = Nothing
subClaims (goal, ctx, (b:bs)) = Just (subClaim ctx b, (goal, ctx, bs))

byContradiction :: Tactic
byContradiction (_, _, []) = Nothing
byContradiction (goal, ctx, (b:bs)) = case formula b of
  F.Not (F.Trm TermThesis [] _ _) ->
    Just (Located (name b) (position b) (ByContradiction goal), (App Bot [], ctx, bs))
  _ -> Nothing

chooses :: Tactic
chooses (_, _, []) = Nothing
chooses (goal, ctx, (b:bs)) = case kind b of
  Block.Selection ->
    let l = position b; n = name b
        vs = Set.map declName $ declaredVariables b
        f = noTags $ typecheck ctx $ bindFree (Map.keysSet $ preBoundVars ctx)
          $ bindExists (Set.toList vs) $ parseFormula (formula b)
        boundVs = Map.fromList $ concat $ flip List.unfoldr f $ \case
            Forall _ (Identity _) t -> Just ([], t)
            Exists v (Identity typ) t
              | v `Set.member` vs -> Just ([(v, typ)], t)
              | otherwise -> Just ([], t)
            _ -> Nothing
        p = convertProof f (link b) ctx (body b)
        ctx' = preBind boundVs ctx
    in Just $ (Located n l $ Choose (Map.toList boundVs) f p, (goal, ctx', bs))
  _ -> Nothing

cases :: Tactic
cases (goal, ctx, bs) = go Nothing bs
  where
    parseCase c b =
      let c' = noTags $ typecheck ctx $ bindFree (Map.keysSet $ preBoundVars ctx) $ parseFormula c
          p' = convertProof goal (link b) ctx (body b)
          l' = (position b)
      in (l', (c', p'))

    go Nothing [] = Nothing
    go (Just (l, ms)) [] = Just (Located "Cases" l $ TerminalCases ms, (goal, ctx, []))
    go m (b:bs) = case formula b of
      F.Imp (F.Tag CaseHypothesisTag c) (F.Trm TermThesis [] _ _) ->
        let (l', (c', p')) = parseCase c b
        in case m of
          Nothing -> go (Just (l', [(c', p')])) bs
          Just (l, ms) -> go (Just (l, (c', p'):ms)) bs
      _ -> case m of
        Nothing -> Nothing
        Just (l, ms) -> Just (Located "Cases" l $ Cases ms, (goal, ctx, b:bs))

-- | Convert a Proof. ... end. part
convertProof :: Term Identity () -> [Text] -> Context -> [ProofText] -> ProofBlock
convertProof goal links ctx pts =
  let ((goal', ctx', _), ps) = go $ concatMap (\case ProofTextBlock b -> [b]; _ -> []) pts
  in Proving ps (termify (Map.keysSet $ preBoundVars ctx') goal') links
  where
    go bs = unfold (goal, ctx, bs) $ \st ->
      autoIntroAssume st <|> cases st <|> chooses st
      <|> byContradiction st <|> subClaims st

    unfold b f = case f b of
      Just (a, b') -> (a:) <$> unfold b' f
      Nothing -> (b, [])

-- | Get the blocks in a Prooftext.
getBlocks :: ProofText -> [Block]
getBlocks (ProofTextBlock b) = [b]
getBlocks (ProofTextRoot ts) = concatMap getBlocks ts
getBlocks p = error $ "Internal error: getBlocks received: " ++ show p

-- | Convert a block into a statement.
convertBlock :: Context -> Block -> [Statement]
convertBlock ctx bl@(Block f b _ _ n l _) = Located n (position bl) <$>
  case f of
    -- top-level blocks:
    (F.Var (VarHole _) _ _) ->
      let (main:assms) = reverse $ concatMap getBlocks b
          mainF = foldr (F.Imp) (formula main) (formula <$> assms)
          (defs, mainT) = traceReprId $ extractDefinitions 
            $ typecheck ctx $ bindFree mempty $ parseFormula mainF
          mainT' = noTags $ mainT
      in case Block.needsProof bl of
        True -> if not (null defs)
          then error $ "Definitions in claim!"
          else [Claim mainT' $ (convertProof mainT' l ctx (body main))]
        False -> defs ++ 
          if mainT == App Top [] then [] else [Axiom (noTags mainT)]
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