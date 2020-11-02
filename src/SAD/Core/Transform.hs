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

module SAD.Core.Transform where

import Data.Text (Text)
import qualified Data.Text as Text
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Functor.Const
import Data.Functor.Identity
import Data.Functor.Product
import Control.DeepSeq (rnf)
import Data.Maybe

import SAD.Data.Formula (Formula, Tag(..))
import qualified SAD.Data.Formula as F
import SAD.Data.VarName
import SAD.Data.Text.Decl
import SAD.Data.Terms
import SAD.Core.SourcePos (SourcePos, noSourcePos)
import SAD.Data.Text.Block (ProofText(..), Block(..))
import qualified SAD.Data.Text.Block as Block
import SAD.Core.Pretty (Pretty(..))

import Debug.Trace

-- | If you encounter a weird error, this may help
-- with debugging it. You need to import Debug.Trace
traceReprId :: Pretty a => a -> a
traceReprId a = a -- trace (Text.unpack (pretty a)) a

-- | Types that can be used as input in a TFF declaration 
data InType 
  = Object -- ^ the base type of un-typed objects
  | Real | Rat | Int -- ^ number types with special support in TPTP
  | Signature TermName -- ^ introduced by signature
  deriving (Eq, Ord, Show, Read)

-- | Types that can be used as output in a TFF declaration
-- except $tType since Sorts are handled seperately.
data OutType = Prop | InType InType
  deriving (Eq, Ord, Show, Read)

-- | A type for a term in TFF.
data Type = Sort | Pred [InType] OutType
  deriving (Eq, Ord, Show, Read)

-- | Operators, both built-in and user-defined.
-- This does not yet include numerical operators with special support
-- in tff like '$sum'. Applications will be checked to have the correct
-- number of correctly typed arguments.
data Operator
  = And | Or | Not | Imp | Iff | Top | Bot | Eq
  | OpTrm TermName
  deriving (Eq, Ord, Show, Read)

-- | An AST of typed first order form.
-- During the first parse we will have f = Const (),
-- then we might accumulate type information (f = [] or f = Set)
-- and when all types are resolved we have f = Identity
-- We start out with t = Tag and end up with t = () once all
-- tag information is processed.
data Term f t
  = Forall VarName (f InType) (Term f t)
  | Exists VarName (f InType) (Term f t)
  | App Operator [Term f t]
  | Tag t (Term f t)
  | Var VarName
deriving instance (Eq (f InType), Eq t) => Eq (Term f t)
deriving instance (Ord (f InType), Ord t) => Ord (Term f t)
deriving instance (Show (f InType), Show t) => Show (Term f t)
deriving instance (Read (f InType), Read t) => Read (Term f t)

-- | Information for the user: Name of a lemma/axiom/sort/.. and position.
data Located a = Located
  { locName :: Text
  , locPos :: SourcePos
  , located :: a
  } deriving (Eq, Ord, Show)

-- | A block in Naproche text can contain several statements:
-- The declaration of a notion, a predicate, axiom or claim.
-- For example, defining 'p(x) iff q' will yield a predicate (p : x -> Prop)
-- and an axiom 'p(x) iff q'.
-- In a future version, coercions between sorts will be added.
data Stmt f t
  = IntroSort TermName
  | Predicate TermName 
    [InType] -- ^ the types of the arguments
    OutType -- ^ the return type
  | Axiom (Term f t)
  | Claim (Term f t) 
    [Text] -- ^ links: theorems that may be useful for proving this claim
    [Located (Prf f t)] -- ^ the proof
  | Coercion 
    TermName -- ^ from notion
    TermName -- ^ to notion
deriving instance (Eq (f InType), Eq t) => Eq (Stmt f t)
deriving instance (Ord (f InType), Ord t) => Ord (Stmt f t)
deriving instance (Show (f InType), Show t) => Show (Stmt f t)

type Statement = Located (Stmt Identity ())

-- | A proof consists of sub-claims that will be given directly to the ATP
-- and a number of tactics.
data Prf f t
  = Subclaim (Term f t) [Text] [Proof]
  | Intro [(VarName, InType)] (Term f t)
  | Use Text
  | Cases [(Term f t, [Proof])]
deriving instance (Eq (f InType), Eq t) => Eq (Prf f t)
deriving instance (Ord (f InType), Ord t) => Ord (Prf f t)
deriving instance (Show (f InType), Show t) => Show (Prf f t)

type Proof = Located (Prf Identity ())

instance Pretty InType where
  pretty (Signature t) = pretty t
  pretty t = Text.pack $ show t

instance Pretty OutType where
  pretty (InType t) = pretty t
  pretty Prop = "Prop"

instance Pretty Type where
  pretty Sort = "Sort"
  pretty (Pred [] t) = pretty t
  pretty (Pred is t) = 
    Text.intercalate " → " (map pretty is) <> " → " <> pretty t

inParens :: [Text] -> Text
inParens [] = ""
inParens xs = "(" <> Text.intercalate ", " xs <> ")"

-- | TODO: This approach is not nice for nested indentations.
renderLines :: [Text] -> Text
renderLines [] = ""
renderLines xs = Text.unlines ("":map ("  " <>) xs)

instance (Pretty (f InType), Show t, Show (f InType)) 
  => Pretty (Term f t) where
  pretty (Forall v t tr) = "∀[" <> pretty v <> " : " 
    <> pretty t <> "] " <> pretty tr
  pretty (Exists v t tr) = "∃[" <> pretty v <> " : " 
    <> pretty t <> "] " <> pretty tr
  pretty (App And [a, b]) = "(" <> pretty a <> " and " <> pretty b <> ")"
  pretty (App Or  [a, b]) = "(" <> pretty a <> " or " <> pretty b <> ")"
  pretty (App Iff [a, b]) = "(" <> pretty a <> " iff " <> pretty b <> ")"
  pretty (App Imp [a, b]) = "(" <> pretty a <> " implies " <> pretty b <> ")"
  pretty (App Eq  [a, b]) = "(" <> pretty a <> " = " <> pretty b <> ")"
  pretty (App Not [a]) = "(not " <> pretty a <> ")"
  pretty (App Top []) = "true"
  pretty (App Bot []) = "false"
  pretty (App (OpTrm (TermSymbolic s)) args) = 
    decode s $ flip map args $ \a -> case a of
      App (OpTrm (TermSymbolic _)) _ -> "(" <> pretty a <> ")"
      _ -> pretty a
  pretty (App (OpTrm op) args) = pretty op  <> inParens (map pretty args) 
  pretty (Var v) = pretty v
  pretty (Tag t tr) = "(" <> Text.pack (show t) <> " :: " <> pretty tr <> ")"
  pretty t = error $ "Malformed term: " ++ show t

instance (Pretty (f InType), Show t, Show (f InType)) 
  => Pretty (Stmt f t) where
  pretty (IntroSort tm) = "Sort: " <> pretty tm
  pretty (Predicate tm [] t) = pretty tm <> " : " <> pretty t
  pretty (Predicate tm ts t) = pretty tm <> " : "
    <> Text.intercalate " → " (map pretty ts) <> " → " <> pretty t
  pretty (Axiom t) = "Axiom: " <> pretty t
  pretty (Claim t ls prfs) = "Claim: " <> pretty t <> " "
    <> inParens ls <> renderLines (map (pretty . located) prfs)
  pretty (Coercion from to) = "Coercion: " <> pretty from 
    <> " to " <> pretty to

instance (Pretty (f InType), Show t, Show (f InType))
  => Pretty (Prf f t) where
  pretty (Subclaim t ls prfs) = pretty t <> " "
    <> inParens ls <> renderLines (map (pretty . located) prfs)
  pretty (Intro vs t) = "Let: [" <> Text.intercalate ", " 
    (map (\(v, t) -> pretty v <> " : " <> pretty t) vs) <> 
    "] such that " <> pretty t
  pretty (Use t) = "Use: " <> t
  pretty (Cases cs) = Text.concat $
    map (\(t, p) -> "Case: " <> pretty t <> renderLines (pretty <$> p)) cs

instance Pretty a => Pretty (Located a) where
  pretty (Located t p a) = "[" <> t  <> "] " 
    <> Text.pack (show p) <> "\n" <> pretty a <> "\n"

-- | Simplify a formula at the head for nicer pretty -printing.
simp :: Term f t -> Term f t
simp = \case
  Forall v t tr -> case simp tr of
    App Top [] -> App Top []
    App Bot [] -> App Bot []
    tr' -> Forall v t tr'
  Exists v t tr -> case simp tr of
    App Top [] -> App Top []
    App Bot [] -> App Bot []
    tr' -> Exists v t tr'
  App And [App Top [], b] -> b
  App And [a, App Top []] -> a
  App And [App Bot [], _] -> App Bot []
  App And [_, App Bot []] -> App Bot []
  App Or  [App Top [], _] -> App Top []
  App Or  [_, App Top []] -> App Top []
  App Or  [App Bot [], b] -> b
  App Or  [a, App Bot []] -> a
  App Imp [App Top [], b] -> b
  App Imp [_, App Top []] -> App Top []
  App Imp [App Bot [], _] -> App Top []
  App Imp [a, App Bot []] -> simp $ App Not [a]
  App Iff [App Top [], b] -> b
  App Iff [a, App Top []] -> a
  App Iff [App Bot [], b] -> simp $ App Not [b]
  App Iff [a, App Bot []] -> simp $ App Not [a]
  App Not [App Not [a]] -> a
  Tag t a -> Tag t $ simp a
  t -> t

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

bindFree :: (VarName -> Term (Const ()) t -> Term (Const ()) t)
  -> Term (Const ()) t -> Term (Const ()) t
bindFree bindV t = bind (Set.toList $ fvToVarSet $ free t) t
  where
    bind vars tr = foldr (\v t -> bindV v t) tr vars

    free = \case
      Forall v (Const ()) t -> bindVar v $ free t
      Exists v (Const ()) t -> bindVar v $ free t
      App _ args -> mconcat $ free <$> args
      Tag _ t -> free t
      Var v -> unitFV v noSourcePos

-- | Bind free variables by forall quantifiers.
bindFreeForall :: Term (Const ()) t -> Term (Const ()) t
bindFreeForall = bindFree (\v t -> Forall v (Const ()) t)

-- | Bind free variables by exists quantifiers.
bindFreeExists :: Term (Const ()) t -> Term (Const ()) t
bindFreeExists = bindFree (\v t -> Forall v (Const ()) t)

-- | Given a list of defined sorts and a TermName,
-- decide if this is a sort.
parseType :: Map TermName Type -> TermName -> Maybe InType
parseType idents = \case 
  (TermNotion "Int") -> Just Int
  (TermNotion "Rat") -> Just Rat
  (TermNotion "Real") -> Just Real
  (TermNotion "Object") -> Just Object
  t@(TermNotion _) -> case Map.lookup t idents of
    Just Sort -> Just $ Signature t
    _ -> Nothing
  _ -> Nothing

-- | Transform type predicates into types.
-- This needs to be seperate from finding types, since
-- the type predicates need to be deleted from the terms
-- and it is not allowed for a variable to have more than
-- one sort (which we check here).
extractGivenTypes :: Map TermName Type -> Term (Const ()) t -> Term Maybe t
extractGivenTypes idents = snd . go
  where
    duplicateType a b = error $ 
      "A variable has been defined with multiple types: " ++ show a ++ " and " ++ show b

    go :: Term (Const ()) t -> (Map VarName InType, Term Maybe t)
    go = \case
      Forall v (Const ()) t ->
        let (typings, t') = go t
        in (typings, Forall v (Map.lookup v typings) t')
      Exists v (Const ()) t ->
        let (typings, t') = go t
        in (typings, Exists v (Map.lookup v typings) t')
      App (OpTrm name) [Var v] -> case parseType idents name of
        Just t -> (Map.insert v t mempty, App Top [])
        Nothing -> (mempty, App (OpTrm name) [Var v])
      App op args ->
        let res = map go args
            typings = Map.unionsWith duplicateType $ map fst res
            args' = map snd res
        in (typings, App op args')
      Tag tag t -> Tag tag <$> go t
      Var v -> (mempty, Var v)

-- | Check that all occuring terms have been defined previously
-- and with correct number of arguments. This will not be checked
-- for HeadTerms of course, which we require to only contain variables.
checkTermsKnown :: Map TermName Type -> Term f Tag -> ()
checkTermsKnown idents = go
  where 
    go = \case
      Forall _ _ t -> go t
      Exists _ _ t -> go t
      App (OpTrm name) args -> case Map.lookup name idents of
        Just Sort -> error $ "A sort may not be used as a predicate!"
        Just (Pred ts _) -> if length ts /= length args then
          error $ "Term was defined with a wrong number of arguments: "
            ++ "The predicate " ++ show name ++ " expects " ++ show (length ts)
            ++ " but got " ++ show (length args)
          else rnf $ map go args
        Nothing -> error $ "Unknown term: " ++ show name
      App _ args -> rnf $ map go args
      Tag HeadTerm (App (OpTrm _) args) -> 
        let nonVarArgs = filter (\case Var _ -> True; _ -> False) args
        in if null nonVarArgs then () else error $ "A definition can only refer to variables."
      Tag _ t -> go t
      Var _ -> ()

-- | Gather the possible types for variables.
-- We will store the explicit typings in the maybe and all implicit
-- typings from applications in the set. We assume all terms to be known
-- and applications to have the correct number of arguments 
-- (except for HeadTerms of course).
gatherTypes :: Map TermName Type -> Term Maybe Tag -> Term (Product Maybe Set) Tag
gatherTypes idents = snd . go (Just Prop) 0
  where
    -- The context is the type that the surrounding context expects.
    -- It is defined in every case but equality statements where we
    -- use Nothing. Therefore Nothing => InType.
    -- The return type of functions needs a special variable here,
    -- numbered by d
    go context d = \case
      Forall v m t -> case context of
        Just Prop -> 
          let (typings, t') = go (Just Prop) d t 
          in (typings, Forall v (Pair m (Map.findWithDefault mempty v typings)) t')
        _ -> error $ "Found a forall term, even though the context assumes a term of type " ++ show context
      Exists v m t -> case context of
        Just Prop -> 
          let (typings, t') = go (Just Prop) d t 
          in (typings, Exists v (Pair m (Map.findWithDefault mempty v typings)) t')
        _ -> error $ "Found an exists term, even though the context assumes a term of type " ++ show context
      App (OpTrm name) args -> case Map.lookup name idents of
        Just Sort -> case (context, args) of
          -- If we use a sort as a predicate aSort(x), we instead use ∃[v : aSort] v = x
          -- and add the coercion later.
          (Just Prop, [arg]) -> go (Just Prop) (d+1) 
            (Exists (VarF d) (Just $ Signature name) (App Eq [Var (VarF d), arg]))
          _ -> error $ "Illegal use of sort as predicate: " ++ show (App (OpTrm name) args) 
            ++ " in context " ++ show context
        Just (Pred ts t) -> if isJust context && context /= (Just t) then
          error $ "Mismatched types: The return type of " ++ show name ++ " is " ++ show t
            ++ " but the surrounding context assumes " ++ show context
          else let res = zipWith (\t' a -> go (Just $ InType t') d a) ts args
          in (Map.unionsWith (<>) $ map fst res, App (OpTrm name) $ map snd res)
        Nothing -> error $ "Undefined identifier: " ++ show name
      App Eq [a, b] -> let res = map (go Nothing d) [a, b] 
        in (Map.unionsWith (<>) $ map fst res, App Eq $ map snd res)
      App op args -> let res = map (go (Just Prop) d) args
        in (Map.unionsWith (<>) $ map fst res, App op $ map snd res)
      -- predicate defintions: check that all args are variables
      Tag HeadTerm (App (OpTrm name) args) ->
        (mempty, Tag HeadTerm $ App (OpTrm name) (map (\case Var v -> Var v; _ -> undefined) args))
      -- function definitions; check that all args are variables
      Tag HeadTerm (App Eq [Var v0, App (OpTrm name) args]) ->
        (mempty, Tag HeadTerm $ App Eq [Var v0, App (OpTrm name) 
          (map (\case Var v -> Var v; _ -> undefined) args)])
      Tag tag t -> Tag tag <$> go context d t
      Var v -> case context of
        Just Prop -> error $ "A variable " ++ show v ++ " may not be of type Prop."
        Just (InType t) -> (Map.insert v (Set.singleton t) mempty, Var v)
        Nothing -> (mempty, Var v)

-- | Merge types or fail if that is not possible.
-- In the future this should be implemented by using coercions,
-- but for now we will only check that all possible types are equal.
mergeTypes :: Term (Product Maybe Set) Tag -> Term Identity Tag
mergeTypes = go
  where
    go = \case
      Forall v m t -> Forall v (Identity $ merge m) (go t)
      Exists v m t -> Exists v (Identity $ merge m) (go t)
      App op args -> App op (map go args)
      Tag tag t -> Tag tag (go t)
      Var v -> Var v

    merge (Pair (Just t) ts) = if Set.null (Set.filter (/=t) ts)
      then t else error $ "Multiple types for var of type " ++ show t ++ ": " ++ show ts
    merge (Pair Nothing ts) = case Set.toList ts of
      [] -> Object
      [t] -> t
      ts -> error $ "Multiple types for var: " ++ show ts

-- | Extract definitions from a typed term.
-- This will find HeadTerms and add them as definitions,
-- as well as delete all HeadTerm Tags.
extractDefinitions :: Term Identity Tag -> ([Stmt Identity ()], Term Identity Tag)
extractDefinitions = go mempty
  where
    go types = \case
      Forall v (Identity m) t -> simp <$> Forall v (Identity m) <$> go (Map.insert v m types) t
      Exists v (Identity m) t -> simp <$> Exists v (Identity m) <$> go (Map.insert v m types) t
      App op args -> let res = map (go types) args
        in (concatMap fst res, simp $ App op $ map snd res)
      -- sorts and predicate definitions
      Tag HeadTerm trm@(App (OpTrm name) args) -> case (name, args) of
        (TermNotion _, [Var _]) -> ([IntroSort name], App Top [])
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
      Tag tag _ -> error $ "Remaining tag: " ++ show tag
      Var v -> Var v

-- | The full pipeline from formula to a terms.
typecheck :: Map TermName Type -> Term (Const ()) Tag -> Term Identity Tag
typecheck idents
  = traceReprId . mergeTypes . traceReprId . gatherTypes idents 
  . traceReprId . extractGivenTypes idents 

-- | Convert a single line of a proof.
convertProofBlock :: Map TermName Type -> Block -> Proof
convertProofBlock idents (Block f b _ _ n l p _) = Located n p $
  let mainF = typecheck idents $ parseFormula f 
  in case mainF of
    _ -> Subclaim (noTags $ mainF) l (convertProof idents b)

gatherCases :: Map TermName Type -> [Block] -> [Either Proof Block]
gatherCases idents = go Nothing
  where
    go _ [] = []
    go m (b:bs) = case formula b of
      F.Imp (F.Tag CaseHypothesisTag c) (F.Trm TermThesis [] _ _) ->
        let c' = noTags $ typecheck idents $ parseFormula c
            p' = convertProof idents (body b)
            l' = (position b)
        in case m of
          Nothing -> go (Just (l', [(c', p')])) bs
          Just (l, ms) -> go (Just (l, (c', p'):ms)) bs
      _ -> case m of
        Nothing -> Right b : go Nothing bs
        Just (l, ms) -> Left (Located "Cases" l $ Cases ms) : Right b : go Nothing bs

-- | Convert a Proof. ... end. part to a proof.
convertProof :: Map TermName Type -> [ProofText] -> [Proof]
convertProof idents = map go . gatherCases idents
  . concatMap (\case ProofTextBlock b -> [b]; _ -> [])
  where
    go = \case
      Left p -> p
      Right b -> convertProofBlock idents b

-- | Get the blocks in a Prooftext.
getBlocks :: ProofText -> [Block]
getBlocks (ProofTextBlock b) = [b]
getBlocks (ProofTextRoot ts) = concatMap getBlocks ts
getBlocks p = error $ "Internal error: getBlocks received: " ++ show p

-- | Convert a block into a statement.
convertBlock :: Map TermName Type -> Block -> [Statement]
convertBlock idents bl@(Block f b _ _ n l p _) = Located n p <$>
  case f of
    -- top-level blocks:
    (F.Var (VarHole _) _ _) ->
      let (main:assms) = reverse $ concatMap getBlocks b
          mainF = foldr (F.Imp) (formula main) (formula <$> assms)
          (defs, mainT) = traceReprId $ extractDefinitions 
            $ typecheck idents $ bindFreeForall $ parseFormula mainF
      in case Block.needsProof bl of
        True -> if not (null defs)
          then error $ "Definitions in claim!"
          else [Claim (noTags mainT) l (convertProof idents (body main))] -- TODO
        False -> case defs of
          (x:y:_) -> error $ "Multiple definitions: " ++ show [x, y]
          _ -> defs ++ [Axiom (noTags mainT)]
    _ -> error "convertBlock should not be applied to proofs!"

convert :: [ProofText] -> [Statement]
convert = go mempty . concatMap (\case ProofTextBlock bl -> [bl]; _ -> [])
  where
    go _ [] = []
    go idents (b:bs) =
      let stmts = convertBlock idents b
      in stmts ++ go (addTypes idents stmts) bs

    addTypes idents [] = idents
    addTypes idents ((Located _ _ s):ss) = case s of
      IntroSort n -> addTypes (Map.insert n Sort idents) ss
      Predicate n ts t -> addTypes (Map.insert n (Pred ts t) idents) ss
      _ -> addTypes idents ss