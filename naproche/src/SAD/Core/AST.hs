{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module SAD.Core.AST
 ( InType(..), OutType(..), ReturnValue(..), Type(..), NFTerm(..)
 , Term(..), Located(..), Prf(..), WfBlock(..)
 , PrfBlock(..), Hypothesis(..), ClassInfo(..)
 , Stmt(..), Operator(..), RIdent(..), RCoercion(..)
 , simp, bindAllExcept
 , termToNF, termFromNF, subst, substAll
 ) where

import Data.Text (Text)
import Data.Set (Set)
import Data.Map (Map)
import qualified Data.Set as Set
import qualified Data.Map as Map
import SAD.Data.Formula.Base (Tag)

import SAD.Helpers (tupled')
import SAD.Data.Identifier
import Data.Text.Prettyprint.Doc
import SAD.Data.SourcePos (SourcePos)

-- | Types that can be used as input in a TFF declaration 
newtype InType
  = Signature Ident -- ^ introduced by signature
  deriving (Eq, Ord, Show, Read)

-- | Types that can be used as output in a TFF declaration
-- except $tType since Sorts are handled seperately.
data OutType = Prop | InType !(Set InType)
  deriving (Eq, Ord, Show, Read)

-- | For type-checking: OutType without specifying a concrete type.
data ReturnValue = Value | Proposition
  deriving (Eq, Ord, Show)

-- | A type for a term in TFF.
data Type = Sort | Pred ![Set InType] !OutType
  deriving (Eq, Ord, Show, Read)

-- | Built-in logical Operators
data Operator
  = And | Or | Not | Imp | Iff | Top | Bot | Eq
  deriving (Eq, Ord, Show, Read)

-- | An identifier which is either resolved or not.
-- This enables re-checking blocks: When the block has
-- already been checked the resolved names appear like this:
data RIdent
  = Resolved   !Ident
  | Unresolved !Identifier
  deriving (Eq, Ord, Show)

-- | A resolved coercion. Give each requested type a list of
-- coercions that will be inserted as well as the type from which
-- this sequence of coercions starts.
newtype RCoercion = RCoercion
  { fromRCoercion :: Map InType (InType, [Ident])
  } deriving (Eq, Ord, Show, Semigroup, Monoid)

-- | This stores information that is important during the desugering of classes.
data ClassInfo = ClassInfo
  { coerceElemsToObject :: !RCoercion
  , classType :: !(Set InType) -- ^ class, set or something user defined
  , coerceClassTypeToClass :: !RCoercion
  } deriving (Eq, Ord, Show)

-- | An AST of typed first order form.
data Term
  = Forall !Ident !(Set InType) Term
  | Exists !Ident !(Set InType) Term
  | FinClass !(Set InType) !(Maybe ClassInfo) [Term]
    -- ^ { t1 : type, t2, ... }
  | Class !Ident !(Set InType) !(Maybe Term) !(Maybe ClassInfo) Term
    -- ^ { v : t "in" M | cond }
  | App !Operator [Term]
  | AppWf !RIdent [Term] !WfBlock
  | Coe !RCoercion Term
    -- ^ give the coercions to every type needed as the result
  | Typing !InType Term
    -- ^ posit that the term has a certain type
  | Tag !Tag Term
  deriving (Eq, Ord, Show)

-- | A term in normal form: A list of forall binders,
-- followed by some assumptions and the main body.
-- The forall bound variables should have pairwise different identifiers.
data NFTerm = NFTerm
  { nfArguments :: [(Ident, Set InType)]
  -- ^ explicit forall-bound variables.
  -- these should be ordered as they appear in the definition.
  , nfAssumptions :: [Term]
  , nfBody :: Term
  }
  deriving (Eq, Ord, Show)

-- | Attach a position to a value.
data Located a = Located
  { locPos :: !SourcePos
  , located :: a
  } deriving (Eq, Ord, Show)

-- | A block in Naproche text can contain several statements:
-- The declaration of a notion, a predicate, axiom or claim.
-- For example, defining 'p(x) iff q' will yield a predicate (p : x -> Prop)
-- and an axiom 'p(x) iff q'.
-- Note that we don't check the term of the claim but only the proof block.
data Stmt
  = IntroSort !Ident -- ^ new types
  | IntroAtom !Ident [(Ident, Set InType)] [Term]
    -- ^ atoms with arguments as well as assumptions
    -- but no body. Their semantics correspond to a predicate that may
    -- never be inlined.
  | IntroSignature !Ident (Set InType) [(Ident, Set InType)] [Term]
    -- ^ functions with arguments as well as assumptions
    -- but no body. Their "body" can be defined through axioms. These are
    -- dangerous, because one can introduce a contradiction through them.
  | Predicate !Ident NFTerm
    -- ^ predicate definitions: ident <=> nfBody
  | Function !Ident (Set InType) NFTerm
    -- ^ function definitions: ident : type = nfBody
  | Axiom !Ident NFTerm
    -- ^ axioms in the text.
  | Claim !Ident NFTerm PrfBlock
    -- ^ lemma/theorem in the text.
  | Coercion
    !Ident -- ^ name of coercion
    !Ident -- ^ from notion
    !Ident -- ^ to notion
  deriving (Eq, Ord, Show)

-- | Wellformed-ness proofs. Initially these are 'NoWf'.
-- Typechecking will either insert 'WellFormed' if no proof is necessary
-- or 'WfProof' if a proof is necessary.
-- With parser support, it should be possible for users to supply proofs.
data WfBlock
  = WellFormed -- ^ No proof necessary.
  | NoWf -- ^ If no proof was given.
  | WfProof NFTerm PrfBlock
    -- ^ A proof for the claim in the first argument (added during type-checking)
  deriving (Eq, Ord, Show)

-- | A proof block. The first two tactics are given by users:
-- either supplying the names of useful theorems or giving a list of tactics.
-- The third is the result of type-checking tactics: Each tactic needs to
-- modify the goal and say what it's new hypotheses are.
-- The fourth is for once the tactics have been evaluated.
data PrfBlock
  = ProofByHints [Text]
  -- ^ given by user: Names of axioms/theorems that may be helpful for the ATP
  -- should match the 'locName's given before.
  | ProofByTactics [Located Prf]
  -- ^ given by user: some tactics that should be run from left to right.
  | ProofByTCTactics [(Located Prf, Term, [Hypothesis])]
  -- ^ after type-checking: Each tactic includes its hypothesis and the next goal.
  deriving (Eq, Ord, Show)

-- | A proof consists of sub-claims that will be given directly to the ATP
-- and a number of tactics. Unlike in Lean, our Tactics need to be completely
-- predictable: They need to specify how they would like to change hypotheses
-- and goal during type-checking (before actually running the tactic).
-- This prevents us from using 'ring'-like tactics that try to reduce the goal
-- as much as possible. Instead you can only have a tactic that tries to reduce
-- the goal by a fixed amount (e.g. split all conjuncts, etc.). Of course,
-- a tactic can fail to actually deliver what was promised.
-- Be aware though that the goal during type-checking may differ from the goal
-- when running the tactic in that classes are desugered in-between!
data Prf
  = Intro Ident (Set InType)
  -- ^ Given goal = Forall i t goal', Intro i t make (i : t) an hypothesis
  -- and set the goal to goal'. During type-checking the type t will be
  -- ignored and set to match the type of i in the goal.
  | Assume Term
  -- ^ Given goal = (ass => goal'), make ass a hypothesis
  -- and set the goal to goal'
  | AssumeTC Term
  -- ^ Given goal = (ass => goal'), make ass a hypothesis
  -- and set the goal to goal'. This version is for internal uses
  -- and assumes that the given term was already type-checked.
  | ByContradiction Term
  -- ^ prove the goal by contradiction (e.g. assume the negation and prove Bot)
  -- The argument is the negated goal. It will be inserted during type-checking.
  | Suffices Term PrfBlock
  -- ^ prove that term => goal and set term as the new goal.
  | Define Ident (Set InType) Term
  -- ^ give a name for an expression (a value).
  | Subclaim !Ident NFTerm PrfBlock
  -- ^ a subclaim, also called 'have'
  -- the binders and assumptions of the NFTerm will be
  -- introduced/assumed automatically for the proof.
  | Choose [(Ident, Set InType)] Term PrfBlock
  -- ^ choose variables such that the term holds
  | Cases [(Term, Term, PrfBlock)]
  -- ^ cases in the middle of a proof (with other tactics following this).
  -- Each triple consists of: case hypothesis, claim to be proven under the hypothesis, proof.
  -- The type-checking will also add all intermediary claims of the case block to the main claim.
  | TerminalCases [(Term, PrfBlock)]
  -- ^ cases at the end of a proof
  -- finishes the proof by proving the goal under each case hypothesis
  -- and then proving that the hypothesis cover all cases.
  deriving (Eq, Ord, Show)

-- | Hypothesis as they are given in TPTP format.
data Hypothesis
  = Given !Ident Term
  | TypeDef !Ident Type
  deriving (Eq, Ord, Show)

-- | Simplify a formula for nicer pretty-printing.
simp :: Term -> Term
simp = \case
  Forall v t tr -> Forall v t (simp tr)
  Exists v t tr -> Exists v t (simp tr)
  Class v m k ci tr -> Class v m k ci (simp tr)
  App And [App Top [], b] -> simp b
  App And [a, App Top []] -> simp a
  App And [App Bot [], _] -> App Bot []
  App And [_, App Bot []] -> App Bot []
  App Or  [App Top [], _] -> App Top []
  App Or  [_, App Top []] -> App Top []
  App Or  [App Bot [], b] -> simp b
  App Or  [a, App Bot []] -> simp a
  App Imp [App Top [], b] -> simp b
  App Imp [_, App Top []] -> App Top []
  App Imp [App Bot [], _] -> App Top []
  App Imp [a, App Bot []] -> simp $ App Not [a]
  App Iff [App Top [], b] -> simp b
  App Iff [a, App Top []] -> simp a
  App Iff [App Bot [], b] -> simp $ App Not [b]
  App Iff [a, App Bot []] -> simp $ App Not [a]
  App Not [App Not [a]] -> simp a
  Tag t a -> Tag t $ simp a
  t -> t

-- | Term in NF
termToNF :: Term -> NFTerm
termToNF t =
  let (t', bs) = stripForall t
      (b , as) = stripAssms t'
  in NFTerm bs (filter (not . isTop) $ map simp as) b
  where
    stripForall = \case
      Forall i m t -> ((i, m):) <$> stripForall t
      b -> (b, [])
    stripAssms = \case
      App Imp [a, b] -> (a:) <$> stripAssms b
      b -> (b, [])
    isTop (App Top []) = True
    isTop _ = False

termFromNF :: NFTerm -> Term
termFromNF (NFTerm ex as b) =
  foldr (uncurry Forall) (
    foldr (\a b -> App Imp [a, b]) b as
  ) ex

-- | Bind free variables by forall quantifiers
-- and turn all bound variables into 'TermVar's.
bindAllExcept :: Set Ident -> Term -> Term
bindAllExcept bound t = bind $ bindVarSet bound $ findFree t
  where
    bind vars = foldr (`Forall` mempty) t $ Set.toList $ fvToVarSet vars

-- | Find free variables
-- TODO: This will currently not look in WfBlocks!
findFree :: Term -> FV
findFree = free
  where
    free = \case
      Forall v _ t -> bindVar v $ free t
      Exists v _ t -> bindVar v $ free t
      FinClass _ _ ts -> mconcat (free <$> ts)
      Class  v _ m _ t -> bindVar v $ free t <> maybe mempty free m
      AppWf (Resolved v) ex _ -> unitFV v <> mconcat (free <$> ex)
      AppWf (Unresolved _) ex _ -> mconcat (free <$> ex)
      App _ args -> mconcat $ free <$> args
      Coe _ t -> free t
      Typing _ t -> free t
      Tag _ t -> free t

-- | (x `subst` t1) t2 == t2[x := t1]
-- TODO: This will currently not substitute in WfBlocks!
subst :: Ident -> Term -> Term -> Term
subst x t1 = substAll (Map.fromList [(x, t1)])

-- | Simultaneous substitution of identifiers with terms.
substAll :: Map Ident Term -> Term -> Term
substAll subMap
  | Map.null subMap = id
  | otherwise = \case
    Forall v m t -> Forall v m $ substAll (Map.delete v subMap) t
    Exists v m t -> Exists v m $ substAll (Map.delete v subMap) t
    FinClass m ci ts -> FinClass m ci (map (substAll subMap) ts)
    Class v m mm ci t -> Class v m (substAll subMap <$> mm) ci
      $ substAll (Map.delete v subMap) t
    App op args -> App op (map (substAll subMap) args)
    Coe cs t -> Coe cs $ substAll subMap t
    Typing ty t -> Typing ty $ substAll subMap t
    Tag tag t -> Tag tag (substAll subMap t)
    AppWf (Resolved v) [] _ | Just t1 <- Map.lookup v subMap -> t1
    AppWf v ex wf -> AppWf v (map (substAll subMap) ex) wf

instance Pretty a => Pretty (Set a) where
  pretty s = case Set.toList s of
    [] -> "∅"
    [s] -> pretty s
    s -> "{" <> hsep (punctuate comma $ map pretty s) <> "}"

instance Pretty InType where
  pretty (Signature t) = pretty t

instance Pretty OutType where
  pretty (InType t) = pretty t
  pretty Prop = "Prop"

instance Pretty Type where
  pretty Sort = "Sort"
  pretty (Pred [] t) = pretty t
  pretty (Pred is t) =
    encloseSep "" "" " → " (map pretty is ++ [pretty t])

instance Pretty WfBlock where
  pretty WellFormed = ""
  pretty NoWf = ""
  pretty (WfProof _ prf) = " (wf." <> pretty prf <> ")"

instance Pretty RIdent where
  pretty (Resolved i) = pretty i
  pretty (Unresolved i) = pretty i

instance Pretty RCoercion where
  pretty (RCoercion m) = tupled' $
    map (\(to, (from, cs)) -> pretty from <> " used as " <> pretty to) $ Map.toList m

instance Pretty Term where
  pretty (Forall v t tr) = "(∀[" <> pretty v <+> ":"
    <+> pretty t <> "]" <> softline <> pretty tr <> ")"
  pretty (Exists v t tr) = "(∃[" <> pretty v <+> ":"
    <+> pretty t <> "]" <> softline <> pretty tr <> ")"
  pretty (FinClass _ _ []) = "{}"
  pretty (FinClass _ _ ts) = "{ " <> hsep (punctuate comma $ map pretty ts) <> " }"
  pretty (Class v t Nothing _ tr) = "{" <+> pretty v <+> ":"
    <+> pretty t <> " | " <> pretty tr <> " }"
  pretty (Class v t (Just m) _ tr) = "{ (" <> pretty v <+> ":"
    <+> pretty t <> ") in " <> pretty m <> " | " <> pretty tr <> " }"
  pretty (App And [a, b]) = "(" <> pretty a <> softline <> "and " <> pretty b <> ")"
  pretty (App Or  [a, b]) = "(" <> pretty a <> softline <> "or " <> pretty b <> ")"
  pretty (App Iff [a, b]) = "(" <> pretty a <> softline <> "iff " <> pretty b <> ")"
  pretty (App Imp [a, b]) = "(" <> pretty a <> softline <> "implies " <> pretty b <> ")"
  pretty (App Eq  [a, b]) = "(" <> pretty a <> softline <> "= " <> pretty b <> ")"
  pretty (App Not [a]) = "(not " <> pretty a <> ")"
  pretty (App Top []) = "true"
  pretty (App Bot []) = "false"
  pretty (AppWf op [] wf) = pretty op <> pretty wf
  pretty (AppWf (Resolved op) args wf) | isSymbol op =
    let args' = flip map args $ \a -> case a of
          AppWf (Resolved op) _ _ | isSymbol op -> "(" <> pretty a <> ")"
          _ -> pretty a
    in prettyWithArgs op args' <> pretty wf
  pretty (AppWf op args wf) = pretty op <> tupled' (map pretty args) <> pretty wf
  pretty (Typing tt t) = "(" <> pretty t <> " : " <> pretty tt <> ")"
  pretty (Coe (RCoercion m) t) = if nonTrivial m then "↑" <> pretty t <+> pretty (RCoercion m) else pretty t
    where nonTrivial m = any (\(_, (_, cs)) -> not $ null cs) $ Map.toList m
  pretty (Tag t tr) = "(" <> pretty (show t) <> " :: " <> pretty tr <> ")"
  pretty t = error $ "Malformed term: " ++ show t

instance Pretty NFTerm where
  pretty (NFTerm ex as b) =
    let explicit = case ex of
          [] -> ""
          _ -> " ∀[" <> hsep (punctuate ("," <> softline) (map (\(v, m) -> pretty v <+> ":" <+> pretty m) ex)) <> "]"
        break d = case ex of
          [] -> d
          _ -> ": " <> nest 2 (line <> d)
        assumptions = case as of
          [] -> ""
          _ -> vsep (pretty <$> as) <> line
    in explicit <> break (assumptions <> pretty b)

instance Pretty Stmt where
  pretty (IntroSort tm) = "Sort: " <> pretty tm
  pretty (IntroAtom i ex as) = "Predicate " <> pretty i <> ": "
    <> pretty (NFTerm ex as (AppWf (Unresolved identifierEmpty) [] NoWf))
  pretty (IntroSignature i t ex as) = "Function " <> pretty i <> ": "
    <> pretty (NFTerm ex as (AppWf (Unresolved identifierEmpty) [] NoWf)) <> ": " <> pretty t
  pretty (Axiom i t) = "Axiom " <> pretty i <> ": " <> pretty t
  pretty (Predicate t nf) = "Definition [" <> pretty t <> "]: " <> pretty nf
  pretty (Function t o nf) = "Definition [" <> pretty t <> " → " <> pretty o <> "]: " <> pretty nf
  pretty (Claim i t prf) = "Claim " <> pretty i <> ": " <> pretty t <> pretty prf
  pretty (Coercion name from to) = "Coercion " <> pretty name <> " : "
    <> pretty from <> " → " <> pretty to

instance Pretty PrfBlock where
  pretty (ProofByHints ls) = tupled' $ map pretty ls
  pretty (ProofByTactics prfs) = nest 4 $ line <>
    vsep (map (pretty . located) prfs)
  pretty (ProofByTCTactics prfs) = nest 4 $ line <>
    vsep (map (pretty . located . (\(a, _, _) -> a)) prfs)

instance Pretty Hypothesis where
  pretty (Given n t) = pretty n <> " : " <> pretty t
  pretty (TypeDef n t) = pretty n <> " : " <> pretty t

instance Pretty Prf where
  pretty (Intro i t) = "Let " <> pretty i <> " : " <> pretty t
  pretty (Assume t) = "Assume that " <> pretty t
  pretty (AssumeTC t) = "Assume that " <> pretty t
  pretty (Subclaim i t prfs) = "We have " <> pretty i <> ": " <> pretty t <> " " <> pretty prfs
  pretty (Choose vs t prfs) = "Choose: "
    <> tupled' (map (\(x, t) -> pretty x <> " : " <> pretty t) vs)
    <> " such that " <> nest 2 (pretty t) <> pretty prfs
  pretty (Define n tt t) = "Define: " <> pretty n <> " : " <> pretty tt <> " = " <> pretty t
  pretty (Cases cs) = vsep $
    map (\(t, c, p) -> case c of
      App Top [] -> "Case: " <> nest 2 (pretty t) <> pretty p
      _ -> "Case: " <> nest 2 (pretty t <> " => " <> pretty c) <> pretty p) cs
  pretty (TerminalCases cs) = vsep $
    map (\(t, p) -> "Case: " <> nest 2 (pretty t) <> pretty p) cs
  pretty (ByContradiction _) = "Assume the contrary."
  pretty (Suffices t prf) = "It suffices to show: " <> pretty t <> pretty prf

instance Pretty a => Pretty (Located a) where
  pretty (Located p a) = pretty (show p) <> "\n" <> pretty a <> "\n"