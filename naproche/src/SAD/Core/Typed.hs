{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module SAD.Core.Typed
 ( InType(..), OutType(..), Type(..), NFTerm(..)
 , Term(..), Located(..), Prf(..), WfBlock(..)
 , PrfBlock(..), Hypothesis(..), ClassInfo(..)
 , Stmt(..), Operator(..)
 , simp, bindAllExcept, findFree
 , termToNF, termFromNF, noWf
 ) where

import Data.Text (Text)
import Data.Set (Set)
import GHC.Generics (Generic)
import Data.Hashable (Hashable)
import Data.Binary (Binary)
import Data.Functor.Identity
import qualified Data.Set as Set
import Data.Functor.Const
import Control.DeepSeq (NFData)

import SAD.Helpers (tupled')
import SAD.Data.Identifier
import Data.Text.Prettyprint.Doc
import SAD.Core.SourcePos (SourcePos)

-- | Types that can be used as input in a TFF declaration 
newtype InType 
  = Signature Ident -- ^ introduced by signature
  deriving (Eq, Ord, Show, Read, Generic)
instance NFData InType
instance Hashable InType
instance Binary InType

-- | Types that can be used as output in a TFF declaration
-- except $tType since Sorts are handled seperately.
data OutType = Prop | InType !InType
  deriving (Eq, Ord, Show, Read, Generic)
instance NFData OutType
instance Hashable OutType
instance Binary OutType

-- | A type for a term in TFF.
data Type = Sort | Pred [InType] OutType
  deriving (Eq, Ord, Show, Read, Generic)
instance NFData Type
instance Hashable Type
instance Binary Type

-- | Built-in logical Operators
data Operator
  = And | Or | Not | Imp | Iff | Top | Bot | Eq
  deriving (Eq, Ord, Show, Read, Generic)
instance NFData Operator
instance Hashable Operator
instance Binary Operator

-- | This stores information that is important during the desugering of classes.
-- TODO: This corresponds to von Neumann Bernays Gödel set theory.
-- Is it also possible to support Morse-Kelley set theory in this framework?
data ClassInfo = ClassInfo
  { coerceElemsToObject :: [Ident]
  , classType :: !InType -- ^ class, set or something user defined
  , coerceClassTypeToClass :: [Ident]
  } deriving (Eq, Ord, Show, Generic)
instance NFData ClassInfo
instance Hashable ClassInfo
instance Binary ClassInfo

-- | An AST of typed first order form.
-- During the first parse we will have f = Const (),
-- then we might accumulate type information (f = [] or f = Set)
-- and when all types are resolved we have f = Identity
-- We start out with t = Tag and end up with t = () once all
-- tag information is processed.
data Term f t
  = Forall !Ident !(f InType) (Term f t)
  | Exists !Ident !(f InType) (Term f t)
  | FinClass !(f InType) !(f ClassInfo) [Term f t]
    -- ^ { t1 : type, t2, ... }
  | Class !Ident !(f InType) (Maybe (Term f t)) !(f ClassInfo) (Term f t)
    -- ^ { v : t "in" M | cond }
  | App !Operator [Term f t]
  | AppWf !Ident [Term f t] (WfBlock f t)
  | Tag !t (Term f t)
deriving instance (Eq (f InType), Eq t, Eq (f ClassInfo)) => Eq (Term f t)
deriving instance (Ord (f InType), Ord t, Ord (f ClassInfo)) => Ord (Term f t)
deriving instance (Show (f InType), Show t, Show (f ClassInfo)) => Show (Term f t)
deriving instance (Generic (f InType), Generic t) => Generic (Term f t)
instance (Generic (f InType), Generic t, Hashable (f InType), Hashable t, Generic (f ClassInfo), Hashable (f ClassInfo)) => Hashable (Term f t)
instance (Generic (f InType), Generic t, Binary (f InType), Binary t, Generic (f ClassInfo), Binary (f ClassInfo)) => Binary (Term f t)

-- | A term in normal form: A list of forall binders,
-- followed by some assumptions and the main body.
-- The forall bound variables should have pairwise different identifiers.
data NFTerm f t = NFTerm
  { nfImplicit :: [(Ident, f InType)]
  -- ^ implicit forall-bound variables.
  -- these could be unordered, but Map has no Hashable instance
  , nfExplicit :: [(Ident, f InType)]
  -- ^ explicit forall-bound variables.
  -- these should be ordered as they appear in the definition.
  , nfAssumptions :: [Term f t]
  , nfBody :: Term f t
  }
deriving instance (Eq (f InType), Eq t, Eq (f ClassInfo)) => Eq (NFTerm f t)
deriving instance (Ord (f InType), Ord t, Ord (f ClassInfo)) => Ord (NFTerm f t)
deriving instance (Show (f InType), Show t, Show (f ClassInfo)) => Show (NFTerm f t)
deriving instance (Generic (f InType), Generic t) => Generic (NFTerm f t)
instance (Generic (f InType), Generic t, Hashable (f InType), Hashable t, Generic (f ClassInfo), Hashable (f ClassInfo)) => Hashable (NFTerm f t)
instance (Generic (f InType), Generic t, Binary (f InType), Binary t, Generic (f ClassInfo), Binary (f ClassInfo)) => Binary (NFTerm f t)

-- | Information for the user: Name of a lemma/axiom/sort/.. and position.
data Located a = Located
  { locName :: !Text
  , locPos :: !SourcePos
  , located :: a
  } deriving (Eq, Ord, Show, Generic)
instance NFData a => NFData (Located a)
instance Binary a => Binary (Located a)
instance Hashable a => Hashable (Located a)

-- | A block in Naproche text can contain several statements:
-- The declaration of a notion, a predicate, axiom or claim.
-- For example, defining 'p(x) iff q' will yield a predicate (p : x -> Prop)
-- and an axiom 'p(x) iff q'.
-- Note that we don't check the term of the claim but only the proof block.
data Stmt f t
  = IntroSort !Ident -- ^ new types
  | IntroAtom !Ident [(Ident, f InType)] [(Ident, f InType)] [Term f t]
    -- ^ atoms with implicit and explicit arguments as well as assumptions
    -- but no body. Their semantics correspond to a predicate that may
    -- never be inlined.
  | IntroSignature !Ident (f InType) [(Ident, f InType)] [(Ident, f InType)] [Term f t]
    -- ^ functions with implicit and explicit arguments as well as assumptions
    -- but no body. Their "body" can be defined through axioms. These are
    -- dangerous, because one can introduce a contradiction through them.
  | Predicate !Ident (NFTerm f t)
    -- ^ predicate definitions: ident <=> nfBody
  | Function !Ident (f InType) (NFTerm f t)
    -- ^ function definitions: ident : type = nfBody
  | Axiom (NFTerm f t)
    -- ^ axioms in the text. At the moment nfExplicit is empty,
    -- but a future version could consider making some variables
    -- explicit, so they have to be provided when the axiom is used
    -- as a hint.
  | Claim (NFTerm f t) (PrfBlock f t)
    -- ^ lemma/theorem in the text. nfExplicit is empty, see above.
  | Coercion
    !Ident -- ^ name of coercion
    !Ident -- ^ from notion
    !Ident -- ^ to notion
deriving instance (Eq (f InType), Eq t, Eq (f ClassInfo)) => Eq (Stmt f t)
deriving instance (Ord (f InType), Ord t, Ord (f ClassInfo)) => Ord (Stmt f t)
deriving instance (Show (f InType), Show t, Show (f ClassInfo)) => Show (Stmt f t)
deriving instance (Generic (f InType), Generic t) => Generic (Stmt f t)
instance (Generic (f InType), Generic t, Hashable (f InType), Hashable t, Generic (f ClassInfo), Hashable (f ClassInfo)) => Hashable (Stmt f t)
instance (Generic (f InType), Generic t, Binary (f InType), Binary t, Generic (f ClassInfo), Binary (f ClassInfo)) => Binary (Stmt f t)

data WfBlock f t = WfBlock 
  { wfImplicits :: [(Ident, Term f t)]
    -- ^ give terms for some implicits
  , wfProof :: Maybe (NFTerm f t, PrfBlock f t)
    -- ^ A proof for the claim in the first argument (added during type-checking):
    --   Exists (implicits \ wfImplicits) st. assumptions
    -- After type-checking 'Nothing' means that nothing needs to be done.
  }
deriving instance (Eq (f InType), Eq t, Eq (f ClassInfo)) => Eq (WfBlock f t)
deriving instance (Ord (f InType), Ord t, Ord (f ClassInfo)) => Ord (WfBlock f t)
deriving instance (Show (f InType), Show t, Show (f ClassInfo)) => Show (WfBlock f t)
deriving instance (Generic (f InType), Generic t) => Generic (WfBlock f t)
instance (Generic (f InType), Generic t, Hashable (f InType), Hashable t, Generic (f ClassInfo), Hashable (f ClassInfo)) => Hashable (WfBlock f t)
instance (Generic (f InType), Generic t, Binary (f InType), Binary t, Generic (f ClassInfo), Binary (f ClassInfo)) => Binary (WfBlock f t)

noWf :: WfBlock f t
noWf = WfBlock [] Nothing

-- | A proof block. The first two tactics are given by users:
-- either supplying the names of useful theorems or giving a list of tactics.
-- The third is the result of type-checking tactics: Each tactic needs to
-- modify the goal and say what it's new hypotheses are.
-- The fourth is for once the tactics have been eva
data PrfBlock f t
  = ProofByHints [Text]
  -- ^ given by user: Names of axioms/theorems that may be helpful for the ATP
  -- should match the 'locName's given before.
  | ProofByTactics [Located (Prf f t)]
  -- ^ given by user: some tactics that should be run from left to right.
  | ProofByTCTactics [(Located (Prf Identity ()), Term Identity (), [Hypothesis])]
  -- ^ after type-checking: Each tactic includes its hypothesis and the next goal.
deriving instance (Eq (f InType), Eq t, Eq (f ClassInfo)) => Eq (PrfBlock f t)
deriving instance (Ord (f InType), Ord t, Ord (f ClassInfo)) => Ord (PrfBlock f t)
deriving instance (Show (f InType), Show t, Show (f ClassInfo)) => Show (PrfBlock f t)
deriving instance (Generic (f InType), Generic t) => Generic (PrfBlock f t)
instance (Generic (f InType), Generic t, Hashable (f InType), Hashable t, Generic (f ClassInfo), Hashable (f ClassInfo)) => Hashable (PrfBlock f t)
instance (Generic (f InType), Generic t, Binary (f InType), Binary t, Generic (f ClassInfo), Binary (f ClassInfo)) => Binary (PrfBlock f t)

-- | A proof consists of sub-claims that will be given directly to the ATP
-- and a number of tactics. Unlike in Lean, our Tactics need to be completely
-- predictable: They need to specify how they would like to change hypotheses
-- and goal during type-checking (before actually running the tactic).
-- This prevents us from using 'ring'-like tactics that try to reduce the goal
-- as much as possible. Instead you can only have a tactic that tries to reduce
-- the goal by a fixed amount (e.g. split all conjuncts, etc.). Of course,
-- a tactic can fail to actually deliver what was promised.
data Prf f t
  = Intro Ident (f InType)
  -- ^ Given goal = Forall i t goal', Intro i t make (i : t) an hypothesis
  -- and set the goal to goal'. During type-checking the type t will be
  -- ignored and set to match the type of i in the goal.
  | Assume (Term f t)
  -- ^ Given goal = (ass => goal'), make ass a hypothesis
  -- and set the goal to goal'
  | ByContradiction (Term f t)
  -- ^ prove the goal by contradiction (e.g. assume the negation and prove Bot)
  -- The argument is the negated goal. It will be inserted during type-checking.
  | Suffices (Term f t) (PrfBlock f t)
  -- ^ prove that term => goal and set term as the new goal.
  | Define Ident (f InType) (Term f t)
  -- ^ give a name for an expression (a value).
  | Subclaim (NFTerm f t) (PrfBlock f t)
  -- ^ a subclaim, also called 'have'
  -- the binders and assumptions of the NFTerm will be
  -- introduced/assumed automatically for the proof.
  | Choose [(Ident, f InType)] (Term f t) (PrfBlock f t)
  -- ^ choose variables such that the term holds
  | Cases [(Term f t, Term f t, PrfBlock f t)]
  -- ^ cases in the middle of a proof (with other tactics following this).
  -- Each triple consists of: case hypothesis, claim to be proven under the hypothesis, proof.
  -- The type-checking will also add all intermediary claims of the case block to the main claim.
  | TerminalCases [(Term f t, PrfBlock f t)]
  -- ^ cases at the end of a proof
  -- finishes the proof by proving the goal under each case hypothesis
  -- and then proving that the hypothesis cover all cases.
deriving instance (Eq (f InType), Eq t, Eq (f ClassInfo)) => Eq (Prf f t)
deriving instance (Ord (f InType), Ord t, Ord (f ClassInfo)) => Ord (Prf f t)
deriving instance (Show (f InType), Show t, Show (f ClassInfo)) => Show (Prf f t)
deriving instance (Generic (f InType), Generic t) => Generic (Prf f t)
instance (Generic (f InType), Generic t, Hashable (f InType), Hashable t, Generic (f ClassInfo), Hashable (f ClassInfo)) => Hashable (Prf f t)
instance (Generic (f InType), Generic t, Binary (f InType), Binary t, Generic (f ClassInfo), Binary (f ClassInfo)) => Binary (Prf f t)

-- | Hypothesis as they are given in TPTP format.
data Hypothesis
  = Given Text (Term Identity ())
  | Typing Ident Type
  deriving (Eq, Ord, Show, Generic)
instance Hashable Hypothesis
instance Binary Hypothesis

-- | Simplify a formula for nicer pretty-printing.
simp :: Term f t -> Term f t
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

-- | Term in NF, with no explicit binders
termToNF :: Term f t -> NFTerm f t
termToNF t =
  let (t', bs) = stripForall t
      (b , as) = stripAssms t'
  in NFTerm bs [] (filter (not . isTop) $ map simp as) b
  where
    stripForall = \case
      Forall i m t -> ((i, m):) <$> stripForall t
      b -> (b, []) 
    stripAssms = \case
      App Imp [a, b] -> (a:) <$> stripAssms b
      b -> (b, [])
    isTop (App Top []) = True
    isTop _ = False


termFromNF :: NFTerm f t -> Term f t
termFromNF (NFTerm im ex as b) = 
  foldr (\(i, t) -> Forall i t) (
    foldr (\(i, t) -> Forall i t) (
      foldr (\a b -> App Imp [a, b]) b as
    ) ex
  ) im

-- | Bind free variables by forall quantifiers
-- and turn all bound variables into 'TermVar's.
bindAllExcept :: Set Ident -> Term (Const ()) t -> Term (Const ()) t
bindAllExcept bound t = bind $ bindVarSet bound $ findFree t
  where
    bind vars = foldr (\v t -> Forall v (Const ()) t) t $ Set.toList $ fvToVarSet $ vars

-- | Find free variables
findFree :: Term f t -> FV
findFree = free
  where
    free = \case
      Forall v _ t -> bindVar v $ free t
      Exists v _ t -> bindVar v $ free t
      FinClass _ _ ts -> mconcat (free <$> ts)
      Class  v _ m _ t -> bindVar v $ free t <> maybe mempty (free) m
      AppWf v ex _ -> unitFV v <> mconcat (free <$> ex)
      App _ args -> mconcat $ free <$> args
      Tag _ t -> free t

instance Pretty a => Pretty (Set a) where
  pretty s = "{" <> hsep (punctuate comma $ map pretty $ Set.toList s) <> "}"

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

instance (Pretty (f InType), Show t, Show (f InType), Show (f ClassInfo)) 
  => Pretty (WfBlock f t) where
  pretty (WfBlock is prf) = case (is, prf) of
    ([], Nothing) -> ""
    (xs, Nothing) -> " (with: " <> hsep (punctuate comma $ map (\(i, t) -> pretty i <> "=" <> pretty t) xs) <> ")"
    ([], Just (_, prf)) -> " (wf. " <> pretty prf <> ")"
    (xs, Just (_, prf)) -> " (with: " <> hsep (punctuate comma $ map (\(i, t) -> pretty i <> "=" <> pretty t) xs) <> "; wf. " <> pretty prf <> ")"

instance (Pretty (f InType), Show t, Show (f InType), Show (f ClassInfo)) 
  => Pretty (Term f t) where
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
  pretty (AppWf op args wf) | isSymbol op = 
    let args' = flip map args $ \a -> case a of
          AppWf op _ _ | isSymbol op -> "(" <> pretty a <> ")"
          _ -> pretty a
    in prettyWithArgs op args' <> pretty wf
  pretty (AppWf op args wf) = pretty op <> tupled' (map pretty args) <> pretty wf
  pretty (Tag t tr) = "(" <> pretty (show t) <> " :: " <> pretty tr <> ")"
  pretty t = error $ "Malformed term: " ++ show t

instance (Pretty (f InType), Show t, Show (f InType), Show (f ClassInfo)) 
  => Pretty (NFTerm f t) where
  pretty (NFTerm im ex as b) =
    let implicit = case im of
          [] -> ""
          _ -> "∀{" <> hsep (punctuate ("," <> softline) (map (\(v, m) -> pretty v <+> ":" <+> pretty m) im)) <> "}"
        explicit = case ex of
          [] -> ""
          _ -> " ∀[" <> hsep (punctuate ("," <> softline) (map (\(v, m) -> pretty v <+> ":" <+> pretty m) ex)) <> "]"
        break d = case im ++ ex of
          [] -> d
          _ -> ": " <> nest 2 (line <> d)
        assumptions = case as of
          [] -> ""
          _ -> vsep (pretty <$> as) <> line
    in implicit <> explicit <> break (assumptions <> pretty b)

instance (Pretty (f InType), Show t, Show (f InType), Show (f ClassInfo)) 
  => Pretty (Stmt f t) where
  pretty (IntroSort tm) = "Sort: " <> pretty tm
  pretty (IntroAtom i im ex as) = "Predicate " <> pretty i <> ": " <> pretty (NFTerm im ex as (AppWf (NormalIdent "") [] noWf))
  pretty (IntroSignature i t im ex as) = "Function " <> pretty i <> ": "
    <> pretty (NFTerm im ex as (AppWf (NormalIdent "") [] noWf)) <> ": " <> pretty t
  pretty (Axiom t) = "Axiom: " <> pretty t
  pretty (Predicate t nf) = "Definition [" <> pretty t <> "]: " <> pretty nf
  pretty (Function t o nf) = "Definition [" <> pretty t <> " → " <> pretty o <> "]: " <> pretty nf
  pretty (Claim t prf) = "Claim: " <> pretty t <> pretty prf
  pretty (Coercion name from to) = "Coercion: " <> pretty name <> " : " 
    <> pretty from <> " → " <> pretty to

instance (Pretty (f InType), Show t, Show (f InType), Show (f ClassInfo))
  => Pretty (PrfBlock f t) where
  pretty (ProofByHints ls) = tupled' $ map pretty ls
  pretty (ProofByTactics prfs) = nest 4 $ line <>
    vsep (map (pretty . located) prfs)
  pretty (ProofByTCTactics prfs) = nest 4 $ line <>
    vsep (map (pretty . located . (\(a, _, _) -> a)) prfs)

instance Pretty Hypothesis where
  pretty (Given n t) = (pretty n) <> " : " <> pretty t
  pretty (Typing n t) = pretty n <> " : " <> pretty t

instance (Pretty (f InType), Show t, Show (f InType), Show (f ClassInfo))
  => Pretty (Prf f t) where
  pretty (Intro i t) = "Let " <> pretty i <> " : " <> pretty t
  pretty (Assume t) = "Assume that " <> pretty t
  pretty (Subclaim t prfs) = "We have: " <> pretty t <> " " <> pretty prfs
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
  pretty (Located t p a) = "[" <> pretty t <> "] " 
    <> pretty (show p) <> "\n" <> pretty a <> "\n"