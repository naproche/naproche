{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module SAD.Core.Typed
 ( InType(..), OutType(..), Type(..), NFTerm(..)
 , Term(..), Located(..), Prf(..), WfBlock(..)
 , Hypothesis(..)
 , Stmt(..), Operator(..)
 , simp, findFree
 , termToNF, termFromNF, subst, substAll
 ) where

import Data.Text (Text)
import Data.Set (Set)
import Data.Map (Map)
import GHC.Generics (Generic)
import Data.Hashable (Hashable)
import Data.Binary (Binary)
import qualified Data.Set as Set
import qualified Data.Map as Map
import Control.DeepSeq (NFData)

import SAD.Helpers (tupled')
import SAD.Data.Identifier
import Data.Text.Prettyprint.Doc
import SAD.Data.SourcePos (SourcePos)
import SAD.Core.Unique

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
data Type = Sort | Pred [InType] !OutType
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

-- | An AST of typed first order form.
data Term
  = Forall !Ident !InType Term
  | Exists !Ident !InType Term
  | App !Operator [Term]
  | AppWf !Ident [Term] WfBlock
  deriving (Eq, Ord, Show, Generic)
instance Hashable Term
instance Binary Term

-- | A term in normal form: A list of forall binders,
-- followed by some assumptions and the main body.
-- The forall bound variables should have pairwise different identifiers.
data NFTerm = NFTerm
  { nfArguments :: [(Ident, InType)]
  -- ^ explicit forall-bound variables.
  -- these should be ordered as they appear in the definition.
  , nfAssumptions :: [Term]
  , nfBody :: Term
  }
  deriving (Eq, Ord, Show, Generic)
instance Hashable NFTerm
instance Binary NFTerm

-- | Information for the user: Name of a lemma/axiom/sort/.. and position.
data Located a = Located
  { locPos :: !SourcePos
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
data Stmt
  = IntroSort !Ident -- ^ new types
  | IntroAtom !Ident [(Ident, InType)] [Term]
    -- ^ atoms with arguments as well as assumptions
    -- but no body. Their semantics correspond to a predicate that may
    -- never be inlined.
  | IntroSignature !Ident InType [(Ident, InType)] [Term]
    -- ^ functions with arguments as well as assumptions
    -- but no body. Their "body" can be defined through axioms. These are
    -- dangerous, because one can introduce a contradiction through them.
  | Predicate !Ident NFTerm
    -- ^ predicate definitions: ident <=> nfBody
  | Function !Ident InType NFTerm
    -- ^ function definitions: ident : type = nfBody
  | Axiom !Ident NFTerm
    -- ^ axioms in the text.
  | Claim !Ident NFTerm Prf
    -- ^ lemma/theorem in the text.
  deriving (Eq, Ord, Show, Generic)
instance Hashable Stmt
instance Binary Stmt

-- | Wellformed-ness proofs.
-- Contains a proof for the claim in the first argument
data WfBlock
  = NoWf
  | WfProof NFTerm Prf
  deriving (Eq, Ord, Show, Generic)
instance Hashable WfBlock
instance Binary WfBlock

data Prf
  = Prf [PrfStep] ClosingPrf
  deriving (Eq, Ord, Show, Generic)
instance Hashable Prf
instance Binary Prf

data PrfStep
  = Have Ident Term Bool Prf -- ^ name, proposition, may contain contradictory axioms, proof
  | Define Ident InType Term
  deriving (Eq, Ord, Show, Generic)
instance Hashable PrfStep
instance Binary PrfStep

data ClosingPrf
  = CallATP [Text] -- ^ hints
  | Trivial -- ^ The goal can be simplified to true or closed by an assumption.
  deriving (Eq, Ord, Show, Generic)
instance Hashable ClosingPrf
instance Binary ClosingPrf

-- | Hypothesis as they are given in TPTP format.
data Hypothesis
  = Given !Text Term
  | TypeDef !Ident Type
  deriving (Eq, Ord, Show, Generic)
instance Hashable Hypothesis
instance Binary Hypothesis

-- | Simplify a formula for nicer pretty-printing.
simp :: Term -> Term
simp = \case
  Forall v t tr -> Forall v t (simp tr)
  Exists v t tr -> Exists v t (simp tr)
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

-- | Find free variables
-- TODO: This will currently not look in WfBlocks!
findFree :: Term -> FV
findFree = free
  where
    free = \case
      Forall v _ t -> bindVar v $ free t
      Exists v _ t -> bindVar v $ free t
      AppWf v ex _ -> unitFV v <> mconcat (free <$> ex)
      App _ args -> mconcat $ free <$> args

-- | (x `subst` t1) t2 == t2[x := t1]
-- TODO: This will currently not substitute in WfBlocks!
subst :: Ident -> Term -> Term -> Term
subst x t1 = substAll (Map.fromList [(x, t1)])

-- | Simultaneous substitution of identifiers with terms.
substAll :: Map Ident Term -> Term -> Term
substAll subMap
  | Map.null subMap = id
  | otherwise = \case
  Forall v m t -> Forall v m $ substAll subMap t
  Exists v m t -> Exists v m $ substAll subMap t
  App op args -> App op (map (substAll subMap) args)
  AppWf v [] _ | Just t1 <- Map.lookup v subMap -> t1
  AppWf v ex wf -> AppWf v (map (substAll subMap) ex) wf

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

instance Pretty Prf where
  pretty (Prf steps close) = vsep (map pretty steps ++ [pretty close])

instance Pretty PrfStep where
  pretty (Have h t _ p) = "have " <> pretty h <> " : " <> pretty t <> " by " <> line <> nest 2 (pretty p)
  pretty (Define f t tt) = "define " <> pretty f <> " : " <> pretty t <> " = " <> pretty tt

instance Pretty ClosingPrf where
  pretty Trivial = "trivial."
  pretty (CallATP hints) = "by ATP (using: " <> pretty hints <> ")."

instance Pretty WfBlock where
  pretty NoWf = ""
  pretty (WfProof _ prf) = " (wf." <> pretty prf <> ")"

instance Pretty Term where
  pretty (Forall v t tr) = "(∀[" <> pretty v <+> ":"
    <+> pretty t <> "]" <> softline <> pretty tr <> ")"
  pretty (Exists v t tr) = "(∃[" <> pretty v <+> ":"
    <+> pretty t <> "]" <> softline <> pretty tr <> ")"
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

instance  Pretty Stmt where
  pretty (IntroSort tm) = "Sort: " <> pretty tm
  pretty (IntroAtom i ex as) = "Predicate " <> pretty i <> ": "
    <> pretty (NFTerm ex as (AppWf identEmpty [] NoWf))
  pretty (IntroSignature i t ex as) = "Function " <> pretty i <> ": "
    <> pretty (NFTerm ex as (AppWf identEmpty [] NoWf)) <> ": " <> pretty t
  pretty (Axiom i t) = "Axiom " <> pretty i <> ": " <> pretty t
  pretty (Predicate t nf) = "Definition [" <> pretty t <> "]: " <> pretty nf
  pretty (Function t o nf) = "Definition [" <> pretty t <> " → " <> pretty o <> "]: " <> pretty nf
  pretty (Claim i t prf) = "Claim " <> pretty i <> ": " <> pretty t <> pretty prf

instance Pretty Hypothesis where
  pretty (Given n t) = pretty n <> " : " <> pretty t
  pretty (TypeDef n t) = pretty n <> " : " <> pretty t

instance Pretty a => Pretty (Located a) where
  pretty (Located p a) = pretty (show p) <> "\n" <> pretty a <> "\n"