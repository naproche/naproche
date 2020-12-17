{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneDeriving #-}

module SAD.Core.Typed
 ( InType(..), OutType(..), Type(..)
 , Term(..), Proof, Located(..), Prf(..)
 , Statement, Stmt(..), Operator(..)
 , simp
 ) where

import Data.Text (Text)
import qualified Data.Text as Text
import Data.Functor.Identity

import SAD.Data.VarName
import SAD.Data.Terms
import SAD.Core.Pretty (Pretty(..))
import SAD.Core.SourcePos (SourcePos)
import SAD.Helpers (inParens)

-- | Types that can be used as input in a TFF declaration 
data InType 
  = Object -- ^ the base type of un-typed objects
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
-- Danger: We assume that except for OpTrm all constructors are logical operators
-- in the type checking!
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
    TermName -- ^ name of coercion
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
  | Intro [(VarName, InType)] (Term f t) [Proof]
  | Choose [(VarName, InType)] (Term f t) [Text] [Proof]
  | Cases [(Term f t, [Proof])]
  | ByContradiction [Proof]
deriving instance (Eq (f InType), Eq t) => Eq (Prf f t)
deriving instance (Ord (f InType), Ord t) => Ord (Prf f t)
deriving instance (Show (f InType), Show t) => Show (Prf f t)

type Proof = Located (Prf Identity ())

-- | Simplify a formula at the head for nicer pretty-printing.
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
  pretty (Coercion name from to) = "Coercion: " <> pretty name <> " : " 
    <> pretty from <> " → " <> pretty to

instance (Pretty (f InType), Show t, Show (f InType))
  => Pretty (Prf f t) where
  pretty (Subclaim t ls prfs) = pretty t <> " "
    <> inParens ls <> renderLines (map (pretty . located) prfs)
  pretty (Intro vs t prfs) = "Let: [" <> Text.intercalate ", " 
    (map (\(v, t) -> pretty v <> " : " <> pretty t) vs) <> 
    "] such that " <> pretty t <> renderLines ((pretty . located) <$> prfs)
  pretty (Choose vs t ls prfs) = "Choose: " <> Text.intercalate ", " 
    (map pretty vs) <> " " <> inParens ls <>
    " such that " <> pretty t <> renderLines ((pretty . located) <$> prfs)
  pretty (Cases cs) = Text.concat $
    map (\(t, p) -> "Case: " <> pretty t <> renderLines ((pretty . located) <$> p)) cs
  pretty (ByContradiction prfs) = "Assume not."
    <> renderLines (map (pretty . located) prfs)

instance Pretty a => Pretty (Located a) where
  pretty (Located t p a) = "[" <> t  <> "] " 
    <> Text.pack (show p) <> "\n" <> pretty a <> "\n"