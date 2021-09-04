{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}

-- | Lean export
-- This converts the type-checked source to Lean expressions.
-- Currently it will fill 'sorry's at every point where a proof
-- step between two tactics is required. In the future, this should
-- be replaced with actual proof objects.
-- Similarly, we don't convert WfBlocks yet (and leave the work to Leans
-- simplifier which may fail where eprover didn't).

-- Confusingly, Lean has a built-in class type which is called "set".
-- See: https://github.com/leanprover-community/lean/blob/master/library/init/data/set.lean
-- It also supports a class syntax like Naproche which would make it a good target.
-- However, Naproches class syntax is more advanced and so we don't use it here.

module SAD.Core.Lean where

import Control.Monad
import Control.Monad.State
import SAD.Core.Typed
import SAD.Data.Identifier
import Data.Text.Prettyprint.Doc
import SAD.Core.Unique

data LeanState = LeanState
  { nextAxiomId :: Int
  , nextLemmaId :: Int
  } deriving (Eq, Show)

getAxiomId :: Lean (Doc ann)
getAxiomId = do
  s <- get
  put $ s { nextAxiomId = nextAxiomId s + 1 }
  pure $ "ax" <> pretty (nextAxiomId s)

getLemmaId :: Lean (Doc ann)
getLemmaId = do
  s <- get
  put $ s { nextLemmaId = nextLemmaId s + 1 }
  pure $ "lm" <> pretty (nextLemmaId s)

type Lean = State LeanState

class ExportLean a where
  toLean :: a -> Lean (Doc ann)

instance ExportLean Ident where
  toLean i = pure $ pretty $ case identifierAsTerm (uniqueIdentifier i) of
    "if" -> "if'"
    t -> t

instance ExportLean InType where
  toLean (Signature i)
    | i == identClass = pure "class'"
    | i == identSet = pure "set'"
    | otherwise = case identifierAsType (uniqueIdentifier i) of
      Just t -> pure $ pretty t
      Nothing -> error $ "Lean export: " <> show i <> " is not a type!"

instance ExportLean OutType where
  toLean Prop = pure "Prop"
  toLean (InType i) = toLean i

instance ExportLean Type where
  toLean Sort = pure "Type"
  toLean (Pred is o) = do
    is' <- mapM toLean is
    o' <- toLean o
    pure $ hsep $ punctuate "→" (is' ++ [o'])

instance ExportLean Operator where
  toLean And = pure "∧"
  toLean Or  = pure "∨"
  toLean Not = pure "¬"
  toLean Imp = pure "→"
  toLean Iff = pure "↔"
  toLean Top = pure "true"
  toLean Bot = pure "false"
  toLean Eq  = pure "="

instance ExportLean Term where
  toLean (Forall v m t) = do
    v' <- toLean v; m' <- toLean m; t' <- toLean t
    pure $ "∀(" <> v' <> " : " <> m' <> "), " <> t'
  toLean (Exists v m t) = do
    v' <- toLean v; m' <- toLean m; t' <- toLean t
    pure $ "∃(" <> v' <> " : " <> m' <> "), " <> t'
  toLean (App op []) = toLean op
  toLean (App op [a]) = do
    op' <- toLean op; a' <- toLean a
    pure $ "(" <> op' <+> a' <> ")"
  toLean (App op [a, b]) = do
    a' <- toLean a; op' <- toLean op; b' <- toLean b;
    pure $ "(" <> a' <+> op' <+> b' <> ")"
  toLean (App _ _) = error "Malformed App in Lean Export"
  toLean (AppWf op args _) | isSymbol op = do
    args' <- forM args $ \a -> case a of
     AppWf op _ _ | isSymbol op -> toLean a >>= \a -> pure $ "(" <> a <> ")"
     _ -> toLean a
    op' <- toLean op
    pure $ op' <+> hsep args'
  toLean (AppWf op args _) = do
    op' <- toLean op; args' <- mapM toLean args
    pure $ "(" <> op' <+> hsep args' <> ")"

mkImplicit :: (Ident, InType) -> Lean (Doc ann)
mkImplicit (i, t) = do
  i' <- toLean i; t' <- toLean t
  pure $ "{" <> i' <> " : " <> t' <> "}"

mkExplicit :: (Ident, InType) -> Lean (Doc ann)
mkExplicit (i, t) = do
  i' <- toLean i; t' <- toLean t
  pure $ "(" <> i' <> " : " <> t' <> ")"

mkAssumptions :: [Term] -> Lean (Doc ann)
mkAssumptions as = do
  fmap hsep $ forM (zip as [1::Int ..]) $ \(a, i) -> do
    a' <- toLean a
    pure $ "{ assm" <> pretty i <> " : " <> a' <> "}"

instance ExportLean Stmt where
  toLean (IntroSort tm) = do
    tm' <- toLean (Signature tm)
    pure $ "axiom " <> tm' <> " : Type"
  toLean (IntroAtom i ex as) = do
    i' <- toLean i;
    ex' <- mapM mkExplicit ex; as' <- mkAssumptions as;
    pure $ "axiom " <> i' <+> hsep ex' <+> as' <> " : Prop"
  toLean (IntroSignature i t ex as) = do
    i' <- toLean i;
    ex' <- mapM mkExplicit ex; as' <- mkAssumptions as; t' <- toLean t
    pure $ "axiom " <> i' <+> hsep ex' <+> as' <> " : " <> t'
  toLean (Predicate i (NFTerm ex as b)) = do
    i' <- toLean i;
    ex' <- mapM mkExplicit ex; as' <- mkAssumptions as; b' <- toLean b
    pure $ "def " <> i' <+> hsep ex' <+> as' <> " : Prop := " <> b'
  toLean (Function i t (NFTerm ex as b)) = do
    i' <- toLean i; t' <- toLean t
    ex' <- mapM mkExplicit ex; as' <- mkAssumptions as; b' <- toLean b
    pure $ "def " <> i' <+> hsep ex' <+> as' <> " : " <> t' <> " := " <> b'
  toLean (Axiom i (NFTerm ex as b)) = do
    i' <- toLean i;
    ex' <- mapM mkExplicit ex; as' <- mkAssumptions as; b' <- toLean b
    pure $ "axiom " <> i' <+> hsep ex' <+> as' <> " : " <> b'
  toLean (Claim i (NFTerm ex as b) _) = do
    i' <- toLean i;
    ex' <- mapM mkExplicit ex; as' <- mkAssumptions as; b' <- toLean b
    pure $ "lemma " <> i' <+> hsep ex' <+> as' <> " : " <> b' <> " := by sorry"

exportLean :: [Located Stmt] -> Doc ann
exportLean ls = vsep $ flip evalState (LeanState 1 1) $ mapM (toLean . located) ls