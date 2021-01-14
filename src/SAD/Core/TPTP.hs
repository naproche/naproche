{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}

-- | Export a task to TPTP syntax.

module SAD.Core.TPTP (tptp) where

import Data.Text (Text)
import qualified Data.Text as Text
import Data.Functor.Identity
import Data.Hashable
import Data.Char

import SAD.Data.Terms
import SAD.Data.VarName
import SAD.Core.Pretty
import SAD.Core.Typed
import SAD.Core.Task
import SAD.Helpers (inParens)

class TPTP a where
  tptp :: a -> Text

instance TPTP TermName where
  tptp (TermSymbolic t) = "s" <> t
  tptp t = pretty t

instance TPTP VarName where
  tptp v = case Text.uncons (pretty v) of
    Nothing -> error $ "Empty variable!"
    Just (a, b) -> Text.cons (toUpper a) b

instance TPTP InType where
  tptp = \case
    Object -> "$i"
    Signature (TermNotion "Object") -> "$i"
    Signature (TermNotion "Int") -> "$int"
    Signature (TermNotion "Rat") -> "$rat"
    Signature (TermNotion "Real") -> "$real"
    Signature t -> tptp t

instance TPTP OutType where
  tptp = \case
    Prop -> "$o"
    InType t -> tptp t

instance TPTP Type where
  tptp = \case
    Sort -> "$tType"
    Pred [] t -> tptp t
    Pred ts t -> "(" <> Text.intercalate " * " (map tptp ts) <> ") > " <> tptp t

instance TPTP a => TPTP (Identity a) where
  tptp (Identity a) = tptp a

instance (f ~ Identity, t ~ ()) => TPTP (Term f t) where
  tptp = \case
    Forall v m t -> "! [" <> tptp v <> ": " <> tptp m <> "] : " <> tptp t
    Exists v m t -> "? [" <> tptp v <> ": " <> tptp m <> "] : " <> tptp t
    App And [a, b] -> "(" <> tptp a <> " & " <> tptp b <> ")"
    App Or  [a, b] -> "(" <> tptp a <> " | " <> tptp b <> ")"
    App Imp [a, b] -> "(" <> tptp a <> " => " <> tptp b <> ")"
    App Iff [a, b] -> "(" <> tptp a <> " <=> " <> tptp b <> ")"
    App Not [a] -> "(~ " <> tptp a <> ")"
    App Top [] -> "$true"
    App Bot [] -> "$false"
    App Eq [a, b] -> "(" <> tptp a <> " = " <> tptp b <> ")"
    App (OpTrm op) args -> tptp op <> inParens (map tptp args)
    a@(App _ _) -> error $ "Mismatched arguments in tptp generation: " ++ show a
    Tag () t -> tptp t
    Var v -> tptp v
    Class _ _ _ -> error "Class left in TPTP!"

tffStatement :: Text -> Text -> Text -> Text
tffStatement n typ inside =
  let h = hash inside
      name = if Text.null n then "m_" <> Text.pack (show (h * signum h)) else n
  in "tff(" <> name <> ", " <> typ <> ", (\n  " <> inside <> "))."

instance TPTP Hypothesis where
  tptp = \case
    Given name t -> tffStatement name "axiom" (tptp t)
    Typing name t -> tffStatement (tptp name) "type" (tptp name <> ": " <> tptp t)

-- | Desuger all classes in the hypothesis and conjecture.
-- We assume the hypothesis to be in reverse order.
desugerClasses' :: [Hypothesis] -> Term Identity () -> ([Hypothesis], Term Identity ())
desugerClasses' hs c =
  let (Given "conj" c' : hs') = go [TermName ("cls" <> Text.pack (show i)) | i <- [1::Int ..]] (Given "conj" c : hs)
  in (hs', c')
  where
    go _ [] = []
    go vars (h:hs) = case h of
      Given name t ->
        let ((vars', axs), t') = desugerClasses vars t
            clsType = InType (Signature (TermNotion "Class"))
        in Given name t' : (concatMap (\(tn@(TermName n), typ, t) -> [Given (n <> "_aux") t, Typing tn (Pred (map runIdentity typ) clsType)]) axs) ++ go vars' hs
      Typing name t -> Typing name t : go vars hs

instance TPTP Task where
  tptp (Task hypo conj _ name _ _) =
    let (hypo', conj') = desugerClasses' hypo conj
    in Text.unlines (map tptp (reverse hypo') ++ [tffStatement name "conjecture" (tptp conj')])