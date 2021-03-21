{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}

-- | Export a task to TPTP syntax.

module SAD.Core.TPTP (ExportLang(..), tptp) where

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

data ExportLang = TF0 | FOF
  deriving (Eq, Ord, Show)

class TPTP a where
  tptp :: ExportLang -> a -> Text

instance TPTP TermName where
  tptp _ (TermSymbolic t) = "s" <> t
  tptp _ t = pretty t

instance TPTP VarName where
  tptp _ v = case Text.uncons (pretty v) of
    Nothing -> error $ "Empty variable!"
    Just (a, b) -> Text.cons (toUpper a) b

instance TPTP InType where
  tptp ex = \case
    Signature (TermNotion "Object") -> "$i"
    Signature (TermNotion "Int") -> "$int"
    Signature (TermNotion "Rat") -> "$rat"
    Signature (TermNotion "Real") -> "$real"
    Signature t -> tptp ex t

instance TPTP OutType where
  tptp ex = \case
    Prop -> "$o"
    InType t -> tptp ex t

instance TPTP Type where
  tptp ex = \case
    Sort -> "$tType"
    Object -> "$tType"
    Pred [] t -> tptp ex t
    Pred ts t -> "(" <> Text.intercalate " * " (map (tptp ex) ts) <> ") > " <> tptp ex t

instance TPTP a => TPTP (Identity a) where
  tptp ex (Identity a) = tptp ex a

instance (f ~ Identity, t ~ ()) => TPTP (Term f t) where
  tptp ex trm = case (ex, trm) of
    (TF0, Forall v m t) -> "! [" <> tptp ex v <> ": " <> tptp ex m <> "] : " <> tptp ex t
    (TF0, Exists v m t) -> "? [" <> tptp ex v <> ": " <> tptp ex m <> "] : " <> tptp ex t
    (FOF, Forall v (Identity (Signature m)) t) -> "! [" <> tptp ex v <> "] : " <> tptp ex (App Imp [App (OpTrm m) [Var v], t])
    (FOF, Exists v (Identity (Signature m)) t) -> "? [" <> tptp ex v <> "] : " <> tptp ex (App And [App (OpTrm m) [Var v], t])
    (_, App And [a, b]) -> "(" <> tptp ex a <> " & " <> tptp ex b <> ")"
    (_, App Or  [a, b]) -> "(" <> tptp ex a <> " | " <> tptp ex b <> ")"
    (_, App Imp [a, b]) -> "(" <> tptp ex a <> " => " <> tptp ex b <> ")"
    (_, App Iff [a, b]) -> "(" <> tptp ex a <> " <=> " <> tptp ex b <> ")"
    (_, App Not [a]) -> "(~ " <> tptp ex a <> ")"
    (_, App Top []) -> "$true"
    (_, App Bot []) -> "$false"
    (_, App Eq [a, b]) -> "(" <> tptp ex a <> " = " <> tptp ex b <> ")"
    (_, App (OpTrm op) args) -> tptp ex op <> inParens (map (tptp ex) args)
    (_, a@(App _ _)) -> error $ "Mismatched arguments in tptp generation: " ++ show a
    (_, Tag () t) -> tptp ex t
    (_, Var v) -> tptp ex v
    (_, Class _ _ _) -> error "Class left in TPTP!"

tffStatement :: ExportLang -> Text -> Text -> Text -> Text
tffStatement ex n typ inside =
  let h = hash inside
      name = if Text.null n || n == "__" then "m_" <> Text.pack (show (h * signum h)) else n
      prefix = case ex of TF0 -> "tff"; FOF -> "fof"
  in prefix <> "(" <> name <> ", " <> typ <> ", (\n  " <> inside <> "))."

instance TPTP Hypothesis where
  tptp ex = \case
      Given name t -> tffStatement ex name "axiom" (tptp ex t)
      Typing name t -> case ex of
        TF0 -> tffStatement ex (tptp ex name) "type" (tptp ex name <> ": " <> tptp ex t)
        FOF -> case t of
          Pred ts (InType (Signature intype)) -> tffStatement ex (tptp ex name) "axiom" $ tptp ex $
            let vars = flip zip ts $ map (VarDefault . Text.pack . ('x':) . show) [1::Int ..]
            in foldr (\(v, t) -> Forall v (Identity t)) (App (OpTrm intype) [App (OpTrm name) (map (Var . fst) vars)]) vars
          _ -> ""

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
  tptp ex (Task hypo conj _ name _ _) =
    let (hypo', conj') = desugerClasses' hypo conj
    in Text.unlines (map (tptp ex) (reverse hypo') ++ [tffStatement ex name "conjecture" (tptp ex conj')])