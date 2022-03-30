{-# LANGUAGE OverloadedStrings #-}

module SAD.Structures.Export where

import SAD.Structures.Type (Expr(..), Decl(..), Constr(..))

import Data.Text.Lazy (Text, intercalate)

class Exportable e where
  export :: e -> Text

instance (Exportable e) => Exportable [e] where
  export :: [e] -> Text
  export es = intercalate "\n" (export `fmap` es)

instance Exportable Decl where
  export :: Decl -> Text
  export = \case
    Axiom name e ->
      "axiom " <> name <> " : " <> export e <> "\n"
    Def name Hole e ->
      "def " <> name <> " :=\n  " <> export e <> "\n"
    Def name ty e ->
      "def " <> name <> " : " <> export ty <> " :=\n  " <> export e <> "\n"
    Theorem name ty e ->
      "theorem " <> name <> " : " <> export ty <> " :=\n  " <> export e <> "\n"
    Inductive name ty constrs ->
      "inductive " <> name <> " : " <> export ty <> "\n"
      <> intercalate "\n" (fmap export constrs)
      <> "\nopen " <> name <> "\n"
    Subtype ty subty ->
      "axiom is" <> subty <> " : " <> ty <> " → Prop\nnotation  `" <> subty <> "` := {x : "
      <> ty <> " // is" <> subty <> " x}\n"

instance Exportable Constr where
  export :: Constr -> Text
  export (Constr constr e) = "| " <> constr <> " : " <> export e

instance Exportable Expr where
  export :: Expr -> Text
  export = \case

    Const c -> c
    Variable v -> v
    Hole -> "_"
    Top -> "true"
    Bot -> "false"
    Omit -> "omitted"

    Const c :@ Variable v1 :@ Variable v2 -> c <> " " <> v1 <> " " <> v2
    Const c :@ Variable v -> c <> " " <> v
    Const c :@ e2 -> c <> " (" <> export e2 <> ")"
    e1 :@ e2 -> "(" <> export e1 <> ") (" <> export e2 <> ")"

    Pi a ty e     -> "(Π " <> a <> " : " <> export ty <> ", " <> export e <> ")"

    All a1 ty1 a@(All a2 ty2 (All a3 ty3 (All a4 ty4 (All a5 ty5 (All a6 ty6 e))))) -> if ty1 == ty2 && ty2 == ty3 && ty3 == ty4 && ty4 == ty5 && ty5 == ty6
      then "∀ " <> a1 <> " " <> a2 <> " " <> a3 <> " " <> a4 <> " " <> a5 <> " " <> a6 <> " : " <> export ty1 <> ", " <> export e
      else "∀ " <> a1 <> " : " <> export ty1 <> ", " <> export a
    All a1 ty1 a@(All a2 ty2 (All a3 ty3 (All a4 ty4 (All a5 ty5 e)))) -> if ty1 == ty2 && ty2 == ty3 && ty3 == ty4 && ty4 == ty5
      then "∀ " <> a1 <> " " <> a2 <> " " <> a3 <> " " <> a4 <> " " <> a5 <>" : " <> export ty1 <> ", " <> export e
      else "∀ " <> a1 <> " : " <> export ty1 <> ", " <> export a
    All a1 ty1 a@(All a2 ty2 (All a3 ty3 (All a4 ty4 e))) -> if ty1 == ty2 && ty2 == ty3 && ty3 == ty4
      then "∀ " <> a1 <> " " <> a2 <> " " <> a3 <> " " <> a4 <> " : " <> export ty1 <> ", " <> export e
      else "∀ " <> a1 <> " : " <> export ty1 <> ", " <> export a
    All a1 ty1 a@(All a2 ty2 (All a3 ty3 e)) -> if ty1 == ty2 && ty2 == ty3
      then "∀ " <> a1 <> " " <> a2 <> " " <> a3 <> " : " <> export ty1 <> ", " <> export e
      else "∀ " <> a1 <> " : " <> export ty1 <> ", " <> export a
    All a1 ty1 a@(All a2 ty2 e) -> if ty1 == ty2
      then "∀ " <> a1 <> " " <> a2 <> " : " <> export ty1 <> ", " <> export e
      else "∀ " <> a1 <> " : " <> export ty1 <> ", " <> export a
    All a ty e    -> "∀ " <> a <> " : " <> export ty <> ", " <> export e

    Abs a ty e    -> "(λ " <> a <> " : " <> export ty <> ", " <> export e <> ")"

    Exists a1 ty1 a@(Exists a2 ty2 (Exists a3 ty3 e)) -> if ty1 == ty2 && ty2 == ty3
      then "(∃ " <> a1 <> " " <> a2 <> " " <> a3 <> " : " <> export ty1 <> ", " <> export e <> ")"
      else "(∃ " <> a1 <> " : " <> export ty1 <> ", " <> export a <> ")"
    Exists a1 ty1 a@(Exists a2 ty2 e) -> if ty1 == ty2
      then "(∃ " <> a1 <> " " <> a2 <> " : " <> export ty1 <> ", " <> export e <> ")"
      else "(∃ " <> a1 <> " : " <> export ty1 <> ", " <> export a  <> ")"
    Exists a ty e -> "(∃ " <> a <> " : " <> export ty <> ", " <> export e <> ")"

    e1 :-> e2@(_e1 :-> _e2) -> export e1 <> " → " <> export e2
    Const c1 :-> Const c2 -> c1 <> " → " <> c2
    e1@(_ :/\ _) :-> e2 -> export e1 <> " → (" <> export e2 <> ")"
    e1 :-> e2@(_ :\/ _) -> "(" <> export e1 <> ") → " <> export e2
    e1 :-> e2 -> "(" <> export e1 <> ") → (" <> export e2 <> ")"
    e1@(_ :@ _) :/\ e2@(_ :@ _) -> export e1 <> " ∧ " <> export e2
    e1@(_ :@ _) :/\ e2 -> export e1 <> " ∧ (" <> export e2 <> ")"
    e1 :/\ e2@(_ :@ _) -> "(" <>  export e1 <> ") ∧ " <> export e2
    e1 :/\ (e2 :/\ e3) -> "(" <> export e1 <> ") ∧ (" <> export e2 <> ") ∧ (" <> export e3 <> ")"
    (e1 :/\ e2) :/\ e3 -> "(" <> export e1 <> ") ∧ (" <> export e2 <> ") ∧ (" <> export e3 <> ")"
    e1 :/\ e2 -> "(" <> export e1 <> ") ∧ (" <> export e2 <> ")"
    e1@(_ :@ _) :\/ e2@(_ :@ _) -> export e1 <> " ∨ " <> export e2
    e1@(_ :@ _) :\/ e2 -> export e1 <> " ∨ (" <> export e2 <> ")"
    e1 :\/ e2@(_ :@ _) -> "(" <> export e1 <> ") ∨ " <> export e2
    e1 :\/ e2 -> "(" <> export e1 <> ") ∨ (" <> export e2 <> ")"
    e1 :<-> e2 -> "(" <> export e1 <> ") ↔ (" <> export e2 <> ")"