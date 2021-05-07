{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}

-- | Export a task to TPTP syntax.

module SAD.Core.TPTP (ExportLang(..), taskToTPTP) where

import Data.Text (Text)
import qualified Data.Text as Text
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Functor.Identity
import Data.Hashable

import SAD.Core.Identifier
import SAD.Core.Typed
import SAD.Core.Task
import Data.Maybe

data TPTPState = TPTPState
  { exportLang :: ExportLang
  , boundAsVars :: Set Ident
    -- ^ identifiers that are bound by a quantifier at the current step
    -- and should be rendered as a variable
  } deriving (Eq, Show)

class TPTP a where
  tptp :: TPTPState -> a -> Text

instance TPTP Ident where
  tptp ex t = if t `Set.member` (boundAsVars ex)
    then identAsVar t
    else identAsTerm t

instance TPTP InType where
  tptp _ (Signature t) = case identAsType t of
    Just t -> t
    Nothing -> identAsTerm t

instance TPTP OutType where
  tptp ex = \case
    Prop -> "$o"
    InType t -> tptp ex t

instance TPTP Type where
  tptp ex = \case
    Sort -> "$tType"
    Pred [] t -> tptp ex t
    Pred ts t -> "(" <> Text.intercalate " * " (map (tptp ex) ts) <> ") > " <> tptp ex t

instance TPTP a => TPTP (Identity a) where
  tptp ex (Identity a) = tptp ex a

inParens :: [Text] -> Text
inParens [] = ""
inParens xs = "(" <> Text.intercalate ", " xs <> ")"

addVar :: Ident -> TPTPState -> TPTPState
addVar i s = s { boundAsVars = Set.insert i (boundAsVars s) }

instance (f ~ Identity, t ~ ()) => TPTP (Term f t) where
  tptp ex trm = case (exportLang ex, trm) of
    (TF0, Forall v m t) ->
      let ex' = addVar v ex in
      "(! [" <> tptp ex' v <> ": " <> tptp ex m <> "] : " <> tptp ex' t <> ")"
    (TF0, Exists v m t) ->
      let ex' = addVar v ex in
      "(? [" <> tptp ex' v <> ": " <> tptp ex m <> "] : " <> tptp ex' t <> ")"
    (FOF, Forall v (Identity (Signature m)) t) ->
      let ex' = addVar v ex in
      "(! [" <> tptp ex' v <> "] : "
      <> tptp ex' (App Imp [AppWf m [AppWf v [] noWf] noWf, t]) <> ")"
    (FOF, Exists v (Identity (Signature m)) t) ->
      let ex' = addVar v ex in
      "(? [" <> tptp ex' v <> "] : "
      <> tptp ex' (App And [AppWf m [AppWf v [] noWf] noWf, t]) <> ")"
    (_, App And [a, b]) -> "(" <> tptp ex a <> " & " <> tptp ex b <> ")"
    (_, App Or  [a, b]) -> "(" <> tptp ex a <> " | " <> tptp ex b <> ")"
    (_, App Imp [a, b]) -> "(" <> tptp ex a <> " => " <> tptp ex b <> ")"
    (_, App Iff [a, b]) -> "(" <> tptp ex a <> " <=> " <> tptp ex b <> ")"
    (_, App Not [a]) -> "(~ " <> tptp ex a <> ")"
    (_, App Top []) -> "$true"
    (_, App Bot []) -> "$false"
    (_, App Eq [a, b]) -> "(" <> tptp ex a <> " = " <> tptp ex b <> ")"
    (_, AppWf op args _) -> tptp ex op <> inParens (map (tptp ex) args)
    (_, a@(App _ _)) -> error $ "Internal error: Mismatched arguments in tptp generation: " ++ show a
    (_, Tag () t) -> tptp ex t
    (_, Class _ _ _ _ _) -> error "Internal error: Class left in TPTP!"
    (_, FinClass _ _ _) -> error "Internal error: FinClass left in TPTP!"

tffStatement :: ExportLang -> Text -> Text -> Text -> Text
tffStatement ex n typ inside =
  let h = hash inside
      name = if Text.null n || n == "__" then "m_" <> Text.pack (show (h * signum h)) else n
      prefix = case ex of TF0 -> "tff"; FOF -> "fof"
  in prefix <> "(" <> name <> ", " <> typ <> ", (\n  " <> inside <> "))."

instance TPTP Hypothesis where
  tptp ex = \case
      Given name t -> tffStatement (exportLang ex) name "axiom" (tptp ex t)
      Typing name t ->
        let name' = fromMaybe (identAsTerm name) $ case t of Sort -> identAsType name; _ -> Nothing
        in case exportLang ex of
          TF0 -> tffStatement (exportLang ex) name' "type" (name' <> ": " <> tptp ex t)
          FOF -> case t of
            Pred ts (InType (Signature intype)) -> tffStatement (exportLang ex) (tptp ex name) "axiom" $ tptp ex $
              let vars = flip zip ts $ map (NormalIdent . Text.pack . ('x':) . show) [1::Int ..]
              in foldr (\(v, t) -> Forall v (Identity t)) (AppWf intype [AppWf name (map (\(v, _) -> AppWf v [] noWf) vars) noWf] noWf) vars
            Pred _ Prop -> "" -- we assume that type-checking has already been done in this code.
            Sort -> "" -- types don't need to be introduced in FOF

instance TPTP Task where
  tptp ex (Task hypo conj _ name _ _) =
    Text.unlines (map (tptp ex) (reverse hypo) ++ [tffStatement (exportLang ex) name "conjecture" (tptp ex conj)])

taskToTPTP :: ExportLang -> Task -> Text
taskToTPTP ex = tptp (TPTPState ex mempty)