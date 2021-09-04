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

import SAD.Data.Identifier
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
  tptp ex t = if t `Set.member` boundAsVars ex
    then identifierAsVar (uniqueIdentifier t)
    else identifierAsTerm (uniqueIdentifier t)

instance TPTP InType where
  tptp _ (Signature t) = case identifierAsType (uniqueIdentifier t) of
    Just t -> t
    Nothing -> identifierAsTerm (uniqueIdentifier t)

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

instance TPTP Term where
  tptp ex trm = case (exportLang ex, trm) of
    (TF0, Forall v m t) ->
      let ex' = addVar v ex in
      "(! [" <> tptp ex' v <> ": " <> tptp ex m <> "] : " <> tptp ex' t <> ")"
    (TF0, Exists v m t) ->
      let ex' = addVar v ex in
      "(? [" <> tptp ex' v <> ": " <> tptp ex m <> "] : " <> tptp ex' t <> ")"
    (FOF, Forall v (Signature m) t) ->
      let ex' = addVar v ex in
      "(! [" <> tptp ex' v <> "] : "
      <> tptp ex' (App Imp [AppWf m [AppWf v [] NoWf] NoWf, t]) <> ")"
    (FOF, Exists v (Signature m) t) ->
      let ex' = addVar v ex in
      "(? [" <> tptp ex' v <> "] : "
      <> tptp ex' (App And [AppWf m [AppWf v [] NoWf] NoWf, t]) <> ")"
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

tffStatement :: ExportLang -> Text -> Text -> Text -> Text
tffStatement ex n typ inside =
  let h = hash inside
      name = if Text.null n || n == "__" then "m_" <> Text.pack (show (h * signum h)) else n
      prefix = case ex of TF0 -> "tff"; FOF -> "fof"
  in prefix <> "(" <> name <> ", " <> typ <> ", (\n  " <> inside <> "))."

instance TPTP Hypothesis where
  tptp ex = \case
      Given name t -> tffStatement (exportLang ex) name "axiom" (tptp ex t)
      TypeDef name t ->
        let name' = fromMaybe (identifierAsTerm $ uniqueIdentifier name) $ case t of Sort -> identifierAsType (uniqueIdentifier name); _ -> Nothing
        in case exportLang ex of
          TF0 -> tffStatement (exportLang ex) name' "type" (name' <> ": " <> tptp ex t)
          FOF -> case t of
            Pred ts (InType (Signature intype)) -> tffStatement (exportLang ex) (tptp ex name) "axiom" $ tptp ex $
              let vars = [undefined] -- flip zip ts $ map (NormalIdent . Text.pack . ('x':) . show) [1::Int ..]
              in foldr (uncurry Forall) (AppWf intype [AppWf name (map (\(v, _) -> AppWf v [] NoWf) vars) NoWf] NoWf) vars
            Pred _ Prop -> "" -- we assume that type-checking has already been done in this code.
            Sort -> "" -- types don't need to be introduced in FOF

instance TPTP Task where
  tptp ex (Task hypo conj _ name _ _) =
    Text.unlines (map (tptp ex) (reverse hypo) ++ [tffStatement (exportLang ex) name "conjecture" (tptp ex conj)])

taskToTPTP :: ExportLang -> Task -> Text
taskToTPTP ex = tptp (TPTPState ex mempty)