{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}

-- | Export a task to TPTP syntax.

module SAD.Core.TPTP (ExportLang(..), taskToTPTP) where

import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.List as L
import Data.Functor.Identity
import Data.Hashable

import SAD.Data.Identifier
import SAD.Data.Terms
import SAD.Core.Typed
import SAD.Core.Typecheck (coercionsToTerm)
import SAD.Core.Task
import Data.Maybe

data ExportLang = TF0 | FOF
  deriving (Eq, Ord, Show)

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

-- | Desuger all classes in the hypothesis and conjecture.
-- We assume the hypothesis to be in reverse order.
desugerClasses' :: [Hypothesis] -> Term Identity () -> ([Hypothesis], Term Identity ())
desugerClasses' hs c =
  let (Given "conj" c' : hs') = go ["cls" <> Text.pack (show i) | i <- [1::Int ..]] (Given "conj" c : hs)
  in (hs', c')
  where
    go _ [] = []
    go vars (h:hs) = case h of
      Given name t ->
        let ((vars', axs), t') = desugerClasses vars t
        in Given name t' : (concatMap (\(n, cc, typ, t) -> [Given (n <> "_aux") t, Typing (NormalIdent n) (Pred (map runIdentity typ) (InType cc))]) axs) ++ go vars' hs
      Typing name t -> Typing name t : go vars hs

-- | Given an infinite stream of Idents,
-- replace each class {x | c} by a new operator cls in a term t and return
-- ((rest of the variables, [∀x x\in cls iff c]), t')
-- If classes are nested, we will return the outermost first.
desugerClasses :: [Text] -> Term Identity () -> (([Text], [(Text, InType, [Identity InType], Term Identity ())]), Term Identity ())
desugerClasses = go mempty
  where
    go typings vars = \case
      Forall v m t -> Forall v m <$> go (Map.insert v m typings) vars t 
      Exists v m t -> Exists v m <$> go (Map.insert v m typings) vars t 
      Class v m mm (Identity ci) t -> 
        let (cls:clss) = vars
            ((clss', stmts), t') = go (Map.insert v m typings) clss t
            free = mapMaybe (\v -> case Map.lookup v typings of Nothing -> Nothing; Just t -> Just (v, t))
              $ Set.toList $ fvToVarSet $ bindVar v $ findFree t'
            clsTrm = AppWf (NormalIdent cls) (map (\(v, _) -> AppWf v [] noWf) free) noWf
            v' = coercionsToTerm (coerceElemsToObject ci) (AppWf v [] noWf) 
            t'' = maybe t' (\s -> App And [AppWf identElement [v', s] noWf, t']) mm
            ext = Forall v m $ App Iff [AppWf identElement [v', coercionsToTerm (coerceClassTypeToClass ci) $ clsTrm] noWf, t'']
            ext' = foldr (\(v, m) -> Forall v m) ext free
        in ((clss', (cls, classType ci, map snd free, ext'):stmts), clsTrm)
      FinClass m (Identity ci) ts -> 
        let (cls:clss) = vars
            v = newIdent (NormalIdent "v") (Map.keysSet typings)
            v' = coercionsToTerm (coerceElemsToObject ci) (AppWf v [] noWf) 
            ts' = foldl (\a b -> App Or [a, b]) (App Top []) $ map (\t -> App Eq [AppWf v [] noWf, t] ) ts
            ((clss', stmts), t') = go typings clss ts'
            free = mapMaybe (\v -> case Map.lookup v typings of Nothing -> Nothing; Just t -> Just (v, t))
              $ Set.toList $ fvToVarSet $ findFree t'
            clsTrm = AppWf (NormalIdent cls) (map (\(v, _) -> AppWf v [] noWf) free) noWf
            ext = Forall v m $ App Iff [AppWf identElement [v', coercionsToTerm (coerceClassTypeToClass ci) $ clsTrm] noWf, t']
            ext' = foldr (\(v, m) -> Forall v m) ext free
        in ((clss', (cls, classType ci, map snd free, ext'):stmts), clsTrm)
      App op ts ->
        let (st, ts') = L.mapAccumL (\(v, ax) t -> 
              let ((v', ax'), t') = go typings v t in ((v', ax ++ ax'), t'))
              (vars, []) ts
        in (st, App op ts')
      AppWf op ex wf ->
        let (st, ex') = L.mapAccumL (\(v, ax) t -> 
              let ((v', ax'), t') = go typings v t in ((v', ax ++ ax'), t'))
              (vars, []) ex
        in (st, AppWf op ex' wf)
      Tag tag t -> Tag tag <$> go typings vars t 

instance TPTP Task where
  tptp ex (Task hypo conj _ name _ _) =
    let (hypo', conj') = desugerClasses' hypo conj
    in Text.unlines (map (tptp ex) (reverse hypo') ++ [tffStatement (exportLang ex) name "conjecture" (tptp ex conj')])

taskToTPTP :: ExportLang -> Task -> Text
taskToTPTP ex = tptp (TPTPState ex mempty)