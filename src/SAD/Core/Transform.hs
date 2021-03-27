{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ViewPatterns #-}

-- | Transform the blocks from a parsed text to TFF form.
-- This code is a bit fragile since it was written mainly
-- by checking that a ton of examples work and not focussing
-- on correctness by design. Therefore we made the concious
-- decision to add many calls to 'error'. This ensures that
-- this transformation is indeed faithful to the Naproche text.

module SAD.Core.Transform
 ( convert, convertBlock
 ) where

import Data.Text (Text)
import Data.Char (toLower)
import qualified Data.Text as Text
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Functor.Const
import Data.Functor.Identity
import qualified Data.List as List
import Data.Maybe (fromMaybe)
import Control.Monad.State

import SAD.Data.Formula (Formula, Tag(..), Decl(..), showFormula)
import qualified SAD.Data.Formula as F
import SAD.Data.VarName
import SAD.Data.Terms
import SAD.Data.Text.Block (ProofText(..), Block(..), position)
import qualified SAD.Data.Text.Block as Block
import Data.Text.Prettyprint.Doc hiding ((<+>))
import Data.Text.Prettyprint.Doc.Render.String (renderString)
import SAD.Helpers (setMapMaybe)
import SAD.Core.SourcePos (SourcePos, noSourcePos)
import qualified SAD.Core.Message as Message
import qualified Isabelle.Naproche as Naproche

import SAD.Core.Typed
import SAD.Core.Coerce

import Debug.Trace

-- | If you encounter a weird error, this may help
-- with debugging it. You need to import Debug.Trace
traceReprId :: Pretty a => a -> a
traceReprId a = a -- trace (Text.unpack (pretty a)) a

data ErrorContext = ErrorContext
  { errorBlock :: Block
  , errorFormula :: Formula
  , errorPosition :: SourcePos
  } deriving (Eq, Ord, Show)

type Err m a = StateT ErrorContext m a

failWithMessage :: Message.Comm m => Doc ann -> Err m a
failWithMessage txt = do
  src <- errorPosition <$> get
  f <- errorFormula <$> get
  b <- errorBlock <$> get
  lift $ Message.error Naproche.origin_reasoner src
    $  "\nWhile checking the block:\n\n" ++ show b
    ++ "\nmore specifically, the formula:\n\n" ++ showFormula f
    ++ "\n\n" ++ (renderString $ layoutCompact txt)

data Context = Context
  { typings :: Map TermName (Maybe Type)
    -- ^ a type for each resolved name
  , resolved :: Map TermName (Set TermName)
    -- ^ resolve functions into names, e.g. + into add_nat 
    -- and and_rat if + was defined twice.
  , coercions :: Coercions TermName TermName
  , preBoundVars :: Map VarName InType
    -- ^ variables bound by a previous choose statement or in the claim.
  } deriving (Eq, Ord, Show)

-- | Danger: Costly in second argument due to coercions
instance Semigroup Context where
  (<>) (Context t1 r1 c1 p1) (Context t2 r2 c2 p2) = Context (t1 <> t2) (r1 <> r2) (c1 <> c2) (p1 <> p2)

-- | This should be kept in sync with SAD.ForTheL.Base.initFS
predefinedTypes :: Map TermName (Maybe Type)
predefinedTypes = Map.fromList
  [ (termSet, Just Sort)
  , (termClass, Just Sort)
  , (termObject, Just Sort)
  , (termElement, Just $ Pred [Signature termObject, Signature termClass] Prop)
  ]

predefinedNames :: Map TermName (Set TermName)
predefinedNames = Map.fromList
  [ (termElement, Set.singleton termElement) ]

instance Monoid Context where
  mempty = Context predefinedTypes predefinedNames mempty mempty

-- | Parse a formula into a term while ignoring all type information.
-- This will only check that no variable overlap and that all de-bruijn
-- indices have a binder. We will subsequently use the variable names at
-- the binders instead of indices since this leads to nicer output.
parseFormula :: Message.Comm m => Formula -> Err m (Term (Const ()) Tag)
parseFormula f = modify (\s -> s { errorFormula = f }) >> go [] f
  where 
    go vars = \case
      F.All (Decl v _ _) f -> Forall v (Const ()) <$> go (addVar v vars) f
      F.Exi (Decl v _ _) f -> Exists v (Const ()) <$> go (addVar v vars) f
      F.Class (Decl v _ _) f -> Class v (Const ()) <$> go (addVar v vars) f
      F.Iff f1 f2 -> App Iff <$> mapM (go vars) [f1, f2]
      F.Imp f1 f2 -> App Imp <$> mapM (go vars) [f1, f2]
      F.And f1 f2 -> App And <$> mapM (go vars) [f1, f2]
      F.Or  f1 f2 -> App Or  <$> mapM (go vars) [f1, f2]
      F.Tag t f   -> Tag t <$> go vars f
      F.Not f -> App Not <$> mapM (go vars) [f]
      F.Top -> pure $ App Top []
      F.Bot -> pure $ App Bot []
      F.Trm TermEquality [f1, f2] _ _ -> App Eq <$> mapM (go vars) [f1, f2]
      F.Trm name args _ _ -> App (OpTrm name) <$> mapM (go vars) args
      F.Var v _ _ -> pure $ Var v
      F.Ind i _ ->
        if length vars > i then pure $ Var $ vars !! i
        else failWithMessage $ pretty $ "Unbound index: " ++ show i
      f -> failWithMessage $ pretty $ "Unexpected formula: " ++ show f

    addVar v vars = v:vars

-- | Given a list of defined sorts and a TermName,
-- decide if this is a sort.
parseType :: Context -> TermName -> Maybe InType
parseType ctx = \case 
  t@(TermNotion _) -> case Map.lookup t (typings ctx) of
    Just (Just Sort) -> Just $ Signature t
    _ -> Nothing
  _ -> Nothing

-- | Transform type predicates into types.
-- This needs to be seperate from finding types, since
-- the type predicates need to be deleted from the terms
-- and it is not allowed for a variable to have more than
-- one sort (which we check here).
extractGivenTypes :: Message.Comm m => Context -> Term (Const ()) Tag -> Err m (Term Maybe Tag)
extractGivenTypes ctx = \t -> snd <$> go t
  where
    duplicateType ma mb = ma >>= \a -> mb >>= \b ->
      if coercibleInto' a b (coercions ctx) /= Nothing then pure a else
      if coercibleInto' b a (coercions ctx) /= Nothing then pure b else
      failWithMessage $ "A variable has been defined with multiple types: " <> pretty a <> " and " <> pretty b

    -- TODO: The hack below is fragile. It would be better to do the following:
    -- We say a term is in negative position if it occurs negated in the DNF
    -- and else say in positive position. For example: "negative => positive".
    -- Then we should use type predicates in negative position for types
    -- and in positive position for coercions.
    -- We need to split "x iff y" into two statements for this to work.
    -- A statement like 'x is an A iff x is a B and P(x)' should be translated to
    -- '(∀[x : A] ∃[y : B] x = y & P(x)) & (∀[x : B] P(x) => ∃[y : A] x = y)'
    -- (with coercions inserted later...)
    go :: Message.Comm m => Term (Const ()) Tag -> Err m (Map VarName InType, Term Maybe Tag)
    go = \case
      Forall v (Const ()) t -> do
        (typings, t') <- go t
        pure (typings, Forall v (Map.lookup v typings) t')
      Exists v (Const ()) t -> do
        (typings, t') <- go t
        pure (typings, Exists v (Map.lookup v typings) t')
      Class v (Const ()) t -> do
        (typings, t') <- go t
        pure (typings, Class v (Just $ Map.findWithDefault (Signature termObject) v typings) t')
      -- this hack allows for new coercions in a lemma or axiom
      -- if it is of the form "Let s be a from. Then s is a to."
      App Imp [App (OpTrm (parseType ctx -> Just from)) [Var v0], App (OpTrm name@(parseType ctx -> Just _)) [Var v1]]
        | v0 == v1 -> pure $ (Map.singleton v0 from, Tag CoercionTag $ App (OpTrm name) [Var v0])
      App (OpTrm name) [Var v] -> case parseType ctx name of
        Just t -> pure $ (Map.singleton v t, App Top [])
        Nothing -> pure $ (mempty, App (OpTrm name) [Var v])
      App op args -> do
        res <- mapM go args
        typings <- sequence $ Map.unionsWith duplicateType $ map (Map.map pure . fst) res
        let args' = map snd res
        pure (typings, App op args')
      Tag tag t -> fmap (Tag tag) <$> go t
      Var v -> pure (mempty, Var v)

coercionsToTerm :: [TermName] -> (Term f t -> Term f t)
coercionsToTerm = go . reverse
  where
    go [] = id
    go (x:xs) = go xs . App (OpTrm x) . (:[])

-- | Like <> for maybe, but prefers Nothing
(<+>) :: Semigroup a => Maybe a -> Maybe a -> Maybe a
(<+>) (Just a) (Just b) = Just (a <> b)
(<+>) _ _ = Nothing

-- | Find the coercions for two 'Type's.
-- If both are Sorts we return just the empty list and if both
-- are predicates, we return the coercions for each argument in order.
coercibleInto :: Type -> Type -> Coercions TermName TermName -> Maybe [[TermName]]
coercibleInto smaller bigger coe = case (smaller, bigger) of
  (Sort, Sort) -> Just []
  (Pred is o, Pred is' o') ->
    let outOk = case (o, o') of
          (Prop, Prop) -> Just [] 
          (InType i, InType i') -> 
            const [] <$> coercibleInto' i' i coe -- contravariant
          _ -> Nothing
        inOk = sequence $ zipWith (\a b -> coercibleInto' a b coe) is is'
    in if length is == length is' then inOk <+> outOk else Nothing
  _ -> Nothing

-- | Find the coercions for two 'InType's.
-- We handle 'TermNotKnown' specially, see 'resolve' below.
coercibleInto' :: InType -> InType -> Coercions TermName TermName -> Maybe [TermName]
coercibleInto' _ (Signature TermNotKnown) _ = Just []
coercibleInto' (Signature smaller) (Signature bigger) coe = coerce (smaller, bigger) coe

data ReturnValue = Value | Proposition
  deriving (Eq, Ord, Show)

resolve :: Message.Comm m => Context -> TermName -> [InType] -> ReturnValue -> Err m ((TermName, [[TermName]]), Type)
resolve (Context idents res coe _) name intypes ret =
  leastGeneral $ Set.toList feasibleNames
  where
    resolvedNames = setMapMaybe (\a -> (\b->(a,b)) <$> (idents Map.! a) ) $ res Map.! name

    feasibleNames = Set.map (\((t, Just a), typ) -> ((t, a), typ)) $ Set.filter (\a -> snd (fst a) /= Nothing) 
        $ Set.map (\t -> ((fst t, coercibleInto typ (snd t) coe), snd t)) resolvedNames

    typ = case ret of
      Proposition -> Pred intypes Prop
      Value -> Pred intypes $ InType $ Signature TermNotKnown

    -- TODO: Remember the smarter O(n) algo
    leastGeneral [] = failWithMessage $ "Resolve failed: " <> pretty name <> " of type " <> pretty typ
    leastGeneral [x] = pure x
    leastGeneral (x:y:xs) = if coercibleInto (snd x) (snd y) coe /= Nothing then leastGeneral (x:xs) else
      if coercibleInto (snd y) (snd x) coe /= Nothing then leastGeneral (y:xs) else
        failWithMessage $ "Resolve ambigous: " <> pretty name <> " of type " <> pretty typ
          <> " can be resolved as " <> pretty (snd x) <> " or " <> pretty (snd y) <> "\n"
          <> "and none of them is more general than the other."

-- | Type check applications and insert coercions.
-- Forward type-checking: We assume that the functions without arguments and variables are typed
-- and infer the type/resolved name of functions with arguments from them.
gatherTypes :: Message.Comm m => Context -> Term Maybe Tag -> Err m (Term Maybe Tag)
gatherTypes c = \t -> snd <$> go Proposition (Map.map Just $ preBoundVars c) 0 t
  where
    -- The context is the type that the surrounding context expects.
    -- When we expect some InType, we use 'Signature "Object"'.
    -- We need to insert special variables for type predicates,
    -- numbered by d
    go context typings d = \case
      Forall v1 Nothing (App Iff [t1, App Eq [Var v2, t2]])
        | v1 == v2 -> do
          (tt2, t2') <- go Value typings d t2
          case tt2 of
            Prop -> failWithMessage "Internal error: recursion malformed in 'gatherTypes'"
            InType tt2 -> do
              (_, t1') <- go Proposition (Map.insert v1 (Just tt2) typings) d t1
              pure (Prop, Forall v1 (Just $ tt2) (App Iff [t1', App Eq [Var v2, t2']]))
      Forall v m t -> case context of
        Proposition -> fmap (Forall v m) <$> go Proposition (Map.insert v m typings) d t
        _ -> failWithMessage $ "Found a forall term where an object was expected"
      Exists v m t -> case context of
        Proposition -> fmap (Exists v m) <$> go Proposition (Map.insert v m typings) d t
        _ -> failWithMessage $ "Found an exists term where an object was expected"
      Class v m t -> case context of
        Value -> do
           (_, inclass) <- go Proposition (Map.insert v m typings) d t
           pure (InType $ Signature (TermNotion "Class"), Class v m inclass)
        Proposition -> failWithMessage $ "Found a class where a proposition was expected."
      -- If we use a sort as a predicate aSort(x), we instead use ∃[v : aSort] v = x.
      App (OpTrm name@(TermNotion _)) [arg] -> do
        (tb, arg') <- go Value typings (d+1) arg
        let ia = Signature name
            a = Var (VarF d)
        eq <- case tb of
          InType ib -> case (coercibleInto' ia ib (coercions c), coercibleInto' ib ia (coercions c)) of
            (Just ts, _) -> pure $ App Eq [coercionsToTerm ts a, arg']
            (_, Just ts) -> pure $ App Eq [a, coercionsToTerm ts arg']

            -- This may happen when a coercion is newly introduced.
            -- When the coercion is not in a CoercionTag, this should
            -- throw an error (because otherwise the prover will complain).
            (Nothing, Nothing) -> pure $ App Eq [a, arg']
          _ -> failWithMessage $ "Proposition was used in coercion: " <> pretty arg
        pure (Prop, (Exists (VarF d) (Just $ Signature name) eq))
      App (OpTrm name@(TermVar v)) args -> case (Map.lookup v typings, args) of
        (Just (Just t), []) -> pure (InType t, App (OpTrm name) [])
        (_, (_:_)) -> failWithMessage "Internal: Variable bound as term can't be applied."
        (_, _) -> failWithMessage "Internal: Variable bound as term in a proof was not registered."
      App (OpTrm name) args -> do
        (argtypes, args') <- unzip <$> mapM (go Value typings d) args
        argintypes <- flip mapM argtypes $ \t -> case t of
              Prop -> failWithMessage "A truth value cannot be passed to a function!"
              InType t' -> pure t'
        res <- resolve c name argintypes context
        case res of
              ((name', _), Sort) -> 
                failWithMessage $ "Illegal use of sort as predicate: " <> pretty (App (OpTrm name') args') 
                  <> " where a value was expected."
              ((name', coe), Pred _ t) -> pure (t, App (OpTrm name') $ zipWith coercionsToTerm coe args')
      App Eq [a, b] -> do
        (ta, a') <- go Value typings d a
        (tb, b') <- go Value typings d b
        case (ta, tb) of
          (InType ia, InType ib) -> case (coercibleInto' ia ib (coercions c), coercibleInto' ib ia (coercions c)) of
            (Just ts, _) -> pure (Prop, App Eq [coercionsToTerm ts a', b'])
            (_, Just ts) -> pure (Prop, App Eq [a', coercionsToTerm ts b'])
            (Nothing, Nothing) -> failWithMessage $
              "Can't coerce one side of equality into the other: " <> pretty (App Eq [a', b']) 
          _ -> failWithMessage $ "Prop in equality: " <> pretty (App Eq [a', b'])
      App op args -> do 
        res <- mapM (go Proposition typings d) args
        pure (Prop, App op $ map snd res)
      -- predicate defintions: check that all args are variables
      Tag HeadTerm (App (OpTrm name) args) -> do
        vs <- mapM (\case Var v -> pure $ Var v; x -> failWithMessage $ "Expected variable in definition but got: " <> pretty x) args
        pure (Prop, Tag HeadTerm $ App (OpTrm name) vs)
      -- function definitions; check that all args are variables
      Tag HeadTerm (App Eq [Var v0, App (OpTrm name) args]) -> do
        vs <- mapM (\case Var v -> pure $ Var v; x -> failWithMessage $ "Expected variable in definition but got: " <> pretty x) args
        pure (Prop, Tag HeadTerm $ App Eq [Var v0, App (OpTrm name) vs])
      Tag tag t -> fmap (Tag tag) <$> go context typings d t
      Var v -> case context of
        Proposition -> failWithMessage $ "A variable " <> pretty v <> " may not appear as a proposition."
        Value -> case Map.lookup v typings of
          Just (Just t) -> pure (InType t, Var v)
          _ -> failWithMessage $ "Unbound variable: " <> pretty v

coercionName :: Message.Comm m => TermName -> TermName -> Err m TermName
coercionName (TermNotion n1) (TermNotion n2) = pure $ TermName $ beginLower n1 <> "To" <> n2
  where beginLower t = case Text.uncons t of
          Just (c, t') -> Text.cons (toLower c) t'
          Nothing -> t
coercionName _ _ = failWithMessage $ "Coercions only between notions"

mkCoercion :: Message.Comm m => InType -> InType -> Err m [Stmt Identity ()]
mkCoercion (Signature from) (Signature to) = do
  name <- coercionName from to
  let [x, y] = [VarDefault "x", VarDefault "y"]
  let coe = coercionsToTerm [name]
  let fromType = Identity $ Signature from
  let inj = Forall x fromType $ Forall y fromType $ App Imp
       [App Eq [coe (Var x), coe (Var y)], App Eq [Var x, Var y]]
  pure [Coercion name from to, Axiom inj]

-- | Extract definitions from a typed term.
-- This will find HeadTerms and add them as definitions,
-- as well as delete all HeadTerm Tags.
extractDefinitions :: Message.Comm m => Term Maybe Tag -> Err m ([Stmt Identity ()], Term Maybe Tag)
extractDefinitions = go mempty
  where
    extractType :: Message.Comm m => TermName -> Map VarName (Maybe p) -> Term Maybe Tag -> Err m p
    extractType name types (Var v) = case Map.lookup v types of
      Just (Just t) -> pure t
      Just Nothing -> failWithMessage $ "In a definition for " <> pretty name <> ", the type of variable "
        <> pretty v <> " could not be guessed. Please provide its type."
      Nothing -> failWithMessage $ "In a definition for " <> pretty name <> ", the variable "
        <> pretty v <> " was found to be unbound."
    extractType name _ e = failWithMessage $ "In a definition for " <> pretty name <> ", I expected a variable, but got:\n" <> pretty e

    go types = \case
      Forall v m t -> fmap (simp . Forall v m) <$> go (Map.insert v m types) t
      Exists v m t -> fmap (simp . Exists v m) <$> go (Map.insert v m types) t
      Class  v m t -> fmap (simp . Class  v m) <$> go (Map.insert v m types) t
      App op args -> do
        res <- mapM (go types) args
        pure (concatMap fst res, simp $ App op $ map snd res)
      -- coercion definitions
      -- TODO: This case does not match when the coercion already exists and thus an error
      -- 'Remaining tag: CoercionTag' is thrown!
      Tag CoercionTag trm@(Exists _ (Just to) (App Eq [_, Var v0])) ->
        case Map.lookup v0 types of
          (Just (Just from)) -> do
            coe <- mkCoercion from to
            pure (coe, App Top [])
          _ -> pure ([], trm)
      -- sorts and predicate definitions
      Tag HeadTerm trm@(App (OpTrm name) args) -> case (name, args) of
        (TermNotion _, [Var v]) -> do
          t <- case Map.lookup v types of
                (Just (Just t')) -> mkCoercion (Signature name) t'
                _ -> pure []
          pure ([IntroSort name] ++ t, App Top [])
        _ -> do
          ts <- mapM (extractType name types) args
          pure ([Predicate name ts Prop], simp $ trm)
      -- function definitions
      Tag HeadTerm trm@(App Eq [Var v0, App (OpTrm name) args]) -> do
        ts <- mapM (extractType name types) args
        out <- extractType name types (Var v0)
        pure ([Predicate name ts (InType out)], trm)
      Tag tag t -> fmap (Tag tag . simp) <$> go types t
      Var v -> pure ([], Var v)

-- | Make sure that there are no tags left.
noTags :: Message.Comm m => Term Identity Tag -> Err m (Term Identity ())
noTags = go
  where
    go = \case
      Forall v m t -> Forall v m <$> go t
      Exists v m t -> Exists v m <$> go t
      Class v m t -> Class v m <$> go t
      App op args -> App op <$> mapM go args
      Tag Replacement t -> go t
      Tag EqualityChain t -> go t
      Tag tag _ -> failWithMessage $ pretty $ "Remaining tag: " ++ show tag
      Var v -> pure $ Var v

-- | The full pipeline from formula to a terms.
typecheck :: Message.Comm m => Context -> Term (Const ()) Tag -> Err m (Term Maybe Tag)
typecheck ctx trm = do
  e <- traceReprId <$> extractGivenTypes ctx trm
  g <- traceReprId <$> gatherTypes ctx e
  pure g

-- | Fail if the type of binds could not be inferred.
noUntypedBinds :: Message.Comm m => Term Maybe t -> Err m (Term Identity t)
noUntypedBinds = \case
  Forall v (Just m) t -> Forall v (Identity m) <$> noUntypedBinds t
  Exists v (Just m) t -> Exists v (Identity m) <$> noUntypedBinds t
  Class v (Just m) t -> Class v (Identity m) <$> noUntypedBinds t
  Forall v Nothing _ -> failWithMessage $ "Untyped bind: " <> pretty v
  Exists v Nothing _ -> failWithMessage $ "Untyped bind: " <> pretty v
  Class v Nothing _ -> failWithMessage $ "Untyped bind: " <> pretty v
  App op args -> App op <$> mapM noUntypedBinds args
  Tag tag t -> Tag tag <$> noUntypedBinds t
  Var v -> pure $ Var v

-- | A tactic takes the goal, the current context and a number of proof lines (Block)
-- and may translate some lines and give a new goal.
type Tactic m = (Term Identity (), Context, [Block]) -> Err m (Maybe (Proof, (Term Identity (), Context, [Block])))

preBind :: Map VarName InType -> Context -> Context
preBind vs ctx = ctx { preBoundVars = vs <> preBoundVars ctx }

-- | Introduce top-level forall-bound variables in the term
-- and the conditions of if-terms as a tactic.
autoIntroAssume :: Message.Comm m => Tactic m
autoIntroAssume (_, _, []) = pure Nothing
autoIntroAssume (goal, ctx, (b:bs)) = pure $ case goal of
    Forall v (Identity typ) t -> Just ((Located "intro" (position b) (Intro v typ)),
      (termify (Set.singleton v) t, preBind (Map.singleton v typ) ctx, b:bs))
    App Imp [ass, goal'] -> Just ((Located "intro" (position b) (Assume $ termify (Map.keysSet $ preBoundVars ctx) ass)), (goal', ctx, b:bs))
    _ -> Nothing

-- | Convert a single line of a proof.
subClaim :: Message.Comm m => Context -> Block -> Err m Proof
subClaim ctx bl@(Block f b _ _ n l _) = Located n (position bl) <$> do
  mainF <- noTags =<< noUntypedBinds
        =<< typecheck ctx =<< bindFree (Map.keysSet $ preBoundVars ctx) <$> parseFormula f
  Subclaim mainF <$> convertProof mainF l ctx b

subClaims :: Message.Comm m => Tactic m
subClaims (_, _, []) = pure Nothing
subClaims (goal, ctx, (b:bs)) = do
  sc <- subClaim ctx b
  pure $ Just (sc, (goal, ctx, bs))

byContradiction :: Message.Comm m => Tactic m
byContradiction (_, _, []) = pure Nothing
byContradiction (goal, ctx, (b:bs)) = pure $ case formula b of
  F.Not (F.Trm TermThesis [] _ _) ->
    Just (Located (name b) (position b) (ByContradiction goal), (App Bot [], ctx, bs))
  _ -> Nothing

chooses :: Message.Comm m => Tactic m
chooses (_, _, []) = pure $ Nothing
chooses (goal, ctx, (b:bs)) = case kind b of
  Block.Selection -> do
    let l = position b; n = name b
        vs = Set.map declName $ declaredVariables b
    f <- noTags =<< noUntypedBinds
          =<< typecheck ctx =<< bindFree (Map.keysSet $ preBoundVars ctx)
          <$> bindExists (Set.toList vs) <$> parseFormula (formula b)
    let boundVs = Map.fromList $ concat $ flip List.unfoldr f $ \case
            Forall _ (Identity _) t -> Just ([], t)
            Exists v (Identity typ) t
              | v `Set.member` vs -> Just ([(v, typ)], t)
              | otherwise -> Just ([], t)
            _ -> Nothing
        ctx' = preBind boundVs ctx
    fHypo <- noTags =<< noUntypedBinds
          =<< typecheck ctx' =<< bindFree (Set.union vs $ Map.keysSet $ preBoundVars ctx)
          <$> parseFormula (formula b)
    p <- convertProof f (link b) ctx (body b)
    pure $ Just $ (Located n l $ Choose (Map.toList boundVs) fHypo p, (goal, ctx', bs))
  _ -> pure $ Nothing

cases :: Message.Comm m => Tactic m
cases (goal, ctx, bs) = go Nothing bs
  where
    parseCase c b = do
      c' <- noTags =<< noUntypedBinds
             =<< typecheck ctx =<< bindFree (Map.keysSet $ preBoundVars ctx) <$> parseFormula c
      p' <- convertProof goal (link b) ctx (body b)
      let l' = (position b)
      pure (l', (c', p'))

    go Nothing [] = pure $ Nothing
    go (Just (l, ms)) [] = pure $ Just (Located "cases" l $ TerminalCases (reverse ms), (goal, ctx, []))
    go m (b:bs) = case formula b of
      F.Imp (F.Tag CaseHypothesisTag c) (F.Trm TermThesis [] _ _) -> do
        (l', (c', p')) <- parseCase c b
        case m of
          Nothing -> go (Just (l', [(c', p')])) bs
          Just (l, ms) -> go (Just (l, (c', p'):ms)) bs
      _ -> pure $ case m of
        Nothing -> Nothing
        Just (l, ms) -> Just (Located "cases" l $ Cases (reverse ms), (goal, ctx, b:bs))

-- | Convert a Proof. ... end. part
convertProof :: Message.Comm m => Term Identity () -> [Text] -> Context -> [ProofText] -> Err m ProofBlock
convertProof goal links ctx pts = do
  ((goal', ctx', _), ps) <- go $ concatMap (\case ProofTextBlock b -> [b]; _ -> []) pts
  pure $ Proving ps (termify (Map.keysSet $ preBoundVars ctx') goal') links
  where
    go bs = unfoldM (goal, ctx, bs) $ \st ->
      takeFirstSucceding
        [ autoIntroAssume st
        , byContradiction st
        , cases st
        , chooses st
        , subClaims st
        ]

    takeFirstSucceding :: Monad m => [m (Maybe a)] -> m (Maybe a)
    takeFirstSucceding [] = pure Nothing
    takeFirstSucceding (x:xs) = do
      m <- x
      case m of
        Just a -> pure $ Just a
        Nothing -> takeFirstSucceding xs

    unfoldM :: Message.Comm m => b -> (b -> Err m (Maybe (a, b))) -> Err m (b, [a])
    unfoldM b f = do
      fb <- f b
      case fb of
        Just (a, b') -> fmap (a:) <$> unfoldM b' f
        Nothing -> pure (b, [])

-- | Get the blocks in a Prooftext.
getBlocks :: Message.Comm m => ProofText -> Err m [Block]
getBlocks (ProofTextBlock b) = pure [b]
getBlocks (ProofTextRoot ts) = concat <$> mapM getBlocks ts
getBlocks p = failWithMessage $ pretty $ "Internal error: getBlocks received: " ++ show p

-- | Convert a block into a statement.
convertBlock :: Message.Comm m => Context -> Block -> Err m [Statement]
convertBlock ctx bl@(Block f b _ _ n l _) = map (Located n (position bl)) <$>
  case f of
    -- top-level blocks:
    (F.Var (VarHole _) _ _) -> do
      gottenBlocks <- reverse <$> concat <$> mapM getBlocks b
      case gottenBlocks of
        [] -> failWithMessage "Internal error: list of blocks is empty"
        (main:assms) -> do
          let mainF = foldl (flip F.Imp) (formula main) (formula <$> assms)
          (defs, mainT) <- fmap traceReprId $ extractDefinitions 
                =<< typecheck ctx =<< bindFree mempty <$> parseFormula mainF
          mainT' <- noTags =<< noUntypedBinds mainT
          case Block.needsProof bl of
            True -> if not (null defs)
              then failWithMessage $ "Definitions in claim!"
              else (:[]) <$> Claim mainT' <$> (convertProof mainT' l ctx (body main))
            False -> pure $ defs ++ 
              if mainT == App Top [] then [] else [Axiom mainT']
    _ -> failWithMessage "Internal: convertBlock should not be applied to proofs!"

convert :: Message.Comm m => [ProofText] -> m [Statement]
convert = flip evalStateT initErrors . go mempty . concatMap (\case ProofTextBlock bl -> [bl]; _ -> [])
  where
    initErrors = ErrorContext undefined F.Top noSourcePos

    go _ [] = pure []
    go c (b:bs) = do
      modify $ \s -> s { errorBlock = b }
      modify $ \s -> s { errorPosition = position b }
      stmts <- convertBlock c b
      (stmts ++) <$> go (List.foldl' updateCtx c stmts) bs

    updateCtx (Context idents res coe pbv) (Located _ _ s) = case s of
      IntroSort n ->
        let n' = newName n res_n 
            res_n = Map.lookup n res
            res_n' = fromMaybe mempty res_n
        in Context (Map.insert n' (Just Sort) idents) (Map.insert n (Set.insert n' res_n') res) coe pbv
      Predicate n is o ->
        let n' = newName n res_n 
            res_n = Map.lookup n res
            res_n' = fromMaybe mempty res_n
        in Context (Map.insert n' (Just (Pred is o)) idents) (Map.insert n (Set.insert n' res_n') res) coe pbv
      Coercion n from to -> Context idents res (add (from, to) n coe) pbv
      _ -> Context idents res coe pbv