{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ApplicativeDo #-}

-- | Our type theory can be roughly described as follows:
--     - We use simple types (= sorts)
--     - But a variable may have several types (= one intersection type)
--     - We keep track of coercions (= embeddings) and add them at each application
--     - If an operator is not overloaded we use Hindley-Milner type inference
--     - If an operator is overloaded we evaluate all its arguments
--         and then infer the correct instantiation based on the argument types

module SAD.Core.Typecheck (typecheck) where

import Control.Monad.Validate
import qualified Data.Sequence as Seq
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.List as List
import Control.Applicative
import Control.Monad.State
import Data.Maybe
import Data.Foldable (foldrM)

import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.String
import SAD.Data.SourcePos (SourcePos)

import SAD.Data.Identifier
import SAD.Core.Unique
import SAD.Core.AST
import SAD.Core.Coerce
import SAD.Core.Errors

data InferType a
  = NotProvided
  | DefaultObject -- ^ use for 'a' in { a | a = a}
  | Provided (Set a)
  deriving (Eq, Ord, Show)

-- | Take the left type if given and else the more informative.
instance Semigroup (InferType a) where
  NotProvided <> a = a
  DefaultObject <> (Provided a) = Provided a
  DefaultObject <> _ = DefaultObject
  Provided a <> _ = Provided a

data Context = Context
  { currentLocation :: TypeErrorLocation
  , typings :: Map Ident Type
    -- ^ a type for each internal name
    -- this is extended after each section and otherwise read-only.
  , overloadings :: Map Identifier (Set Ident)
    -- ^ possible overloadings for an identifier
    -- this maps names as the user provided them to internal
    -- names which are unique. For example when several
    -- notions of subset are defined, the internal names
    -- might be "subset, subset2, ..."
    -- this is extended after each section and otherwise read-only.
  , inferMap :: Map Ident (InferType InType)
    -- ^ the types of variables as they were inferred.
    -- When the type of a variable was not provided
    -- (for example because the variable was inserted by the parser)
    -- we try to infer it. This is biased towards the first occurrence
    -- of the variable similar to HM type inference.
    -- This is only used during type-checking and empty otherwise.
  , coercions :: Coercions Ident Ident
    -- ^ coercions defined in the text
  , defs :: Map Ident NFTerm
    -- ^ definitions: the difference to 'typings' is that
    -- this contains well-formedness instead of type information
    -- This is used to check the well-formedness blocks in the text.
  , assumptions :: [Term]
    -- ^ assumptions for ontological checking. This includes
    -- the 'a' in  'a => b' and 'a /\ b' as well as case
    -- hypotheses
  } deriving (Show)

newtype TC m a = TC { fromTC :: ValidateT TypeErrors (StateT Context m) a }
  deriving (Functor, Applicative, Monad, MonadState Context, MonadValidate TypeErrors)

instance MonadTrans TC where
  lift ma = TC (lift (lift ma))

instance HasUnique m => HasUnique (TC m) where
  newIdent n = TC (lift (lift (newIdent n)))

-- | Danger: Costly in second argument due to coercions
instance Semigroup Context where
  (<>) (Context _ t1 r1 i1 c1 d1 as1) (Context el t2 r2 i2 c2 d2 as2) = Context el (t1 <> t2) (r1 <> r2) (i1 <> i2) (c1 <> c2) (d1 <> d2) (as1 <> as2)

instance Monoid Context where
  mempty = Context noLocation mempty mempty mempty mempty mempty []

failWithMessage :: Monad m => TypeErrorMessage -> TC m a
failWithMessage msg = do
  ctx <- get
  refute $ Seq.singleton $ TypeError (currentLocation ctx) msg

errorWithMessage :: Monad m => Doc ann -> TC m a
errorWithMessage txt = do
  ctx <- get
  let loc = currentLocation ctx
  error $ renderString $ layoutSmart
        (defaultLayoutOptions { layoutPageWidth = AvailablePerLine 120 1.0 })
    $  (case errorBlock loc of Nothing -> ""; Just f -> "\nWhile checking the block:\n\n" <> pretty f)
    <> (case errorFormula loc of Nothing -> ""; Just f -> "\nmore specifically, the formula:\n\n" <> pretty f <> "\n")
    <> "\nInternal: " <> txt
    <> "\n  Please report this in the bugtracker of https://github.com/naproche/naproche\n"

-- | 'xs `coerceInto` ys' means that xs needs to fulfil the constraints given by ys.
-- For example: '[{N, Q}] `coerceInto` [{R}]' or '[{set, object}] `coerceInto` [{class}]'.
-- We return the coercions for each argument.
coerceInto :: [Set InType] -> [Set InType] -> Coercions Ident Ident -> Maybe [RCoercion]
coerceInto is is' coe = if length is == length is'
  then sequence $ coerceInto' is is' coe
  else Nothing

coerceInto' :: [Set InType] -> [Set InType] -> Coercions Ident Ident -> [Maybe RCoercion]
coerceInto' is is' coe =
 zipWith (\sa sb -> setAll (\b -> RCoercion . Map.singleton b <$> setAny (\a -> (a,) <$> coerceSig a b coe) sa) sb) is is'
  where
    coerceSig (Signature a) (Signature b) = coerce (a, b)
    setAny f = Set.foldr' (\a b -> f a <|> b) Nothing
    setAll f = Set.foldr' (\a b -> f a <> b) (Just mempty)

-- | Given a list of coercible values, try to find a value that is generalized by
-- all of them and is in the list. Then give the coercions to this value.
-- O(n) calls to coerceInto.
-- Depending of the direction of the arrows, this will either compute the most
-- or least general form.
generalize :: (forall a b. (a -> a -> b) -> a -> a -> b)
  -> [(t, [Set InType])] -> Coercions Ident Ident -> Maybe ((t, [Set InType]), [[RCoercion]])
generalize _ [] _ = Nothing
generalize direction (x:xs) coe = checkRoot (getRoot x xs) (x:xs)
  where
    -- We find an element 'root' with the property that if it is
    -- comparable with another element 'x' then 'x -> root'.
    -- If the coercions form a DAG this is actually a root.
    -- Due to transitivity this can be done in O(n).
    -- We then check if it is comparable to all elements.
    getRoot root [] = root
    getRoot root (x:xs) = case direction coerceInto (snd x) (snd root) coe of
      Just _ -> getRoot x xs
      Nothing -> getRoot root xs
    checkRoot root = fmap (root,) . mapM (\x -> direction coerceInto (snd root) (snd x) coe)

-- | Consider the following scenario:
-- times : natural number x natural number -> natural number (1)
-- times : rational number x rational number -> rational number (2)
-- times : rational number x rational vector -> rational vector (3)
-- coercion: natural number => rational number
-- This is easy (we just choose option (3)): 3 * (4 5)
-- This is hard, do we choose (1) or (2): 3 * 4 ?
--   Solution: take the least general (1):
leastGeneral :: [(t, [Set InType])] -> Coercions Ident Ident
  -> Maybe ((t, [Set InType]), [[RCoercion]])
leastGeneral = generalize id

-- Used for finding the most general element of a set:
-- { 4, 4.5 } is a set of rationals.
mostGeneral :: [(t, [Set InType])] -> Coercions Ident Ident
  -> Maybe ((t, [Set InType]), [[RCoercion]])
mostGeneral = generalize flip

-- | Get the types and internal names of an identifier.
-- This may be empty if none was found.
getInternalNames :: Monad m => Identifier -> TC m (Set (Ident, Type))
getInternalNames name = do
  (Context _ idents res _ _ _ _) <- get
  Set.map (\a -> (a, idents Map.! a)) <$>
    case Map.lookup name res of
      Nothing -> pure mempty
      Just x -> pure x

-- | Given a function name for error messages, a set of possible instantiations, a list of argument types
-- and a return value, try to find an instantiation together with the necessary coercions.
resolve :: Monad m => Identifier -> Set (Ident, Type) -> [Set InType] -> ReturnValue -> TC m ((Ident, [RCoercion]), OutType)
resolve name res' intypes ret = do
  coe <- coercions <$> get
  pick coe $ Set.toList (feasibleNames coe res')
  where
    feasibleNames coe =
        Set.map (\((t, Just a), typ) -> ((t, a), typ)) . Set.filter (isJust . snd . fst)
        . Set.map (\(a, t) -> ((a, coerceTo t coe), t))

    coerceTo t coe = case t of
      Sort -> Nothing
      Pred is _ -> coerceInto intypes is coe

    typ = case ret of
      Proposition -> Pred intypes Prop
      Value -> Pred intypes $ InType $ Set.singleton $ Signature identHole 

    getArgs (t, Pred is o) = pure ((t, o), is)
    getArgs _ = errorWithMessage "getArgs pattern not matched!"

    pick _ [] = failWithMessage $ ResolveFailed name typ
    pick coe xs = do
      xs' <- mapM getArgs xs
      case leastGeneral xs' coe of
        Just (x, _) -> pure $ fst x
        Nothing -> failWithMessage $ ResolveAmbigous name typ (map snd xs)

addType :: Monad m => Ident -> Type -> TC m ()
addType i t = do
  modify $ \s -> s
    { typings = Map.insert i t (typings s)
    , overloadings = Map.insertWith (<>) (sourceIdentifier i) (Set.singleton i) (overloadings s)}

locally :: Monad m => TC m a -> TC m a
locally action = do
  ctx <- get
  a <- action
  put ctx
  pure a

checkWf :: Monad m => SourcePos -> Ident -> [Term] -> WfBlock -> TC m WfBlock
checkWf p name' ex' wf = do
  m <- (Map.lookup name' . defs) <$> get
  case m of
    Just (NFTerm ex [] _) ->
      pure WellFormed
    Just (NFTerm ex as _) -> do
      let goal = simp $ List.foldl1' (\a b -> App And [a, b]) as
      let goal' = substAll (Map.fromList $ zip (map fst ex) ex') goal
      assm <- assumptions <$> get
      vars <- inferMap <$> get
      let vars' = catMaybes $ flip map (Map.toList vars) $ \(i, x) -> case x of
            Provided xs -> Just (i, xs)
            DefaultObject -> Just (i, Set.singleton $ Signature identObject)
            NotProvided -> Nothing -- TODO (not ideal, but else wf blocks obstruct inference)
      let nfgoal = NFTerm vars' assm goal'
      pure $ WfProof nfgoal (ProofByHints [])
    Nothing -> errorWithMessage $ "Definition " <> pretty name' <> " not found!"

addVar :: Monad m => Ident -> InferType InType -> TC m ()
addVar v m = get >>= \i -> put $ i { inferMap = Map.insert v m (inferMap i) }

setVar :: Monad m => Ident -> InferType InType -> TC m ()
setVar v m = get >>= \i -> put $ i { inferMap = Map.insert v m (inferMap i) }

delVar :: Monad m => Ident -> TC m ()
delVar v = get >>= \i -> put $ i { inferMap = Map.delete v (inferMap i) }

lookupVar :: Monad m => Ident -> TC m (Maybe (InferType InType))
lookupVar v = gets $ Map.lookup v . inferMap

withVar :: Monad m => Ident -> InferType InType -> TC m a -> TC m (a, InferType InType)
withVar v m a = do addVar v m; x <- a; t <- lookupVar v; delVar v; pure (x, inferFromMaybe t)
  where
    inferFromMaybe Nothing = NotProvided
    inferFromMaybe (Just a) = a

withAssumption :: Monad m => Term -> TC m a -> TC m a
withAssumption assm action = do
  modify $ \s -> s { assumptions = assm : assumptions s }
  a <- action
  modify $ \s -> s { assumptions = tail $ assumptions s }
  pure a

-- | Type check applications and insert coercions.
-- Forward type-checking: We assume that the identifiers without arguments are typed
-- and infer the type/resolved name of identifiers with arguments from them.
checkTerm :: Monad m => SourcePos -> ReturnValue -> Term -> TC m (OutType, Term)
checkTerm p retval t = do
  modify $ \s -> s { currentLocation = (currentLocation s) { errorFormula = Just t } }
  (o, t') <- go NotProvided t
  case (o, retval) of
    (Prop, Proposition) -> pure (o, simp t')
    (InType _, Value) -> pure (o, simp t')
    _ -> failWithMessage $ WrongReturnValue o retval
  where
    goBinder v m' t err = do
      ((ret, t), inferredType) <- withVar v m' $ go NotProvided t
      case ret of
        Prop -> pure ()
        _ -> failWithMessage err
      m'' <- case m' <> inferredType of
        Provided m' -> pure m'
        DefaultObject -> pure $ Set.singleton $ Signature identObject
        NotProvided -> failWithMessage $ CouldntInferTypeOf v 
      pure (m'', t)

    checkApp p name' type' explicit wf = case type' of
      Sort -> failWithMessage $ SortInTerm name'
      Pred is t -> do
        if length is /= length explicit
          then failWithMessage $ WrongNumberOfArgumentsFor name'
          else do
            (argtypes, explicit') <- unzip <$> zipWithM go (map Provided is) explicit
            argintypes <- forM argtypes $ \case
                  Prop -> failWithMessage $ PropAsArgOf (sourceIdentifier name')
                  InType t' -> pure t'
            coe <- coercions <$> get
            let coes = coerceInto' argintypes is coe
            coes' <- forM (List.zip4 coes [1::Int ..] is argintypes) $ \(c, i, exp, have) -> case c of
                  Nothing -> failWithMessage $ NoCoercionFound i name' exp have
                  Just t -> pure t
            let ex' = zipWith Coe coes' explicit'
            wf' <- checkWf p name' ex' wf
            pure (t, AppWf (Resolved name') ex' wf')

    go :: Monad m => InferType InType -> Term -> TC m (OutType, Term)
    go inferCtx = \case
      Forall v m t -> do
        let m' = if Set.null m then NotProvided else Provided m
        (m'', t) <- goBinder v m' t $ ForallOfValue v
        pure (Prop, Forall v m'' t)
      Exists v m t -> do
        let m' = if Set.null m then NotProvided else Provided m
        (m'', t) <- goBinder v m' t $ ExistsOfValue v
        pure (Prop, Exists v m'' t)
      FinClass t cv ts -> do
        let t' = if Set.null t then NotProvided else Provided t
        let toInType x = case x of
               Prop -> failWithMessage PropInFiniteClass
               InType x -> pure x
        ts' <- mapM (\(a,b) -> toInType a >>= \c -> pure (b, [c])) =<< mapM (go t') ts
        coe <- coercions <$> get
        case mostGeneral ts' coe of
          Just ((_, [tt]), coes) -> do
            let ts'' = zipWith ($) (map (Coe . head) coes) $ map fst ts'
            mv <- case coerceInto [tt] [Set.singleton $ Signature identObject] coe of
              Just ts -> pure $ head ts
              Nothing -> failWithMessage $ FiniteClassOfNonObjects (FinClass t cv ts) tt
            (retType, retTypeCoe) <- case coerceInto [Set.singleton $ Signature identSet] [Set.singleton $ Signature identClass] coe of
              Just ts -> pure $ (Set.singleton $ Signature identSet, head ts)
              Nothing -> errorWithMessage "Finset syntax needs to coerce sets to classes!"
            pure (InType retType, FinClass tt (Just (ClassInfo mv retType retTypeCoe)) ts'')
          _ -> failWithMessage $ FiniteClassNoLeastGeneral (FinClass t cv ts) (map snd ts')
      Class v m mm _ t -> do
        let m' = if Set.null m then NotProvided else Provided m
        (m'', t) <- goBinder v (m' <> DefaultObject) t $ ClassOfValue v
        coe <- coercions <$> get
        mm' <- traverse (go NotProvided) mm
        mv <- case coerceInto [m''] [Set.singleton $ Signature identObject] coe of
          Just ts -> pure $ head ts
          Nothing -> failWithMessage $ ClassOfNonObjects (Class v m'' (snd <$> mm') (Just (ClassInfo mempty (Set.singleton $ Signature identClass) mempty)) t) m''
        (retType, retTypeCoe, mm'') <- case maybe (InType $ Set.singleton $ Signature identClass) fst mm' of
          Prop -> failWithMessage InClassIsProp
          InType retType -> case coerceInto [retType] [Set.singleton $ Signature identClass] coe of
            Just ts -> pure $ (retType, head ts, Coe (head ts) . snd <$> mm')
            Nothing -> failWithMessage $ InClassIsNotClass (snd <$> mm') retType
        pure (InType retType, Class v m'' mm'' (Just (ClassInfo mv retType retTypeCoe)) t)
      AppWf (Resolved name) explicit wf -> do
        varType <- lookupVar name
        case (varType, explicit) of
          (Just t, []) -> case t <> inferCtx of
            Provided t -> do setVar name $ Provided t; pure (InType t, AppWf (Resolved name) [] NoWf)
            DefaultObject -> do
              let t = Signature identObject
              setVar name $ Provided $ Set.singleton t; pure (InType $ Set.singleton t, AppWf (Resolved name) [] NoWf)
            NotProvided -> failWithMessage $ CouldntInferTypeOf name
          (Just _, (_:_)) -> failWithMessage $ VarAppliedTo name explicit
          (Nothing, _) -> do
              type' <- fromJust . Map.lookup name . typings <$> get
              checkApp p name type' explicit wf
      AppWf (Unresolved name) explicit wf -> do
        names <- getInternalNames name
        case Set.toList names of
          [] -> failWithMessage $ UnknownFunction name
          [(name', type')] -> checkApp p name' type' explicit wf
          (_:_:_) -> do
            (argtypes, explicit') <- unzip <$> mapM (go NotProvided) explicit
            argintypes <- forM argtypes $ \case
                  Prop -> failWithMessage $ PropAsArgOf name
                  InType t' -> pure t'
            res <- resolve name names argintypes retval
            case res of
              ((name', coe), t) -> do
                let ex' = zipWith Coe coe explicit'
                wf' <- checkWf p name' ex' wf
                pure (t, AppWf (Resolved name') ex' wf')
      App Eq [a, b] -> do
        inferMap' <- inferMap <$> get
        case a of
          -- This case is important for the auto-generated finite set code.
          -- Here we can infer the type of the implicit variable.
          AppWf (Resolved v0) [] _ | Just DefaultObject <- Map.lookup v0 inferMap' -> do
            (tb, b') <- go NotProvided b
            case tb of
              Prop -> failWithMessage $ PropInEquality (AppWf (Resolved v0) [] NoWf) b'
              InType ib -> do
                setVar v0 (Provided ib)
                pure (Prop, App Eq [AppWf (Resolved v0) [] NoWf, b'])
          _ -> do
            (ta, a') <- go NotProvided a
            (tb, b') <- go NotProvided b
            coe <- coercions <$> get
            case (ta, tb) of
              (InType ia, InType ib) -> case (coerceInto [ia] [ib] coe, coerceInto [ib] [ia] coe) of
                (Just ts, _) -> pure (Prop, App Eq [Coe (head ts) a', b'])
                (_, Just ts) -> pure (Prop, App Eq [a', Coe (head ts) b'])
                (Nothing, Nothing) -> failWithMessage $ NonCoercibleEquality a' ia b' ib
              _ -> failWithMessage $ PropInEquality a' b'
      App And [a, b] -> do
        (_, a') <- go NotProvided a
        (_, b') <- withAssumption a' $ go NotProvided b
        pure (Prop, simp $ App And [a', b'])
      App Imp [a, b] -> do
        (_, a') <- go NotProvided a
        (_, b') <- withAssumption a' $ go NotProvided b
        pure (Prop, simp $ App Imp [a', b'])
      App op args -> do
        (_, res) <- unzip <$> mapM (go NotProvided) args
        pure (Prop, simp $ App op res)
      Coe cs t -> go inferCtx t
      Typing ty t -> do
        (_, t) <- fmap (Typing ty) <$> go inferCtx t
        pure (Prop, t)
      Tag _ t -> go inferCtx t

checkNFTerm :: Monad m => SourcePos -> ReturnValue -> NFTerm -> TC m (OutType, NFTerm)
checkNFTerm p retval (NFTerm ex as b) = do
  mapM_ restrictAndAdd ex
  as' <- mapM (fmap snd . checkTerm p Proposition) as
  (o, b') <- checkTerm p retval b
  ex' <- mapM lookupProvided ex
  pure (o, NFTerm ex' as' b')
  where
    restrictAndAdd (i, s) = addVar i $ if Set.null s then NotProvided else Provided s
    lookupProvided (i, _) = do
      t <- lookupVar i
      delVar i
      case t of
        Just (Provided t) -> pure (i, t)
        _ -> failWithMessage $ CouldntInferTypeOf i

splitExists :: Term -> (Term, [(Ident, Set InType)])
splitExists = \case
  Exists i t e -> ((i, t):) <$> splitExists e
  e -> (e, [])

lastMay :: [a] -> Maybe a
lastMay [] = Nothing
lastMay [x] = Just x
lastMay (_:xs) = lastMay xs

checkProof :: HasUnique m => Term -> Located Prf
           -> TC m (Located Prf, Term, [Hypothesis])
checkProof goal (Located p t) = case t of
  Intro i _ -> do
    case goal of
      Forall i' t goal' | i == i' -> do
        addVar i (Provided t)
        pure (Located p $ Intro i t, goal', [TypeDef i (Pred [] $ InType t)])
      _ -> failWithMessage $ IntroNotApplicable i t goal
  Assume as -> do
    (_, as') <- checkTerm p Proposition as
    case goal of
      App Imp [a, b] | a == as' -> do
        assume <- newIdent $ NormalIdent "assume"
        pure (Located p $ Assume as', b, [Given assume as'])
      _ -> failWithMessage $ AssumptionNotApplicable as' goal
  AssumeTC as -> do
    case goal of
      App Imp [a, b] | a == as -> do
        assume <- newIdent $ NormalIdent "assume"
        pure (Located p $ Assume as, b, [Given assume as])
      _ -> failWithMessage $ AssumptionNotApplicable as goal
  ByContradiction _ -> do
    let negGoal = App Not [goal]
    negatedGoal <- newIdent $ NormalIdent "negated_goal"
    pure (Located p (ByContradiction negGoal), App Bot [], [Given negatedGoal negGoal])
  Suffices t pbl -> do
    (_, t') <- checkTerm p Proposition t
    bl <- checkProofBlock (termToNF $ App Imp [t', goal]) p pbl
    pure (Located p $ Suffices t' bl, t', [])
  Define x tt t -> do
    let givenType = if Set.null tt then NotProvided else Provided tt
    (o, t') <- checkTerm p Value t
    type' <- case o of
      Prop -> errorWithMessage "Definition: expected value but got proposition"
      InType o -> case givenType of
        Provided o' -> if o == o' then pure o
          else failWithMessage $ DefinitionWronglyTyped x o' o 
        _ -> pure o
    addVar x (Provided type')
    defineName <- newIdent $ NormalIdent "define"
    pure (Located p $ Define x type' t', goal,
      [Given defineName (App Eq [AppWf (Resolved x) [] NoWf, t']), TypeDef x $ Pred [] $ InType type'])
  Subclaim n nf pbl -> do
    (_, nf') <- checkNFTerm p Proposition nf
    bl <- checkProofBlock nf' p pbl
    pure (Located p $ Subclaim n nf' bl, goal, [Given n (termFromNF nf')])
  Choose vs t pbl -> do
    let ex = List.foldl' (\e (i, t) -> Exists i t e) t vs
    (_, ex') <- checkTerm p Proposition ex
    let (t', vs') = splitExists ex'
    let vst = map (\(v, t) -> TypeDef v $ Pred [] (InType t)) vs'
    bl <- checkProofBlock (NFTerm [] [] ex') p pbl
    mapM_ (\(i, t) -> addVar i (Provided t)) vs'
    chooseName <- newIdent $ NormalIdent "choose"
    pure (Located p $ Choose vs' t' bl, goal,
      Given chooseName t' : vst)
  Cases cs -> do
    cs' <- forM cs $ \(c, topClaim, pbl) -> do
      (_, c') <- checkTerm p Proposition c
      withAssumption c' $ do
        (_, topClaim') <- checkTerm p Proposition topClaim
        bl <- checkProofBlock (NFTerm [] [] topClaim') p pbl
        claim <- case bl of
          ProofByTCTactics ts -> pure $ foldrM (flip unroll) topClaim'
            $ map (\(a, _, _) -> located a) ts
          _ -> failWithMessage EmptyCases
        case claim of
          Just claim -> pure (c', claim, bl)
          Nothing -> errorWithMessage $ "Terminal cases appear in a non-terminal case statement."
    casesName <- newIdent $ NormalIdent "cases"
    pure (Located p $ Cases cs', goal, map (\(a, b, _) -> Given casesName $ App Imp [a,b]) cs')
  TerminalCases cs -> do
    cs' <- forM cs $ \(c, pbl) -> do
      (_, c') <- checkTerm p Proposition c
      withAssumption c' $ do
        bl <- checkProofBlock (NFTerm [] [] goal) p pbl
        pure (c', bl)
    pure (Located p $ TerminalCases cs', App Top [], [])

-- | Unroll (or turn-back) a tactic that has been applied before a term.
-- This is used for subclaims and not goals: e.g. the Suffices tactic is ignored.
unroll :: Term -> Prf -> Maybe Term
unroll claim = \case
  Intro i t -> Just $ Forall i t claim
  Assume as -> Just $ App Imp [as, claim]
  AssumeTC as -> Just $ App Imp [as, claim]
  ByContradiction negGoal -> Just $ App Imp [negGoal, claim]
  Suffices _ _ -> Just $ claim
  Define x tt t -> Just $ Exists x tt (App Eq [AppWf (Resolved x) [] NoWf, t])
  Subclaim _ t _ -> Just $ App And [termFromNF t, claim]
  Choose vs t _ -> Just $ List.foldl' (\c (i, t) -> Exists i t c) (App And [t, claim]) vs
  Cases cs -> Just $ List.foldl' (\a b -> App And [a, b]) claim $ map (\(a, b, _) -> App Imp [a, b]) cs
  TerminalCases _ -> Nothing

foldTactics :: Monad m => (g -> t -> m (t', g, hs)) -> g -> [t] -> m [(t', g, hs)]
foldTactics _ _ [] = pure []
foldTactics f g (t:ts) = do
  r@(_, g', _) <- f g t
  (r:) <$> foldTactics f g' ts

-- | Check a proof block and insert intro/assume automatically.
checkProofBlock :: HasUnique m => NFTerm -> SourcePos -> PrfBlock -> TC m PrfBlock
checkProofBlock nf@(NFTerm ex as _) p = \case
  ProofByHints hs -> pure $ ProofByHints hs
  ProofByTactics ts -> locally $ do
    let intros = map (Located p . uncurry Intro) ex
    let assms = map (Located p . AssumeTC) as
    ts1 <- foldTactics checkProof (termFromNF nf) $ intros ++ assms
    let g2 = maybe (termFromNF nf) (\(_, g, _) -> g) (lastMay ts1)
    ts2 <- foldTactics checkProof g2 $ ts
    pure $ ProofByTCTactics $ ts1 ++ ts2
  ProofByTCTactics ts -> pure $ ProofByTCTactics ts

typecheck :: HasUnique m => [Located Stmt] -> m (Either TypeErrors [Located Stmt])
typecheck = flip evalStateT mempty . runValidateT . fromTC . mapM go
  where
    go :: HasUnique m => Located Stmt -> TC m (Located Stmt)
    go (Located p stmt) = do
      modify $ \s -> s { currentLocation = (currentLocation s) { errorBlock = Just stmt, errorPosition = p }}
      Located p <$> case stmt of
        IntroSort sort -> do
          modify $ \s -> s { typings = Map.insert sort Sort (typings s) }
          pure $ IntroSort sort
        IntroAtom i ex as -> do
          (_, nf') <- checkNFTerm p Proposition (NFTerm ex as (App Top []))
          let is = map snd $ nfArguments nf'
          addType i (Pred is Prop)
          modify $ \s -> s { defs = Map.insert i nf' (defs s) }
          pure $ IntroAtom i (nfArguments nf') (nfAssumptions nf')
        IntroSignature i o ex as -> do
          (_, nf') <- checkNFTerm p Proposition (NFTerm ex as (App Top []))
          let is = map snd $ nfArguments nf'
          addType i (Pred is (InType o))
          modify $ \s -> s { defs = Map.insert i nf' (defs s) }
          pure $ IntroSignature i o (nfArguments nf') (nfAssumptions nf')
        Predicate i nf -> do
          (_, nf') <- checkNFTerm p Proposition nf
          let is = map snd (nfArguments nf')
          addType i (Pred is Prop)
          modify $ \s -> s { defs = Map.insert i nf' (defs s) }
          pure $ Predicate i nf'
        Function i _ nf -> do
          (o, nf') <- checkNFTerm p Value nf
          case o of
            Prop -> errorWithMessage "Function checking returned a prop where a value was expected."
            InType o -> do
              let is = map snd (nfArguments nf')
              addType i (Pred is (InType o))
              modify $ \s -> s { defs = Map.insert i nf' (defs s) }
              pure $ Function i o nf'
        Axiom n nf -> do
          (_, nf') <- checkNFTerm p Proposition nf
          pure $ Axiom n nf'
        Claim n nf pbl -> do
          (_, nf') <- checkNFTerm p Proposition nf
          bl <- checkProofBlock nf' p pbl
          pure $ Claim n nf' bl
        Coercion name from to -> do
          modify $ \s -> s { coercions = add (from, to) name (coercions s) }
          _ <- addType name (Pred [Set.singleton $ Signature from] (InType $ Set.singleton $ Signature to))
          x <- newIdent $ NormalIdent "x"
          let nf = NFTerm [(x, Set.singleton $ Signature from)] [] (App Top [])
          modify $ \s -> s { defs = Map.insert name nf (defs s) }
          pure $ Coercion name from to