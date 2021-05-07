{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RankNTypes #-}

-- | Basic type-checking using a type-inference modelled
-- roughly after the paper 'A Second Look at Overloading' by Odersky et al.

module SAD.Core.Typecheck (typecheck, coercionsToTerm) where

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.List as List
import Data.Functor.Identity
import Control.Monad.State
import Data.Maybe
import Data.Foldable (foldrM)

import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.String (renderString)
import SAD.Core.SourcePos (SourcePos, noSourcePos)
import qualified SAD.Core.Message as Message
import qualified Isabelle.Naproche as Naproche

import SAD.Core.Identifier
import SAD.Core.Typed
import SAD.Core.Coerce

data InferType a
  = NotProvided
  | DefaultObject
  | Provided a
  deriving (Eq, Ord, Show)

-- | Take the left type if given and else the more informative.
instance Semigroup (InferType a) where
  NotProvided <> a = a
  DefaultObject <> (Provided a) = Provided a
  DefaultObject <> _ = DefaultObject
  Provided a <> _ = Provided a

data Context = Context
  { errorBlock :: Stmt Set ()
  , errorFormula :: Maybe (Doc ())
  , errorPosition :: SourcePos
  , typings :: Map Ident Type
    -- ^ a type for each internal name
    -- this is extended after each section and otherwise read-only.
  , overloadings :: Map Ident (Set Ident)
    -- ^ possible overloadings for an identifier
    -- this maps names as the user provided them to internal
    -- names which are unique. For example when several
    -- notions of subset are defined, the internal names
    -- might be "subset, subset2, ..."
    -- this is extended after each section and otherwise read-only.
  , inferMap :: Map Ident [InferType InType]
    -- ^ the types of variables as the were inferred.
    -- When the type of a variable was not provided
    -- (for example because the variable was inserted by the parser)
    -- we try to infer it. This is biased towards the first occurrence
    -- of the variable similar to HM type inference.
    -- this is only used during type-checking and emtpy otherwise.
    -- When variables shadow others we add them to the front of the
    -- list. Once the shadowing is over, we pop that entry.
  , coercions :: Coercions Ident Ident
    -- ^ coercions defined in the text
  , defs :: Map Ident (NFTerm Identity ())
    -- ^ definitions: the difference to 'typings' is that
    -- this contains well-formedness instead of type information
    -- This is used to check the well-formedness blocks in the text.
  } deriving (Show)

type TC m a = StateT Context m a

failWithMessage :: Message.Comm m => Doc ann -> TC m a
failWithMessage txt = do
  src <- errorPosition <$> get
  f <- errorFormula <$> get
  b <- errorBlock <$> get
  w <- lift $ Message.textFieldWidth
  lift $ Message.error Naproche.origin_reasoner src
    $ renderString $ layoutSmart
        (defaultLayoutOptions { layoutPageWidth = AvailablePerLine w 1.0 })
    $  "\nWhile checking the block:\n\n" <> pretty b
    <> (case f of Nothing -> ""; Just f -> "\nmore specifically, the formula:\n\n" <> unAnnotate f <> "\n")
    <> "\n" <> txt

-- | Danger: Costly in second argument due to coercions
instance Semigroup Context where
  (<>) (Context _ _ _ t1 r1 i1 c1 d1) (Context eb ef ep t2 r2 i2 c2 d2) = Context eb ef ep (t1 <> t2) (r1 <> r2) (i1 <> i2) (c1 <> c2) (d1 <> d2)

instance Monoid Context where
  mempty = Context undefined Nothing noSourcePos mempty mempty mempty mempty mempty

coercionsToTerm :: [Ident] -> (Term f t -> Term f t)
coercionsToTerm = go . reverse
  where
    go [] = id
    go (x:xs) = go xs . \t -> AppWf x [t] noWf

coerceInto :: [InType] -> [InType] -> Coercions Ident Ident -> Maybe [[Ident]]
coerceInto is is' coe = if length is == length is'
  then sequence $ zipWith (\(Signature a) (Signature b) -> coerce (a, b) coe) is is'
  else Nothing

-- | Given a list of coercible values, try to find a value that is generalized by
-- all of them and is in the list. Then give the coercions to this value.
-- O(n) calls to coerceInto.
-- Depending of the direction of the arrows, this will either compute the most
-- or least general form.
generalize :: (forall a b. (a -> a -> b) -> a -> a -> b) -> [(t, [InType])] -> Coercions Ident Ident -> Maybe ((t, [InType]), [[[Ident]]])
generalize _ [] _ = Nothing
generalize direction (x:xs) coe = flip checkRoot (x:xs) $ getRoot x xs
  where
    -- We find an element 'root' with the property that if it is
    -- comparable with another element 'x' then 'x -> root'.
    -- If the coercions form a DAG this is actually a root.
    -- Due to transitivity this can be done in O(n).
    -- We then check if it is comparable to all elements.
    getRoot root [] = root
    getRoot root (x:xs) = case (direction coerceInto) (snd x) (snd root) coe of
      Just _ -> getRoot x xs
      Nothing -> getRoot root xs
    checkRoot root = fmap (\b -> (root,b)) . mapM (\x -> (direction coerceInto) (snd root) (snd x) coe)

leastGeneral :: [(t, [InType])] -> Coercions Ident Ident -> Maybe ((t, [InType]), [[[Ident]]])
leastGeneral = generalize id

mostGeneral :: [(t, [InType])] -> Coercions Ident Ident -> Maybe ((t, [InType]), [[[Ident]]])
mostGeneral = generalize flip

data ReturnValue = Value | Proposition
  deriving (Eq, Ord, Show)

-- | Get the types and internal names of an identifier.
-- This may be empty if none was found.
getInternalNames :: Message.Comm m => Ident -> TC m (Set (Ident, Type))
getInternalNames name = do
  (Context _ _ _ idents res _ _ _) <- get
  Set.map (\a -> (a, idents Map.! a)) <$>
    case Map.lookup name res of
      Nothing -> pure mempty
      Just x -> pure x

resolve :: Message.Comm m => Ident -> Set (Ident, Type) -> [InType] -> ReturnValue -> TC m ((Ident, [[Ident]]), OutType)
resolve name res' intypes ret = do
  (Context _ _ _ _ _ _ coe _) <- get
  pick coe $ Set.toList (feasibleNames coe res')
  where
    feasibleNames coe =
        Set.map (\((t, Just a), typ) -> ((t, a), typ)) . Set.filter (\a -> snd (fst a) /= Nothing) 
        . Set.map (\(a, t) -> ((a, coerceTo t coe), t))

    coerceTo t coe = case t of
      Sort -> Nothing
      Pred is _ -> coerceInto intypes is coe

    typ = case ret of
      Proposition -> Pred intypes Prop
      Value -> Pred intypes $ InType $ Signature (NormalIdent "[??]")

    getArgs (t, (Pred is o)) = pure ((t, o), is)
    getArgs _ = failWithMessage $ "Internal: getArgs pattern not matched!"

    pick _ [] = failWithMessage $ "Resolve failed: " <> pretty name <> " of type " <> pretty typ
    pick coe xs = do
      xs' <- mapM getArgs xs
      case leastGeneral xs' coe of
        Just (x, _) -> pure $ fst x
        Nothing -> failWithMessage $ "Resolve ambigous: " <> pretty name <> " of type\n  " <> nest 2 (pretty typ)
            <> "\ncan be resolved as any of:\n  " <> nest 2 (vsep (map (pretty . snd) xs))

addType :: Monad m => Ident -> Type -> TC m Ident
addType i t = do
  taken <- Map.lookup i . overloadings <$> get
  let i' = newIdent i $ fromMaybe mempty taken
  modify $ \s -> s
    { typings = Map.insert i' t (typings s)
    , overloadings = Map.insertWith (<>) i (Set.singleton i') (overloadings s)}
  pure i'

locally :: Monad m => TC m a -> TC m a
locally action = do
  ctx <- get
  a <- action
  put ctx
  pure a

-- | Ad-hoc monad for inference. This was added to make the types match,
-- but should be refactored away once we have proper type inference.
class (Show (f InType), Pretty (f InType), Show (f ClassInfo)) => Infer f where
  restrictType :: Message.Comm m => Ident -> f InType -> TC m (InferType InType)

instance Infer Identity where
  restrictType _ (Identity t) = pure $ Provided t

instance Infer Set where
  -- | Restrict the set of types of a variable to no more than one.
  -- This is achieved by trying to find a least general type to
  -- coerce into and fails if that is not possible.
  restrictType :: Message.Comm m => Ident -> Set InType -> TC m (InferType InType)
  restrictType v s = do
    coe <- coercions <$> get
    case Set.toList s of
      [] -> pure NotProvided
      s -> case leastGeneral (map (\i -> (i, [i])) s) coe of
        Nothing -> failWithMessage $ "The variable " <> pretty v
          <> " has been defined with the mutually non-coercible types: "
          <> vsep (map pretty s)
        Just ((a, _), _) -> pure $ Provided a

singleTypedVar :: (Infer f, Message.Comm m) => Ident -> f InType -> TC m InType
singleTypedVar v s = do
  m <- restrictType v s
  case m of
    Provided m -> pure m
    _ -> failWithMessage $ "Untyped bind: " <> pretty v

checkWf :: (Infer f, Message.Comm m) => SourcePos -> Ident -> [Term Identity ()] -> (WfBlock f ()) -> TC m (WfBlock Identity ())
checkWf p name' ex' wf = do
  m <- (Map.lookup name' . defs) <$> get
  case m of
    Just (NFTerm im ex as _) -> do
      let imSet = Set.fromList $ map fst im
      let wfSet = Set.fromList $ map fst $ wfImplicits wf
      let superflous = wfSet Set.\\ imSet
      when (not $ Set.null superflous) $ do
        failWithMessage $ "The following implicits where supplied but could not be used: " <> pretty superflous
      let notGivenSet = imSet Set.\\ wfSet
      let (given, notGiven) = List.partition (\x -> fst x `Set.member` notGivenSet) im
      let as' = map (substAll (Map.fromList $ zip (map fst ex) ex')) as

      -- TODO: 'notGiven' variables may shadow variables used in the terms supplied as ex'
      let goal = simp $ foldr (\(i, t) -> Exists i t) (List.foldl' (\a b -> App And [a, b]) (App Top []) as') notGiven
      assms <- flip mapM (wfImplicits wf) $ \(i, t) -> do 
        (o, t') <- checkTerm p Value t
        case o of
          Prop -> failWithMessage $ "Given implicit is a proposition!"
          InType o -> do
            let (Identity expected) = fromJust $ List.lookup i im
            if o /= expected then
              failWithMessage $ "Implicit " <> pretty i <> " should have type " <> pretty expected <> " but you supplied an expression of type " <> pretty o
            else pure (i, t')
      let assms' = map (\(i, t) -> App Eq [AppWf i [] noWf, t]) assms
      let nfgoal = (NFTerm given [] assms' goal)
      case goal of
        App Top [] -> pure $ WfBlock assms Nothing
        _ -> do
          wfPrf' <- case snd <$> wfProof wf of
            Nothing -> checkProofBlock nfgoal p $ (ProofByHints [] :: PrfBlock Identity ())
            Just (ProofByHints hs) -> checkProofBlock nfgoal p $ (ProofByHints hs :: PrfBlock Identity ())
            Just (ProofByTactics ts) -> checkProofBlock nfgoal p $ ProofByTactics ts
            Just (ProofByTCTactics ts') -> pure (ProofByTCTactics ts')
          pure $ WfBlock assms $ Just (nfgoal, wfPrf')
    Nothing -> pure noWf

addVar :: Message.Comm m => Ident -> InferType InType -> TC m ()
addVar v m = get >>= \i -> put $ i { inferMap = Map.insertWith (++) v [m] (inferMap i) }

setVar :: Message.Comm m => Ident -> InferType InType -> TC m ()
setVar v m = get >>= \i -> put $ i { inferMap = Map.update headSet v (inferMap i) }
  where headSet xs = case xs of [] -> Just [m]; _:xs -> Just (m:xs)

delVar :: Message.Comm m => Ident -> TC m ()
delVar v = get >>= \i -> put $ i { inferMap = Map.update tailMay v (inferMap i) }
  where tailMay xs = case xs of [] -> Nothing; _:xs -> Just xs

lookupVar :: Monad m => Ident -> TC m (Maybe (InferType InType))
lookupVar v = (flip (>>=) headMay . Map.lookup v . inferMap) <$> get
  where headMay xs = case xs of [] -> Nothing; x:_ -> Just x

withVar :: Message.Comm m => Ident -> InferType InType -> TC m a -> TC m (a, InferType InType)
withVar v m a = do addVar v m; x <- a; t <- lookupVar v; delVar v; pure (x, inferFromMaybe t)
  where
    inferFromMaybe Nothing = NotProvided
    inferFromMaybe (Just a) = a

-- | Type check applications and insert coercions.
-- Forward type-checking: We assume that the identifiers without arguments are typed
-- and infer the type/resolved name of identifiers with arguments from them.
checkTerm :: (Infer f, Message.Comm m) => SourcePos -> ReturnValue -> Term f () -> TC m (OutType, Term Identity ())
checkTerm p retval t = do
  modify $ \s -> s { errorFormula = Just $ pretty t }
  (o, t') <- go NotProvided t
  case (o, retval) of
    (Prop, Proposition) -> pure (o, simp t')
    (InType _, Value) -> pure (o, simp t')
    _ -> failWithMessage $ "The term has type " <> pretty o <> " but was expected to return a " <> pretty (show retval)
  where
    goBinder v m' t err = do
      ((ret, t), inferredType) <- withVar v m' $ go NotProvided t
      case ret of
        Prop -> pure ()
        _ -> failWithMessage err
      m'' <- case m' <> inferredType of
        Provided m' -> pure m'
        DefaultObject -> pure $ Signature identObject
        NotProvided -> failWithMessage $ "Couldn't infer type of " <> pretty v
      pure $ (m'', t)

    th 1 = "st"
    th 2 = "nd"
    th _ = "th"

    go :: (Message.Comm m, Infer f) => InferType InType -> Term f () -> StateT Context m (OutType, Term Identity ())
    go inferCtx = \case
      Forall v m t -> do
        m' <- restrictType v m
        (m'', t) <- goBinder v m' t $ "Read ∀" <> pretty v <> " _ and expected a proposition but got a value!"
        pure $ (Prop, Forall v (Identity m'') t)
      Exists v m t -> do
        m' <- restrictType v m
        (m'', t) <- goBinder v m' t $ "Read ∃" <> pretty v <> " _ and expected a proposition but got a value!"
        pure $ (Prop, Exists v (Identity m'') t)
      FinClass t cv ts -> do
        t' <- restrictType (NormalIdent "") t
        let toInType x = case x of
               Prop -> failWithMessage $ "Proposition in finite class syntax!"
               InType x -> pure x
        ts' <- mapM (\(a,b) -> toInType a >>= \c -> pure (b, [c])) =<< mapM (go t') ts
        coe <- coercions <$> get
        case mostGeneral ts' coe of
          Just ((_, [tt]), coes) -> do
            let ts'' = zipWith ($) (map (coercionsToTerm . head) coes) $ map fst ts'
            mv <- case coerceInto [tt] [Signature identObject] coe of
              Just ts -> pure $ head ts
              Nothing -> failWithMessage $ "The finite class: " <> pretty (FinClass t cv ts)
                <> "\n contains elements of type " <> pretty tt <> " but those can't be coerced to objects!"
            (retType, retTypeCoe) <- case coerceInto [Signature identSet] [Signature identClass] coe of
              Just ts -> pure $ (Signature identSet, head ts)
              Nothing -> failWithMessage $ "Internal error: Finset syntax needs to coerce sets to classes!"
            pure (InType $ retType, FinClass (Identity tt) (Identity (ClassInfo mv retType retTypeCoe)) ts'')
          _ -> failWithMessage $ "Finite class contains elements which are of different types "
            <> " and a least general one couldn't be found among: " <> pretty (map snd ts')
      Class v m mm _ t -> do
        m' <- restrictType v m
        (m'', t) <- goBinder v (m' <> DefaultObject) t
          $ "Read {" <> pretty v <> " | _ } and expected a proposition but got a value!"
        coe <- coercions <$> get
        mm' <- traverse (go NotProvided) mm
        mv <- case coerceInto [m''] [Signature identObject] coe of
          Just ts -> pure $ head ts
          Nothing -> failWithMessage $ "The class: " <> pretty (Class v (Identity m'') (snd <$> mm') (Identity (ClassInfo [] (Signature identClass) [])) t)
            <> "\n contains elements of type " <> pretty m'' <> " but those can't be coerced to objects!"
        (retType, retTypeCoe, mm'') <- case maybe (InType $ Signature identClass) fst mm' of
          Prop -> failWithMessage $ "Prop can't be used as 'in' class."
          InType retType -> case coerceInto [retType] [Signature identClass] coe of
            Just ts -> pure $ (retType, head ts, (coercionsToTerm (head ts) . snd) <$> mm')
            Nothing -> failWithMessage $ "The " <> pretty retType <> " given as " <> pretty (snd <$> mm')
              <> " can't be coerced into a class despite being used as an 'in' term."
        pure (InType retType, Class v (Identity m'') mm'' (Identity (ClassInfo mv retType retTypeCoe)) t)
      AppWf name explicit wf -> do
        varType <- lookupVar name
        case (varType, explicit) of
          (Just t, []) -> case t <> inferCtx of
            Provided t -> do setVar name $ Provided t; pure (InType t, AppWf name [] noWf)
            DefaultObject -> do
              let t = Signature identObject
              setVar name $ Provided t; pure (InType t, AppWf name [] noWf)
            NotProvided -> failWithMessage $ "Couldn't infer the type of variable: " <> pretty name
          (Just _, (_:_)) -> failWithMessage $ pretty name <> " is a variable but it has been applied to " <> pretty explicit
          (Nothing, _) -> do
            names <- getInternalNames name
            case Set.toList names of
              [] -> failWithMessage $ "Unknown function: " <> pretty name
              [(name', type')] -> do
                case type' of
                  Sort -> failWithMessage $ "Sort in a term: " <> pretty name
                  Pred is t -> do
                    if length is /= length explicit
                      then failWithMessage $ "The number of arguments of " <> pretty name <> " is wrong!"
                      else do
                        (argtypes, explicit') <- unzip <$> zipWithM go (map Provided is) explicit
                        argintypes <- flip mapM argtypes $ \t -> case t of
                              Prop -> failWithMessage "A truth value cannot be passed to a function!"
                              InType t' -> pure t'
                        coe <- coercions <$> get
                        let coes = zipWith (\(Signature a) (Signature b) -> coerce (a, b) coe) argintypes is
                        coes' <- flip mapM (List.zip4 coes [1::Int ..] is argintypes) $ \(c, i, exp, have) -> case c of
                              Nothing -> failWithMessage $ "The " <> pretty i <> (th i) <> " argument of "
                                <> pretty name <> " could not be coerced into the correct type!\n"
                                <> pretty name <> " expects: " <> pretty exp
                                <> " but we got: " <> pretty have
                              Just t -> pure t
                        let ex' = zipWith coercionsToTerm coes' explicit'
                        wf' <- checkWf p name' ex' wf
                        -- TODO: By using name' instead of name we make re-checking this impossible
                        -- when the name is overloaded!
                        -- In fact, we re-check the assumptions though, so this will become an error
                        -- once we have overloading in any assumption in a text!
                        pure (t, AppWf name' ex' wf')
              (_:_:_) -> do
                (argtypes, explicit') <- unzip <$> mapM (go NotProvided) explicit
                argintypes <- flip mapM argtypes $ \t -> case t of
                      Prop -> failWithMessage "A truth value cannot be passed to a function!"
                      InType t' -> pure t'
                res <- resolve name names argintypes retval
                case res of
                  ((name', coe), t) -> do
                    let ex' = zipWith coercionsToTerm coe explicit'
                    wf' <- checkWf p name' ex' wf
                    -- TODO: By using name' instead of name we make re-checking this impossible
                    -- when the name is overloaded!
                    -- In fact, we re-check the assumptions though, so this will become an error
                    -- once we have overloading in any assumption in a text!
                    pure (t, AppWf name' ex' wf')
      App Eq [a, b] -> do
        inferMap' <- inferMap <$> get
        case a of
          -- This case is important for the auto-generated finite set code.
          -- Here we can infer the type of the implicit variable.
          AppWf v0 [] _ | Just (DefaultObject:_) <- Map.lookup v0 inferMap' -> do
            (tb, b') <- go NotProvided b
            case tb of
              Prop -> failWithMessage $ "Prop in equality: " <> pretty (App Eq [AppWf v0 [] noWf, b'])
              InType ib -> do
                setVar v0 (Provided ib)
                pure (Prop, App Eq [AppWf v0 [] noWf, b'])
          _ -> do
            (ta, a') <- go NotProvided a
            (tb, b') <- go NotProvided b
            coe <- coercions <$> get
            case (ta, tb) of
              (InType ia, InType ib) -> case (coerceInto [ia] [ib] coe, coerceInto [ib] [ia] coe) of
                (Just ts, _) -> pure (Prop, App Eq [coercionsToTerm (head ts) a', b'])
                (_, Just ts) -> pure (Prop, App Eq [a', coercionsToTerm (head ts) b'])
                (Nothing, Nothing) -> failWithMessage $
                  "Can't coerce one side of equality into the other: " <> pretty (App Eq [a', b']) <> line
                  <> pretty a' <> " : " <> pretty ia <> line
                  <> pretty b' <> " : " <> pretty ib
              _ -> failWithMessage $ "Prop in equality: " <> pretty (App Eq [a', b'])
      App op args -> do 
        (_, res) <- unzip <$> mapM (go NotProvided) args
        pure (Prop, simp $ App op res)
      Tag () t -> go inferCtx t >>= \(a,c) -> pure (a, Tag () c)

checkNFTerm :: (Infer f, Message.Comm m) => SourcePos -> ReturnValue -> NFTerm f () -> TC m (OutType, NFTerm Identity ())
checkNFTerm p retval (NFTerm im ex as b) = do
  mapM_ restrictAndAdd im
  mapM_ restrictAndAdd ex
  as' <- mapM (fmap snd . checkTerm p Proposition) as
  (o, b') <- checkTerm p retval b
  ex' <- mapM lookupProvided ex
  im' <- mapM lookupProvided im
  pure $ (o, NFTerm im' ex' as' b')
  where
    restrictAndAdd (i, s) = restrictType i s >>= addVar i
    lookupProvided (i, _) = do
      t <- lookupVar i
      delVar i
      case t of
        Just (Provided t) -> pure (i, Identity t)
        _ -> failWithMessage $ "Couldn't infer type of variable " <> pretty i

splitExists :: Term Identity () -> (Term Identity (), [(Ident, InType)])
splitExists = \case
  Exists i (Identity t) e -> ((i, t):) <$> splitExists e
  e -> (e, [])

lastMay :: [a] -> Maybe a
lastMay [] = Nothing
lastMay [x] = Just x
lastMay (_:xs) = lastMay xs

checkProof :: (Infer f, Message.Comm m) => Term Identity () -> Located (Prf f ())
           -> TC m (Located (Prf Identity ()), Term Identity (), [Hypothesis])
checkProof goal (Located n p t) = case t of
  Intro i _ -> do
    case goal of
      Forall i' (Identity t) goal' | i == i' -> do
        addVar i (Provided t)
        pure (Located n p $ Intro i (Identity t), goal', [Typing i (Pred [] $ InType t)])
      _ -> failWithMessage $ "Malformed Intro(" <> pretty i <> ", " <> pretty t
        <> ") could not be applied to goal: " <> pretty goal
  Assume as -> do
    (_, as') <- checkTerm p Proposition as
    case goal of
      App Imp [a, b] | a == as' -> do
        pure $ (Located n p $ Assume as', b, [Given "assume" as'])
      _ -> failWithMessage $ "Couldn't introduce the assumption " <> pretty as
        <> " for the goal: " <> pretty goal
  ByContradiction _ -> do
    let negGoal = App Not [goal]
    pure (Located n p (ByContradiction negGoal), App Bot [], [Given "negated_goal" negGoal])
  Suffices t pbl -> do
    (_, t') <- checkTerm p Proposition t
    bl <- checkProofBlock (termToNF $ App Imp [t', goal]) p pbl
    pure (Located n p $ Suffices t' bl, t', [])
  Define x tt t -> do
    givenType <- restrictType x tt
    (o, t') <- checkTerm p Value t
    type' <- case o of
      Prop -> failWithMessage $ "Internal: expected value but got proposition"
      InType o -> case givenType of
        Provided o' -> if o == o' then pure o
          else failWithMessage $ "Definition gave the type of " <> pretty x <> " as " <> pretty o'
            <> " but it should be equal to an expression of type: " <> pretty o
        _ -> pure o
    addVar x (Provided type')
    pure (Located n p $ Define x (Identity type') t', goal,
      [Given "define" (App Eq [AppWf x [] noWf, t']), Typing x $ Pred [] $ InType type'])
  Subclaim nf pbl -> do
    (_, nf') <- checkNFTerm p Proposition nf
    bl <- checkProofBlock nf' p pbl
    pure (Located n p $ Subclaim nf' bl, goal, [Given n (termFromNF nf')])
  Choose vs t pbl -> do
    let ex = List.foldl' (\e (i, t) -> Exists i t e) t vs
    (_, ex') <- checkTerm p Proposition ex
    let (t', vs') = splitExists ex'
    let vst = map (\(v, t) -> Typing v $ Pred [] (InType t)) vs'
    bl <- checkProofBlock (NFTerm [] [] [] ex') p pbl
    mapM_ (\(i, t) -> addVar i (Provided t)) vs'
    pure (Located n p $ Choose (map (fmap Identity) vs') t' bl, goal,
      Given n t' : vst)
  Cases cs -> do
    cs' <- flip mapM cs $ \(c, topClaim, pbl) -> do
      (_, c') <- checkTerm p Proposition c
      (_, topClaim') <- checkTerm p Proposition topClaim
      bl <- checkProofBlock (NFTerm [] [] [] topClaim') p pbl
      claim <- case bl of
        ProofByTCTactics ts -> pure $ foldrM (flip unroll) topClaim'
          $ map (\(a, _, _) -> located a) ts
        _ -> failWithMessage $ "Cases must contain tactics!"
      case claim of
        Just claim -> pure (c', claim, bl)
        Nothing -> failWithMessage $ "Terminal cases may not appear in a non-terminal case statement!"
    pure (Located n p $ Cases cs', goal, map (\(a, b, _) -> Given "cases" $ App Imp [a,b]) cs')
  TerminalCases cs -> do
    cs' <- flip mapM cs $ \(c, pbl) -> do
      (_, c') <- checkTerm p Proposition c
      bl <- checkProofBlock (NFTerm [] [] [] goal) p pbl
      pure (c', bl)
    pure (Located n p $ TerminalCases cs', App Top [], [])

-- | Unroll (or turn-back) a tactic that has been applied before a term.
-- This is used for subclaims and not goals: e.g. the Suffices tactic is ignored.
unroll :: Term Identity () -> Prf Identity () -> Maybe (Term Identity ())
unroll claim = \case
  Intro i t -> Just $ Forall i t claim
  Assume as -> Just $ App Imp [as, claim]
  ByContradiction negGoal -> Just $ App Imp [negGoal, claim]
  Suffices _ _ -> Just $ claim
  Define x tt t -> Just $ Exists x tt (App Eq [AppWf x [] noWf, t])
  Subclaim t _ -> Just $ App And [termFromNF t, claim]
  Choose vs t _ -> Just $ List.foldl' (\c (i, t) -> Exists i t c) (App And [t, claim]) vs
  Cases cs -> Just $ List.foldl' (\a b -> App And [a, b]) claim $ map (\(a, b, _) -> App Imp [a, b]) cs
  TerminalCases _ -> Nothing

foldTactics :: Monad m => (g -> t -> m (t', g, hs)) -> g -> [t] -> m [(t', g, hs)]
foldTactics _ _ [] = pure []
foldTactics f g (t:ts) = do
  r@(_, g', _) <- f g t
  (r:) <$> foldTactics f g' ts

-- | Check a proof block and insert intro/assume automatically.
checkProofBlock :: (Infer f, Message.Comm m) => NFTerm Identity () -> SourcePos -> PrfBlock f () -> TC m (PrfBlock Identity ())
checkProofBlock nf@(NFTerm im ex as _) p = \case
  ProofByHints hs -> pure $ ProofByHints hs
  ProofByTactics ts -> locally $ do
    let intros = map (\(i, t) -> Located "intro" p (Intro i t)) (im ++ ex)
    let assms = map (\a -> Located "assume" p (Assume a)) as
    ts1 <- foldTactics checkProof (termFromNF nf) $ intros ++ assms
    let g2 = fromMaybe (termFromNF nf) $ fmap (\(_, g, _) -> g) $ lastMay ts1
    ts2 <- foldTactics checkProof g2 $ ts
    pure $ ProofByTCTactics $ ts1 ++ ts2
  ProofByTCTactics ts -> pure $ ProofByTCTactics ts

typecheck :: Message.Comm m => [Located (Stmt Set ())] -> m [Located (Stmt Identity ())]
typecheck = flip evalStateT mempty . mapM go
  where
    go :: Message.Comm m => Located (Stmt Set ()) -> TC m (Located (Stmt Identity ()))
    go (Located n p stmt) = do
      modify $ \s -> s { errorBlock = stmt, errorPosition = p }
      case stmt of
        IntroSort sort -> do
          modify $ \s -> s { typings = Map.insert sort Sort (typings s) }
          pure $ Located n p (IntroSort sort)
        IntroAtom i im ex as -> do
          (_, nf') <- checkNFTerm p Proposition (NFTerm im ex as (App Top []))
          let is = map (\(_, Identity t) -> t) (nfExplicit nf')
          i' <- addType i (Pred is Prop)
          modify $ \s -> s { defs = Map.insert i' nf' (defs s) }
          pure $ Located n p (IntroAtom i' (nfImplicit nf') (nfExplicit nf') (nfAssumptions nf'))
        IntroSignature i o im ex as -> do
          o' <- singleTypedVar i o
          (_, nf') <- checkNFTerm p Proposition (NFTerm im ex as (App Top []))
          let is = map (\(_, Identity t) -> t) (nfExplicit nf')
          i' <- addType i (Pred is (InType o'))
          modify $ \s -> s { defs = Map.insert i' nf' (defs s) }
          pure $ Located n p (IntroSignature i' (Identity o') (nfImplicit nf') (nfExplicit nf') (nfAssumptions nf'))
        Predicate i nf -> do
          (_, nf') <- checkNFTerm p Proposition nf
          let is = map (\(_, Identity t) -> t) (nfExplicit nf')
          i' <- addType i (Pred is Prop)
          modify $ \s -> s { defs = Map.insert i' nf' (defs s) }
          pure $ Located n p (Predicate i' nf')
        Function i _ nf -> do
          (o, nf') <- checkNFTerm p Value nf
          case o of
            Prop -> failWithMessage $ "Internal error: Function checking returned a prop where a value was expected."
            InType o -> do
              let is = map (\(_, Identity t) -> t) (nfExplicit nf')
              i' <- addType i (Pred is (InType o))
              modify $ \s -> s { defs = Map.insert i' nf' (defs s) }
              pure $ Located n p (Function i' (Identity o) nf')
        Axiom nf -> do
          (_, nf') <- checkNFTerm p Proposition nf
          pure $ Located n p (Axiom nf')
        Claim nf pbl -> do
          (_, nf') <- checkNFTerm p Proposition nf
          bl <- checkProofBlock nf' p pbl
          pure $ Located n p (Claim nf' bl)
        Coercion name from to -> do
          modify $ \s -> s { coercions = add (from, to) name (coercions s) }
          _ <- addType name (Pred [Signature from] (InType $ Signature to))
          pure $ Located n p (Coercion name from to)