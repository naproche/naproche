{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TupleSections #-}

-- | Basic type-checking
-- In the future this should also support type inference
-- so that the user can write e.g. $for every subset S of P$
-- and it is inferred that $S$ is actually a set.
-- If you want to implement it, you may wish to consider
-- the paper 'A Second Look at Overloading' by Odersky et al.

module SAD.Core.Typecheck (typecheck) where

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Functor.Identity
import Control.Monad.State
import Data.List (foldl')
import Data.Maybe
import Data.Foldable (foldrM)

import SAD.Data.Terms (identObject, identClass, identElement)
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.String (renderString)
import SAD.Core.SourcePos (SourcePos, noSourcePos)
import qualified SAD.Core.Message as Message
import qualified Isabelle.Naproche as Naproche

import SAD.Data.Identifier
import SAD.Core.Typed
import SAD.Core.Coerce

data Context = Context
  { errorBlock :: Stmt Set ()
  , errorFormula :: Maybe (Doc ())
  , errorPosition :: SourcePos
  , typings :: Map Ident Type
    -- ^ a type for each resolved name
  , overloadings :: Map Ident (Set Ident)
    -- ^ possible overloadings for an identifier
  , coercions :: Coercions Ident Ident
  , defs :: Map Ident (NFTerm Identity ())
  -- ^ definitions
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
  (<>) (Context _ _ _ t1 r1 c1 d1) (Context eb ef ep t2 r2 c2 d2) = Context eb ef ep (t1 <> t2) (r1 <> r2) (c1 <> c2) (d1 <> d2)

-- | This should be kept in sync with SAD.ForTheL.Base.initFS
-- Equalities can be omitted since they are a feature of TPTP syntax.
predefinedTypes :: Map Ident Type
predefinedTypes = Map.fromList
  [ (identClass, Sort)
  , (identObject, Sort)
  , (identElement, Pred [Signature identObject, Signature identClass] Prop)
  ]

predefinedNames :: Map Ident (Set Ident)
predefinedNames = Map.fromList
  [ (identElement, Set.singleton identElement) ]

predefinedStmts :: [Located (Stmt Identity ())]
predefinedStmts =
  [ Located "predef" noSourcePos $ IntroSort identClass
  , Located "predef" noSourcePos $ IntroSort identObject
  , Located "predef" noSourcePos $ IntroAtom identElement
      [] [(NormalIdent "x", Identity (Signature identObject)), (NormalIdent "C", Identity (Signature identClass))] []
  ]

instance Monoid Context where
  mempty = Context undefined Nothing noSourcePos predefinedTypes predefinedNames mempty mempty

coercionsToTerm :: [Ident] -> (Term f t -> Term f t)
coercionsToTerm = go . reverse
  where
    go [] = id
    go (x:xs) = go xs . \t -> AppNF x [] [t] []

coerceInto :: [InType] -> [InType] -> Coercions Ident Ident -> Maybe [[Ident]]
coerceInto is is' coe = if length is == length is'
  then sequence $ zipWith (\(Signature a) (Signature b) -> coerce (a, b) coe) is is'
  else Nothing

-- | Given a list of coercible values, try to find a value that is generalized by
-- all of them and is in the list. Then give the coercions to this value.
-- O(n) calls to coerceInto.
leastGeneral :: [(t, [InType])] -> Coercions Ident Ident -> Maybe ((t, [InType]), [[[Ident]]])
leastGeneral [] _ = Nothing
leastGeneral (x:xs) coe = flip checkRoot (x:xs) $ getRoot x xs
  where
    -- We find an element 'root' with the property that if it is
    -- comparable with another element 'x' then 'x -> root'.
    -- If the coercions form a DAG this is actually a root.
    -- Due to transitivity this can be done in O(n).
    -- We then check if it is comparable to all elements.
    getRoot root [] = root
    getRoot root (x:xs) = case coerceInto (snd x) (snd root) coe of
      Just _ -> getRoot x xs
      Nothing -> getRoot root xs
    checkRoot root = fmap (\b -> (root,b)) . mapM (\x -> coerceInto (snd root) (snd x) coe)

data ReturnValue = Value | Proposition
  deriving (Eq, Ord, Show)

resolve :: Message.Comm m => Ident -> [InType] -> ReturnValue -> TC m ((Ident, [[Ident]]), OutType)
resolve name intypes ret = do
  (Context _ _ _ idents res coe _) <- get
  res' <- resolvedNames idents res
  pick coe $ Set.toList (feasibleNames coe res')
  where
    resolvedNames idents res = Set.map (\a -> (a, idents Map.! a)) <$>
      case Map.lookup name res of
        Nothing -> failWithMessage $ "Internal: name not registered: " <> pretty name
        Just x -> pure x

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

addType :: Monad m => Ident -> Type -> TC m ()
addType i t = do
  taken <- Map.keysSet . overloadings <$> get
  let i' = newIdent i taken
  modify $ \s -> s
    { typings = Map.insert i' t (typings s)
    , overloadings = Map.insertWith (<>) i (Set.singleton i') (overloadings s)}

addVar :: Monad m => Ident -> InType -> TC m ()
addVar i t = addType i (Pred [] $ InType t)

locally :: Monad m => TC m a -> TC m a
locally action = do
  ctx <- get
  a <- action
  put ctx
  pure a

-- | Ad-hoc monad for inference. This was added to make the types match,
-- but should be refactored away once we have proper type inference.
class (Show (f InType), Pretty (f InType)) => Infer f where
  restrictType :: Message.Comm m => Ident -> f InType -> TC m (Maybe InType)

instance Infer Identity where
  restrictType _ (Identity t) = pure $ Just t

instance Infer Set where
  -- | Restrict the set of types of a variable to no more than one.
  -- This is achieved by trying to find a least general type to
  -- coerce into and fails if that is not possible.
  restrictType :: Message.Comm m => Ident -> Set InType -> TC m (Maybe InType)
  restrictType v s = do
    coe <- coercions <$> get
    case Set.toList s of
      [] -> pure Nothing
      s -> case leastGeneral (map (\i -> (i, [i])) s) coe of
        Nothing -> failWithMessage $ "The variable " <> pretty v
          <> " has been defined with the mutually non-coercible types: "
          <> vsep (map pretty s)
        Just ((a, _), _) -> pure $ Just a

singleTypedVar :: (Infer f, Message.Comm m) => Ident -> f InType -> TC m InType
singleTypedVar v s = do
  m <- restrictType v s
  case m of
    Nothing -> failWithMessage $ "Untyped bind: " <> pretty v
    Just m -> pure m

-- | Type check applications and insert coercions.
-- Forward type-checking: We assume that the identifiers without arguments are typed
-- and infer the type/resolved name of identifiers with arguments from them.
checkTerm :: (Infer f, Message.Comm m) => SourcePos -> ReturnValue -> Term f () -> TC m (OutType, Term Identity ())
checkTerm p retval t = locally $ do
  modify $ \s -> s { errorFormula = Just $ pretty t }
  (o, t') <- go retval t
  case (o, retval) of
    (Prop, Proposition) -> pure (o, simp t')
    (InType _, Value) -> pure (o, simp t')
    _ -> failWithMessage $ "The term has type " <> pretty o <> " but was expected to return a " <> pretty (show retval)
  where
    go :: (Message.Comm m, Infer f) => ReturnValue -> Term f () -> StateT Context m (OutType, Term Identity ())
    go retval = \case
      Forall v m t -> case retval of
        Proposition -> do
          m' <- singleTypedVar v m
          addVar v m'
          fmap (Forall v (Identity m')) <$> go Proposition t
        _ -> failWithMessage $ "Found a forall term where an object was expected"
      Exists v m t -> case retval of
        Proposition -> do
          m' <- singleTypedVar v m
          addVar v m'
          fmap (Exists v (Identity m')) <$> go Proposition t
        _ -> failWithMessage $ "Found an exists term where an object was expected"
      Class v m t -> case retval of
        Value -> do
          m' <- fromMaybe (Signature identObject) <$> restrictType v m
          addVar v m'
          (_, inclass) <- go Proposition t
          pure (InType $ Signature identClass, Class v (Identity m') inclass)
        Proposition -> failWithMessage $ "Found a class where a proposition was expected."
      AppNF name implicit explicit assms -> do
        -- assms has already been checked in 'infer'
        (_, implicit') <- unzip <$> mapM (go Value) implicit
        (argtypes, explicit') <- unzip <$> mapM (go Value) explicit
        argintypes <- flip mapM argtypes $ \t -> case t of
              Prop -> failWithMessage "A truth value cannot be passed to a function!"
              InType t' -> pure t'
        res <- resolve name argintypes retval
        case res of
          ((name', coe), t) -> do
            m <- (Map.lookup name' . defs) <$> get
            as' <- case (assms, m) of
              (_, Just (NFTerm _ _ as _)) -> do
                mapM (\(g, a) -> checkProofBlock (NFTerm [] [] [] g) p a) $ zip as assms
              ([], Nothing) -> pure []
              (_, Nothing) -> failWithMessage $ "Unknown function or predicate: " <> pretty name'

            -- TODO: By using name' instead of name we make re-checking this impossible!
            -- In fact, we re-check the assumptions though, so this will become an error
            -- once we have overloading in any assumption in a text!
            pure (t, AppNF name' implicit' (zipWith coercionsToTerm coe explicit') as')
      App Eq [a, b] -> do
        (ta, a') <- go Value a
        (tb, b') <- go Value b
        coe <- coercions <$> get
        case (ta, tb) of
          (InType ia, InType ib) -> case (coerceInto [ia] [ib] coe, coerceInto [ib] [ia] coe) of
            (Just ts, _) -> pure (Prop, App Eq [coercionsToTerm (head ts) a', b'])
            (_, Just ts) -> pure (Prop, App Eq [a', coercionsToTerm (head ts) b'])
            (Nothing, Nothing) -> failWithMessage $
              "Can't coerce one side of equality into the other: " <> pretty (App Eq [a', b']) 
          _ -> failWithMessage $ "Prop in equality: " <> pretty (App Eq [a', b'])
      App op args -> do 
        res <- mapM (go Proposition) args
        pure (Prop, App op $ map snd res)
      Tag () t -> fmap (Tag ()) <$> go retval t

checkNFTerm :: (Infer f, Message.Comm m) => SourcePos -> ReturnValue -> NFTerm f () -> TC m (OutType, NFTerm Identity ())
checkNFTerm p retval (NFTerm im ex as b) = locally $ do
  im' <- flip mapM im $ \(i, s) -> do
      t <- singleTypedVar i s
      addVar i t
      pure (i, Identity t)
  ex' <- flip mapM ex $ \(i, s) -> do
      t <- singleTypedVar i s
      addVar i t
      pure (i, Identity t)
  as' <- mapM (fmap snd . checkTerm p Proposition) as
  (o, b') <- checkTerm p retval b
  pure $ (o, NFTerm im' ex' as' b')

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
        addVar i t
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
  Subclaim nf pbl -> do
    (_, nf') <- checkNFTerm p Proposition nf
    bl <- checkProofBlock nf' p pbl
    pure (Located n p $ Subclaim nf' bl, goal, [Given n (termFromNF nf')])
  Choose vs t pbl -> do
    let ex = foldl' (\e (i, t) -> Exists i t e) t vs
    (_, ex') <- checkTerm p Proposition ex
    let (t', vs') = splitExists ex'
    let vst = map (\(v, t) -> Typing v $ Pred [] (InType t)) vs'
    bl <- checkProofBlock (NFTerm [] [] [] ex') p pbl
    mapM_ (uncurry addVar) vs'
    pure (Located n p $ Choose (map (fmap Identity) vs') t' bl, goal,
      Given n t' : vst)
  Cases cs -> do
    cs' <- flip mapM cs $ \(c, topClaim, pbl) -> do
      (_, c') <- checkTerm p Proposition c
      (_, topClaim') <- checkTerm p Proposition topClaim
      bl <- checkProofBlock (NFTerm [] [] [] goal) p pbl
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
  Subclaim t _ -> Just $ App And [termFromNF t, claim]
  Choose vs t _ -> Just $ foldl' (\c (i, t) -> Exists i t c) (App And [t, claim]) vs
  Cases cs -> Just $ foldl' (\a b -> App And [a, b]) claim $ map (\(a, b, _) -> App Imp [a, b]) cs
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
  ProofByTCTactics _ -> failWithMessage $ "Internal: Type-checked tactics passed to type-checking!"

typecheck :: Message.Comm m => [Located (Stmt Set ())] -> m [Located (Stmt Identity ())]
typecheck = fmap appendStmts . flip evalStateT mempty . mapM go
  where
    appendStmts = (predefinedStmts <>)

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
          addType i (Pred is Prop)
          modify $ \s -> s { defs = Map.insert i nf' (defs s) }
          pure $ Located n p (IntroAtom i (nfImplicit nf') (nfExplicit nf') (nfAssumptions nf'))
        IntroSignature i o im ex as -> do
          o' <- singleTypedVar i o
          (_, nf') <- checkNFTerm p Proposition (NFTerm im ex as (App Top []))
          let is = map (\(_, Identity t) -> t) (nfExplicit nf')
          addType i (Pred is (InType o'))
          modify $ \s -> s { defs = Map.insert i nf' (defs s) }
          pure $ Located n p (IntroSignature i (Identity o') (nfImplicit nf') (nfExplicit nf') (nfAssumptions nf'))
        Predicate i nf -> do
          (_, nf') <- checkNFTerm p Proposition nf
          let is = map (\(_, Identity t) -> t) (nfExplicit nf')
          addType i (Pred is Prop)
          modify $ \s -> s { defs = Map.insert i nf' (defs s) }
          pure $ Located n p (Predicate i nf')
        Function i _ nf -> do
          (o, nf') <- checkNFTerm p Value nf
          case o of
            Prop -> failWithMessage $ "Internal error: Function checking returned a prop where a value was expected."
            InType o -> do
              let is = map (\(_, Identity t) -> t) (nfExplicit nf')
              addType i (Pred is (InType o))
              modify $ \s -> s { defs = Map.insert i nf' (defs s) }
              pure $ Located n p (Function i (Identity o) nf')
        Axiom nf -> do
          (_, nf') <- checkNFTerm p Proposition nf
          pure $ Located n p (Axiom nf')
        Claim nf pbl -> do
          (_, nf') <- checkNFTerm p Proposition nf
          bl <- checkProofBlock nf' p pbl
          pure $ Located n p (Claim nf' bl)
        Coercion name from to -> do
          modify $ \s -> s { coercions = add (from, to) name (coercions s) }
          addType name (Pred [Signature from] (InType $ Signature to))
          pure $ Located n p (Coercion name from to)