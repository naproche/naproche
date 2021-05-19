{-# LANGUAGE OverloadedStrings #-}

-- | Desuger classes into definitions
-- This is surprisingly tricky: Classes need to be ordered in the correct way
-- when they are nested and the same class may occur multiple times in the
-- AST (for example as part of a goal that is transformed several times).

-- TODO: This does not take into account that wellformedness proofs are
-- sometimes impossible when we take classes out of their context.
-- See the bug in cantor.ftl.tex
-- This can be fixed by lifting the wellformedness proofs out of the classes
-- and into the class application.

module SAD.Core.Desuger (desuger) where

import qualified Data.Text as Text
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Functor.Identity
import Control.Monad.State

import SAD.Core.SourcePos
import SAD.Core.Identifier
import SAD.Core.Typed
import SAD.Core.Typecheck (coercionsToTerm)
import Data.Maybe
import Data.List (sortOn)

-- | A class definition of type 'outtype' (may be set/class/..)
-- with arguments 'intypes' (= free variables of the class body).
-- The class's body is in 'cond' and may contain classes itself!
data ClassDef = ClassDef
  { outtype :: InType
  , intypes :: [(Ident, Identity InType)]
  , implicits :: [(Ident, Identity InType)]
  , assumptions :: [Term Identity ()]
  , v :: Ident
  , m :: InType
  , ci :: ClassInfo
  , cond :: Term Identity ()
  } deriving (Eq, Ord, Show)

-- | Map the original class definition (with nested classes)
-- to the given identifier and desugered class def.
-- If we encounter a new class we can thus check if we have seen it
-- before (in the same stmt).
data DesugerState = DesugerState
  { classIdx :: Int
  , classes :: Map ClassDef (Ident, ClassDef)
  , typings :: Map Ident (Identity InType)
    -- ^ this map may contain variables that are out of scope,
    -- but we don't care since the stmts are all type-checked.
  } deriving (Eq, Ord, Show)

type Desuger a = State DesugerState a

runDesuger :: Desuger a -> a
runDesuger = flip evalState (DesugerState 1 mempty mempty)

newClassId :: Desuger Ident
newClassId = do
  s <- get
  put $ s { classIdx = (classIdx s + 1) }
  pure $ NormalIdent $ "cls" <> Text.pack (show (classIdx s))

addClass :: ClassDef -> Desuger (Term Identity ())
addClass c = do
  cls <- classes <$> get
  case Map.lookup c cls of
    Nothing -> do
      i <- newClassId
      c' <- desugerClass c
      modify $ \s -> s { classes = Map.insert c (i, c') (classes s) }
      pure $ getClassTerm i c'
    Just (i, c') -> pure $ getClassTerm i c'

addType :: Ident -> Identity InType -> Desuger ()
addType i t = modify $ \s -> s { typings = Map.insert i t (typings s) }

-- | Remove all classes from the state and return them together with
-- all their nested classes in the correct order.
dumpClasses :: Desuger [Stmt Identity ()]
dumpClasses = do
  cls <- map snd . Map.toList . classes <$> get
  let cls' = sortOn fst cls
  modify $ \s -> s { classes = mempty }
  pure $ concatMap (uncurry fromClassDef) cls'

getClassTerm :: Ident -> ClassDef -> Term Identity ()
getClassTerm cls (ClassDef _ intypes im as _ _ _ _)
  = AppWf (Resolved cls) (map (\(v, _) -> AppWf (Resolved v) [] WellFormed) intypes) WellFormed

fromClassDef :: Ident -> ClassDef -> [Stmt Identity ()]
fromClassDef cls c@(ClassDef outtype intypes im as v m ci cond) =
  let v' = coercionsToTerm (coerceElemsToObject ci) (AppWf (Resolved v) [] WellFormed)
      clsTrm = getClassTerm cls c
      ext = Forall v (Identity m) $ App Iff [AppWf (Resolved identElement) [v', coercionsToTerm (coerceClassTypeToClass ci) clsTrm] WellFormed, cond]
      ext' = foldr (uncurry Forall) ext intypes
  in [IntroSignature cls (Identity outtype) intypes [], Axiom cls (termToNF ext')]

desugerClass :: ClassDef -> Desuger ClassDef
desugerClass (ClassDef o is im as v m ci cond) = do
  cond' <- desugerTerm cond
  pure $ ClassDef o is im as v m ci cond'

-- | Given an infinite stream of Idents,
-- replace each class {x | c} by a new operator cls in a term t and return
-- ((rest of the variables, [∀x x\in cls iff c]), t')
-- If classes are nested, we will return the outermost first.
desugerTerm :: Term Identity () -> Desuger (Term Identity ())
desugerTerm = go
  where
    getFreeTyped fv typings = mapMaybe
      (\v -> case Map.lookup v typings of Nothing -> Nothing; Just t -> Just (v, t))
      $ Set.toList $ fvToVarSet fv

    go :: Term Identity () -> Desuger (Term Identity ())
    go = \case
      Forall v m t -> (Forall v m) <$> (addType v m >> go t)
      Exists v m t -> (Exists v m) <$> (addType v m >> go t)
      Class v (Identity m) mm (Identity ci) t -> do
        typs <- typings <$> get
        let free = getFreeTyped (bindVar v $ findFree t) typs
            v' = coercionsToTerm (coerceElemsToObject ci) (AppWf (Resolved v) [] WellFormed )
            t' = maybe t (\s -> App And [AppWf (Resolved identElement) [v', s] WellFormed, t]) mm
            stmt = ClassDef (classType ci) free [] [] v m ci t'
        addClass stmt
      FinClass (Identity m) (Identity ci) ts -> do
        typs <- typings <$> get
        let v = newIdent (NormalIdent "v") (Map.keysSet typs)
            ts' = foldl (\a b -> App Or [a, b]) (App Top []) $ map (\t -> App Eq [AppWf (Resolved v) [] WellFormed, t] ) ts
            free = getFreeTyped (findFree ts') typs
            stmt = ClassDef (classType ci) free [] [] v m ci ts'
        addClass stmt
      App op ts -> do
        ts' <- mapM go ts
        pure $ App op ts'
      AppWf op ex wf -> do
        ex' <- mapM go ex
        wf' <- desugerWfBlock wf
        pure $ AppWf op ex' wf'
      Tag tag t -> Tag tag <$> go t

desugerNFTerm :: NFTerm Identity () -> Desuger (NFTerm Identity ())
desugerNFTerm (NFTerm ex as bd) = do
  mapM_ (uncurry addType) ex
  as' <- mapM desugerTerm as
  bd' <- desugerTerm bd
  pure $ NFTerm ex as' bd'

desugerWfBlock :: WfBlock Identity () -> Desuger (WfBlock Identity ())
desugerWfBlock (WfProof nf pbl) = do
  nf' <- desugerNFTerm nf
  pbl' <- desugerPrfBlock pbl
  pure $ WfProof nf' pbl'
desugerWfBlock p = pure p

desugerPrfBlock :: PrfBlock Identity () -> Desuger (PrfBlock Identity ())
desugerPrfBlock (ProofByHints hs) = pure $ ProofByHints hs
desugerPrfBlock (ProofByTactics _) = error $ "Internal error: Desugering should run after type-checking!"
desugerPrfBlock (ProofByTCTactics xs) = do
  xs' <- mapM f xs
  pure $ ProofByTCTactics xs'
  where
    f (Located p prf, t, hs) = do
      t' <- desugerTerm t
      hs' <- mapM desugerHypothesis hs
      prf' <- desugerProof prf
      pure (Located p prf', t', hs')

desugerProof :: Prf Identity () -> Desuger (Prf Identity ())
desugerProof = \case
  Intro i t -> pure $ Intro i t
  Assume t -> Assume <$> desugerTerm t
  ByContradiction t -> ByContradiction <$> desugerTerm t
  Suffices t pbl -> do
    t' <- desugerTerm t
    pbl' <- desugerPrfBlock pbl
    pure $ Suffices t' pbl'
  Define i m t -> do
    addType i m
    t' <- desugerTerm t
    pure $ Define i m t'
  Subclaim n nf pbl -> do
    nf' <- desugerNFTerm nf
    pbl' <- desugerPrfBlock pbl
    pure $ Subclaim n nf' pbl'
  Choose vs t pbl -> do
    mapM_ (uncurry addType) vs
    t' <- desugerTerm t
    pbl' <- desugerPrfBlock pbl
    pure $ Choose vs t' pbl'
  Cases ts -> fmap Cases $ forM ts $ \(c, g, pbl) -> do
    c' <- desugerTerm c
    g' <- desugerTerm g
    pbl' <- desugerPrfBlock pbl
    pure (c', g', pbl')
  TerminalCases ts -> fmap TerminalCases $ forM ts $ \(c, pbl) -> do
    c' <- desugerTerm c
    pbl' <- desugerPrfBlock pbl
    pure (c', pbl')

desugerHypothesis :: Hypothesis -> Desuger Hypothesis
desugerHypothesis (Typing i t) = pure $ Typing i t
desugerHypothesis (Given n t) = Given n <$> desugerTerm t

locate :: SourcePos -> [Stmt Identity ()] -> [Located (Stmt Identity ())]
locate p = map (Located p)

desugerStmt :: Located (Stmt Identity ()) -> Desuger [Located (Stmt Identity ())]
desugerStmt (Located p stmt) = case stmt of
  IntroSort s -> pure $ [Located p $ IntroSort s]
  IntroAtom i ex as -> do
    as' <- mapM desugerTerm as
    ss <- dumpClasses
    pure $ locate p ss ++ [Located p $ IntroAtom i ex as']
  IntroSignature i t ex as -> do
    as' <- mapM desugerTerm as
    ss <- dumpClasses
    pure $ locate p ss ++ [Located p $ IntroSignature i t ex as']
  Predicate i nf -> do
    nf' <- desugerNFTerm nf
    ss <- dumpClasses
    pure $ locate p ss ++ [Located p $ Predicate i nf']
  Function i t nf -> do
    nf' <- desugerNFTerm nf
    ss <- dumpClasses
    pure $ locate p ss ++ [Located p $ Function i t nf']
  Axiom n' nf -> do
    nf' <- desugerNFTerm nf
    ss <- dumpClasses
    pure $ locate p ss ++ [Located p $ Axiom n' nf']
  Claim n' nf pbl -> do
    nf' <- desugerNFTerm nf
    pbl' <- desugerPrfBlock pbl
    ss <- dumpClasses
    pure $ locate p ss ++ [Located p $ Claim n' nf' pbl']
  Coercion i f t -> pure [Located p $ Coercion i f t]

desuger :: [Located (Stmt Identity ())] -> [Located (Stmt Identity ())]
desuger = concat . runDesuger . mapM desugerStmt