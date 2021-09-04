{-# LANGUAGE OverloadedStrings #-}

-- | This module desugeres the parsing AST into the TFF syntax.
-- There are two main tasks:
--  - Desuger classes into definitions
--    This is surprisingly tricky: Classes need to be ordered in the correct way
--    when they are nested and the same class may occur multiple times in the
--    AST (for example as part of a goal that is transformed several times).
--  - Turn intersection types into regular types by adding a variable for each
--    type in the intersection and an axiom that all these variables are equal
--    (where equality means equality on the variables coerced to $i).

module SAD.Core.Desuger (desuger) where

import qualified Data.Text as Text
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Monad.State

import SAD.Data.SourcePos
import SAD.Data.Identifier
import qualified SAD.Core.AST as A
import qualified SAD.Core.Typed as T
import Data.Maybe
import Data.List (sortOn)

-- -- | A class definition of type 'outtype' (may be set/class/..)
-- -- with arguments 'intypes' (= free variables of the class body).
-- -- The class's body is in 'cond' and may contain classes itself!
-- data ClassDef = ClassDef
  -- { outtype :: T.InType
  -- , intypes :: [(Ident, T.InType)]
  -- , implicits :: [(Ident, T.InType)]
  -- , assumptions :: [T.Term]
  -- , v :: Ident
  -- , m :: A.InType
  -- , ci :: A.ClassInfo
  -- , cond :: A.Term
  -- } deriving (Eq, Ord, Show)

-- -- | Map the original class definition (with nested classes)
-- -- to the given identifier and desugered class def.
-- -- If we encounter a new class we can thus check if we have seen it
-- -- before (in the same stmt).
-- data DesugerState = DesugerState
  -- { classIdx :: Int
  -- , classes :: Map ClassDef (Ident, ClassDef)
  -- , typings :: Map Ident (Map T.InType Ident)
    -- -- ^ this map may contain variables that are out of scope,
    -- -- but we don't care since the stmts are all type-checked.
    -- -- We map an ident to a map that associates each of its type
    -- -- with the variable that implements this variant.
  -- } deriving (Eq, Ord, Show)

-- type Desuger a = State DesugerState a

-- coercionsToTerm :: [Ident] -> (T.Term -> T.Term)
-- coercionsToTerm = go . reverse
  -- where
    -- go [] = id
    -- go (x:xs) = go xs . \t -> T.AppWf x [t] T.WellFormed

-- runDesuger :: Desuger a -> a
-- runDesuger = flip evalState (DesugerState 1 mempty mempty)

-- newClassId :: Desuger Ident
-- newClassId = do
  -- s <- get
  -- put $ s { classIdx = (classIdx s + 1) }
  -- pure $ NormalIdent $ "cls" <> Text.pack (show (classIdx s))

-- addClass :: ClassDef -> Desuger T.Term
-- addClass c = do
  -- cls <- classes <$> get
  -- case Map.lookup c cls of
    -- Nothing -> do
      -- i <- newClassId
      -- c' <- desugerClass c
      -- modify $ \s -> s { classes = Map.insert c (i, c') (classes s) }
      -- pure $ getClassTerm i c'
    -- Just (i, c') -> pure $ getClassTerm i c'

-- addType :: Ident -> T.InType -> Desuger ()
-- addType i t = modify $ \s -> s { typings = Map.insert i t (typings s) }

-- -- | Remove all classes from the state and return them together with
-- -- all their nested classes in the correct order.
-- dumpClasses :: Desuger [T.Stmt]
-- dumpClasses = do
  -- cls <- map snd . Map.toList . classes <$> get
  -- let cls' = sortOn fst cls
  -- modify $ \s -> s { classes = mempty }
  -- pure $ concatMap (uncurry fromClassDef) cls'

-- getClassTerm :: Ident -> ClassDef -> T.Term
-- getClassTerm cls (ClassDef _ intypes im as _ _ _ _)
  -- = T.AppWf cls (map (\(v, _) -> T.AppWf v [] T.WellFormed) intypes) T.WellFormed

-- fromClassDef :: Ident -> ClassDef -> [T.Stmt]
-- fromClassDef cls c@(ClassDef outtype intypes im as v m ci cond) =
  -- let v' = coercionsToTerm (A.coerceElemsToObject ci) (T.AppWf v [] T.WellFormed)
      -- clsTrm = getClassTerm cls c
      -- ext = T.Forall v m $ T.App T.Iff [T.AppWf identElement [v', coercionsToTerm (A.coerceClassTypeToClass ci) clsTrm] T.WellFormed, cond]
      -- ext' = foldr (uncurry T.Forall) ext intypes
  -- in [T.IntroSignature cls outtype intypes [], T.Axiom cls (T.termToNF ext')]

-- desugerClass :: ClassDef -> Desuger ClassDef
-- desugerClass (ClassDef o is im as v m ci cond) = do
  -- cond' <- desugerTerm cond
  -- pure $ ClassDef o is im as v m ci cond'

-- -- | Replace each class {x | c} by a new operator cls in a term t and return
-- -- ((rest of the variables, [∀x x\in cls iff c]), t')
-- -- If classes are nested, we will return the outermost first.
-- desugerTerm :: A.Term -> Desuger T.Term
-- desugerTerm = go
  -- where
    -- getFreeTyped fv typings = mapMaybe
      -- (\v -> case Map.lookup v typings of Nothing -> Nothing; Just t -> Just (v, t))
      -- $ Set.toList $ fvToVarSet fv

    -- go :: A.Term -> Desuger T.Term
    -- go = \case
      -- A.Forall v m t -> T.Forall v m <$> (addType v m >> go t)
      -- A.Exists v m t -> T.Exists v m <$> (addType v m >> go t)
      -- A.Class v m mm ci t -> do
        -- typs <- typings <$> get
        -- let free = getFreeTyped (bindVar v $ A.findFree t) typs
            -- v' = coercionsToTerm (A.coerceElemsToObject ci) (T.AppWf v [] T.WellFormed )
            -- t' = maybe t (\s -> A.App A.And [A.AppWf (A.Resolved identElement) [v', s] A.WellFormed, t]) mm
            -- stmt = ClassDef (A.classType ci) free [] [] v m ci t'
        -- addClass stmt
      -- A.FinClass m ci ts -> do
        -- typs <- typings <$> get
        -- let v = newIdent (NormalIdent "v") (Map.keysSet typs)
            -- ts' = foldl (\a b -> A.App A.Or [a, b]) (A.App A.Top []) $ map (\t -> A.App A.Eq [A.AppWf (A.Resolved v) [] A.WellFormed, t] ) ts
            -- free = getFreeTyped (A.findFree ts') typs
            -- stmt = ClassDef (A.classType ci) free [] [] v m ci ts'
        -- addClass stmt
      -- A.App op ts -> do
        -- ts' <- mapM go ts
        -- pure $ T.App op ts'
      -- A.AppWf op ex wf -> do
        -- ex' <- mapM go ex
        -- wf' <- desugerWfBlock wf
        -- pure $ T.AppWf op ex' wf'
      -- A.Coe cs t -> _
      -- A.Typing ty t -> _
      -- A.Tag tag t -> failWithMessage $ "Internal: Tag left after type checking!"

-- desugerInType :: A.InType -> T.InType
-- desugerInType (A.Signature i) = T.Signature i

-- desugerNFTerm :: A.NFTerm -> Desuger T.NFTerm
-- desugerNFTerm (A.NFTerm ex as bd) = do
  -- mapM_ (uncurry addType) ex
  -- as' <- mapM desugerTerm as
  -- bd' <- desugerTerm bd
  -- pure $ T.NFTerm ex as' bd'

-- desugerWfBlock :: A.WfBlock -> Desuger T.WfBlock
-- desugerWfBlock (A.WfProof nf pbl) = do
  -- nf' <- desugerNFTerm nf
  -- pbl' <- desugerPrfBlock pbl
  -- pure $ T.WfProof nf' pbl'
-- desugerWfBlock A.WellFormed = pure T.WellFormed
-- desugerWfBlock A.NoWf = failWithMessage $ "Internal: WfBlock not checked!"

-- desugerPrfBlock :: A.PrfBlock -> Desuger T.PrfBlock
-- desugerPrfBlock (A.ProofByHints hs) = pure $ T.ProofByHints hs
-- desugerPrfBlock (A.ProofByTactics _) = error $ "Internal error: Desugering should run after type-checking!"
-- desugerPrfBlock (A.ProofByTCTactics xs) = do
  -- xs' <- mapM f xs
  -- pure $ T.ProofByTCTactics xs'
  -- where
    -- f (A.Located p prf, t, hs) = do
      -- t' <- desugerTerm t
      -- hs' <- mapM desugerHypothesis hs
      -- prf' <- desugerProof prf
      -- pure (T.Located p prf', t', hs')

-- desugerProof :: A.Prf -> Desuger T.Prf
-- desugerProof = \case
  -- A.Intro i t -> pure $ T.Intro i t
  -- A.Assume t -> T.Assume <$> desugerTerm t
  -- A.ByContradiction t -> T.ByContradiction <$> desugerTerm t
  -- A.Suffices t pbl -> do
    -- t' <- desugerTerm t
    -- pbl' <- desugerPrfBlock pbl
    -- pure $ T.Suffices t' pbl'
  -- A.Define i m t -> do
    -- addType i m
    -- t' <- desugerTerm t
    -- pure $ T.Define i m t'
  -- A.Subclaim n nf pbl -> do
    -- nf' <- desugerNFTerm nf
    -- pbl' <- desugerPrfBlock pbl
    -- pure $ T.Subclaim n nf' pbl'
  -- A.Choose vs t pbl -> do
    -- mapM_ (uncurry addType) vs
    -- t' <- desugerTerm t
    -- pbl' <- desugerPrfBlock pbl
    -- pure $ T.Choose vs t' pbl'
  -- A.Cases ts -> fmap T.Cases $ forM ts $ \(c, g, pbl) -> do
    -- c' <- desugerTerm c
    -- g' <- desugerTerm g
    -- pbl' <- desugerPrfBlock pbl
    -- pure (c', g', pbl')
  -- A.TerminalCases ts -> fmap T.TerminalCases $ forM ts $ \(c, pbl) -> do
    -- c' <- desugerTerm c
    -- pbl' <- desugerPrfBlock pbl
    -- pure (c', pbl')

-- desugerHypothesis :: A.Hypothesis -> Desuger T.Hypothesis
-- desugerHypothesis (A.TypeDef i t) = pure $ T.TypeDef i t
-- desugerHypothesis (A.Given n t) = T.Given n <$> desugerTerm t

-- locate :: SourcePos -> [T.Stmt] -> [T.Located T.Stmt]
-- locate p = map (T.Located p)

-- desugerStmt :: A.Located A.Stmt -> Desuger [T.Located T.Stmt]
-- desugerStmt (A.Located p stmt) = case stmt of
  -- A.IntroSort s -> pure $ [T.Located p $ T.IntroSort s]
  -- A.IntroAtom i ex as -> do
    -- as' <- mapM desugerTerm as
    -- ss <- dumpClasses
    -- pure $ locate p ss ++ [T.Located p $ T.IntroAtom i ex as']
  -- A.IntroSignature i t ex as -> do
    -- as' <- mapM desugerTerm as
    -- ss <- dumpClasses
    -- pure $ locate p ss ++ [T.Located p $ T.IntroSignature i t ex as']
  -- A.Predicate i nf -> do
    -- nf' <- desugerNFTerm nf
    -- ss <- dumpClasses
    -- pure $ locate p ss ++ [T.Located p $ T.Predicate i nf']
  -- A.Function i t nf -> do
    -- nf' <- desugerNFTerm nf
    -- ss <- dumpClasses
    -- pure $ locate p ss ++ [T.Located p $ T.Function i t nf']
  -- A.Axiom n' nf -> do
    -- nf' <- desugerNFTerm nf
    -- ss <- dumpClasses
    -- pure $ locate p ss ++ [T.Located p $ T.Axiom n' nf']
  -- A.Claim n' nf pbl -> do
    -- nf' <- desugerNFTerm nf
    -- pbl' <- desugerPrfBlock pbl
    -- ss <- dumpClasses
    -- pure $ locate p ss ++ [T.Located p $ T.Claim n' nf' pbl']
  -- A.Coercion i f t -> pure [T.Located p $ A.Coercion i f t]

desuger :: [A.Located A.Stmt] -> [T.Located T.Stmt]
desuger _ = [] -- concat . runDesuger . mapM desugerStmt