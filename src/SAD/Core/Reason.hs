{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018)

The reasoner handles proof tasks.

Trivial proof tasks can be discharged quickly without calling an external prover.
Non-trivial proof tasks are exported to an external prover. If the direct proof
by an external prover fails, the reasoner expands some definitions and tries again.
-}

{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}
{-# LANGUAGE FlexibleContexts #-}

module SAD.Core.Reason (
  thesis,
  reason,
  withContext,
  proveThesis,
  reduceWithEvidence, trivialByEvidence,
  trivialityCheck
) where

import Control.Exception (evaluate)
import Control.Monad.Reader
import Data.Maybe (fromJust, fromMaybe, maybeToList)
import Data.Monoid (Sum, getSum)
import Data.Functor ((<&>))
import System.Timeout (timeout)

import qualified Control.Monad.Writer as W
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Text.Lazy as Text
import qualified Isabelle.Isabelle_Thread as Isabelle_Thread

import SAD.Core.Base
import SAD.Data.Definition
import SAD.Data.Formula
import SAD.Data.Instr (Limit(..), Flag(..))
import SAD.Data.Text.Context (Context(Context))
import SAD.Data.Text.Decl (newDecl)
import qualified SAD.Export.Prover as Prover
import qualified SAD.Prove.MESON as MESON

import qualified SAD.Core.Message as Message
import qualified SAD.Data.Definition as Definition
import qualified SAD.Data.Structures.DisTree as DT
import qualified SAD.Data.Text.Block as Block
import qualified SAD.Data.Text.Context as Context

import qualified Isabelle.Position as Position
import qualified Naproche.Prover as Prover


-- Reasoner

reason :: Position.T -> Context -> VM ()
reason pos tc =
  local (\st -> st {currentThesis = tc}) (proveThesis pos)

withGoal :: VM a -> Formula -> VM a
withGoal action goal =
  local (\st -> st { currentThesis = Context.setFormula (currentThesis st) goal}) action

withContext :: VM a -> [Context] -> VM a
withContext action context =
  local (\st -> st { currentContext = context }) action

thesis :: VM Context
thesis = asks currentThesis


proveThesis :: Position.T -> VM ()
proveThesis pos = do
  depthlimit <- askInstructionInt Depthlimit 3
  guard (depthlimit > 0) -- Fallback to defaulting of the underlying CPS Maybe monad.
  ctx <- asks currentContext
  thesis <- asks currentThesis
  filterContext pos (sequenceGoals pos depthlimit (splitGoal thesis)) ctx

sequenceGoals :: Position.T -> Int -> [Formula] -> VM ()
sequenceGoals pos depthlimit = sequence 0
  where
    sequence _ [] = return ()
    sequence iteration (goal : restGoals) = do
      (trivial <|> prover <|> reason) `withGoal` reducedGoal
      sequence iteration restGoals
      where
        reducedGoal = reduceWithEvidence goal
        trivial = guard (isTop reducedGoal) >> updateTrivialStatistics
        prover = launchProver pos iteration
        reason =
          if iteration >= depthlimit then warnDepthExceeded >> mzero
          else do
            newTask <- unfold pos
            let Context {Context.formula = Not newGoal} : newContext = newTask
            sequence (iteration + 1) [newGoal] `withContext` newContext

        warnDepthExceeded =
          whenInstruction Printreason False $
            reasonLog Message.WARNING pos "reasoning depth exceeded"

        updateTrivialStatistics =
          unless (isTop goal) $ whenInstruction Printreason False $ do
            reasonLog Message.WRITELN pos ("trivial: " <> show goal)
            incrementCounter TrivialGoals

splitGoal :: Context -> [Formula]
splitGoal = normalizedSplit . strip . Context.formula

normalizedSplit :: Formula -> [Formula]
normalizedSplit = split . albet
  where
    split (All u f) = map (All u) (normalizedSplit f)
    split (And f g) = normalizedSplit f ++ normalizedSplit (Imp f g)
    split (Or f g)  = map (zOr f) (normalizedSplit g)
    split fr        = return fr


-- Call prover

launchProver :: Position.T -> Int -> VM ()
launchProver pos iteration = do
  whenInstruction Printfulltask False printTask
  instrList <- asks instructions
  goal <- thesis
  context <- asks currentContext
  let callATP = justIO $ pure $ Prover.export pos iteration instrList context goal
  callATP >>= timeWith ProofTimer . justIO >>= guardResult
  res <- head <$> askRS trackers
  case res of
    Timer _ time -> do
      addToTimer SuccessTimer time
      incrementCounter SuccessfulGoals
    _ -> error "No matching case in launchProver"
  where
    printTask = do
      contextFormulas <- asks $ map Context.formula . reverse . currentContext
      concl <- thesis
      reasonLog Message.WRITELN pos $ "prover task:\n" <>
        concatMap (\form -> "  " <> show form <> "\n") contextFormulas <>
        "  |- " <> show (Context.formula concl) <> "\n"

    guardResult Prover.Success = pure ()
    guardResult Prover.Contradictory_Axioms = do
      checkConsistency <- askInstructionBool CheckConsistency True
      if checkConsistency then do
        reasonLog Message.WRITELN pos "Found contradictory axioms. Make sure you are in a proof by contradiction!"
        mzero
      else pure ()
    guardResult _ = mzero


-- Triviality check

trivialByMeson :: Formula -> VM ()
trivialByMeson goal = do
  context <- asks currentContext
  n <- asks skolemCounter
  (positives, negatives) <- asks mesonRules
  let lowlevelContext = takeWhile Context.isLowLevel context
      proveGoal = MESON.prove n lowlevelContext positives negatives goal
      -- timeout: usually not necessary as max proof depth is limited
      prove = do
        Isabelle_Thread.expose_stopped
        timeout 10000 $ evaluate proveGoal
  justIO prove >>= guard . (==) (Just True)

trivialityCheck :: Formula -> VM (Either Formula Formula)
trivialityCheck goal =
  if   trivialByEvidence goal
  then return $ Right goal  -- triviality check
  else (trivialByMeson goal >> return (Right goal)) <|> return (Left goal)


-- Context filtering

{- if an explicit list of theorems is given, we set the asks context that
  plus all definitions/sigexts (as they usually import type information that
  is easily forgotten) and the low level context. Otherwise the whole
  context is selected. -}
filterContext :: Position.T -> VM a -> [Context] -> VM a
filterContext pos action context = do
  link <- asks (Set.fromList . Context.link . currentThesis)
  if Set.null link
    then action `withContext`
         map replaceSignHead (filter (not . isTop . Context.formula) context)
    else do
         linkedContext <- retrieveContext pos link
         action `withContext` (lowlevelContext ++ linkedContext ++ defsAndSigs)
  where
    (lowlevelContext, toplevelContext) = span Context.isLowLevel context
    defsAndSigs =
      let defOrSig c = (isDefinitionBlock c || isSignatureBlock c)
      in  map replaceHeadTerm $ filter defOrSig toplevelContext

isDefinitionBlock, isSignatureBlock :: Context -> Bool
isDefinitionBlock ctx = Block.Definition == Block.kind (Context.head ctx)
isSignatureBlock  ctx = Block.Signature  == Block.kind (Context.head ctx)

replaceHeadTerm :: Context -> Context
replaceHeadTerm c = Context.setFormula c $ dive 0 $ Context.formula c
  where
    dive :: Int -> Formula -> Formula
    dive n (All _ (Imp (Tag HeadTerm Trm {trmName = TermEquality, trmArgs = [_, t]}) f)) =
      subst t VarEmpty $ inst VarEmpty f
    dive n (All _ (Iff (Tag HeadTerm eq@Trm {trmName = TermEquality, trmArgs = [_, t]}) f))
      = And (subst t VarEmpty $ inst VarEmpty f) (All (newDecl VarEmpty) $ Imp f eq)
    dive n (All _ (Imp (Tag HeadTerm Trm{}) Top)) = Top
    dive n (All v f) =
      bool $ All v $ bind (VarDefault $ Text.pack $ show n) $ dive (n + 1) $ inst (VarDefault $ Text.pack $ show n) f
    dive n (Imp f g) = bool $ Imp f $ dive n g
    dive _ f = f

{- the mathematical function here is the same as replaceHeadTerm, but we save
some work by only diving into signature extensions and definitions-}
replaceSignHead :: Context -> Context
replaceSignHead c
  | isDefinitionBlock c || isSignatureBlock c = replaceHeadTerm c
  | otherwise = c


-- reduction by collected info

trivialByEvidence :: Formula -> Bool
trivialByEvidence f = isTop $ reduceWithEvidence f

reduceWithEvidence :: Formula -> Formula
reduceWithEvidence t@Trm{trmName = TermEquality} = t -- leave equality untouched
reduceWithEvidence l | isLiteral l = -- try to reduce literals
  fromMaybe l $ msum $ map (lookFor l) (trmArgs $ ltAtomic l)
reduceWithEvidence f = bool $ mapF reduceWithEvidence $ bool f


{- lookFor the right evidence -}
lookFor :: Formula -> Formula -> Maybe Formula
lookFor _ Ind{} = Nothing -- bound variables have no evidence
lookFor literal (Tag _ t) = lookFor literal t -- ignore tags
lookFor literal t =
  let negatedLiteral = albet $ Not literal
  in  checkFor literal negatedLiteral $ trInfo t
  where
    checkFor literal negatedLiteral [] = Nothing
    checkFor literal negatedLiteral (atomic:rest)
      | ltTwins literal (replace t ThisT atomic)        = Just Top
      | ltTwins negatedLiteral (replace t ThisT atomic) = Just Bot
      | otherwise = checkFor literal negatedLiteral rest


-- unfolding of local properties

data UnfoldState = UF {
  defs             :: Definitions,
  evals            :: DT.DisTree Evaluation,
  unfoldSetting    :: Bool, -- user parameters that control what is unfolded
  unfoldSetSetting :: Bool }


-- FIXME the reader monad transformer used here is completely superfluous
unfold :: Position.T -> VM [Context]
unfold pos = do
  thesis <- asks currentThesis
  context <- asks currentContext
  let task = Context.setFormula thesis (Not $ Context.formula thesis) : context
  definitions <- asks definitions
  evaluations <- asks evaluations
  generalUnfoldSetting <- askInstructionBool Unfold True
  lowlevelUnfoldSetting <- askInstructionBool Unfoldlow True
  generalSetUnfoldSetting <- askInstructionBool Unfoldsf True
  lowlevelSetUnfoldSetting <- askInstructionBool Unfoldlowsf False
  guard (generalUnfoldSetting || generalSetUnfoldSetting)
  let (goal : toUnfold, topLevelContext) = span Context.isLowLevel task
      unfoldState = UF
        { defs = definitions
        , evals = evaluations
        , unfoldSetting = generalUnfoldSetting && lowlevelUnfoldSetting
        , unfoldSetSetting = generalSetUnfoldSetting && lowlevelSetUnfoldSetting }
      (newLowLevelContext, numberOfUnfolds) =
        W.runWriter $ flip runReaderT unfoldState $
          liftM2 (:)
            (let localState st = st { -- unfold goal with general settings
                  unfoldSetting    = generalUnfoldSetting,
                  unfoldSetSetting = generalSetUnfoldSetting}
             in  local localState $ unfoldConservative goal)
            (mapM unfoldConservative toUnfold)
  unfoldLog newLowLevelContext
  when (numberOfUnfolds == 0) $ nothingToUnfold >> mzero
  addToCounter Unfolds (getSum numberOfUnfolds)
  return $ newLowLevelContext ++ topLevelContext
  where
    nothingToUnfold =
      whenInstruction Printunfold False $ reasonLog Message.WRITELN pos "nothing to unfold"

    unfoldLog (goal:lowLevelContext) =
      whenInstruction Printunfold False $ reasonLog Message.WRITELN pos $ "unfold to:\n"
        <> unlines (reverse $ map ((<>) "  " . show . Context.formula) lowLevelContext)
        <> "  |- " <> show (neg $ Context.formula goal)

    neg (Not f) = f
    neg f = f


{- conservative unfolding of local properties -}
unfoldConservative :: Context -> ReaderT UnfoldState (W.Writer (Sum Int)) Context
unfoldConservative toUnfold
  | isDeclaration toUnfold = pure toUnfold
  | otherwise = fmap (Context.setFormula toUnfold) $ fill [] (Just True) 0 $ Context.formula toUnfold
  where
    fill :: [Formula] -> Maybe Bool -> Int -> Formula -> ReaderT UnfoldState (W.Writer (Sum Int)) Formula
    fill localContext sign n f
      | hasDMK f = return f -- check if f has been unfolded already
      | isTrm f = reduceWithEvidence <$> unfoldAtomic (fromJust sign) f
    -- Iff is changed to double implication -> every position has a polarity
    fill localContext sign n (Iff f g) = fill localContext sign n $ zIff f g
    fill localContext sign n f = roundFM VarU fill localContext sign n f

    isDeclaration :: Context -> Bool
    isDeclaration = (==) Block.LowDefinition . Block.kind . Context.head

{- unfold an atomic formula f occurring with polarity sign -}
unfoldAtomic :: (W.MonadWriter w m, MonadTrans t,
                 MonadReader UnfoldState (t m), Num w) =>
                Bool -> Formula -> t m Formula
unfoldAtomic sign f = do
  nbs <- localProperties f <&> foldr (if sign then And else Or ) marked
  subtermLocalProperties f <&> foldr (if sign then And else Imp) nbs
  where
    -- we mark the term so that it does not get
    -- unfolded again in subsequent iterations
    marked = Tag GenericMark f

    subtermLocalProperties (Tag GenericMark _) = return [] -- do not expand marked terms
    subtermLocalProperties h = foldFM termLocalProperties h
    termLocalProperties h =
      liftM2 (++) (subtermLocalProperties h) (localProperties h)
    localProperties (Tag GenericMark _) = return []
    localProperties Trm {trmName = TermEquality, trmArgs = [l,r]} =
      liftM3 (\a b c -> a ++ b ++ c)
             (definitionalProperties l r)
             (definitionalProperties r l)
             (extensionalities l r)
  -- we combine definitional information for l, for r and if
  -- we have set/class equality we also throw in extensionality for sets/classes
  -- and if we have maps we throw in map extensionality

    localProperties t
      | isApplication t || isElem t = setFunDefinitionalProperties t
      | otherwise = definitionalProperties t t

    -- return definitional property of f instantiated with g
    definitionalProperties f g = do
      definitions <- asks defs
      let definingFormula = maybeToList $ do
            id <- guard (isTrm f) >> pure (trmId f)
            def <- Map.lookup id definitions;
            -- only unfold a definitions or (a sigext in a positive position)
            guard (sign || Definition.isDefinition def)
            sb <- match (defTerm def) f
            let definingFormula = replace (Tag GenericMark g) ThisT $ sb $ defFormula def
        -- substitute the (marked) term
            guard (not . isTop $ definingFormula)
            return definingFormula
      unfGuard unfoldSetting $
        unless (null definingFormula) (lift $ W.tell 1) >>
        return definingFormula
        -- increase the counter by 1 and return what we got

    extensionalities f g =
      let extensionalityFormula =
            -- set extensionality
            (guard (setType f && setType g) >> return (classExtensionality f g))
            `mplus`
            -- class extensionality
            (guard (classType f && classType g) >> return (classExtensionality f g))
            `mplus`
            -- map extensionality
            (guard (functionType f && functionType g) >> return (mapExtensionality f g))
            `mplus`
            -- map extensionality
            (guard (mapType f && mapType g) >> return (mapExtensionality f g))
      in  lift (W.tell 1) >> return extensionalityFormula

    classExtensionality f g =
      let v = mkVar VarEmpty in mkAll VarEmpty $ Iff (mkElem v f) (mkElem v g)
    mapExtensionality f g =
      let v = mkVar VarEmpty
      in domainEquality (mkDom f) (mkDom g) `And`
         mkAll VarEmpty (Imp (mkElem v $ mkDom f) $ mkEquality (mkApp f v) (mkApp g v))

    -- depending on the sign we choose the more convenient form of class equality
    domainEquality =
      let v = mkVar VarEmpty; sEqu x y = mkAll VarEmpty (Iff (mkElem v x) (mkElem v y))
      in  if sign then mkEquality else sEqu

    setFunDefinitionalProperties t = do
      evaluations <- asks evals
      let evaluationFormula = maybeToList $
            DT.lookup t evaluations >>= msum . map findev
      unfGuard unfoldSetSetting $
        unless (null evaluationFormula) (lift $ W.tell 1) >>
        return evaluationFormula
      where
        findev ev = do
          sb <- match (evaluationTerm ev) t
          guard (all (trivialByEvidence . sb) $ evaluationConditions ev)
          return $ replace (Tag GenericMark t) ThisT $ sb $
            if sign then evaluationPositives ev else evaluationNegatives ev

    unfGuard unfoldSetting action =
      asks unfoldSetting >>= \p -> if p then action else return []

hasDMK :: Formula -> Bool
hasDMK (Tag GenericMark _ ) = True
hasDMK _ = False

setType :: Formula -> Bool
setType Var {varInfo = info} = any (infoTwins ThisT $ mkSet ThisT) info
setType Trm {trmInfo = info} = any (infoTwins ThisT $ mkSet ThisT) info
setType _ = False

classType :: Formula -> Bool
classType Var {varInfo = info} = any (infoTwins ThisT $ mkClass ThisT) info
classType Trm {trmInfo = info} = any (infoTwins ThisT $ mkClass ThisT) info
classType _ = False

functionType :: Formula -> Bool
functionType Var {varInfo = info} = any (infoTwins ThisT $ mkFunction ThisT) info
functionType Trm {trmInfo = info} = any (infoTwins ThisT $ mkFunction ThisT) info
functionType _ = False

mapType :: Formula -> Bool
mapType Var {varInfo = info} = any (infoTwins ThisT $ mkMap ThisT) info
mapType Trm {trmInfo = info} = any (infoTwins ThisT $ mkMap ThisT) info
mapType _ = False
