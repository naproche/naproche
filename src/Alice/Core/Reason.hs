{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018)

Reasoning methods and export to an external prover.
-}
{-# LANGUAGE FlexibleContexts #-}
module Alice.Core.Reason (
  reason,
  withGoal, withContext,
  proveThesis,
  reduceWithEvidence, trivialByEvidence,
  launchReasoning,
  thesis
  ) where
-- FIXME reconcept some functions so that this module does not need to export
--       the small fries anymore
import Control.Monad
import Data.Char
import Data.List
import Data.Maybe
import System.Timeout
import Control.Exception
import Data.Monoid (Sum, getSum)
import qualified Data.IntMap.Strict as IM
import qualified Control.Monad.Writer as W
import qualified Data.Set as Set
import qualified Data.Map as M
import Control.Monad.State
import Control.Monad.Reader

import Alice.Parser.Position
import Alice.Core.Base
import Alice.Data.Formula
import Alice.Data.Instr
import Alice.Data.Text.Context as Context
import Alice.Data.Text.Block as Block
import Alice.Data.Definition
import Alice.Data.Evaluation
import Alice.Export.Prover
import Alice.ForTheL.Base
import Alice.Prove.MESON
import qualified Alice.Data.Structures.DisTree as DT


-- Reasoner

reason :: Context -> VM ()
reason tc = local (\st -> st {currentThesis = tc}) proveThesis

withGoal :: VM a -> Formula -> VM a
withGoal action goal = local (\vState ->
  vState { currentThesis = setForm (currentThesis vState) goal}) action

withContext :: VM a -> [Context] -> VM a
withContext action context = local (\vState -> 
  vState { currentContext = context }) action

thesis = asks currentThesis; context = asks currentContext


proveThesis :: VM ()
proveThesis = do
  reasoningDepth <- askInstructionInt IIdpth 3;  guard $ reasoningDepth > 0
  context >>= filterContext (splitGoal >>= sequenceGoals reasoningDepth 0)

sequenceGoals :: Int -> Int -> [Formula] -> VM ()
sequenceGoals reasoningDepth iteration (goal:restGoals) = do
  (trivial <|> proofByATP <|> reason) `withGoal` reducedGoal
  sequenceGoals reasoningDepth iteration restGoals
  where
    reducedGoal = reduceWithEvidence goal
    trivial = guard (isTop reducedGoal) >> updateTrivialStatistics
    proofByATP = launchProver iteration

    reason 
      | reasoningDepth == 1 = depthExceedMessage >> mzero
      | otherwise = do  
          newTask <- unfold
          let Context {cnForm = Not newGoal} : newContext = newTask
          sequenceGoals (pred reasoningDepth) (succ iteration) [newGoal]
            `withContext` newContext

    depthExceedMessage =
      whenInstruction IBPrsn False $
        reasonerLog0 Normal noPos "reasoning depth exceeded"

    updateTrivialStatistics = 
      unless (isTop goal) $ whenInstruction IBPrsn False $
         reasonerLog0 Normal noPos ("trivial: " ++ show goal)
      >> incrementIntCounter TrivialGoals

sequenceGoals  _ _ _ = return ()

splitGoal :: VM [Formula]
splitGoal = asks (normalizedSplit . strip . cnForm . currentThesis)
  where
    normalizedSplit = split . albet
    split (All u f) = map (All u) (normalizedSplit f)
    split (And f g) = normalizedSplit f ++ normalizedSplit (Imp f g)
    split (Or f g)  = map (zOr f) (normalizedSplit g)
    split fr        = return fr


-- Call prover

launchProver :: Int -> VM ()
launchProver iteration = do
  reductionSetting <- askInstructionBin IBOnto False
  whenInstruction IBPtsk False (printTask reductionSetting)
  proverList <- askRS provers ; instrList <- askRS instructions
  goal <- thesis; context <- context
  let callATP = justIO $ 
        export reductionSetting iteration proverList instrList context goal
  callATP >>= timer ProofTime . justIO >>= guard
  TimeCounter _ time <- fmap head $ askRS counters
  addTimeCounter SuccessTime time ; incrementIntCounter SuccessfulGoals
  where
    printTask reductionSetting = do
      let getFormula = if reductionSetting then cnRedu else cnForm
      contextFormulas <- asks $ map getFormula . reverse . currentContext
      concl <- thesis
      reasonerLog0 Normal noPos $ "prover task:\n" ++
        concatMap (\form -> "  " ++ show form ++ "\n") contextFormulas ++
        "  |- " ++ show (cnForm concl) ++ "\n"


launchReasoning :: VM ()
launchReasoning = do 
  goal <- thesis; context <- context
  skolemInt <- askGlobalState skolemCounter
  mesonPos <- askGlobalState mesonPositives
  mesonNeg <- askGlobalState mesonNegatives
  let lowlevelContext = takeWhile cnLowL context
      proveGoal = prove skolemInt lowlevelContext mesonPos mesonNeg goal
      -- set timelimit to 10^4 
      -- (usually not necessary as max proof depth is limited)
      callOwn = timeout (10^4) $ evaluate $ proveGoal
  justIO callOwn >>= guard . (==) (Just True)



-- Context filtering

{- if an explicit list of theorems is given, we set the context to that 
  plus all definitions/sigexts (as they usually import type information that
  is easily forgotten) and the low level context. Otherwise the whole 
  context is selected. -}
filterContext :: VM a -> [Context] -> VM a
filterContext action context = do
  link <- asks (cnLink . currentThesis) >>= getLink;
  if Set.null link 
    then action `withContext` 
         (map replaceSignHead $ filter (not . isTop . cnRedu) context)
    else do
         linkedContext <- retrieveContext link 
         action `withContext` (lowlevelContext ++ linkedContext ++ defsAndSigs)
  where
    (lowlevelContext, toplevelContext) = span cnLowL context
    defsAndSigs = 
      let defOrSig c = (not . isTop . cnRedu $ c) 
                    && (isDefinition c || isSignature c)
      in  map replaceHeadTerm $ filter defOrSig toplevelContext

isDefinition, isSignature :: Context -> Bool
isDefinition = (==) Block.Definition . kind . cnHead
isSignature  = (==) Block.Signature  . kind . cnHead

replaceHeadTerm :: Context -> Context
replaceHeadTerm c = setForm c $ dive 0 $ cnForm c
  where
    dive n (All _ (Imp (Tag DHD Trm {trName = "=", trArgs = [_, t]}) f)) =
      subst t "" $ inst "" f
    dive n (All _ (Iff (Tag DHD eq@Trm {trName = "=", trArgs = [_, t]}) f))
      = And (subst t "" $ inst "" f) (All "" $ Imp f eq)
    dive n (All _ (Imp (Tag DHD Trm{}) Top)) = Top
    dive n (All v f) =
      bool $ All v $ bind (show n) $ dive (succ n) $ inst (show n) f
    dive n (Imp f g) = bool $ Imp f $ dive n g
    dive _ f = f

{- the mathematical function here is the same as replaceHeadTerm, but we save
some work by only diving into signature extensions and definitions-}
replaceSignHead :: Context -> Context
replaceSignHead c
  | isDefinition c || isSignature c = replaceHeadTerm c
  | otherwise = c


-- reduction by collected info

trivialByEvidence :: Formula -> Bool
trivialByEvidence f = isTop $ reduceWithEvidence f

reduceWithEvidence :: Formula -> Formula
reduceWithEvidence t@Trm{trName = "="} = t -- leave equality untouched
reduceWithEvidence l | isLiteral l = -- try to reduce literals
  fromMaybe l $ msum $ map (lookFor l) (trArgs $ ltAtomic l)
reduceWithEvidence f = bool $ mapF reduceWithEvidence $ bool f 


{- lookFor the right evidence -}
lookFor :: Formula -> Formula -> Maybe Formula
lookFor _ Ind{} = Nothing -- bound variables have no evidence
lookFor literal (Tag _ t) = lookFor literal t -- ignore tags
lookFor literal t =
  let tId = trId (ltAtomic literal)
      negatedLiteral = albet $ Not literal
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
  evals            :: DT.DisTree Eval,
  unfoldSetting    :: Bool, -- user parameters that control what is unfolded
  unfoldSetSetting :: Bool }


-- FIXME the reader monad transformer used here is completely superfluous
unfold :: VM [Context]
unfold = do  
  thesis <- thesis; context <- context
  let task = setForm thesis (Not $ cnForm thesis) : context
  definitions  <- askGlobalState definitions; evaluations <- asks evaluations
  generalUnfoldSetting     <- askInstructionBin IBUnfl True
  lowlevelUnfoldSetting    <- askInstructionBin IBUfdl True
  generalSetUnfoldSetting  <- askInstructionBin IBUnfs True
  lowlevelSetUnfoldSetting <- askInstructionBin IBUfds False
  guard (generalUnfoldSetting || generalSetUnfoldSetting)
  let ((goal:toUnfold), topLevelContext) = span cnLowL task
      unfoldState = UF
        definitions 
        evaluations
        (generalUnfoldSetting    && lowlevelUnfoldSetting)
        (generalSetUnfoldSetting && lowlevelSetUnfoldSetting)
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
  addIntCounter Unfolds (getSum numberOfUnfolds)
  return $ newLowLevelContext ++ topLevelContext
  where
    nothingToUnfold =
      whenInstruction IBPunf False $ reasonerLog0 Normal noPos "nothing to unfold"
    unfoldLog (goal:lowLevelContext) =
      whenInstruction IBPunf False $ reasonerLog0 Normal noPos $ "unfold to:\n"
        ++ unlines (reverse $ map ((++) "  " . show . cnForm) lowLevelContext)
        ++ "  |- " ++ show (neg $ cnForm goal)
    neg (Not f) = f; neg f = f


{- conservative unfolding of local properties -}
unfoldConservative :: Context
  -> ReaderT UnfoldState (W.Writer (Sum Int)) Context
unfoldConservative toUnfold 
  | isDeclaration toUnfold = return toUnfold
  | otherwise =
      fmap (setForm toUnfold) $ fill [] (Just True) 0 $ cnForm toUnfold
  where
    fill localContext sign n f 
      | hasDMK f = return f -- check if f has been unfolded already
      | isTrm f  =  fmap reduceWithEvidence $ unfoldAtomic (fromJust sign) f
    -- Iff is changed to double implication -> every position has a polarity
    fill localContext sign n (Iff f g) = fill localContext sign n $ zIff f g
    fill localContext sign n f = roundFM 'u' fill localContext sign n f

    isDeclaration = (==) LowDefinition . kind . cnHead

{- unfold an atomic formula f occuring with polarity sign -}
unfoldAtomic sign f = do
  nbs <- localProperties f >>= return . foldr (if sign then And else Or ) marked
  subtermLocalProperties f >>= return . foldr (if sign then And else Imp) nbs
  where
    -- we mark the term so that it does not get 
    -- unfolded again in subsequent iterations
    marked = Tag DMK f

    subtermLocalProperties (Tag DMK _) = return [] -- do not expand marked terms
    subtermLocalProperties h = foldFM termLocalProperties h
    termLocalProperties h = 
      liftM2 (++) (subtermLocalProperties h) (localProperties h)
    localProperties (Tag DMK _) = return []
    localProperties Trm {trName = "=", trArgs = [l,r]} =
      liftM3 (\a b c -> a ++ b ++ c) 
             (definitionalProperties l r)
             (definitionalProperties r l) 
             (extensionalities l r)
  -- we combine definitional information for l, for r and if
  -- we have set equality we also throw in extensionality for sets and if
  -- we have functions we throw in function extensionality

    localProperties t 
      | isApplication t || isElem t = setFunDefinitionalProperties t
      | otherwise = definitionalProperties t t
    
    -- return definitional property of f instantiated with g
    definitionalProperties f g = do
      definitions <- asks defs
      let definingFormula = maybeToList $ do
            id <- tryToGetID f; def <- IM.lookup id definitions;
            -- only unfold a definitions or (a sigext in a positive position)
            guard (sign || dfSign def)
            sb <- match (dfTerm def) f
            let definingFormula = replace (Tag DMK g) ThisT $ sb $ dfForm def
        -- substitute the (marked) term
            guard (not . isTop $ definingFormula)
            return definingFormula
      unfGuard unfoldSetting $
        unless (null definingFormula) (lift $ W.tell 1) >>
        return definingFormula
        -- increase the counter by 1 and return what we got

    extensionalities f g =
      let extensionalityFormula = -- set extensionality
            (guard (setType f && setType g) >> return (setExtensionality f g))
            `mplus`  -- function extensionality
            (guard (funType f && funType g) >> return (funExtensionality f g))
      in  lift (W.tell 1) >> return extensionalityFormula

    setExtensionality f g =
      let v = zVar "" in zAll "" $ Iff (zElem v f) (zElem v g)
    funExtensionality f g =
      let v = zVar ""
      in (domainEquality (zDom f) (zDom g)) `And` 
         zAll "" (Imp (zElem v $ zDom f) $ zEqu (zApp f v) (zApp g v))
    
    -- depending on the sign we choose the more convenient form of set equality
    domainEquality = 
      let v = zVar ""; sEqu x y = zAll "" (Iff (zElem v x) (zElem v y))
      in  if sign then zEqu else sEqu 

    setFunDefinitionalProperties t = do 
      evaluations <- asks evals
      let evaluationFormula = maybeToList $
            DT.lookup t evaluations >>= msum . map findev
      unfGuard unfoldSetSetting $
        unless (null evaluationFormula) (lift $ W.tell 1) >> 
        return evaluationFormula
      where
        findev ev = do
          sb <- match (evTerm ev) t
          guard (all trivialByEvidence $ map sb $ evCond ev)
          return $ replace (Tag DMK t) ThisT $ sb $ 
            if sign then evPos ev else evNeg ev

    unfGuard unfoldSetting action =
      asks unfoldSetting >>= \p -> if p then action else return []

hasDMK (Tag DMK _ ) = True
hasDMK _ = False

setType f | hasInfo f = any (infoTwins ThisT $ zSet ThisT) $ trInfo f
setType _ = False

funType f | hasInfo f = any (infoTwins ThisT $ zFun ThisT) $ trInfo f
funType _ = False

hasInfo f = isTrm f || isVar f
