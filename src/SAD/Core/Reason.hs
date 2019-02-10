{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018)

Reasoning methods and export to an external prover.
-}
{-# LANGUAGE FlexibleContexts #-}
module SAD.Core.Reason (
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
import qualified Isabelle.Standard_Thread as Standard_Thread

import SAD.Core.SourcePos
import SAD.Core.Base
import qualified SAD.Core.Message as Message
import SAD.Data.Formula
import SAD.Data.Instr (Instr)
import qualified SAD.Data.Instr as Instr
import SAD.Data.Text.Context (Context(Context))
import qualified SAD.Data.Text.Context as Context
import SAD.Data.Text.Block (Block, Section(..))
import qualified SAD.Data.Text.Block as Block
import SAD.Data.Definition (Definitions)
import qualified SAD.Data.Definition as Definition
import SAD.Data.Evaluation (Evaluation)
import qualified SAD.Data.Evaluation as Evaluation
import SAD.Export.Prover
import SAD.ForTheL.Base
import SAD.Prove.MESON
import qualified SAD.Data.Structures.DisTree as DT
import qualified SAD.Data.Text.Decl as Decl

-- Reasoner

reason :: Context -> VM ()
reason tc = local (\st -> st {currentThesis = tc}) proveThesis

withGoal :: VM a -> Formula -> VM a
withGoal action goal = local (\vState ->
  vState { currentThesis = Context.setForm (currentThesis vState) goal}) action

withContext :: VM a -> [Context] -> VM a
withContext action context = local (\vState -> 
  vState { currentContext = context }) action

thesis = asks currentThesis; context = asks currentContext


proveThesis :: VM ()
proveThesis = do
  reasoningDepth <- askInstructionInt Instr.Depthlimit 3;  guard $ reasoningDepth > 0
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
          let Context {Context.formula = Not newGoal} : newContext = newTask
          sequenceGoals (pred reasoningDepth) (succ iteration) [newGoal]
            `withContext` newContext

    depthExceedMessage =
      whenInstruction Instr.Printreason False $
        reasonLog Message.WARNING noPos "reasoning depth exceeded"

    updateTrivialStatistics = 
      unless (isTop goal) $ whenInstruction Instr.Printreason False $
         reasonLog Message.WRITELN noPos ("trivial: " ++ show goal)
      >> incrementIntCounter TrivialGoals

sequenceGoals  _ _ _ = return ()

splitGoal :: VM [Formula]
splitGoal = asks (normalizedSplit . strip . Context.formula . currentThesis)
  where
    normalizedSplit = split . albet
    split (All u f) = map (All u) (normalizedSplit f)
    split (And f g) = normalizedSplit f ++ normalizedSplit (Imp f g)
    split (Or f g)  = map (zOr f) (normalizedSplit g)
    split fr        = return fr


-- Call prover

launchProver :: Int -> VM ()
launchProver iteration = do
  reductionSetting <- askInstructionBool Instr.Ontored False
  whenInstruction Instr.Printfulltask False (printTask reductionSetting)
  proverList <- asks provers ; instrList <- asks instructions
  goal <- thesis; context <- context
  let callATP = justIO $ 
        export reductionSetting iteration proverList instrList context goal
  callATP >>= timer ProofTime . justIO >>= guard
  TimeCounter _ time <- fmap head $ askRS counters
  addTimeCounter SuccessTime time ; incrementIntCounter SuccessfulGoals
  where
    printTask reductionSetting = do
      let getFormula = if reductionSetting then Context.reducedFormula else Context.formula
      contextFormulas <- asks $ map getFormula . reverse . currentContext
      concl <- thesis
      reasonLog Message.WRITELN noPos $ "prover task:\n" ++
        concatMap (\form -> "  " ++ show form ++ "\n") contextFormulas ++
        "  |- " ++ show (Context.formula concl) ++ "\n"


launchReasoning :: VM ()
launchReasoning = do
  goal <- thesis; context <- context
  skolemInt <- asks skolemCounter
  (mesonPos, mesonNeg) <- asks mesonRules
  let lowlevelContext = takeWhile Context.isLowLevel context
      proveGoal = prove skolemInt lowlevelContext mesonPos mesonNeg goal
      -- set timelimit to 10^4 
      -- (usually not necessary as max proof depth is limited)
      callOwn = do
        Standard_Thread.expose_stopped
        timeout (10^4) $ evaluate $ proveGoal
  justIO callOwn >>= guard . (==) (Just True)



-- Context filtering

{- if an explicit list of theorems is given, we set the context to that 
  plus all definitions/sigexts (as they usually import type information that
  is easily forgotten) and the low level context. Otherwise the whole 
  context is selected. -}
filterContext :: VM a -> [Context] -> VM a
filterContext action context = do
  link <- asks (Set.fromList . Context.link . currentThesis);
  if Set.null link 
    then action `withContext` 
         (map replaceSignHead $ filter (not . isTop . Context.formula) context)
    else do
         linkedContext <- retrieveContext link 
         action `withContext` (lowlevelContext ++ linkedContext ++ defsAndSigs)
  where
    (lowlevelContext, toplevelContext) = span Context.isLowLevel context
    defsAndSigs = 
      let defOrSig c = (not . isTop . Context.reducedFormula $ c) 
                    && (isDefinition c || isSignature c)
      in  map replaceHeadTerm $ filter defOrSig toplevelContext

isDefinition, isSignature :: Context -> Bool
isDefinition = (==) Definition . Block.kind . Context.head
isSignature  = (==) Signature  . Block.kind . Context.head

replaceHeadTerm :: Context -> Context
replaceHeadTerm c = Context.setForm c $ dive 0 $ Context.formula c
  where
    dive n (All _ (Imp (Tag HeadTerm Trm {trName = "=", trArgs = [_, t]}) f)) =
      subst t "" $ inst "" f
    dive n (All _ (Iff (Tag HeadTerm eq@Trm {trName = "=", trArgs = [_, t]}) f))
      = And (subst t "" $ inst "" f) (All (Decl.nonText "") $ Imp f eq)
    dive n (All _ (Imp (Tag HeadTerm Trm{}) Top)) = Top
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
  evals            :: DT.DisTree Evaluation,
  unfoldSetting    :: Bool, -- user parameters that control what is unfolded
  unfoldSetSetting :: Bool }


-- FIXME the reader monad transformer used here is completely superfluous
unfold :: VM [Context]
unfold = do  
  thesis <- thesis; context <- context
  let task = Context.setForm thesis (Not $ Context.formula thesis) : context
  definitions <- asks definitions; evaluations <- asks evaluations
  generalUnfoldSetting <- askInstructionBool Instr.Unfold True
  lowlevelUnfoldSetting <- askInstructionBool Instr.Unfoldlow True
  generalSetUnfoldSetting <- askInstructionBool Instr.Unfoldsf True
  lowlevelSetUnfoldSetting <- askInstructionBool Instr.Unfoldlowsf False
  guard (generalUnfoldSetting || generalSetUnfoldSetting)
  let ((goal:toUnfold), topLevelContext) = span Context.isLowLevel task
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
      whenInstruction Instr.Printunfold False $ reasonLog Message.WRITELN noPos "nothing to unfold"
    unfoldLog (goal:lowLevelContext) =
      whenInstruction Instr.Printunfold False $ reasonLog Message.WRITELN noPos $ "unfold to:\n"
        ++ unlines (reverse $ map ((++) "  " . show . Context.formula) lowLevelContext)
        ++ "  |- " ++ show (neg $ Context.formula goal)
    neg (Not f) = f; neg f = f


{- conservative unfolding of local properties -}
unfoldConservative :: Context
  -> ReaderT UnfoldState (W.Writer (Sum Int)) Context
unfoldConservative toUnfold 
  | isDeclaration toUnfold = return toUnfold
  | otherwise =
      fmap (Context.setForm toUnfold) $ fill [] (Just True) 0 $ Context.formula toUnfold
  where
    fill localContext sign n f 
      | hasDMK f = return f -- check if f has been unfolded already
      | isTrm f  =  fmap reduceWithEvidence $ unfoldAtomic (fromJust sign) f
    -- Iff is changed to double implication -> every position has a polarity
    fill localContext sign n (Iff f g) = fill localContext sign n $ zIff f g
    fill localContext sign n f = roundFM 'u' fill localContext sign n f

    isDeclaration = (==) LowDefinition . Block.kind . Context.head

{- unfold an atomic formula f occuring with polarity sign -}
unfoldAtomic sign f = do
  nbs <- localProperties f >>= return . foldr (if sign then And else Or ) marked
  subtermLocalProperties f >>= return . foldr (if sign then And else Imp) nbs
  where
    -- we mark the term so that it does not get 
    -- unfolded again in subsequent iterations
    marked = Tag GenericMark f

    subtermLocalProperties (Tag GenericMark _) = return [] -- do not expand marked terms
    subtermLocalProperties h = foldFM termLocalProperties h
    termLocalProperties h = 
      liftM2 (++) (subtermLocalProperties h) (localProperties h)
    localProperties (Tag GenericMark _) = return []
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
            guard (sign || Definition.isDefinition def)
            sb <- match (Definition.term def) f
            let definingFormula = replace (Tag GenericMark g) ThisT $ sb $ Definition.formula def
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
          sb <- match (Evaluation.term ev) t
          guard (all trivialByEvidence $ map sb $ Evaluation.conditions ev)
          return $ replace (Tag GenericMark t) ThisT $ sb $ 
            if sign then Evaluation.positives ev else Evaluation.negatives ev

    unfGuard unfoldSetting action =
      asks unfoldSetting >>= \p -> if p then action else return []

hasDMK (Tag GenericMark _ ) = True
hasDMK _ = False

setType f | hasInfo f = any (infoTwins ThisT $ zSet ThisT) $ trInfo f
setType _ = False

funType f | hasInfo f = any (infoTwins ThisT $ zFun ThisT) $ trInfo f
funType _ = False

hasInfo f = isTrm f || isVar f
