{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018)

Well-definedness check and evidence collection.
-}

module Alice.Core.Check (fillDef) where

import Control.Monad
import Data.Maybe
import Data.Either (lefts,rights, isRight)
import Data.List
import qualified Data.IntMap.Strict as IM
import Control.Monad.State
import Control.Monad.Trans.Class
import Control.Monad.Reader

import Alice.Data.Formula
import Alice.Data.Instr
import Alice.Data.Text.Context
import Alice.Data.Text.Block (link, position)
import Alice.Data.Definition
import Alice.Core.Base
import Alice.Core.Message
import Alice.Core.Reason
import Alice.Prove.Normalize
import Alice.Prove.MESON
import Alice.Core.Reduction
import Alice.Core.ProofTask
import qualified Alice.Data.Structures.DisTree as DT


{- check definitions and fortify terms with evidences in a formula -}
fillDef :: Context -> VM Formula
fillDef context = fill True False [] (Just True) 0 $ cnForm context
  where
    fill isPredicat isNewWord localContext sign n (Tag tag f)
      | tag == DHD = -- newly introduced symbol
          fmap (Tag DHD) $ fill isPredicat True localContext sign n f
      | fnTag tag  = -- macros in function delcarations
          fmap cnForm thesis >>= getMacro context tag
      | otherwise  =  -- ignore every other tag
          fmap (Tag tag) $ fill isPredicat isNewWord localContext sign n f
    fill _ _ _ _ _ t  | isThesis t = thesis >>= return . cnForm
    fill _ _ localContext _ _ v | isVar v = do
      userInfoSetting <- askInstructionBin IBinfo True
      newContext      <- cnRaise context localContext
      collectInfo userInfoSetting v `withContext` newContext -- fortify the term
    fill isPredicat isNewWord localContext sign n 
         term@Trm {trName = t, trArgs = tArgs, trInfo = infos, trId = tId} = do
      userInfoSetting <- askInstructionBin IBinfo True
      fortifiedArgs   <- mapM (fill False isNewWord localContext sign n) tArgs
      newContext      <- cnRaise context localContext
      fortifiedTerm   <- setDef isNewWord context term {trArgs = fortifiedArgs} 
        `withContext` newContext
      collectInfo (not isPredicat && userInfoSetting) fortifiedTerm 
        `withContext` newContext        -- fortify term
    fill isPredicat isNewWord localContext sign n f = -- round throuth formula
      roundFM 'w' (fill isPredicat isNewWord) localContext sign n f 

    collectInfo infoSetting term
      | infoSetting = setInfo term
      | True        = return  term

cnRaise :: Context -> [Formula] -> VM [Context]
cnRaise thisBlock local = 
  asks currentContext >>=  return . flip (foldr $ (:) . setForm thisBlock) local




setDef :: Bool -> Context -> Formula -> VM Formula
setDef isNewWord context term@Trm{trName = t, trId = tId} = 
  incrementIntCounter Symbols >>
    (    guard isNewWord >> return term -- do not check new word
    <|>  findDef term >>= testDef context term -- check term's definition
    <|>  out >> mzero ) -- failure message
  where
    out =
      reasonLog NORMAL (position (cnHead context)) $
        "unrecognized: " ++ showsPrec 2 term ""


-- Find relevant definitions and test them
type Guards = [Formula]
type FortifiedTerm = Formula
type DefDuo = (Guards, FortifiedTerm)


findDef :: Formula -> VM DefDuo
findDef term@Trm{trArgs = tArgs} = do
  def <- getDef term
  sb  <- match (dfTerm def) term
  let guards   = map (infoSub sb) $ dfGrds def -- definition's guards
      evidence = map sb $ dfEvid def -- definitional evidence
      newTerm  = term { trInfo = evidence } -- fortified term
  return (guards, newTerm)

{-
testDef does what the name suggests and tests a definition. if the use has
disabled ontological checking we just assume that the definition fits, else we
check it. setup and cleanup take care of the special proof times that we allow
an ontological check. easyCheck are inbuild reasoning methods, hardCheck passes
a task to an ATP.
-}


testDef :: Context -> Formula -> DefDuo -> VM Formula
testDef context term (guards, fortifiedTerm) = do
  userCheckSetting <- askInstructionBin IBchck True
  if   userCheckSetting
  then setup >> easyCheck >>= hardCheck >> return fortifiedTerm 
  else return fortifiedTerm
  where
    easyCheck = mapM trivialityCheck guards
    hardCheck hardGuards 
      | all isRight hardGuards =
          incrementIntCounter TrivialChecks >>
          defLog ("trivial " ++ header rights hardGuards) >>
          cleanup
      | otherwise =
          (incrementIntCounter HardChecks >>
          defLog (header lefts hardGuards ++ thead (rights hardGuards)) >>
          mapM_ (reason . setForm (wipeLink context)) (lefts hardGuards) >>
          incrementIntCounter SuccessfulChecks >>
          cleanup) 
          <|> (cleanup >> mzero)

    setup = do
      askInstructionInt IIchtl 1 >>= addInstruction . InInt IItlim
      askInstructionInt IIchdp 3 >>= addInstruction . InInt IIdpth
      askInstructionBin IBOnch False >>= addInstruction. InBin IBOnto


    cleanup = do
      dropInstruction $ IdInt IItlim
      dropInstruction $ IdInt IIdpth
      dropInstruction $ IdBin IBOnto

    wipeLink context =
      let block:restBranch = cnBran context
      in  context {cnBran = block {link = []} : restBranch}


    header select guards =
      "check: " ++ showsPrec 2 term " vs " ++ format (select guards)
    thead [] = ""; thead guards = "(trivial: " ++ format guards ++ ")"
    format guards = if null guards then " - " else unwords . map show $ guards
    defLog =
      whenInstruction IBPchk False .
        reasonLog NORMAL (position (head $ cnBran context))



    trivialityCheck g = 
      if   trivialByEvidence g
      then return $ Right g  -- triviality check
      else launchReasoning `withGoal` g >> return (Right g) <|> return (Left g)


-- Info heuristic

{- moves through the low level context and collects typings of a given term. In
   case of equality we also add the typings of the equated term -}
typings :: (MonadPlus m) => [Context] -> Formula -> m [Formula]
typings [] _ = mzero
typings (context:restContext) term = 
  albetDive (cnForm context) `mplus` typings restContext term
  where
    albetDive = dive . albet
    -- when we encouter a literal, compare its arguments with term
    dive f | isLiteral f = compare [] $ ltArgs f 
      where
        compare _ [] = mzero
        compare ls (arg:rs) = -- try to match argument, else compare with rest
          matchThisArgument ls arg rs `mplus` compare (arg:ls) rs 
        
        matchThisArgument ls arg rs = 
          let sign = mbNot f; predicat = ltAtomic f in do 
            match term arg
            let newInfo = sign predicat {trArgs = reverse ls ++ (ThisT : rs)}
            return $ newInfo : notionEvidence ls predicat ++ trInfo arg

    dive e@Trm {trName = "=", trArgs = [l,r]} = 
      if   twins l term
      then return $ joinEvidences (trInfo l) (trInfo r)
      else if   twins r term
           then return $ joinEvidences (trInfo r) (trInfo l)
           else mzero
    dive (And f g) = albetDive g `mplus` albetDive f
    dive (Tag _ f) = albetDive f
    dive _         = mzero

    joinEvidences ls rs =
      filter (\l -> all (not . infoTwins term l) rs) ls ++ rs

    notionEvidence [] prd | isNotion prd = trInfo prd
    notionEvidence _ _ = []



setInfo :: Formula -> VM Formula
setInfo t = do
  context <- asks currentContext
  let lowlevelContext  = takeWhile cnLowL context
      lowlevelEvidence = fromMaybe [] $ typings lowlevelContext t
  return $ t {trInfo = trInfo t ++ lowlevelEvidence}
