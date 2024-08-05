-- |
-- Module      : SAD.Core.Check
-- Copyright   : (c) 2001 - 2008, Andrei Paskevich,
--               (c) 2017 - 2018, Steffen Frerix
-- License     : GPL-3
--
-- Well-definedness check and evidence collection.


{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}
{-# LANGUAGE OverloadedStrings #-}

module SAD.Core.Check (fillDef) where

import Data.Maybe (fromMaybe)
import Data.Either (lefts,rights, isRight)
import Control.Monad (MonadPlus(..), guard)
import Control.Monad.Reader
import Data.Text.Lazy qualified as Text

import SAD.Core.Base
import SAD.Core.Reason as Reason
import SAD.Data.Definition hiding (Guards)
import SAD.Data.Formula
import SAD.Data.Instr
import SAD.Data.Text.Context (Context)
import SAD.Core.Message qualified as Message
import SAD.Data.Text.Block qualified as Block (link, position)
import SAD.Data.Text.Context qualified as Context

import Isabelle.Position qualified as Position


{- check definitions and fortify terms with evidences in a formula -}
fillDef :: Position.T -> Context -> VerifyMonad Formula
fillDef pos context = fill True False [] (Just True) 0 (Context.formula context)
  where
    fill :: Bool -> Bool -> [Formula] -> Maybe Bool -> Int -> Formula -> VerifyMonad Formula
    fill isPredicate isNewWord localContext sign n = \case
      Tag HeadTerm f' -> Tag HeadTerm <$> fill isPredicate True localContext sign n f'

      Tag tag f' -> Tag tag <$> fill isPredicate isNewWord localContext sign n f'

      Trm{trmName = TermThesis} -> asks (Context.formula . currentThesis)

      v@Var{} -> do
        userInfoSetting <- asks (getInstruction infoParam)
        newContext      <- cnRaise context localContext
        collectInfo userInfoSetting v `withContext` newContext -- fortify the term

      term@Trm{trmName = t, trmArgs = tArgs, trmInfo = infos, trId = tId} ->
        do
          userInfoSetting <- asks (getInstruction infoParam)
          fortifiedArgs   <- mapM (fill False isNewWord localContext sign n) tArgs
          newContext      <- cnRaise context localContext
          fortifiedTerm   <- setDef pos isNewWord context term{trmArgs = fortifiedArgs} `withContext` newContext
          collectInfo (not isPredicate && userInfoSetting) fortifiedTerm `withContext` newContext -- fortify term

      f -> roundFM VarW (fill isPredicate isNewWord) localContext sign n f


    collectInfo :: Bool -> Formula -> VerifyMonad Formula
    collectInfo infoSetting term = if infoSetting
      then setInfo term
      else return term


cnRaise :: Context -> [Formula] -> VerifyMonad [Context]
cnRaise thisBlock local = do
  context <- asks currentContext
  return ((foldr $ (:) . Context.setFormula thisBlock) context local)




setDef :: Position.T -> Bool -> Context -> Formula -> VerifyMonad Formula
setDef pos isNewWord context term@Trm{trmName = t, trId = tId} =
  incrementCounter Symbols >>
    (    (guard isNewWord >> return term) -- do not check new word
    <|>  (findDef term >>= testDef pos context term) -- check term's definition
    <|>  (out >> mzero )) -- failure message
  where
    out =
      reasonLog Message.ERROR (Block.position (Context.head context)) $
        "unrecognized: " <> Text.pack (showsPrec 2 term "")


-- Find relevant definitions and test them
type Guards = [Formula]
type FortifiedTerm = Formula


findDef :: Formula -> VerifyMonad (Guards, FortifiedTerm)
findDef term@Trm{trmArgs = tArgs} = do
  def <- getDef term
  sb  <- match (defTerm def) term
  let guards   = map (infoSub sb) $ defGuards def -- definition's guards
      evidence = map sb $ defEvidence def -- definitional evidence
      newTerm  = term { trmInfo = evidence } -- fortified term
  return (guards, newTerm)

{-
testDef does what the name suggests and tests a definition. if the use has
disabled ontological checking we just assume that the definition fits, else we
check it. setup and cleanup take care of the special proof times that we allow
an ontological check. easyCheck are inbuild reasoning methods, hardCheck passes
a task to an ATP.
-}
testDef :: Position.T -> Context -> Formula -> (Guards, FortifiedTerm) -> VerifyMonad Formula
testDef pos context term (guards, fortifiedTerm) = do
  userCheckSetting <- asks (getInstruction checkParam)
  if   userCheckSetting
  then local setup $ easyCheck >>= hardCheck >> return fortifiedTerm
  else return fortifiedTerm
  where
    easyCheck = mapM trivialityCheck guards
    hardCheck hardGuards
      | all isRight hardGuards =
          incrementCounter TrivialChecks >>
          defLog ("trivial " <> header rights hardGuards)
      | otherwise =
          incrementCounter HardChecks >>
          defLog (header lefts hardGuards <> thead (rights hardGuards)) >>
          mapM_ (proveThesis' pos . Context.setFormula (wipeLink context)) (lefts hardGuards) >>
          incrementCounter SuccessfulChecks

    setup state =
      let
        timelimit = SetInt timelimitParam $ getInstruction checktimeParam state
        depthlimit = SetInt depthlimitParam $ getInstruction checkdepthParam state
      in addInstruction timelimit $ addInstruction depthlimit state

    wipeLink context =
      let block:restBranch = Context.branch context
      in  context {Context.branch = block {Block.link = []} : restBranch}


    header select guards =
      "check: " <> showsPrec 2 term " vs " <> format (select guards)
    thead [] = ""; thead guards = "(trivial: " <> format guards <> ")"
    format guards = if null guards then " - " else unwords . map show $ guards
    defLog =
      whenInstruction printcheckParam .
        reasonLog Message.WRITELN (Block.position (head $ Context.branch context))


-- Info heuristic

{- moves through the low level context and collects typings of a given term. In
   case of equality we also add the typings of the equated term -}
typings :: (MonadPlus m) => [Context] -> Formula -> m [Formula]
typings [] _ = mzero
typings (context:restContext) term =
  albetDive (Context.formula context) `mplus` typings restContext term
  where
    albetDive = dive . albet
    -- when we encouter a literal, compare its arguments with term
    dive f | isLiteral f = compare [] $ trmArgs $ ltAtomic f
      where
        compare _ [] = mzero
        compare ls (arg:rs) = -- try to match argument, else compare with rest
          matchThisArgument ls arg rs `mplus` compare (arg:ls) rs

        matchThisArgument ls arg rs =
          let sign = mbNot f; predicate = ltAtomic f in do
            match term arg
            let newInfo = sign predicate {trmArgs = reverse ls ++ (ThisT : rs)}
            return $ newInfo : notionEvidence ls predicate ++ trInfo arg

    dive e@Trm {trmName = TermEquality, trmArgs = [l,r]} =
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



setInfo :: Formula -> VerifyMonad Formula
setInfo t = do
  context <- asks currentContext
  let lowlevelContext  = takeWhile Context.isLowLevel context
      lowlevelEvidence = fromMaybe [] $ typings lowlevelContext t
  case t of
    t@Trm {} -> pure $ t {trmInfo = trmInfo t ++ lowlevelEvidence}
    v@Var {} -> pure $ v {varInfo = varInfo v ++ lowlevelEvidence}
