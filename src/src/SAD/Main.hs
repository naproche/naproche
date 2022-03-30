{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018), Makarius Wenzel (2018)

Main application entry point: console or server mode.
-}

{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}

module SAD.Main where

import Control.Monad (unless)
import Data.Char (toLower)
import Data.Time (UTCTime, addUTCTime, getCurrentTime, diffUTCTime)
import Data.List (isSuffixOf)

import qualified Data.Text.Lazy as Text
import qualified System.Console.GetOpt as GetOpt

import qualified Isabelle.Bytes as Bytes
import Isabelle.Bytes (Bytes)
import qualified Isabelle.Position as Position
import Isabelle.Library

import qualified SAD.Prove.MESON as MESON
import qualified SAD.Export.Prover as Prover
import SAD.Data.Instr
import SAD.API

import qualified Naproche.Param as Param
import Naproche.File (MonadFile)
import Control.Monad.IO.Class (MonadIO(liftIO))
import qualified SAD.Core.Message as Kind

mainBody :: MonadFile m => [Instr] -> [ProofText] -> Maybe FilePath -> m Int
mainBody opts0 text0 fileArg = do
  mesonCache <- liftIO $ MESON.init_cache
  proverCache <- liftIO $ Prover.init_cache

  startTime <- liftIO getCurrentTime

  -- parse input text
  txts <- readProofText (getInstr libraryParam opts0) text0

  case map toLower $make_string $ getInstr theoryParam opts0 of
    "fol" -> do
      -- if -T / --onlytranslate is passed as an option, only print the translated text
      if getInstr onlytranslateParam opts0
        then do { liftIO $ showTranslation txts startTime; return 0 }
        else do
          success <- liftIO $ proveFOL txts opts0 mesonCache proverCache startTime fileArg
          liftIO $ MESON.prune_cache mesonCache
          liftIO $ Prover.prune_cache proverCache
          return (if success then 0 else 1)
    "cic" -> return 0
    "lean" -> do { liftIO $ exportLean txts; return 0 }
    s -> errorWithoutStackTrace ("Bad theory (fol|cic|lean): " <> quote s)

showTranslation :: [ProofText] -> UTCTime -> IO ()
showTranslation txts startTime = do
  let timeDifference finishTime = showTimeDiff (diffUTCTime finishTime startTime)
  mapM_ (\case ProofTextBlock bl -> outputTranslate Kind.WRITELN Position.none (show bl); _ -> return ()) txts

  -- print statistics
  finishTime <- getCurrentTime
  outputMain TRACING Position.none $ make_bytes $ "total " <> timeDifference finishTime

exportCiC :: ProofText -> IO ()
exportCiC pt = do
  case fmap (unlines . map ppForthelExpr) $ mapM toStatement $ extractBlocks pt of
    Left t -> putStrLn $ Text.unpack t
    Right s -> putStrLn s
  return ()

exportLean :: [ProofText] -> IO ()
exportLean txts = do
  case fmap toLeanCode $ mapM toStatement $ concatMap extractBlocks txts of
    Left t -> putStrLn $ Text.unpack t
    Right t -> putStrLn $ Text.unpack t
  return ()

proveFOL :: [ProofText] -> [Instr] -> MESON.Cache -> Prover.Cache -> UTCTime
  -> Maybe FilePath -> IO Bool
proveFOL txts opts0 mesonCache proverCache startTime fileArg = do
  -- initialize reasoner state
  proveStart <- getCurrentTime

  (success, trackers) <- case concatMap parseErrors txts of
    [] -> do
      let file = maybe "" Text.pack fileArg
      let filePos = Position.file_only $ make_bytes file
      let txts' = ProofTextInstr Position.none (GetArgument (File NonTex) file) : txts
      verifyRoot mesonCache proverCache filePos txts'
    err : _ -> do
      errorParser (errorPos err) (show_bytes err)
      pure (False, [])

  finishTime <- getCurrentTime

  let accumulate = sumCounter trackers

  -- print statistics
  (outputMain TRACING Position.none . make_bytes) $
    "sections "       ++ show (accumulate Sections)
    ++ " - goals "    ++ show (accumulate Goals)
    ++ (case accumulate FailedGoals of
        0 -> ""
        n -> " - failed " ++ show n)
    ++ " - trivial "   ++ show (accumulate TrivialGoals)
    ++ " - proved "    ++ show (accumulate SuccessfulGoals)
    ++ " - equations " ++ show (accumulate Equations)
    ++ (case accumulate FailedEquations of
        0 -> ""
        n -> " - failed " ++ show n)

  let trivialChecks = accumulate TrivialChecks

  (outputMain TRACING Position.none . make_bytes) $
    "symbols "        ++ show (accumulate Symbols)
    ++ " - checks "   ++ show (sumCounter trackers HardChecks + trivialChecks)
    ++ " - trivial "  ++ show trivialChecks
    ++ " - proved "   ++ show (accumulate SuccessfulChecks)
    ++ " - unfolds "  ++ show (accumulate Unfolds)

  let proverTime     = sumTimer trackers ProofTimer
  let simplifyTime   = sumTimer trackers SimplifyTimer
  let proveFinish    = addUTCTime proverTime proveStart
  let simplifyFinish = addUTCTime simplifyTime proveFinish

  (outputMain TRACING Position.none . make_bytes) $
    "parser "           <> showTimeDiff (diffUTCTime proveStart startTime)
    <> " - reasoner "   <> showTimeDiff (diffUTCTime finishTime simplifyFinish)
    <> " - simplifier " <> showTimeDiff simplifyTime
    <> " - prover "     <> showTimeDiff proverTime
    <> "/" <> showTimeDiff (maximalTimer trackers SuccessTimer)

  (outputMain TRACING Position.none . make_bytes) $
    "total " <> showTimeDiff (diffUTCTime finishTime startTime)

  return success


-- Command line parsing

readArgs :: MonadFile m => [String] -> m ([(Position.T, Instr)], ParserKind, Maybe FilePath)
readArgs args = do
  let (instrs, files, errs) = GetOpt.getOpt GetOpt.Permute options args

  let fail msgs = errorWithoutStackTrace (unlines (map trim_line msgs))
  unless (null errs) $ fail errs

  initFile <- readInit (getInstr initParam instrs)
  let initialOpts = initFile ++ map (Position.none,) instrs

  let revInitialOpts = reverse initialOpts
  let useTexArg = getInstr texParam $ map snd revInitialOpts
  let fileArg =
        case files of
          [file] -> Just file
          [] -> Nothing
          _ -> fail ["More than one file argument\n"]
  let parserKind =
        if useTexArg || maybe False (\f -> ".tex.ftl" `isSuffixOf` f || ".ftl.tex" `isSuffixOf` f) fileArg
        then Tex else NonTex
  pure (revInitialOpts, parserKind, fileArg)

usageHeader :: String
usageHeader =
  "\nUsage: Naproche-SAD <options...> <file...>\n\n  At most one file argument may be given; \"\" refers to stdin.\n\n  FLAG may be {on|off} or {yes|no}.\n\n  THEORY may be:\n    fol   (First-Order-Logic)\n    cic   (Calculus of inductive Constructions)\n    lean  (Lean Prover)\n\n  Options are:\n"

optParam :: [Char] -> Param.T a -> GetOpt.ArgDescr b -> String -> GetOpt.OptDescr b
optParam chars p = GetOpt.Option chars [name | not (null name)]
  where name = make_string $ Param.name p

optSwitch :: [Char] -> Param.T Bool -> Bool -> Bytes -> GetOpt.OptDescr Instr
optSwitch chars p b s = optParam chars (if b then p else Param.unnamed p) arg s'
  where arg = GetOpt.NoArg (SetBool p b)
        s' = make_string (if Bytes.null s then Param.description p else s)

optFlag :: [Char] -> Param.T Bool -> GetOpt.OptDescr Instr
optFlag chars p = optParam chars p arg s
  where arg = GetOpt.ReqArg (SetBool p . Param.parse p . make_bytes) "FLAG"
        s = make_string $ Param.description_default p

optNat :: [Char] -> Param.T Int -> GetOpt.OptDescr Instr
optNat chars p = optParam chars p arg s
  where arg = GetOpt.ReqArg (SetInt p . Param.parse p . make_bytes) "N"
        s = make_string $ Param.description_default p

optArgument :: [Char] -> Param.T Bytes -> String -> GetOpt.OptDescr Instr
optArgument chars p a = optParam chars p arg s
  where arg = GetOpt.ReqArg (SetBytes p . make_bytes) a
        s = make_string $ Param.description_default p
        
options :: [GetOpt.OptDescr Instr]
options = [
  optSwitch "h" helpParam True "",
  optArgument "" initParam "FILE",
  optSwitch "T" onlytranslateParam True "",
  optFlag "" translationParam,
  optSwitch "" serverParam True "",
  optArgument "" libraryParam "DIR",
  optArgument "P" proverParam "NAME",
  optNat "t" timelimitParam,
  optNat "m" memorylimitParam,
  optNat "" depthlimitParam,
  optNat "" checktimeParam,
  optNat "" checkdepthParam,
  optSwitch "n" proveParam False "cursory mode (equivalent to --prove=off)",
  optSwitch "r" checkParam False "raw mode (equivalent to --check=off)",
  optFlag "" proveParam,
  optArgument "" theoryParam "THEORY",
  optFlag "" checkParam,
  optFlag "" symsignParam,
  optFlag "" infoParam,
  optFlag "" thesisParam,
  optFlag "" filterParam,
  optFlag "" skipfailParam,
  optFlag "" flatParam,
  GetOpt.Option "q" [] (GetOpt.NoArg (Verbose False)) "print no details",
  GetOpt.Option "v" [] (GetOpt.NoArg (Verbose True)) "print more details",
  optFlag "" printgoalParam,
  optFlag "" printreasonParam,
  optFlag "" printsectionParam,
  optFlag "" printcheckParam,
  optFlag "" printproverParam,
  optFlag "" printunfoldParam,
  optFlag "" printfulltaskParam,
  optFlag "" printsimpParam,
  optFlag "" printthesisParam,
  optFlag "" unfoldlowParam,
  optFlag "" unfoldParam,
  optFlag "" unfoldsfParam,
  optFlag "" unfoldlowsfParam,
  optFlag "" dumpParam,
  optFlag "" texParam]
