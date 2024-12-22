-- |
-- Module      : SAD.Main
-- Copyright   : (c) 2001 - 2008, Andrei Paskevich,
--               (c) 2017 - 2018, Steffen Frerix,
--               (c) 2018, Makarius Wenzel
--               (c) 2024, Marcel Schütz
-- License     : GPL-3
--
-- Main application entry point: Terminal or PIDE mode.


{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}

module SAD.Main where

import Control.Monad (unless, when)
import Data.Time (addUTCTime, getCurrentTime, diffUTCTime)
import Data.Maybe (mapMaybe)
import Control.Exception qualified as Exception
import Control.Exception (catch)
import System.Console.GetOpt qualified as GetOpt
import System.Environment qualified as Environment
import System.IO
import System.FilePath
import Network.Socket (Socket)

import SAD.Prove.MESON qualified as MESON
import SAD.Export.Prover qualified as Prover
import SAD.Data.Instr
import SAD.API hiding (error)

import Isabelle.Bytes qualified as Bytes
import Isabelle.Bytes (Bytes)
import Isabelle.Byte_Message qualified as Byte_Message
import Isabelle.Naproche qualified as Naproche
import Isabelle.Server qualified as Server
import Isabelle.Options qualified as Options
import Isabelle.Isabelle_Thread qualified as Isabelle_Thread
import Isabelle.UUID qualified as UUID
import Isabelle.Position qualified as Position
import Isabelle.YXML qualified as YXML
import Isabelle.Process_Result qualified as Process_Result
import Isabelle.Library
import Isabelle.File qualified as File

import Naproche.Program qualified as Program
import Naproche.Console qualified as Console
import Naproche.Param qualified as Param


main :: IO ()
main  = do
  Console.setup
  -- Get the initial arguments. When Naproche is run in a terminal, they are
  -- given by the command line arguments that have been passed to Naproche by
  -- the user; when Naproche is run in a PIDE, they are a fixed set of
  -- arguments that are hard-coded into the PIDE integration.
  args <- Environment.getArgs
  (initInstrs, nonInstrArgs) <- readArgs args
  -- Run Naproche either in PIDE or terminal mode, depending on whether the
  -- server parameter is set to @True@ in the initial options. Note that unless
  -- Naproche is run in a PIDE, it is set to @False@.
  if getInstr serverParam initInstrs
    then mainPIDE initInstrs
    else mainTerminal initInstrs nonInstrArgs


-- * Terminal Mode

mainTerminal :: [Instr] -> [String] -> IO ()
mainTerminal initInstrs nonInstrArgs = do
  if getInstr helpParam initInstrs
    then putStr $ GetOpt.usageInfo usageHeader options
    else do
      -- Initialize MESON and prover cache:
      mesonCache <- MESON.init_cache
      proverCache <- Prover.init_cache
      -- Turn the initial instructions into proof texts:
      let locatedInitInstrs = reverse $ map (Position.none,) initInstrs
          initInstrProofTexts = map (uncurry ProofTextInstr) locatedInitInstrs
      -- Get the input text (either via a given file path or if no file path is
      -- provided via the stdin stream) as a proof text:
      (dialect, inputText) <- case nonInstrArgs of
        -- If a single non-instruction command line argument is given, regard it
        -- as the path to the input text file and determine the ForTheL dialect
        -- of its contents via its file name extension:
        [filePath] -> do
          let dialect = case takeExtensions filePath of
                ".ftl" -> Ftl
                ".ftl.tex" -> Tex
                _ -> error "Invalid file name extension"
          inputText <- make_bytes <$> File.read filePath
          return (dialect, inputText)
        -- If no non-instruction command line argument is given, regard the
        -- content of the stdin stream as the input text. Determind the ForTheL
        -- dialect of the text by whether the @tex@ flag is set in the command
        -- line arguments or not.
        [] -> do
          let tex = getInstr texParam initInstrs
              dialect = if tex then Tex else Ftl
              dialectStr = case dialect of
                Tex -> "TEX"
                Ftl -> "FTL"
          hSetBuffering stdout LineBuffering
          putStrLn $ "Enter a ForTheL text (in the " ++ dialectStr ++ " dialect)."
            ++ " Type CTRL+D to finish your input.\n"
          inputText <- make_bytes <$> getContents'
          putStr "\n"
          return (dialect, inputText)
        -- If more than one non-instruction command line arguments are given,
        -- throw an error:
        _ -> error "More than one file argument"
      -- Append the input text proof text to the instruction proof texts:
      let inputTextProofTexts = [ProofTextInstr Position.none $ GetText dialect inputText]
          proofTexts = initInstrProofTexts ++ inputTextProofTexts
      -- Verify the input text:
      Program.init_console
      resultCode <- do
        (if getInstr onlytranslateParam initInstrs
          then translateInputText proofTexts
          else verifyInputText mesonCache proverCache proofTexts)
        `catch` (\Exception.UserInterrupt -> do
          Program.exit_thread
          Console.stderr ("Interrupt" :: String)
          return Process_Result.interrupt_rc)
        `catch` (\(err :: Exception.SomeException) -> do
          Program.exit_thread
          Console.stderr (Exception.displayException err)
          return Process_Result.error_rc)
      Console.exit resultCode

usageHeader :: String
usageHeader =
  "Usage: Naproche <options> <file>\n\n" ++
  "  At most one file argument may be given; \"\" refers to stdin.\n\n" ++
  "  FLAG may be {on|off} or {yes|no}.\n\n" ++
  "  Options are:\n"


-- * PIDE Mode

mainPIDE :: [Instr] -> IO ()
mainPIDE initInstrs = do
  -- Initialize MESON and prover cache:
  mesonCache <- MESON.init_cache
  proverCache <- Prover.init_cache
  Server.server (Server.publish_stdout "Naproche-SAD") $ pideServer mesonCache proverCache initInstrs

pideServer :: MESON.Cache -> Prover.Cache -> [Instr] -> Socket -> IO ()
pideServer mesonCache proverCache initInstrs socket =
  let
    exchange_message0 = Byte_Message.exchange_message0 socket
    robust_error msg =
      exchange_message0 [Naproche.output_error_command, msg]
        `catch` (\(_ :: Exception.IOException) -> return ())
  in
    do
      chunks <- Byte_Message.read_message socket
      case chunks of
        Just (command : threads) | command == Naproche.cancel_program ->
          mapM_ Isabelle_Thread.stop_uuid (mapMaybe UUID.parse threads)

        Just [command, more_args, opts, text] | command == Naproche.forthel_program -> do
          let options = Options.decode $ YXML.parse_body opts

          Exception.bracket_ (Program.init_pide socket options)
            Program.exit_thread
            (do
              thread_uuid <- Isabelle_Thread.my_uuid
              mapM_ (\uuid -> exchange_message0 [Naproche.threads_command, UUID.print uuid]) thread_uuid

              (moreInstrs, nonInstrArgs) <- readArgs $ lines (make_string more_args)
              let instrs = initInstrs ++ moreInstrs
                  locatedInstrs = map (Position.none,) instrs
                  instrProofTexts = map (uncurry ProofTextInstr) locatedInstrs
                  tex = getInstr texParam instrs
                  dialect = if tex then Tex else Ftl
                  inputTextProofTexts = [ProofTextInstr Position.none (GetText dialect text)]
              let proofTexts = instrProofTexts ++ inputTextProofTexts

              rc <- do
                verifyInputText mesonCache proverCache proofTexts
                  `catch` (\(err :: Program.Error) -> do
                    robust_error $ Program.print_error err
                    return 0)
                  `catch` (\(err :: Exception.SomeException) -> do
                    robust_error $ make_bytes $ Exception.displayException err
                    return 0)

              when (rc /= 0) $ robust_error "ERROR")

        _ -> return ()


-- * Translating or Verifying the Input Text

translateInputText :: [ProofText] -> IO Int
translateInputText proofTexts = do
  -- Get the starting time of the parsing process:
  startTime <- getCurrentTime
  -- Parse the input text:
  txts <- readProofText proofTexts
  -- Translate the input text and print the result:
  mapM_ (\case ProofTextBlock bl -> print bl; _ -> return ()) txts
  -- Get the finish time of the translation process:
  finishTime <- getCurrentTime
  -- Print the time it took to translate the input text:
  let timeDifference finishTime = showTimeDiff (diffUTCTime finishTime startTime)
  outputMain TRACING Position.none $ make_bytes $ "total " <> timeDifference finishTime
  return 0

verifyInputText :: MESON.Cache -> Prover.Cache -> [ProofText] -> IO Int
verifyInputText mesonCache proverCache proofTexts = do
  -- Get the starting time of the parsing process:
  startTime <- getCurrentTime
  -- Parse the input text:
  txts <- readProofText proofTexts
  -- Get the starting time of the verification process:
  proveStart <- getCurrentTime
  -- Verify the input text:
  (success, trackers) <- case concatMap parseErrors txts of
    [] -> verifyRoot mesonCache proverCache Position.none txts
    err : _ -> do
      errorParser (errorPos err) (show_bytes err)
      pure (False, [])
  -- Get the finish time of the verification process:
  finishTime <- getCurrentTime
  let accumulate = sumCounter trackers
  -- Print statistics:
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
  -- Prune MESON and prover chaches:
  MESON.prune_cache mesonCache
  Prover.prune_cache proverCache
  -- Return a result code:
  return $ if success
    then 0
    else 1


-- * Arguments

readArgs :: [String] -> IO ([Instr], [String])
readArgs args = do
  let (instrs, nonInstrArgs, errors) = GetOpt.getOpt GetOpt.Permute options args

  let fail msgs = errorWithoutStackTrace (unlines $ map trim_line msgs)
  unless (null errors) $ fail errors
  return (instrs, nonInstrArgs)

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
