{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

-- |
-- Module      : SAD.Main
-- Description : Main application entry point: Terminal or PIDE mode.
-- Copyright   : (c) 2001 - 2008, Andrei Paskevich
--               (c) 2017 - 2018, Steffen Frerix
--               (c) 2018, Makarius Wenzel
--               (c) 2024 - 2026, Marcel Schütz
-- License     : GPL-3
module SAD.Main where

import Control.Exception (catch)
import Control.Exception qualified as Exception
import Control.Monad (when)

import Data.Maybe (mapMaybe)
import Data.Time (addUTCTime, diffUTCTime, getCurrentTime)

import Isabelle.Byte_Message qualified as Byte_Message
import Isabelle.Bytes (Bytes)
import Isabelle.Bytes qualified as Bytes
import Isabelle.File qualified as File
import Isabelle.Isabelle_Thread qualified as Isabelle_Thread
import Isabelle.Library
import Isabelle.Naproche qualified as Naproche
import Isabelle.Options qualified as Options
import Isabelle.Position qualified as Position
import Isabelle.Process_Result qualified as Process_Result
import Isabelle.Server qualified as Server
import Isabelle.UUID qualified as UUID
import Isabelle.YXML qualified as YXML

import Naproche.Console qualified as Console
import Naproche.Param qualified as Param
import Naproche.Program qualified as Program
import Naproche.Prover (Prover)

import Network.Socket (Socket)

import SAD.Core.Base (Counter(..), Timer(..), maximalTimer, showTimeDiff, sumCounter, sumTimer)
import SAD.Core.Message (Kind(..), errorParser, outputMain)
import SAD.Core.Reader (readProofText)
import SAD.Core.Verify (verifyRoot)
import SAD.Data.Instr
import SAD.Data.Text.Block (ProofText(..), parseErrors)
import SAD.Export.Pretty
import SAD.Export.Prover qualified as Prover
import SAD.Parser.Error (ParseError(..))
import SAD.Parser.FTL.Lexer qualified as FTL
import SAD.Parser.FTL.Token qualified as FTL
import SAD.Parser.STEX.Lexer qualified as STEX
import SAD.Parser.STEX.Token qualified as STEX
import SAD.Parser.TEX.Lexer qualified as TEX
import SAD.Parser.TEX.Token qualified as TEX
import SAD.Parser.Token (renderTokens)
import SAD.Prove.MESON qualified as MESON

import System.Console.GetOpt qualified as GetOpt
import System.Directory
import System.Environment qualified as Environment
import System.IO


main :: IO ()
main = do
  Console.setup
  -- Get the initial arguments. When Naproche is run in a terminal, they are
  -- given by the command line arguments that have been passed to Naproche by
  -- the user; when Naproche is run in a PIDE, they are a fixed set of
  -- arguments that are hard-coded into the PIDE integration.
  args <- Environment.getArgs
  (initInstrs, mbFileArg) <- readArgs args
  -- Run Naproche either in PIDE or terminal mode, depending on whether the
  -- server parameter is set to @True@ in the initial options. Note that unless
  -- Naproche is run in a PIDE, it is set to @False@.
  if getInstr serverParam initInstrs
    then mainPIDE initInstrs
    else mainTerminal initInstrs mbFileArg


-- * Terminal Mode

mainTerminal :: [Instr] -> Maybe FilePath -> IO ()
mainTerminal initInstrs mbFileArg = do
  if getInstr helpParam initInstrs
    then Console.stdout usageInfo
    else do
      -- Initialize MESON and prover cache:
      mesonCache <- MESON.init_cache
      proverCache <- Prover.init_cache
      -- Turn the initial instructions into proof texts:
      let locatedInitInstrs = reverse $ map (Position.none,) initInstrs
          initInstrProofTexts = map (uncurry ProofTextInstr) locatedInitInstrs
          mode = getInstr modeParam initInstrs
      -- Get the input text (either via a given file path or if no file path is
      -- provided via the stdin stream) as a proof text:
      (dialect, inputText, mbInputPath) <- do
        let dialect = getInstr dialectParam initInstrs
        case mbFileArg of
          Just filePath -> do
            fileExists <- doesFileExist filePath
            inputText <- File.read filePath
            return (dialect, inputText, Just filePath)
          Nothing -> do
            hSetBuffering stdout LineBuffering
            Console.stdout $ "Enter a ForTheL text (in the " <> pretty_print dialect <> " dialect)."
              <> " Type CTRL+D to finish your input."
            inputText <- make_bytes <$> getContents'
            Console.stdout ""
            return (dialect, inputText, Nothing)
      -- Append the input text proof text to the instruction proof texts:
      let inputTextProofTexts = [ProofTextInstr Position.none $ GetText inputText]
          proofTexts = initInstrProofTexts ++ inputTextProofTexts
      -- Verify the input text:
      Program.init_console
      context <- Program.thread_context
      resultCode <- do
        (case mode of
          Lex_Mode -> lexInputText dialect inputText
          Tokenize_Mode -> tokenizeInputText dialect inputText
          Translate_Mode -> translateInputText dialect proofTexts
          Verify_Mode -> verifyInputText dialect mesonCache proverCache proofTexts)
        `catch` (\Exception.UserInterrupt -> do
          Program.exit_thread
          Console.stderr "Interrupt"
          return Process_Result.interrupt_rc)
        `catch` (\(err :: Exception.SomeException) -> do
          Program.exit_thread
          Console.stderr (make_bytes $ Exception.displayException err)
          return Process_Result.error_rc)
      Console.exit resultCode


usageInfo :: Bytes
usageInfo = make_bytes $ GetOpt.usageInfo usageHeader options

usageHeader :: String
usageHeader =
  "Usage: Naproche <options> <file>\n\n" ++
  "  At most one file argument may be given; \"\" refers to stdin.\n\n" ++
  "  FLAG may be {on|off}.\n\n" ++
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

              (moreInstrs, _) <- readArgs $ lines (make_string more_args)
              let instrs = initInstrs ++ moreInstrs
                  locatedInstrs = map (Position.none,) instrs
                  instrProofTexts = map (uncurry ProofTextInstr) locatedInstrs
                  inputTextProofTexts = [ProofTextInstr Position.none (GetText text)]
                  proofTexts = instrProofTexts ++ inputTextProofTexts
                  dialect = getInstr dialectParam instrs

              rc <- do
                verifyInputText dialect mesonCache proverCache proofTexts
                  `catch` (\(err :: Program.Error) -> do
                    robust_error $ Program.print_error err
                    return 0)
                  `catch` (\(err :: Exception.SomeException) -> do
                    robust_error $ make_bytes $ Exception.displayException err
                    return 0)

              when (rc /= 0) $ robust_error "ERROR")

        _ -> return ()


-- * Translating or Verifying the Input Text

lexInputText :: Dialect -> Bytes -> IO Int
lexInputText dialect bytes = do
  -- Get the starting time of the parsing process:
  startTime <- getCurrentTime
  -- Lex the input text and print the result:
  case dialect of
    Ftl_Dialect -> FTL.lex Position.start bytes >>= Console.stdout . FTL.renderLexemes
    Tex_Dialect -> TEX.lex Position.start bytes >>= Console.stdout . TEX.renderLexemes
    Stex_Dialect -> STEX.lex Position.start bytes >>= Console.stdout . STEX.renderLexemes
  -- Get the finish time of the translation process:
  finishTime <- getCurrentTime
  -- Print the time it took to translate the input text:
  let timeDifference finishTime = showTimeDiff (diffUTCTime finishTime startTime)
  outputMain TRACING Position.none $ "total " <> timeDifference finishTime
  return 0

tokenizeInputText :: Dialect -> Bytes -> IO Int
tokenizeInputText dialect bytes = do
  -- Get the starting time of the parsing process:
  startTime <- getCurrentTime
  -- Lex and tokenize the input text and print the result:
  tokens <- case dialect of
    Ftl_Dialect -> FTL.lex Position.start bytes >>= FTL.tokenize
    Tex_Dialect -> TEX.lex Position.start bytes >>= TEX.tokenize
    Stex_Dialect -> STEX.lex Position.start bytes >>= STEX.tokenize
  Console.stdout $ renderTokens tokens
  -- Get the finish time of the translation process:
  finishTime <- getCurrentTime
  -- Print the time it took to translate the input text:
  let timeDifference finishTime = showTimeDiff (diffUTCTime finishTime startTime)
  outputMain TRACING Position.none $ "total " <> timeDifference finishTime
  return 0

translateInputText :: Dialect -> [ProofText] -> IO Int
translateInputText dialect proofTexts = do
  -- Get the starting time of the parsing process:
  startTime <- getCurrentTime
  -- Parse the input text:
  txts <- readProofText dialect proofTexts
  -- Translate the input text and print the result:
  mapM_ (\case ProofTextBlock bl -> Console.stdout $ pretty_print bl; _ -> return ()) txts
  -- Get the finish time of the translation process:
  finishTime <- getCurrentTime
  -- Print the time it took to translate the input text:
  let timeDifference finishTime = showTimeDiff (diffUTCTime finishTime startTime)
  outputMain TRACING Position.none $ "total " <> timeDifference finishTime
  return 0

verifyInputText :: Dialect -> MESON.Cache -> Prover.Cache -> [ProofText] -> IO Int
verifyInputText dialect mesonCache proverCache proofTexts = do
  -- Get the starting time of the parsing process:
  startTime <- getCurrentTime
  -- Parse the input text:
  txts <- readProofText dialect proofTexts
  -- Get the starting time of the verification process:
  proveStart <- getCurrentTime
  -- Verify the input text:
  (success, trackers) <- case concatMap parseErrors txts of
    [] -> verifyRoot mesonCache proverCache Position.none txts
    err : _ -> do
      errorParser (errorPos err) (pretty_print err)
      pure (False, [])
  -- Get the finish time of the verification process:
  finishTime <- getCurrentTime
  let accumulate = sumCounter trackers
  -- Print statistics:
  outputMain TRACING Position.none $
    "sections "       <> show_bytes (accumulate Sections)
    <> " - goals "    <> show_bytes (accumulate Goals)
    <> (case accumulate FailedGoals of
        0 -> ""
        n -> " - failed " <> show_bytes n)
    <> " - trivial "   <> show_bytes (accumulate TrivialGoals)
    <> " - proved "    <> show_bytes (accumulate SuccessfulGoals)
    <> " - equations " <> show_bytes (accumulate Equations)
    <> (case accumulate FailedEquations of
        0 -> ""
        n -> " - failed " <> show_bytes n)
  let trivialChecks = accumulate TrivialChecks
  outputMain TRACING Position.none $
    "symbols "        <> show_bytes (accumulate Symbols)
    <> " - checks "   <> show_bytes (sumCounter trackers HardChecks + trivialChecks)
    <> " - trivial "  <> show_bytes trivialChecks
    <> " - proved "   <> show_bytes (accumulate SuccessfulChecks)
    <> " - unfolds "  <> show_bytes (accumulate Unfolds)
  let proverTime = sumTimer trackers ProofTimer
  let simplifyTime = sumTimer trackers SimplifyTimer
  let proveFinish = addUTCTime proverTime proveStart
  let simplifyFinish = addUTCTime simplifyTime proveFinish
  outputMain TRACING Position.none $
    "parser "           <> showTimeDiff (diffUTCTime proveStart startTime)
    <> " - reasoner "   <> showTimeDiff (diffUTCTime finishTime simplifyFinish)
    <> " - simplifier " <> showTimeDiff simplifyTime
    <> " - prover "     <> showTimeDiff proverTime
    <> "/" <> showTimeDiff (maximalTimer trackers SuccessTimer)
  outputMain TRACING Position.none $
    "total " <> showTimeDiff (diffUTCTime finishTime startTime)
  -- Prune MESON and prover chaches:
  MESON.prune_cache mesonCache
  Prover.prune_cache proverCache
  -- Return a result code:
  return $ if success
    then 0
    else 1


-- * Arguments

readArgs :: [String] -> IO ([Instr], Maybe FilePath)
readArgs args = do
  let (instrs, nonInstrArgs, errors) = GetOpt.getOpt GetOpt.Permute options args
  mapM_ (Program.error . make_bytes) errors

  case nonInstrArgs of
    [] -> return (instrs, Nothing)
    [fileArg] -> do
      dialectArg <- getDialectArg (make_bytes fileArg)
      let dialectInstr = SetDialect dialectParam dialectArg
      return (dialectInstr : instrs, Just fileArg)
    _ -> Program.error "More than one file argument"
    where
      getDialectArg fileName
        | ".ftl.en.tex" `Bytes.isSuffixOf` fileName = return Stex_Dialect
        | ".ftl.tex" `Bytes.isSuffixOf` fileName = return Tex_Dialect
        | ".ftl" `Bytes.isSuffixOf` fileName = return Ftl_Dialect
        | otherwise = Program.error $ "Invalid file name extension " <> quote fileName

optParam :: [Char] -> Param.T a -> GetOpt.ArgDescr b -> String -> GetOpt.OptDescr b
optParam chars p = GetOpt.Option chars [name | not (null name)]
  where name = make_string $ Param.name p

optSwitch :: [Char] -> Param.T Bool -> GetOpt.OptDescr Instr
optSwitch chars p = optParam chars p arg s
  where arg = GetOpt.NoArg (SetBool p True)
        s = make_string (Param.description p)

optArgument :: (Param.T a -> a -> Instr) -> String -> [Char] -> Param.T a -> GetOpt.OptDescr Instr
optArgument setter a chars p = optParam chars p arg s
  where arg = GetOpt.ReqArg (setter p . Param.parse p . make_bytes) a
        s = make_string $ Param.description_default p

optFlag :: [Char] -> Param.T Bool -> GetOpt.OptDescr Instr
optFlag = optArgument SetBool "FLAG"

optNat :: [Char] -> Param.T Int -> GetOpt.OptDescr Instr
optNat = optArgument SetInt "N"

optMode :: [Char] -> Param.T Mode -> GetOpt.OptDescr Instr
optMode = optArgument SetMode "MODE"

optDialect :: [Char] -> Param.T Dialect -> GetOpt.OptDescr Instr
optDialect = optArgument SetDialect "DIALECT"

optProver :: [Char] -> Param.T Prover -> GetOpt.OptDescr Instr
optProver = optArgument SetProver "NAME"

options :: [GetOpt.OptDescr Instr]
options = [
  optSwitch "h" helpParam,
  optSwitch "" serverParam,
  optSwitch "q" quietParam,
  optSwitch "v" verboseParam,
  optMode "" modeParam,
  optDialect "" dialectParam,
  optProver "" proverParam,
  optNat "t" timelimitParam,
  optNat "m" memorylimitParam,
  optNat "" depthlimitParam,
  optNat "" checktimeParam,
  optNat "" checkdepthParam,
  optFlag "" translationParam,
  optFlag "" proveParam,
  optFlag "" checkParam,
  optFlag "" symsignParam,
  optFlag "" infoParam,
  optFlag "" thesisParam,
  optFlag "" filterParam,
  optFlag "" skipfailParam,
  optFlag "" flatParam,
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
  optFlag "" dumpParam]
