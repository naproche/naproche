{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

-- |
-- Module      : SAD.Main
-- Description : Main application entry point: Terminal or PIDE mode.
-- Copyright   : (c) 2001 - 2008, Andrei Paskevich
--               (c) 2017 - 2018, Steffen Frerix
--               (c) 2018, Makarius Wenzel
--               (c) 2024 - 2025, Marcel Schütz
-- License     : GPL-3
module SAD.Main where

import Control.Exception (Exception, catch, handle, throwIO)
import Control.Exception qualified as Exception
import Control.Monad (when)

import Data.List (isSuffixOf)
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
import Naproche.System (is_windows)

import Network.Socket (Socket)

import SAD.Core.Base (Counter(..), Timer(..), maximalTimer, showTimeDiff,
                      sumCounter, sumTimer)
import SAD.Core.Message (Kind(..), errorParser, outputMain)
import SAD.Core.Verify (verifyRoot)
import SAD.Data.Instr
import SAD.Data.Text.Block (ProofText(..), parseErrors)
import SAD.Export.Prover qualified as Prover
import SAD.Import.Reader (readProofText)
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
import System.FilePath.Posix
import System.IO
import System.Process (callCommand)


main :: IO ()
main = do
  Console.setup
  -- Get the initial arguments. When Naproche is run in a terminal, they are
  -- given by the command line arguments that have been passed to Naproche by
  -- the user; when Naproche is run in a PIDE, they are a fixed set of
  -- arguments that are hard-coded into the PIDE integration.
  args <- Environment.getArgs
  (initInstrs, mbFileArg) <- handle readArgsHandler $ readArgs args
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
    then putStr $ GetOpt.usageInfo usageHeader options
    else do
      -- Initialize MESON and prover cache:
      mesonCache <- MESON.init_cache
      proverCache <- Prover.init_cache
      -- Turn the initial instructions into proof texts:
      let locatedInitInstrs = reverse $ map (Position.none,) initInstrs
          initInstrProofTexts = map (uncurry ProofTextInstr) locatedInitInstrs
          mode = getInstr modeParam initInstrs
          texExe = getInstr texExeParam initInstrs
          bibtexExe = getInstr bibtexExeParam initInstrs
      -- Get the input text (either via a given file path or if no file path is
      -- provided via the stdin stream) as a proof text:
      (dialect, inputText, mbInputPath) <- do
        case mbFileArg of
          Just filePath -> do
            let dialect = getDialect initInstrs
            fileExists <- doesFileExist filePath
            inputText <- File.read filePath
            return (dialect, inputText, Just filePath)
          Nothing -> do
            let dialect = getDialect initInstrs
            hSetBuffering stdout LineBuffering
            putStrLn $ "Enter a ForTheL text (in the " ++ show dialect ++ " dialect)."
              ++ " Type CTRL+D to finish your input.\n"
            inputText <- make_bytes <$> getContents'
            putStr "\n"
            return (dialect, inputText, Nothing)
      -- Append the input text proof text to the instruction proof texts:
      let inputTextProofTexts = [ProofTextInstr Position.none $ GetText inputText]
          proofTexts = initInstrProofTexts ++ inputTextProofTexts
      -- Verify the input text:
      Program.init_console
      context <- Program.thread_context
      resultCode <- do
        (case mode of
          "lex" -> lexInputText dialect inputText
          "tokenize" -> tokenizeInputText dialect inputText
          "translate" -> translateInputText dialect proofTexts
          "verify" -> verifyInputText dialect mesonCache proverCache proofTexts
          "render" -> case mbInputPath of
            Nothing -> putStrLn "Unable to render input text: No input file given." >> return 1
            Just inputPath -> case dialect of
              Ftl -> putStrLn "Unable to render input text: No \".ftl.tex\" file given." >> return 1
              Tex -> renderInputFile inputPath (make_string texExe) (make_string bibtexExe)
              Stex -> renderInputFile inputPath (make_string texExe) (make_string bibtexExe)
          modeArg -> putStrLn ("Invalid mode: " ++ make_string modeArg) >> return 1)
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

              (moreInstrs, _) <- readArgs $ lines (make_string more_args)
              let instrs = initInstrs ++ moreInstrs
                  locatedInstrs = map (Position.none,) instrs
                  instrProofTexts = map (uncurry ProofTextInstr) locatedInstrs
                  dialect = getDialect instrs
                  inputTextProofTexts = [ProofTextInstr Position.none (GetText text)]
              let proofTexts = instrProofTexts ++ inputTextProofTexts

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
    Ftl -> FTL.lex Position.start bytes >>= putStrLn . FTL.renderLexemes
    Tex -> TEX.lex Position.start bytes >>= putStrLn . TEX.renderLexemes
    Stex -> STEX.lex Position.start bytes >>= putStrLn . STEX.renderLexemes
  -- Get the finish time of the translation process:
  finishTime <- getCurrentTime
  -- Print the time it took to translate the input text:
  let timeDifference finishTime = showTimeDiff (diffUTCTime finishTime startTime)
  outputMain TRACING Position.none $ make_bytes $ "total " <> timeDifference finishTime
  return 0

tokenizeInputText :: Dialect -> Bytes -> IO Int
tokenizeInputText dialect bytes = do
  -- Get the starting time of the parsing process:
  startTime <- getCurrentTime
  -- Lex and tokenize the input text and print the result:
  tokens <- case dialect of
    Ftl -> FTL.lex Position.start bytes >>= FTL.tokenize
    Tex -> TEX.lex Position.start bytes >>= TEX.tokenize
    Stex -> STEX.lex Position.start bytes >>= STEX.tokenize
  putStrLn $ renderTokens tokens
  -- Get the finish time of the translation process:
  finishTime <- getCurrentTime
  -- Print the time it took to translate the input text:
  let timeDifference finishTime = showTimeDiff (diffUTCTime finishTime startTime)
  outputMain TRACING Position.none $ make_bytes $ "total " <> timeDifference finishTime
  return 0

translateInputText :: Dialect -> [ProofText] -> IO Int
translateInputText dialect proofTexts = do
  -- Get the starting time of the parsing process:
  startTime <- getCurrentTime
  -- Parse the input text:
  txts <- readProofText dialect proofTexts
  -- Translate the input text and print the result:
  mapM_ (\case ProofTextBlock bl -> print bl; _ -> return ()) txts
  -- Get the finish time of the translation process:
  finishTime <- getCurrentTime
  -- Print the time it took to translate the input text:
  let timeDifference finishTime = showTimeDiff (diffUTCTime finishTime startTime)
  outputMain TRACING Position.none $ make_bytes $ "total " <> timeDifference finishTime
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
  let proverTime = sumTimer trackers ProofTimer
  let simplifyTime = sumTimer trackers SimplifyTimer
  let proveFinish = addUTCTime proverTime proveStart
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

renderInputFile :: FilePath -> FilePath -> FilePath -> IO Int
renderInputFile inputPath texExe bibtexExe = do
  if is_windows
    then do
      putStrLn "[Error] \"render\" mode is not supported on Windows."
      return 1
  else do
    putStrLn "[Warning] This is an experimental feature. Please be gentle.\n"

    mathhubVar <- make_string <$> getenv "NAPROCHE_MATHHUB"

    putStrLn $ "[Info] PDFLaTeX binary:  " ++ texExe
    putStrLn $ "[Info] BibTeX binary:    " ++ bibtexExe
    putStrLn $ "[Info] MATHHUB variable: " ++ mathhubVar

    putStr $ "\nReady to render \"" ++ inputPath ++ "\" to PDF. Continue? (Y/n) "
    hFlush stdout
    answer <- getLine
    putStr "\n"

    when (answer `elem` ["Y", "y", ""]) $ do
      -- Render the input file as PDF:
      let inputDir = takeDirectory inputPath
          inputFile = takeFileName inputPath
          inputFileBase = takeBaseName inputFile
      setCurrentDirectory inputDir
      callCommand $ "MATHHUB=\"" ++ mathhubVar ++ "\" STEX_WRITESMS=true " ++ texExe ++ " " ++ inputFile
      callCommand $ bibtexExe ++ " " ++ inputFileBase ++ " | true" -- succeed even if bibtex fails
      callCommand $ "MATHHUB=\"" ++ mathhubVar ++ "\" STEX_USESMS=true " ++ texExe ++ " " ++ inputFile
      callCommand $ "MATHHUB=\"" ++ mathhubVar ++ "\" STEX_USESMS=true " ++ texExe ++ " " ++ inputFile

    return 0


-- * Arguments

data ReadArgException =
    GetOptFailure String
  | TooManyFiles
  | InvalidFileNameExt String
  deriving (Show)

readArgsHandler :: ReadArgException -> IO a
readArgsHandler (GetOptFailure msg) = errorWithoutStackTrace msg
readArgsHandler TooManyFiles = errorWithoutStackTrace "more than one file argument"
readArgsHandler (InvalidFileNameExt ext) = errorWithoutStackTrace $ "invalid file name extension: " ++ quote ext

instance Exception ReadArgException

readArgs :: [String] -> IO ([Instr], Maybe FilePath)
readArgs args = do
  let (instrs, nonInstrArgs, errors) = GetOpt.getOpt GetOpt.Permute options args
  mapM_ (throwIO . GetOptFailure) errors

  case nonInstrArgs of
    [] -> return (instrs, Nothing)
    [fileArg] -> do
      dialectArg <- getDialectArg fileArg
      let dialectInstr = SetBytes dialectParam dialectArg
      return (dialectInstr : instrs, Just fileArg)
    _ -> throwIO TooManyFiles
    where
      getDialectArg fileName
        | ".ftl.en.tex" `isSuffixOf` fileName = return "stex"
        | ".ftl.tex" `isSuffixOf` fileName = return "tex"
        | ".ftl" `isSuffixOf` fileName = return "ftl"
        | otherwise = throwIO (InvalidFileNameExt fileName)

getDialect :: [Instr] -> Dialect
getDialect instrs = case getInstr dialectParam instrs of
  "ftl" -> Ftl
  "tex" -> Tex
  "stex" -> Stex
  dialectArg -> error "Invalid dialect argument"

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
  optArgument "M" modeParam "MODE",
  optArgument "" dialectParam "DIALECT",
  optFlag "" translationParam,
  optSwitch "" serverParam True "",
  optArgument "P" proverParam "NAME",
  optArgument "" texExeParam "EXE",
  optArgument "" bibtexExeParam "EXE",
  optNat "t" timelimitParam,
  optNat "m" memorylimitParam,
  optNat "" depthlimitParam,
  optNat "" checktimeParam,
  optNat "" checkdepthParam,
  optSwitch "n" proveParam False "cursory mode (equivalent to --prove=off)",
  optSwitch "r" checkParam False "raw mode (equivalent to --check=off)",
  optFlag "" proveParam,
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
  optFlag "" dumpParam]
