{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018), Makarius Wenzel (2018)

Main application entry point: console or server mode.
-}

{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}

module SAD.Main where

import Control.Monad (unless, when)
import Data.Char (toLower)
import Data.IORef
import Data.Time (UTCTime, addUTCTime, getCurrentTime, diffUTCTime)
import Data.List (isSuffixOf)
import Data.Maybe (mapMaybe)

import qualified Control.Exception as Exception
import Control.Exception (catch)
import qualified Data.Text.Lazy as Text
import qualified System.Console.GetOpt as GetOpt
import qualified System.Environment as Environment
import Network.Socket (Socket)

import qualified Isabelle.Bytes as Bytes
import Isabelle.Bytes (Bytes)
import qualified Isabelle.Byte_Message as Byte_Message
import qualified Isabelle.Naproche as Naproche
import qualified Isabelle.Server as Server
import qualified Isabelle.Options as Options
import qualified Isabelle.Isabelle_Thread as Isabelle_Thread
import qualified Isabelle.UUID as UUID
import qualified Isabelle.Position as Position
import qualified Isabelle.YXML as YXML
import qualified Isabelle.Value as Value
import qualified Isabelle.Process_Result as Process_Result
import Isabelle.Library

import SAD.Data.Instr
import SAD.API

import qualified Naproche.Program as Program
import qualified Naproche.Console as Console
import qualified Naproche.Param as Param


newtype Cache = Cache (IORef (Int, ProofText))

init_cache :: IO Cache
init_cache = Cache <$> newIORef (0, ProofTextRoot [])

reinit_cache :: Cache -> Int -> IO ()
reinit_cache (Cache ref) i = do
  (j, _) <- readIORef ref
  when (i /= j || j == 0) (writeIORef ref (i, ProofTextRoot []))

read_cache :: Cache -> IO ProofText
read_cache (Cache ref) = snd <$> readIORef ref

write_cache :: Cache -> ProofText -> IO ()
write_cache (Cache ref) text = do
  (i, _) <- readIORef ref
  writeIORef ref (i, text)


main :: IO ()
main  = do
  Console.setup

  -- command line and init file
  args0 <- Environment.getArgs
  (opts0, pk, fileArg) <- readArgs args0
  text0 <- (map (uncurry ProofTextInstr) (reverse opts0) ++) <$> case fileArg of
    Nothing -> do
      stdin <- getContents
      pure [ProofTextInstr Position.none $ GetArgument (Text pk) (Text.pack stdin)]
    Just name -> do
      pure [ProofTextInstr Position.none $ GetArgument (File pk) (Text.pack name)]
  let opts1 = map snd opts0

  cache <- init_cache

  if askParam helpParam opts1 then
    putStr (GetOpt.usageInfo usageHeader options)
  else -- main body with explicit error handling, notably for PIDE
      (if askParam serverParam opts1 then
        Server.server (Server.publish_stdout "Naproche-SAD") (mainServer cache args0)
      else do
        Program.init_console
        rc <- do
          mainBody cache opts1 text0 fileArg
            `catch` (\Exception.UserInterrupt -> do
              Program.exit_thread
              Console.stderr ("Interrupt" :: String)
              return Process_Result.interrupt_rc)
            `catch` (\(err :: Exception.SomeException) -> do
              Program.exit_thread
              Console.stderr (Exception.displayException err)
              return 1)
        Console.exit rc)

mainServer :: Cache -> [String] -> Socket -> IO ()
mainServer cache args0 socket =
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

              let more_text = Text.pack $ make_string text

              (opts0, pk, fileArg) <- readArgs (args0 ++ lines (make_string more_args))
              let opts1 = map snd opts0
              let text0 = map (uncurry ProofTextInstr) (reverse opts0)
              let text1 = text0 ++ [ProofTextInstr Position.none (GetArgument (Text pk) more_text)]

              reinit_cache cache $ Options.int options Naproche.naproche_pos_context

              rc <- do
                mainBody cache opts1 text1 fileArg
                  `catch` (\(err :: Program.Error) -> do
                    robust_error $ Program.print_error err
                    return 0)
                  `catch` (\(err :: Exception.SomeException) -> do
                    robust_error $ make_bytes $ Exception.displayException err
                    return 0)

              when (rc /= 0) $ robust_error "ERROR")

        _ -> return ()

mainBody :: Cache -> [Instr] -> [ProofText] -> Maybe FilePath -> IO Int
mainBody cache opts0 text0 fileArg = do
  startTime <- getCurrentTime

  oldProofText <- read_cache cache
  -- parse input text
  txts <- readProofText (askParam libraryParam opts0) text0
  let text1 = ProofTextRoot txts

  case map toLower $make_string $ askParam theoryParam opts0 of
    "fol" -> do
      -- if -T / --onlytranslate is passed as an option, only print the translated text
      if askParam onlytranslateParam opts0
        then do { showTranslation txts startTime; return 0 }
        else do
          success <- proveFOL text1 opts0 oldProofText cache startTime fileArg
          return (if success then 0 else 1)
    "cic" -> return 0
    "lean" -> do { exportLean text1; return 0 }
    s -> errorWithoutStackTrace ("Bad theory (fol|cic|lean): " <> quote s)

showTranslation :: [ProofText] -> UTCTime -> IO ()
showTranslation txts startTime = do
  let timeDifference finishTime = showTimeDiff (diffUTCTime finishTime startTime)
  mapM_ (\case ProofTextBlock bl -> print bl; _ -> return ()) txts

  -- print statistics
  finishTime <- getCurrentTime
  outputMain TRACING Position.none $ make_bytes $ "total " <> timeDifference finishTime

exportCiC :: ProofText -> IO ()
exportCiC pt = do
  case fmap (unlines . map ppForthelExpr) $ mapM toStatement $ extractBlocks pt of
    Left t -> putStrLn $ Text.unpack t
    Right s -> putStrLn s
  return ()

exportLean :: ProofText -> IO ()
exportLean pt = do
  case fmap toLeanCode $ mapM toStatement $ extractBlocks pt of
    Left t -> putStrLn $ Text.unpack t
    Right t -> putStrLn $ Text.unpack t
  return ()

proveFOL :: ProofText -> [Instr] -> ProofText -> Cache -> UTCTime -> Maybe FilePath -> IO Bool
proveFOL text1 opts0 oldProofText cache startTime fileArg = do
  -- initialize reasoner state
  reasonerState <- newIORef initRState

  proveStart <- getCurrentTime

  success <- case findParseError text1 of
    Nothing -> do
      let ProofTextRoot text = textToCheck oldProofText text1
      let file = maybe "" Text.pack fileArg
      let filePos = Position.file_only $ make_bytes file
      let text' = ProofTextInstr Position.none (GetArgument (File NonTex) file) : text
      (success, newProofText) <- verifyRoot filePos reasonerState text'
      mapM_ (write_cache cache . ProofTextRoot) newProofText
      pure success
    Just err -> do
      errorParser (errorPos err) (show_bytes err)
      pure False

  finishTime <- getCurrentTime

  trackers <- trackers <$> readIORef reasonerState
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

readArgs :: [String] -> IO ([(Position.T, Instr)], ParserKind, Maybe FilePath)
readArgs args = do
  let (instrs, files, errs) = GetOpt.getOpt GetOpt.Permute options args

  let fail msgs = errorWithoutStackTrace (unlines (map trim_line msgs))
  unless (null errs) $ fail errs

  initFile <- readInit (askParam initParam instrs)
  let initialOpts = initFile ++ map (Position.none,) instrs

  let revInitialOpts = reverse initialOpts
  let useTexArg = askParam texParam $ map snd revInitialOpts
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

optLimit :: [Char] -> Param.T Int -> GetOpt.OptDescr Instr
optLimit chars p = optParam chars p arg s
  where arg = GetOpt.ReqArg (SetInt p . Param.parse p . make_bytes) "N"
        s = make_string $ Param.description_default p

optText :: [Char] -> Param.T Bytes -> String -> GetOpt.OptDescr Instr
optText chars p a = optParam chars p arg s
  where arg = GetOpt.ReqArg (SetBytes p . make_bytes) a
        s = make_string $ Param.description_default p

options :: [GetOpt.OptDescr Instr]
options = [
  optSwitch "h" helpParam True "",
  optText "" initParam "FILE",
  optSwitch "T" onlytranslateParam True "",
  optFlag "" translationParam,
  optSwitch "" serverParam True "",
  optText "" libraryParam "DIR",
  optText "P" proverParam "NAME",
  optLimit "t" timelimitParam,
  optLimit "m" memorylimitParam,
  optLimit "" depthlimitParam,
  optLimit "" checktimeParam,
  optLimit "" checkdepthParam,
  optSwitch "n" proveParam False "cursory mode (equivalent to --prove=off)",
  optSwitch "r" checkParam False "raw mode (equivalent to --check=off)",
  optFlag "" proveParam,
  optText "" theoryParam "THEORY",
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

parseFlag :: String -> Bool
parseFlag s =
  case Param.parse_flag (make_bytes s) of
    Just b -> b
    Nothing -> errorWithoutStackTrace ("Bad flag: " <> quote s)

parseNat :: String -> Int
parseNat s =
  case Value.parse_nat $ make_bytes s of
    Just n -> n
    Nothing -> errorWithoutStackTrace ("Bad natural number: " <> quote s)
