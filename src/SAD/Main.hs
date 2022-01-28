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

import qualified Isabelle.Byte_Message as Byte_Message
import qualified Isabelle.Naproche as Naproche
import qualified Isabelle.Server as Server
import qualified Isabelle.Options as Options
import qualified Isabelle.Isabelle_Thread as Isabelle_Thread
import qualified Isabelle.UUID as UUID
import qualified Isabelle.Position as Position
import qualified Isabelle.YXML as YXML
import qualified Isabelle.Process_Result as Process_Result
import Isabelle.Library

import SAD.API

import qualified Naproche.Program as Program
import qualified Naproche.Console as Console


newtype Cache = Cache (IORef (Int, ProofText))

init_cache :: IO Cache
init_cache = Cache <$> newIORef (0, ProofTextRoot [])

check_cache :: Cache -> Int -> IO ()
check_cache (Cache ref) i = do
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
  (opts0, pk, mFileName) <- readArgs args0
  text0 <- (map (uncurry ProofTextInstr) (reverse opts0) ++) <$> case mFileName of
    Nothing -> do
      stdin <- getContents
      pure [ProofTextInstr Position.none $ GetArgument (Text pk) (Text.pack stdin)]
    Just f -> do
      pure [ProofTextInstr Position.none $ GetArgument (File pk) (Text.pack f)]
  let opts1 = map snd opts0

  cache <- init_cache

  if askFlag Help False opts1 then
    putStr (GetOpt.usageInfo usageHeader options)
  else -- main body with explicit error handling, notably for PIDE
      (if askFlag Server False opts1 then
        Server.server (Server.publish_stdout "Naproche-SAD") (mainServer cache args0)
      else do
        Program.init_console
        rc <- do
          mainBody cache opts1 text0 mFileName
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

              (opts0, pk, fileName) <- readArgs (args0 ++ lines (make_string more_args))
              let opts1 = map snd opts0
              let text0 = map (uncurry ProofTextInstr) (reverse opts0)
              let text1 = text0 ++ [ProofTextInstr Position.none (GetArgument (Text pk) more_text)]

              check_cache cache $ Options.int options Naproche.naproche_pos_context

              rc <- do
                mainBody cache opts1 text1 fileName
                  `catch` (\(err :: Program.Error) -> do
                    robust_error $ Program.print_error err
                    return 0)
                  `catch` (\(err :: Exception.SomeException) -> do
                    robust_error $ make_bytes $ Exception.displayException err
                    return 0)

              if rc == 0 then return () else robust_error "ERROR")

        _ -> return ()

mainBody :: Cache -> [Instr] -> [ProofText] -> Maybe FilePath -> IO Int
mainBody cache opts0 text0 fileName = do
  startTime <- getCurrentTime

  oldProofText <- read_cache cache
  -- parse input text
  txts <- readProofText (askArgument Library "." opts0) text0
  let text1 = ProofTextRoot txts

  case askTheory FirstOrderLogic opts0 of
    FirstOrderLogic -> do
      -- if -T / --onlytranslate is passed as an option, only print the translated text
      if askFlag OnlyTranslate False opts0
        then do { showTranslation txts startTime; return 0 }
        else do
          success <- proveFOL text1 opts0 oldProofText cache startTime fileName
          return (if success then 0 else 1)
    CiC -> return 0
    Lean -> do { exportLean text1; return 0 }

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
proveFOL text1 opts0 oldProofText cache startTime fileName = do
  -- initialize reasoner state
  reasonerState <- newIORef (RState [] False False)

  proveStart <- getCurrentTime

  success <- case findParseError text1 of
    Nothing -> do
      let ProofTextRoot text = textToCheck oldProofText text1
      let file = maybe "" Text.pack fileName
      let filePos = Position.file_only $ make_bytes file
      let text' = ProofTextInstr Position.none (GetArgument (File NonTex) file) : text
      (success, newProofText) <- verifyRoot filePos reasonerState text'
      mapM_ (write_cache cache . ProofTextRoot) newProofText
      pure success
    Just err -> do
      errorParser (errorPos err) (show_bytes err)
      pure False

  finishTime <- getCurrentTime

  finalReasonerState <- readIORef reasonerState

  let trackerList = trackers finalReasonerState
  let accumulate  = sumCounter trackerList

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
    ++ " - checks "   ++ show (sumCounter trackerList HardChecks + trivialChecks)
    ++ " - trivial "  ++ show trivialChecks
    ++ " - proved "   ++ show (accumulate SuccessfulChecks)
    ++ " - unfolds "  ++ show (accumulate Unfolds)

  let proverTime     = sumTimer trackerList ProofTimer
  let simplifyTime   = sumTimer trackerList SimplifyTimer
  let proveFinish    = addUTCTime proverTime proveStart
  let simplifyFinish = addUTCTime simplifyTime proveFinish

  (outputMain TRACING Position.none . make_bytes) $
    "parser "           <> showTimeDiff (diffUTCTime proveStart startTime)
    <> " - reasoner "   <> showTimeDiff (diffUTCTime finishTime simplifyFinish)
    <> " - simplifier " <> showTimeDiff simplifyTime
    <> " - prover "     <> showTimeDiff proverTime
    <> "/" <> showTimeDiff (maximalTimer trackerList SuccessTimer)

  (outputMain TRACING Position.none . make_bytes) $
    "total " <> showTimeDiff (diffUTCTime finishTime startTime)

  return success


-- Command line parsing

readArgs :: [String] -> IO ([(Position.T, Instr)], ParserKind, Maybe FilePath)
readArgs args = do
  let (instrs, files, errs) = GetOpt.getOpt GetOpt.Permute options args

  let fail msgs = errorWithoutStackTrace (unlines (map trim_line msgs))
  unless (null errs) $ fail errs

  initFile <- readInit (askArgument Init "init.opt" instrs)
  let initialOpts = initFile ++ map (Position.none,) instrs

  let revInitialOpts = reverse initialOpts
  let useTexArg = askFlag UseTex False $ map snd revInitialOpts
  let fileName = case files of
                  [file] -> Just file
                  [] -> Nothing
                  _ -> fail ["More than one file argument\n"]
  let parserKind = if useTexArg || maybe False (\f -> ".tex.ftl" `isSuffixOf` f || ".ftl.tex" `isSuffixOf` f) fileName
      then Tex else NonTex
  pure (revInitialOpts, parserKind, fileName)

usageHeader :: String
usageHeader =
  "\nUsage: Naproche-SAD <options...> <file...>\n\n  At most one file argument may be given; \"\" refers to stdin.\n\n  Options are:\n"

options :: [GetOpt.OptDescr Instr]
options = [
  GetOpt.Option "h" ["help"] (GetOpt.NoArg (SetFlag Help True)) "show command-line help",
  GetOpt.Option ""  ["init"] (GetOpt.ReqArg (GetArgument Init . Text.pack) "FILE")
    "init file, empty to skip (def: init.opt)",
  GetOpt.Option "T" ["onlytranslate"] (GetOpt.NoArg (SetFlag OnlyTranslate True))
    "translate input text and exit",
  GetOpt.Option "" ["translate"] (GetOpt.ReqArg (SetFlag Translation . parseConsent) "{on|off}")
    "print first-order translation of sentences",
  GetOpt.Option "" ["server"] (GetOpt.NoArg (SetFlag Server True))
    "run in server mode",
  GetOpt.Option ""  ["library"] (GetOpt.ReqArg (GetArgument Library . Text.pack) "DIR")
    "place to look for library texts (def: examples)",
  GetOpt.Option "P" ["prover"] (GetOpt.ReqArg (GetArgument Prover . Text.pack) "NAME")
    "use prover NAME (def: first listed)",
  GetOpt.Option "t" ["timelimit"] (GetOpt.ReqArg (LimitBy Timelimit . getLeadingPositiveInt) "N")
    "N seconds per prover call (def: 3)",
  GetOpt.Option "m" ["memorylimit"] (GetOpt.ReqArg (LimitBy Memorylimit . getLeadingPositiveInt) "N")
    "maximum N MiB of memory usage per prover call (def: 2048)",
  GetOpt.Option ""  ["depthlimit"] (GetOpt.ReqArg (LimitBy Depthlimit . getLeadingPositiveInt) "N")
    "N reasoner loops per goal (def: 7)",
  GetOpt.Option ""  ["checktime"] (GetOpt.ReqArg (LimitBy Checktime . getLeadingPositiveInt) "N")
    "timelimit for checker's tasks (def: 1)",
  GetOpt.Option ""  ["checkdepth"] (GetOpt.ReqArg (LimitBy Checkdepth . getLeadingPositiveInt) "N")
    "depthlimit for checker's tasks (def: 3)",
  GetOpt.Option "n" [] (GetOpt.NoArg (SetFlag Prove False))
    "cursory mode (equivalent to --prove off)",
  GetOpt.Option "r" [] (GetOpt.NoArg (SetFlag Check False))
    "raw mode (equivalent to --check off)",
  GetOpt.Option "" ["prove"] (GetOpt.ReqArg (SetFlag Prove . parseConsent) "{on|off}")
    "prove goals in the text (def: on)",
  GetOpt.Option "" ["theory"] (GetOpt.ReqArg (Theory . parseTheory) "{fol|lean|cic}")
    "Choose the underlying theory (First-Order-Logic, Lean Prover, Calculus of inductive Constructions) (def: fol)",
  GetOpt.Option "" ["check"] (GetOpt.ReqArg (SetFlag Check . parseConsent) "{on|off}")
    "check symbols for definedness (def: on)",
  GetOpt.Option "" ["symsign"] (GetOpt.ReqArg (SetFlag Symsign . parseConsent) "{on|off}")
    "prevent ill-typed unification (def: on)",
  GetOpt.Option "" ["info"] (GetOpt.ReqArg (SetFlag Info . parseConsent) "{on|off}")
    "collect \"evidence\" literals (def: on)",
  GetOpt.Option "" ["thesis"] (GetOpt.ReqArg (SetFlag Thesis . parseConsent) "{on|off}")
    "maintain current thesis (def: on)",
  GetOpt.Option "" ["filter"] (GetOpt.ReqArg (SetFlag Filter . parseConsent) "{on|off}")
    "filter prover tasks (def: on)",
  GetOpt.Option "" ["skipfail"] (GetOpt.ReqArg (SetFlag Skipfail . parseConsent) "{on|off}")
    "ignore failed goals (def: off)",
  GetOpt.Option "" ["flat"] (GetOpt.ReqArg (SetFlag Flat . parseConsent) "{on|off}")
    "do not read proofs (def: off)",
  GetOpt.Option "q" [] (GetOpt.NoArg (SetFlag Verbose False))
    "print no details",
  GetOpt.Option "v" [] (GetOpt.NoArg (SetFlag Verbose True))
    "print more details (-vv, -vvv, etc)",
  GetOpt.Option "" ["printgoal"] (GetOpt.ReqArg (SetFlag Printgoal . parseConsent) "{on|off}")
    "print current goal (def: on)",
  GetOpt.Option "" ["printreason"] (GetOpt.ReqArg (SetFlag Printreason . parseConsent) "{on|off}")
    "print reasoner's messages (def: off)",
  GetOpt.Option "" ["printsection"] (GetOpt.ReqArg (SetFlag Printsection . parseConsent) "{on|off}")
    "print sentence translations (def: off)",
  GetOpt.Option "" ["printcheck"] (GetOpt.ReqArg (SetFlag Printcheck . parseConsent) "{on|off}")
    "print checker's messages (def: off)",
  GetOpt.Option "" ["printprover"] (GetOpt.ReqArg (SetFlag Printprover . parseConsent) "{on|off}")
    "print prover's messages (def: off)",
  GetOpt.Option "" ["printunfold"] (GetOpt.ReqArg (SetFlag Printunfold . parseConsent) "{on|off}")
    "print definition unfoldings (def: off)",
  GetOpt.Option "" ["printfulltask"] (GetOpt.ReqArg (SetFlag Printfulltask . parseConsent) "{on|off}")
    "print full prover tasks (def: off)",
  GetOpt.Option "" ["printsimp"] (GetOpt.ReqArg (SetFlag Printsimp . parseConsent) "{on|off}")
    "print simplification process (def: off)",
  GetOpt.Option "" ["printthesis"] (GetOpt.ReqArg (SetFlag Printthesis . parseConsent) "{on|off}")
    "print thesis development (def: off)",
  GetOpt.Option "" ["unfoldlow"] (GetOpt.ReqArg (SetFlag Unfoldlow . parseConsent) "{on|off}")
    "enable unfolding of definitions in the whole low level context (def: on)",
  GetOpt.Option "" ["unfold"] (GetOpt.ReqArg (SetFlag Unfold . parseConsent) "{on|off}")
    "enable unfolding of definitions (def: on)",
  GetOpt.Option "" ["unfoldsf"] (GetOpt.ReqArg (SetFlag Unfoldsf . parseConsent) "{on|off}")
    "enable unfolding of class conditions and map evaluations (def: on)",
  GetOpt.Option "" ["unfoldlowsf"] (GetOpt.ReqArg (SetFlag Unfoldlowsf . parseConsent) "{on|off}")
    "enable unfolding of class and map conditions in general (def: off)",
  GetOpt.Option "" ["dump"]
    (GetOpt.ReqArg (SetFlag Dump . parseConsent) "{on|off}")
    "print tasks in prover's syntax (def: off)",
  GetOpt.Option "" ["tex"]
    (GetOpt.ReqArg (SetFlag UseTex . parseConsent) "{on|off}")
    "parse passed file with forthel tex parser (def: off)"
  ]

parseConsent :: String -> Bool
parseConsent "yes" = True ; parseConsent "on"  = True
parseConsent "no"  = False; parseConsent "off" = False
parseConsent s     = errorWithoutStackTrace $ "Invalid boolean argument: \"" ++ s ++ "\""

parseTheory :: String -> UnderlyingTheory
parseTheory s = go (map toLower s)
  where
    go "fol" = FirstOrderLogic
    go "cic" = CiC
    go "lean" = Lean
    go s = errorWithoutStackTrace $ "Invalid theory: \"" ++ s ++ "\""

getLeadingPositiveInt :: String -> Int
getLeadingPositiveInt s = case reads s of
  ((n, []) : _) | n >= 0 -> n
  _ -> errorWithoutStackTrace $ "Invalid integer argument: \"" ++ s ++ "\""
