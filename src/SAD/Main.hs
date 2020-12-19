{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018), Makarius Wenzel (2018)

Main application entry point: console or server mode.
-}

{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}

module SAD.Main where

import Control.Monad (unless)
import Data.Char (toLower)
import Data.IORef
import Data.Maybe (fromMaybe)
import Data.Time (UTCTime, addUTCTime, getCurrentTime, diffUTCTime)
import Data.ByteString (ByteString)

import qualified Control.Exception as Exception
import qualified Data.Text.Lazy as Text
import qualified System.Console.GetOpt as GetOpt
import qualified System.Environment as Environment
import qualified System.Exit as Exit
import qualified System.IO as IO

import Isabelle.Library (trim_line)
import qualified Data.ByteString.UTF8 as UTF8
import qualified Isabelle.Byte_Message as Byte_Message
import qualified Isabelle.File as File
import qualified Isabelle.Naproche as Naproche
import qualified Isabelle.Properties as Properties
import qualified Isabelle.Server as Server
import qualified Isabelle.Standard_Thread as Standard_Thread
import qualified Isabelle.UUID as UUID
import qualified Isabelle.XML as XML
import qualified Isabelle.YXML as YXML
import Network.Socket (Socket)

import SAD.API

main :: IO ()
main  = do
  -- setup stdin/stdout
  File.setup IO.stdin
  File.setup IO.stdout
  File.setup IO.stderr
  IO.hSetBuffering IO.stdout IO.LineBuffering
  IO.hSetBuffering IO.stderr IO.LineBuffering

  -- command line and init file
  args0 <- Environment.getArgs
  (opts0, text0) <- readArgs args0

  oldProofTextRef <- newIORef $ ProofTextRoot []

  if askFlag Help False opts0 then
    putStr (GetOpt.usageInfo usageHeader options)
  else -- main body with explicit error handling, notably for PIDE
    Exception.catch
      (if askFlag Server False opts0 then
        Server.server (Server.publish_stdout "Naproche-SAD") (serverConnection oldProofTextRef args0)
      else do consoleThread; mainBody Nothing oldProofTextRef (opts0, text0))
      (\err -> do
        exitThread
        let msg = Exception.displayException (err :: Exception.SomeException)
        IO.hPutStrLn IO.stderr msg
        Exit.exitFailure)

mainBody :: Maybe ByteString -> IORef ProofText -> ([Instr], [ProofText]) -> IO ()
mainBody proversYaml oldProofTextRef (opts0, text0) = do
  startTime <- getCurrentTime

  oldProofText <- readIORef oldProofTextRef
  -- parse input text
  txts <- readProofText (askFlag Tex False opts0) (askArgument Library "." opts0) text0
  let text1 = ProofTextRoot txts

  case askTheory FirstOrderLogic opts0 of
    FirstOrderLogic -> do
      -- if -T / --onlytranslate is passed as an option, only print the translated text
      if askFlag OnlyTranslate False opts0
        then showTranslation txts startTime
        else do proveFOL proversYaml text1 opts0 oldProofText oldProofTextRef startTime
    CiC -> return ()
    Lean -> exportLean text1

showTranslation :: [ProofText] -> UTCTime -> IO ()
showTranslation txts startTime = do
  let timeDifference finishTime = showTimeDiff (diffUTCTime finishTime startTime)
  mapM_ (\case ProofTextBlock bl -> print bl; _ -> return ()) txts

  -- print statistics
  finishTime <- getCurrentTime
  outputMain TRACING noSourcePos $ Text.unpack $ "total " <> timeDifference finishTime

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

proveFOL :: Maybe ByteString -> ProofText -> [Instr] -> ProofText -> IORef ProofText -> UTCTime -> IO ()
proveFOL proversYaml text1 opts0 oldProofText oldProofTextRef startTime = do
  -- read provers.yaml
  provers <- case proversYaml of
    Nothing -> readProverFile $ Text.unpack (askArgument Provers "provers.yaml" opts0)
    Just txt -> readProverDatabase "" txt
  -- initialize reasoner state
  reasonerState <- newIORef (RState [] False False)

  proveStart <- getCurrentTime

  success <- case findParseError text1 of
    Nothing -> do
      let text = textToCheck oldProofText text1
      (success, newProofText) <- verify (askArgument File "" opts0) provers reasonerState text
      mapM_ (writeIORef oldProofTextRef) newProofText
      pure success
    Just err -> do errorParser (errorPos err) (show err); pure False

  finishTime <- getCurrentTime
  finalReasonerState <- readIORef reasonerState

  let trackerList = trackers finalReasonerState
  let accumulate  = sumCounter trackerList

  -- print statistics
  outputMain TRACING noSourcePos $
    "sections "       ++ show (accumulate Sections)
    ++ " - goals "    ++ show (accumulate Goals)
    ++ (let ignoredFails = accumulate FailedGoals
        in  if   ignoredFails == 0
            then ""
            else " - failed "   ++ show ignoredFails)
    ++ " - trivial "   ++ show (accumulate TrivialGoals)
    ++ " - proved "    ++ show (accumulate SuccessfulGoals)
    ++ " - equations " ++ show (accumulate Equations)
    ++ (let failedEquations = accumulate FailedEquations
        in  if   failedEquations == 0
            then ""
            else " - failed " ++ show failedEquations)

  let trivialChecks = accumulate TrivialChecks

  outputMain TRACING noSourcePos $
    "symbols "        ++ show (accumulate Symbols)
    ++ " - checks "   ++ show
      (sumCounter trackerList HardChecks + trivialChecks)
    ++ " - trivial "  ++ show trivialChecks
    ++ " - proved "   ++ show (accumulate SuccessfulChecks)
    ++ " - unfolds "  ++ show (accumulate Unfolds)

  let proverTime     = sumTimer trackerList ProofTimer
  let simplifyTime   = sumTimer trackerList SimplifyTimer
  let proveFinish    = addUTCTime proverTime proveStart
  let simplifyFinish = addUTCTime simplifyTime proveFinish

  outputMain TRACING noSourcePos $ Text.unpack $
    "parser "           <> showTimeDiff (diffUTCTime proveStart startTime)
    <> " - reasoner "   <> showTimeDiff (diffUTCTime finishTime simplifyFinish)
    <> " - simplifier " <> showTimeDiff simplifyTime
    <> " - prover "     <> showTimeDiff proverTime
    <> "/" <> showTimeDiff (maximalTimer trackerList SuccessTimer)

  outputMain TRACING noSourcePos $ Text.unpack $
    "total " <> showTimeDiff (diffUTCTime finishTime startTime)

  unless success Exit.exitFailure

serverConnection :: IORef ProofText -> [String] -> Socket -> IO ()
serverConnection oldProofTextRef args0 connection = do
  thread_uuid <- Standard_Thread.my_uuid
  mapM_ (Byte_Message.write_line_message connection . UUID.bytes) thread_uuid

  res <- Byte_Message.read_line_message connection
  case fmap (YXML.parse . UTF8.toString) res of
    Just (XML.Elem ((command, _), body)) | command == Naproche.cancel_command ->
      mapM_ Standard_Thread.stop_uuid (UUID.parse_string (XML.content_of body))

    Just (XML.Elem ((command, props), body)) | command == Naproche.forthel_command ->
      Exception.bracket_ (initThread props (Byte_Message.write connection))
        exitThread
        (do
          let args1 = lines (fromMaybe "" (Properties.get props Naproche.command_args))
          (opts1, text0) <- readArgs (args0 ++ args1)
          let text1 = text0 ++ [ProofTextInstr noPos (GetArgument Text (Text.pack $ XML.content_of body))]

          Exception.catch (mainBody Nothing oldProofTextRef (opts1, text1))
            (\err -> do
              let msg = Exception.displayException (err :: Exception.SomeException)
              Exception.catch
                (if YXML.detect msg then
                  Byte_Message.write connection [UTF8.fromString msg]
                 else outputMain ERROR noSourcePos msg)
                (\(err2 :: Exception.IOException) -> pure ())))

    _ -> return ()


-- Command line parsing

readArgs :: [String] -> IO ([Instr], [ProofText])
readArgs args = do
  let (instrs, files, errs) = GetOpt.getOpt GetOpt.Permute options args

  let fail msgs = errorWithoutStackTrace (unlines (map trim_line msgs))
  unless (null errs) $ fail errs
  commandLine <- case files of
                  [file] -> return $ instrs ++ [GetArgument File (Text.pack file)]
                  [] -> return instrs
                  _ -> fail ["More than one file argument\n"]

  initFile <- readInit (askArgument Init "init.opt" commandLine)
  let initialOpts = initFile ++ map (noPos,) commandLine

  let revInitialOpts = map snd $ reverse initialOpts
  let initialProofText = map (uncurry ProofTextInstr) initialOpts
  return (revInitialOpts, initialProofText)

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
    "place to look for library texts (def: .)",
  GetOpt.Option ""  ["provers"] (GetOpt.ReqArg (GetArgument Provers . Text.pack) "FILE")
    "index of provers (def: provers.yaml)",
  GetOpt.Option "P" ["prover"] (GetOpt.ReqArg (GetArgument Prover . Text.pack) "NAME")
    "use prover NAME (def: first listed)",
  GetOpt.Option "t" ["timelimit"] (GetOpt.ReqArg (LimitBy Timelimit . getLeadingPositiveInt) "N")
    "N seconds per prover call (def: 3)",
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
    "enable unfolding of set conditions and function evaluations (def: on)",
  GetOpt.Option "" ["unfoldlowsf"] (GetOpt.ReqArg (SetFlag Unfoldlowsf . parseConsent) "{on|off}")
    "enable unfolding of set and function conditions in general (def: off)",
  GetOpt.Option "" ["dump"]
    (GetOpt.ReqArg (SetFlag Dump . parseConsent) "{on|off}")
    "print tasks in prover's syntax (def: off)",
  GetOpt.Option "" ["tex"]
    (GetOpt.ReqArg (SetFlag Tex . parseConsent) "{on|off}")
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
