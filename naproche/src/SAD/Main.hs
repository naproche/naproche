{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018), Makarius Wenzel (2018),
  Anton Lorenzen (2019 - 2021)

Main application entry point: console or server mode.
-}

{-# LANGUAGE OverloadedStrings #-}

module SAD.Main (Args(..), ParseArgs(..), ProveArgs(..), translate, check, exportLean) where

import Data.Text (Text)
import qualified Data.Text as Text
import qualified System.Exit as Exit
import qualified Data.Map as Map
import Data.Map (Map)
import Control.Monad.State
import Data.Either (isRight)
import Data.Time (NominalDiffTime, UTCTime, getCurrentTime, diffUTCTime)
import Data.Maybe (isNothing)
import Data.List (isSuffixOf)
import Data.Foldable (toList)

import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.String (renderString)
import SAD.Data.Message (Comm, errorParser, outputMain, Kind(..), textFieldWidth)
import SAD.Core.Prove (ProveArgs(..), RunProver(..), verify, runProveT, ProveState(..))
import SAD.Core.Reader (readProofText, HasLibrary(..))
import SAD.Data.SourcePos (SourcePos, noSourcePos, fileOnlyPos)
import SAD.Data.Text.Block (ProofText(..), findParseError)
import SAD.Data.Instr (Instr(..), Argument(..), ParserKind(..), noPos)
import SAD.Parser.Error (errorPos)
import SAD.Core.Transform (transform)
import SAD.Core.AST (located)
import SAD.Core.Cache (CacheStorage)
import SAD.Core.Task (Task(..))
import SAD.Core.Tactic (proofTasks, ontologicalTasks)
import SAD.Core.Typecheck (typecheck)
import SAD.Core.Desuger (desuger)
import SAD.Core.Unique
import qualified SAD.Core.Lean as Lean (exportLean)
import System.Exit (exitFailure)

newtype ParseArgs = ParseArgs
  { useTex :: Bool
  } deriving (Eq, Ord, Show)

data Args = Args
  { parseArgs :: ParseArgs
  , proveArgs :: ProveArgs
  } deriving (Eq, Ord, Show)

parse :: (MonadIO m, RunProver m, Comm m, CacheStorage m, HasLibrary m)
  => Args -> FilePath -> Times m [ProofText]
parse opts0 file = do
  let pk = if useTex (parseArgs opts0) || ".tex.ftl" `isSuffixOf` file || ".ftl.tex" `isSuffixOf` file
      then Tex else NonTex
  let text0 = [ProofTextInstr noPos $ GetArgument (Read pk) (Text.pack file)]
  beginTimedSection ParsingTime
  txts <- lift $ readProofText text0
  case findParseError $ ProofTextRoot txts of
    Just err -> do
      lift $ errorParser (errorPos err) (show err)
    Nothing -> do
      endTimedSection ParsingTime
      pure $ txts

proveTasks :: (MonadIO m, RunProver m, Comm m, CacheStorage m)
  => [Task] -> Args -> Times m ProveState
proveTasks tasks opts0 = do
  lift $ fmap snd $ runProveT (proveArgs opts0) $ verify tasks

printFailure :: (MonadIO m, Pretty a, Foldable t, Comm m) => Either (t a) b -> m b
printFailure x = case x of
  Left errs -> do
    mapM_ (writeOut noSourcePos . pretty) $ toList errs
    liftIO exitFailure
  Right x -> pure x

translate :: (MonadIO m, RunProver m, Comm m, CacheStorage m, HasLibrary m, HasUnique m)
  => Args -> FilePath -> m Exit.ExitCode
translate opts0 file = flip evalStateT mempty $ runTimes $ do
  txts <- parse opts0 file
  -- lift $ mapM_ (\case (ProofTextBlock b) -> outputMain WRITELN (fileOnlyPos "") $ show b; _ -> pure ()) txts
  converted <-lift $ printFailure =<< transform txts
  beginTimedSection CheckTime
  -- lift $ mapM_ (writeOut (fileOnlyPos "") . pretty . located) converted
  typed <- lift $ printFailure =<< typecheck converted
  endTimedSection CheckTime
  lift $ mapM_ (writeOut (fileOnlyPos "") . pretty . located) typed

  beginTimedSection OntoTime
  let numberOfSections = length typed
  let ontoTasks = ontologicalTasks $ desuger typed
  unless (null ontoTasks) $ do
    lift $ writeOut noSourcePos $ "Ontological checking:"
  proveOut <- proveTasks ontoTasks opts0
  endTimedSection OntoTime

  -- print statistics
  beginTimedSection ProvingTime
  endTimedSection ProvingTime

  exitWithProveState numberOfSections (checkConsistency $ proveArgs opts0) $ proveOut

check :: (MonadIO m, RunProver m, Comm m, CacheStorage m, HasLibrary m, HasUnique m)
  => Args -> FilePath -> m Exit.ExitCode
check opts0 file = flip evalStateT mempty $ runTimes $ do
  txts <- parse opts0 file
  beginTimedSection CheckTime
  converted <- lift $ printFailure =<< transform txts
  typed <- lift $ printFailure =<< typecheck converted
  endTimedSection CheckTime

  beginTimedSection OntoTime
  let desugered = desuger typed
  proveOut1 <- proveTasks (ontologicalTasks desugered) opts0
  endTimedSection OntoTime

  beginTimedSection ProvingTime
  let numberOfSections = length typed
  proveOut2 <- proveTasks (proofTasks desugered) opts0
  endTimedSection ProvingTime
  exitWithProveState numberOfSections (checkConsistency $ proveArgs opts0) $ proveOut1 <> proveOut2

exportLean :: (MonadIO m, RunProver m, Comm m, CacheStorage m, HasLibrary m, HasUnique m)
  => Args -> FilePath -> m Exit.ExitCode
exportLean opts0 file = flip evalStateT mempty $ runTimes $ do
  txts <- parse opts0 file
  converted <- lift $ printFailure =<< transform txts
  typed <- lift $ printFailure =<< typecheck converted
  let desugered = desuger typed
  lift $ writeOut (fileOnlyPos "") $ Lean.exportLean desugered
  pure $ Exit.ExitSuccess

writeOut :: (Comm m) => SourcePos -> Doc ann -> m ()
writeOut pos doc = do
  w <- textFieldWidth
  outputMain WRITELN pos $ renderString $ layoutSmart
    (defaultLayoutOptions { layoutPageWidth = AvailablePerLine w 1.0 })
    (doc <> hardline)

exitWithProveState :: (MonadIO m, RunProver m, Comm m, CacheStorage m)
  => Int -> Bool -> ProveState -> Times m Exit.ExitCode
exitWithProveState numberOfSections checkConsistency proveOut = do
  let numberOfNotSuccessful = length (proveGoalsFailed proveOut ++ proveGoalsTimeout proveOut)
  let numberProved = proveGoalsSentToATP proveOut - numberOfNotSuccessful

  if null (proveGoalsTimeout proveOut) then pure ()
    else do
      lift $ writeOut (fileOnlyPos "") $ "The following claims could not be shown to hold:"
      lift $ mapM_ (\t -> writeOut (taskPos t) $ pretty $ conjecture t) (proveGoalsTimeout proveOut)
  if null (proveGoalsFailed proveOut) then pure ()
    else do
      lift $ writeOut (fileOnlyPos "") $ "The following claims do not follow from the axioms:"
      lift $ mapM_ (\t -> writeOut (taskPos t) $ pretty $ conjecture t) (proveGoalsFailed proveOut)

  case (checkConsistency, proveFirstContradiction proveOut) of
    (True, Just t) -> lift $ writeOut (taskPos t) $
      "Ouch, there is a contradiction in your axioms!" <> softline
      <> "It was first found in the claim:" <> softline
      <> pretty (conjecture t) <> hardline
      <> "Make sure you are in a proof by contradiction by writing 'Assume the contrary.'"
    _ -> lift $ outputMain TRACING noSourcePos $
      "sections "       ++ show numberOfSections
      ++ " - goals "    ++ show (proveGoalsSentToATP proveOut)
      ++ (if numberOfNotSuccessful == 0
              then ""
              else " - failed "   ++ show numberOfNotSuccessful)
      ++ " - proved "    ++ show numberProved
      ++ " - cached "    ++ show (proveGoalsCached proveOut)

  getTimes >>= lift . showTimes
  pure $ if numberOfNotSuccessful == 0 && (not checkConsistency || isNothing (proveFirstContradiction proveOut))
    then Exit.ExitSuccess else Exit.ExitFailure 1

-- Show final statistics

data TimedSection = ParsingTime | CheckTime | OntoTime | ProvingTime
  deriving (Eq, Ord, Show)

newtype Times m a = Times { runTimes :: StateT (Map TimedSection (Either UTCTime NominalDiffTime)) m a }
  deriving (Functor, Applicative, Monad, MonadTrans, MonadIO, MonadState (Map TimedSection (Either UTCTime NominalDiffTime)))

beginTimedSection :: MonadIO m => TimedSection -> Times m ()
beginTimedSection t = do
  time <- liftIO $ getCurrentTime
  modify $ Map.insert t (Left time)

endTimedSection :: MonadIO m => TimedSection -> Times m ()
endTimedSection t = do
  time <- liftIO $ getCurrentTime
  times <- get
  case Map.lookup t times of
    Just (Left begin) -> modify $ Map.insert t (Right $ diffUTCTime time begin)
    _ -> pure ()

getTimes :: MonadIO m => Times m (Map TimedSection NominalDiffTime)
getTimes = takeRights <$> get
  where takeRights = Map.map (\(Right r) -> r) . Map.filter isRight

showTimeDiff :: NominalDiffTime -> Text
showTimeDiff t =
  if hours == 0
    then format minutes <> ":" <> format restSeconds <> "." <> format restCentis
    else format hours   <> ":" <> format restMinutes <> ":" <> format restSeconds
  where
    format n = Text.pack $ if n < 10 then '0':show n else show n
    centiseconds = (truncate $ t * 100) :: Int
    (seconds, restCentis)  = divMod centiseconds 100
    (minutes, restSeconds) = divMod seconds 60
    (hours,   restMinutes) = divMod minutes 60

showTimes :: (Comm m) => Map TimedSection NominalDiffTime -> m ()
showTimes times = do
  outputMain TRACING noSourcePos $ Text.unpack $
    "parser "           <> showTimeDiff (times Map.! ParsingTime)
    <> " - checker "     <> showTimeDiff (times Map.! CheckTime)
    <> " - ontological "     <> showTimeDiff (times Map.! OntoTime)
    <> " - prover "     <> showTimeDiff (times Map.! ProvingTime)

  outputMain TRACING noSourcePos $ Text.unpack $
    "total " <> showTimeDiff ((times Map.! ParsingTime) + (times Map.! CheckTime) + (times Map.! ProvingTime))
