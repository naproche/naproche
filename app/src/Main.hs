{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module Main where

import Options.Applicative
import qualified System.Exit as Exit
import SAD.Main
import CommandLine

-- Commandline options:

data Arguments = Arguments
  { args :: Args
  , library :: FilePath
  , inputFile :: FilePath
  } deriving (Eq, Show)

data CommandArgs
  = ExportLean Arguments
  | Translate Arguments
  | Check Arguments
  deriving (Eq, Show)

plibrary :: Parser String
plibrary = strOption
  (  long "library"
  <> short 'l'
  <> metavar "DIRECTORY"
  <> value "lib/"
  <> help "Place to look for library texts")

ptimelimit :: Parser Int
ptimelimit = option auto
  (  long "timelimit"
  <> short 't'
  <> metavar "SECONDS"
  <> value 1
  <> help "seconds per prover call")

pmemorylimit :: Parser Int
pmemorylimit = option auto
  (  long "memorylimit"
  <> short 'm'
  <> metavar "MEGABYTE"
  <> value 2048
  <> help "maximum memory usage of the prover")

pprover :: Parser String
pprover = strOption
  (  long "prover"
  <> short 'P'
  <> metavar "PROVER"
  <> value "eprover"
  <> help "default prover out of: spass, eprover, vampire")

pdump :: Parser Bool
pdump = switch
  (  long "dump"
  <> help "Dump the TPTP input for the prover")

ptex :: Parser Bool
ptex = switch
  (  long "tex"
  <> help "Use TeX mode")

pprintGoal :: Parser Bool
pprintGoal = switch
  (  long "no-print-goal"
  <> help "Don't print the goal for each proof task")

pabortOnFail :: Parser Bool
pabortOnFail = switch
  (  long "abort-on-fail"
  <> help "Abort on the first failed goal")

pcheckConsistency :: Parser Bool
pcheckConsistency = not <$> switch
  (  long "no-check-consistency"
  <> help "Don't check that the given axioms are consistent")

pinputFile :: Parser String
pinputFile = argument str
  (  metavar "FILE"
  <> help "The input file to be checked: extension .ftl or .ftl.tex")

arguments :: Parser Arguments
arguments = Arguments <$>
  (Args <$> (ParseArgs <$> ptex) 
        <*> (ProveArgs <$> ptimelimit
                       <*> pmemorylimit
                       <*> pprover
                       <*> pdump
                       <*> pprintGoal
                       <*> pabortOnFail
                       <*> pcheckConsistency))
  <*> plibrary
  <*> pinputFile

checkDesc, translateDesc, exportLeanDesc, mainDesc :: String
checkDesc = "Check every proof goal in the file"
translateDesc = "Translate the file into its internal representation"
exportLeanDesc = "Return a Lean translation"
mainDesc = "Naproche - Natural Proof Checker"

commandArgs :: Parser CommandArgs
commandArgs = hsubparser
  (  command "check" (info (Check <$> arguments) (progDesc checkDesc))
  <> command "translate" (info (Translate <$> arguments) (progDesc translateDesc))
  <> command "export-lean" (info (ExportLean <$> arguments) (progDesc exportLeanDesc)))

main :: IO ()
main = do
  args' <- execParser (info (commandArgs <**> helper) (progDesc mainDesc))
  case args' of
    Check (Arguments args library file) -> do
      exit <- runCommandLine library $ do
        check args file
      Exit.exitWith exit
    Translate (Arguments args library file) -> do
      exit <- runCommandLine library $ do
        translate args file
      Exit.exitWith exit
    ExportLean (Arguments args library file) -> do
      exit <- runCommandLine library $ do
        exportLean args file
      Exit.exitWith exit