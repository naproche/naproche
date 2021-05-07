{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018)

Construct prover database.
-}

{-# LANGUAGE OverloadedStrings #-}

module SAD.Core.Provers (Prover(..), provers) where

import Data.Text (Text)
import SAD.Core.Task (ExportLang(..))

data Prover = Prover {
  name           :: String,
  path           :: String,
  arguments      :: [String],
  exportLang     :: ExportLang,
  successMessage :: [Text],
  contradictionMessage :: [Text],
  failureMessage :: [Text],
  resourceOutMessage :: [Text] }
  deriving (Eq, Ord, Show)

provers :: [Prover]
provers =
  [ Prover
      "eprover"
      "eprover"
      [ "--auto"
      , "-s"
      , "--memory-limit=%m"
      , "--cpu-limit=%t"
      ]
      TF0
      [ "# SZS status Theorem" ]
      [ "# SZS status ContradictoryAxioms" ]
      [ "# SZS status CounterSatisfiable" ]
      [ "# SZS status ResourceOut"
      , "# SZS status GaveUp"
      ]
   , Prover
      "spass"
      "SPASS"
      [ "-TPTP"
      , "-CNFOptSkolem=0"
      , "-PProblem=0"
      , "-PGiven=0"
      , "-TimeLimit=%t"
      ]
      FOF
      [ "SPASS beiseite: Proof found." ]
      []
      [ "SPASS beiseite: Completion found." ]
      [ "SPASS beiseite: Ran out of time." ]
   , Prover
      "vampire"
      "vampire"
      [ "--mode"
      , "casc"
      , "-t %t"
      ]
      TF0
      [ "% SZS output end Proof for" ]
      []
      [ "% SZS status CounterSatisfiable for" ]
      [ "% SZS status Timeout for" ]
   ]
