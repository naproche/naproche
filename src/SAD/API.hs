-- | Authors: Anton Lorenzen (2019)
-- This is an re-export of the relevant parts of SAD's API which means that the rest can
-- remain out of the 'exposed-modules'. That allows us to detect unnecessary exports
-- and leads to better encapsulation.

module SAD.API
  ( module SAD.Core.Base
  , module SAD.Core.Message
  , module SAD.Core.Verify
  , module SAD.Data.Instr
  , module SAD.Data.Text.Block
  , module SAD.Import.Reader
  , module SAD.Parser.Error
  , module SAD.Data.Formula
  , module SAD.Structures.StructureTree
  ) where

import SAD.Core.Base (showTimeDiff, RState(..), initRState, sumCounter, Counter(..), sumTimer, Timer(..), maximalTimer)
import SAD.Core.Message
import SAD.Core.Verify (verifyRoot)
import SAD.Data.Instr (Instr(..), Flag(..), askFlag, Limit(..), askLimit, Argument(..), askArgument, Arguments(..), UnderlyingTheory(..), askTheory, ParserKind(..))
import SAD.Data.Text.Block (ProofText(..), textToCheck, findParseError)
import SAD.Import.Reader (readInit, readProofText)
import SAD.Parser.Error (errorPos)
import SAD.Data.Formula (Formula)
import SAD.Structures.StructureTree
