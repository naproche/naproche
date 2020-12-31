-- | Authors: Anton Lorenzen (2019)
-- This is an re-export of the relevant parts of SAD's API which means that the rest can
-- remain out of the 'exposed-modules'. That allows us to detect unnecessary exports
-- and leads to better encapsulation.

module SAD.API
  ( module SAD.Core.Base
  , module SAD.Core.Message
  , module SAD.Core.SourcePos
  , module SAD.Core.Verify
  , module SAD.Data.Instr
  , module SAD.Data.Text.Block
  , module SAD.Export.Base
  , module SAD.Import.Reader
  , module SAD.Parser.Error
  , module SAD.Helpers
  , module SAD.Data.Formula
  , module SAD.Structures.StructureTree
  ) where

import SAD.Core.Base (showTimeDiff, RState(..), sumCounter, Counter(..), sumTimer, Timer(..), maximalTimer)
import SAD.Core.Message (consoleThread, exitThread, errorParser, outputMain, initThread, Kind(..))
import SAD.Core.SourcePos (noSourcePos)
import SAD.Core.Verify (verify)
import SAD.Data.Instr (Instr(..), Flag(..), askFlag, Limit(..), askLimit, Argument(..), askArgument, Arguments(..), noPos
  , UnderlyingTheory(..), askTheory, ParserKind(..), Pos)
import SAD.Data.Text.Block (ProofText(..), textToCheck, findParseError)
import SAD.Export.Base (readProverFile, readProverDatabase)
import SAD.Import.Reader (readInit, readProofText)
import SAD.Parser.Error (errorPos)
import SAD.Helpers (trimLine)
import SAD.Data.Formula (Formula)
import SAD.Structures.StructureTree
