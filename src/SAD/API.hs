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
  ) where

import SAD.Core.Base
import SAD.Core.Message
import SAD.Core.SourcePos (noSourcePos)
import SAD.Core.Verify (verify)
import SAD.Data.Instr
import SAD.Data.Text.Block (Text(..), textToCheck, findParseError)
import SAD.Export.Base (readProverDatabase)
import SAD.Import.Reader (readInit, readText)
import SAD.Parser.Error (errorPos)