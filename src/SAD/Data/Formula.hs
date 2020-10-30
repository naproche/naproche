module SAD.Data.Formula (
  module SAD.Data.Formula.Base,
  module SAD.Data.Formula.Kit,
  module SAD.Data.Formula.Show,
  module SAD.Data.Terms,
  module SAD.Data.VarName,
  dec, inc
  ) where

import SAD.Data.Formula.Base
import SAD.Data.Formula.Kit
import SAD.Data.Formula.Show
import SAD.Data.VarName
import SAD.Data.Terms

-- | Increment all de Bruijn indices by one.
inc :: Formula -> Formula
inc = incAbove 0
  where
    incAbove n = \case
      v@Ind{indIndex = i} -> v{indIndex = if n <= i then succ i else i}
      All x f -> All x $ incAbove (succ n) f
      Exi x f -> Exi x $ incAbove (succ n) f
      f -> mapF (incAbove n) f

-- | Decrement all de Bruijn indices by one.
dec :: Formula -> Formula
dec = decAbove 0
  where
    decAbove n = \case
      v@Ind{indIndex = i} -> v{indIndex = if n <= i then pred i else i}
      All x f -> All x $ decAbove (succ n) f
      Exi x f -> Exi x $ decAbove (succ n) f
      f -> mapF (decAbove n) f