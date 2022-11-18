-- |
-- Authors: Adrian De Lon (2021)
--
-- TODO: Add description.


module Naproche.Helpers where

import Control.Monad


-- | Like 'guard', but the guard is monadic.
guardM :: MonadPlus m => m Bool -> m ()
guardM f = guard =<< f
