{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018)

Verifier state monad and common functions.
-}
{-# LANGUAGE OverloadedStrings #-}

module SAD.Core.Base
  ( RState(..)

  , Timer(..), Counter(..), Tracker(..)
  , sumCounter
  , sumTimer
  , maximalTimer
  , showTimeDiff
  ) where

import Data.Text (Text)
import Data.Time (NominalDiffTime)
import qualified Data.Text as Text



-- | Reasoner state
data RState = RState
  { trackers       :: [Tracker]
  , failed         :: Bool
  , alreadyChecked :: Bool
  } deriving (Eq, Ord, Show)


-- | All of these counters are for gathering statistics to print out later
data Tracker
  = Timer Timer NominalDiffTime
  | Counter Counter Int
  deriving (Eq, Ord, Show)

data Timer
  = ProofTimer
  | SuccessTimer  -- successful prove time
  | SimplifyTimer
  deriving (Eq, Ord, Show)

data Counter
-- TODO append 'Counter' to each of these?
  = Sections
  | Goals
  | FailedGoals
  | SuccessfulGoals
  deriving (Eq, Ord, Show)

projectCounter :: [Tracker] -> Counter -> [Int]
projectCounter trackers counter =
  [ value | Counter counter' value <- trackers, counter == counter' ]

projectTimer :: [Tracker] -> Timer -> [NominalDiffTime]
projectTimer trackers timer =
  [ time | Timer timer' time <- trackers, timer == timer' ]


sumCounter :: [Tracker] -> Counter -> Int
sumCounter trackers counter = sum (projectCounter trackers counter)

sumTimer :: [Tracker] -> Timer -> NominalDiffTime
sumTimer trackers timer = sum (projectTimer trackers timer)

maximalTimer :: [Tracker] -> Timer -> NominalDiffTime
maximalTimer trackers timer = foldr max 0 (projectTimer trackers timer)

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