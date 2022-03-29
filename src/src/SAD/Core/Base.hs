{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018)

Verifier state monad and common functions.
-}

{-# LANGUAGE PolymorphicComponents #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}


module SAD.Core.Base
  ( CRM
  , readTrackers
  , modifyTrackers
  , justIO
  , (<|>)

  , retrieveContext
  , initVState
  , defForm
  , getDef

  , VState(..), VerifyMonad, runVerifyMonad

  , Tracker(..), Timer(..), Counter(..)
  , sumCounter
  , sumTimer
  , maximalTimer
  , showTimeDiff
  , timeWith

  , getInstruction, addInstruction, dropInstruction
  , addToTimer, addToCounter, incrementCounter
  , guardInstruction, whenInstruction

  , reasonLog, simpLog, thesisLog, translateLog
  ) where

import Control.Applicative (Alternative(..))
import Control.Monad.Reader
import Control.Monad.State
import Data.IORef
import Data.Maybe (isJust, fromJust)
import Data.Text.Lazy (Text)
import Data.Time (NominalDiffTime, getCurrentTime, diffUTCTime)

import qualified Data.Set as Set
import qualified Data.Map as Map

import SAD.Data.Definition
import SAD.Data.Formula
import SAD.Data.Instr
import SAD.Data.Rules (Rule)
import SAD.Data.Text.Block (Block)
import SAD.Data.Text.Context (Context(Context), MRule(..))
import qualified SAD.Prove.MESON as MESON
import qualified SAD.Export.Prover as Prover

import qualified SAD.Core.Message as Message
import SAD.Data.Structures.DisTree (DisTree)
import qualified SAD.Data.Structures.DisTree as DisTree
import qualified SAD.Data.Text.Context as Context (name)

import qualified Isabelle.Bytes as Bytes
import qualified Isabelle.Position as Position
import Isabelle.Library (BYTES, make_bytes)

import qualified Naproche.Param as Param


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
  | TrivialGoals
  | SuccessfulGoals
  | Symbols
  | TrivialChecks
  | HardChecks
  | SuccessfulChecks
  | Unfolds
  | Equations
  | FailedEquations
  deriving (Eq, Ord, Show)


-- | CPS IO Maybe monad
newtype CRM b = CRM
  { runCRM :: forall a . IO a -> (b -> IO a) -> IO a }

instance Functor CRM where
  fmap = liftM

instance Applicative CRM where
  pure = return
  (<*>) = ap

instance Monad CRM where
  return r = CRM (\_ k -> k r)
  m >>= n = CRM (\z k -> runCRM m z (\r -> runCRM (n r) z k))

instance Alternative CRM where
  empty = mzero
  (<|>) = mplus

instance MonadPlus CRM where
  mzero = CRM (\z _ -> z)
  mplus m n = CRM (\z k -> runCRM m (runCRM n z k) k)


data VState = VState
  { thesisMotivated :: Bool
  , rewriteRules    :: [Rule]
  , evaluations     :: DisTree Evaluation -- (low level) evaluation rules
  , currentThesis   :: Context
  , currentBranch   :: [Block] -- branch of the current block
  , currentContext  :: [Context]
  , mesonRules      :: (DisTree MRule, DisTree MRule)
  , definitions     :: Definitions
  , guards          :: Guards -- tracks which atomic formulas appear as guard
  , skolemCounter   :: Int
  , instructions    :: [Instr]
  , trackers        :: IORef [Tracker]
  , mesonCache      :: MESON.Cache
  , proverCache     :: Prover.Cache
  }

initVState :: MESON.Cache -> Prover.Cache -> IO VState
initVState mesonCache proverCache = do
  trackers <- newIORef ([] :: [Tracker])
  return
    VState
    { thesisMotivated = False
    , rewriteRules    = []
    , evaluations     = DisTree.empty
    , currentThesis   = Context Bot [] []
    , currentBranch   = []
    , currentContext  = []
    , mesonRules      = (DisTree.empty, DisTree.empty)
    , definitions     = initDefinitions
    , guards          = initGuards
    , skolemCounter   = 0
    , instructions    = []
    , trackers        = trackers
    , mesonCache      = mesonCache
    , proverCache     = proverCache
    }

type VerifyMonad = ReaderT VState CRM

justIO :: IO a -> VerifyMonad a
justIO m = lift $ CRM (\_ k -> m >>= k)

runVerifyMonad :: VState -> VerifyMonad a -> IO (Maybe a)
runVerifyMonad s m = runCRM (runReaderT m s) (return Nothing) (return . Just)


-- State management from inside the verification monad

readTrackers :: VerifyMonad [Tracker]
readTrackers = do
  r <- asks trackers
  justIO (readIORef r)

modifyTrackers :: ([Tracker] -> [Tracker]) -> VerifyMonad ()
modifyTrackers f = do
  r <- asks trackers
  justIO (modifyIORef r f)

getInstruction :: Param.T a -> VState -> a
getInstruction p = getInstr p . instructions

addInstruction :: Instr -> VState -> VState
addInstruction instr state =
  state { instructions = addInstr instr $ instructions state }

dropInstruction :: Drop -> VState -> VState
dropInstruction instr state =
  state { instructions = dropInstr instr $ instructions state }


-- Trackers

addToTimer :: Timer -> NominalDiffTime -> VerifyMonad ()
addToTimer timer time = modifyTrackers (Timer timer time : )

addToCounter :: Counter -> Int -> VerifyMonad ()
addToCounter counter increment = modifyTrackers (Counter counter increment : )

incrementCounter :: Counter -> VerifyMonad ()
incrementCounter counter = addToCounter counter 1

-- Time proof tasks.
timeWith :: Timer -> VerifyMonad a -> VerifyMonad a
timeWith timer task = do
  begin  <- justIO getCurrentTime
  result <- task
  end    <- justIO getCurrentTime
  addToTimer timer (diffUTCTime end begin)
  return result

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

showTimeDiff :: NominalDiffTime -> String
showTimeDiff t =
  if hours == 0
    then format minutes <> ":" <> format restSeconds <> "." <> format restCentis
    else format hours   <> ":" <> format restMinutes <> ":" <> format restSeconds
  where
    format n = if n < 10 then '0':show n else show n
    centiseconds = (truncate $ t * 100) :: Int
    (seconds, restCentis)  = divMod centiseconds 100
    (minutes, restSeconds) = divMod seconds 60
    (hours,   restMinutes) = divMod minutes 60


guardInstruction :: Param.T Bool -> VerifyMonad ()
guardInstruction p = asks (getInstruction p) >>= guard

whenInstruction :: Param.T Bool -> VerifyMonad () -> VerifyMonad ()
whenInstruction p action = asks (getInstruction p) >>= \b -> when b action


-- common messages

reasonLog :: BYTES a => Message.Kind -> Position.T -> a -> VerifyMonad ()
reasonLog kind pos = justIO . Message.outputReasoner kind pos

thesisLog :: BYTES a => Message.Kind -> Position.T -> Int -> a -> VerifyMonad ()
thesisLog kind pos indent msg =
  justIO (Message.outputThesis kind pos (Bytes.spaces (3 * indent) <> make_bytes msg))

simpLog :: BYTES a => Message.Kind -> Position.T -> a -> VerifyMonad ()
simpLog kind pos = justIO . Message.outputSimplifier kind pos

translateLog :: BYTES a => Message.Kind -> Position.T -> a -> VerifyMonad ()
translateLog kind pos = justIO . Message.outputTranslate kind pos



retrieveContext :: Position.T -> Set.Set Text -> VerifyMonad [Context]
retrieveContext pos names = do
  globalContext <- asks currentContext
  let (context, unfoundSections) = runState (retrieve globalContext) names

  unless (Set.null unfoundSections) $
    reasonLog Message.WARNING pos $
      "Could not find sections " <> unwords (map show $ Set.elems unfoundSections)
  return context
  where
    retrieve [] = return []
    retrieve (context:restContext) =
      let name = Context.name context in
        gets (Set.member name) >>= \p ->
          if p
          then modify (Set.delete name) >> fmap (context:) (retrieve restContext)
          else retrieve restContext




-- Definitions

initDefinitions :: Definitions
initDefinitions = Map.fromList [
  (EqualityId,  equality),
  (LessId,  less),
  (MapId, mapd),
  (FunctionId,  function),
  (ApplicationId,  mapApplication),
  (DomainId,  domain),
  (SetId,  set),
  (ClassId,  clss),
  (ElementId,  elementOf),
  (PairId, pair),
  (ObjectId, object) ]

v0, v1 :: Formula
v0 = mkVar $ VarHole "0"
v1 = mkVar $ VarHole "1"

signature_, definition :: [Formula] -> Formula -> Formula -> [Formula] -> [[Formula]] -> DefEntry
signature_ g f = DefEntry g f Signature
definition g f = DefEntry g f Definition


equality :: DefEntry
equality = signature_ [] Top (mkEquality v0 v1) [] []

less :: DefEntry
less = signature_ [] Top (mkLess v0 v1) [] []

set :: DefEntry
set = definition [] (mkClass v0 `And` mkObject v0) (mkSet v0) [mkSet ThisT] []

object :: DefEntry
object = signature_ [] Top (mkObject v0) [] []

clss :: DefEntry
clss = signature_ [] Top (mkClass v0) [] []

elementOf :: DefEntry
elementOf =
  signature_ [mkClass v1] Top (mkElem v0 v1) [mkObject v0] [[mkObject v0], [mkClass v1]]

function :: DefEntry
function =
  definition [] (mkMap v0 `And` mkObject v0) (mkFunction v0) [mkFunction ThisT] []

mapd :: DefEntry
mapd = signature_ [] Top (mkMap v0) [] []

domain :: DefEntry
domain = signature_ [mkMap v0] (mkClass ThisT) (mkDom v0) [mkClass ThisT] [[mkMap v0]]

pair :: DefEntry
pair =
  signature_ [mkObject v0, mkObject v1] (mkObject ThisT) (mkPair v0 v1) [mkObject ThisT] []

mapApplication :: DefEntry
mapApplication =
  signature_ [mkMap v0, mkElem v1 $ mkDom v0] Top
    (mkApp v0 v1) [mkObject ThisT] [[mkMap v0], [mkElem v1 $ mkDom v0]]


initGuards :: DisTree Bool
initGuards = foldr (`DisTree.insert` True) DisTree.empty [
  mkClass v1,
  mkMap v0,
  mkElem v1 $ mkDom v0]


-- retrieve definitional formula of a term
defForm :: Definitions -> Formula -> Maybe Formula
defForm definitions term = do
  def <- Map.lookup (trmId term) definitions
  guard $ isDefinition def
  sb <- match (defTerm def) term
  return $ sb $ defFormula def


-- retrieve definition of a symbol (monadic)
getDef :: Formula -> VerifyMonad DefEntry
getDef term = do
  defs <- asks definitions
  let mbDef = Map.lookup (trmId term) defs
  guard $ isJust mbDef
  return $ fromJust mbDef
