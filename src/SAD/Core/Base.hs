{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018)

Verifier state monad and common functions.
-}

{-# LANGUAGE PolymorphicComponents #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}


module SAD.Core.Base
  ( RState(..), initRState, CRM
  , readRState
  , modifyRState
  , justIO
  , reportBracketIO
  , (<|>)
  , runRM

  , retrieveContext
  , initVState
  , defForm
  , getDef

  , setFailed
  , ifFailed
  , setChecked

  , VState(..), VM

  , Tracker(..), Timer(..), Counter(..)
  , sumCounter
  , sumTimer
  , maximalTimer
  , showTimeDiff
  , timeWith

  , askInstructionInt, askInstructionBool, askInstructionText
  , addInstruction, dropInstruction
  , addToTimer, addToCounter, incrementCounter
  , guardInstruction, guardNotInstruction, whenInstruction

  , reasonLog, simpLog, thesisLog, translateLog
  ) where

import Control.Applicative (Alternative(..))
import Control.Monad.Reader
import Control.Monad.State
import Control.Exception (SomeException, try, throw)
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
import SAD.Data.Text.Block (Block, ProofText)
import SAD.Data.Text.Context (Context(Context), MRule(..))

import qualified SAD.Core.Message as Message
import qualified SAD.Data.Structures.DisTree as DT
import qualified SAD.Data.Text.Context as Context (name)

import qualified Isabelle.Bytes as Bytes
import qualified Isabelle.Markup as Markup
import qualified Isabelle.Position as Position
import Isabelle.Library (BYTES, make_bytes)



-- | Reasoner state
data RState = RState
  { trackers       :: [Tracker]
  , failed         :: Bool
  , alreadyChecked :: Bool
  } deriving (Eq, Ord, Show)

initRState :: RState
initRState = RState [] False False

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
  { runCRM :: forall a . IORef RState -> IO a -> (b -> IO a) -> IO a }

instance Functor CRM where
  fmap = liftM

instance Applicative CRM where
  pure = return
  (<*>) = ap

instance Monad CRM where
  return r  = CRM $ \ _ _ k -> k r
  m >>= n   = CRM $ \ s z k -> runCRM m s z (\ r -> runCRM (n r) s z k)

instance Alternative CRM where
  empty = mzero
  (<|>) = mplus

instance MonadPlus CRM where
  mzero     = CRM $ \ _ z _ -> z
  mplus m n = CRM $ \ s z k -> runCRM m s (runCRM n s z k) k


-- | @runCRM@ with defaults.
runRM :: CRM a -> IORef RState -> IO (Maybe a)
runRM m s = runCRM m s (return Nothing) (return . Just)

data VState = VState
  { thesisMotivated :: Bool
  , rewriteRules    :: [Rule]
  , evaluations     :: DT.DisTree Evaluation -- (low level) evaluation rules
  , currentThesis   :: Context
  , currentBranch   :: [Block] -- branch of the current block
  , currentContext  :: [Context]
  , mesonRules      :: (DT.DisTree MRule, DT.DisTree MRule)
  , definitions     :: Definitions
  , guards          :: Guards -- tracks which atomic formulas appear as guard
  , skolemCounter   :: Int
  , instructions    :: [Instr]
  , restProofText   :: [ProofText]
  }

initVState :: [ProofText] -> VState
initVState text = VState
  { thesisMotivated = False
  , rewriteRules    = []
  , evaluations     = DT.empty
  , currentThesis   = Context Bot [] []
  , currentBranch   = []
  , currentContext  = []
  , mesonRules      = (DT.empty, DT.empty)
  , definitions     = initDefinitions
  , guards          = initGuards
  , skolemCounter   = 0
  , instructions    = []
  , restProofText   = text
  }

type VM = ReaderT VState CRM

justRS :: VM (IORef RState)
justRS = lift $ CRM $ \ s _ k -> k s

justIO :: IO a -> VM a
justIO m = lift $ CRM $ \ _ _ k -> m >>= k


-- State management from inside the verification monad

readRState :: (RState -> a) -> VM a
readRState f = justRS >>= (justIO . fmap f . readIORef)

modifyRState :: (RState -> RState) -> VM ()
modifyRState f = justRS >>= (justIO . flip modifyIORef f)

askInstructionInt :: Limit -> Int -> VM Int
askInstructionInt instr _default =
  asks (askLimit instr _default . instructions)

askInstructionBool :: Flag -> Bool -> VM Bool
askInstructionBool instr _default =
  asks (askFlag instr _default . instructions)

askInstructionText :: Argument -> Text -> VM Text
askInstructionText instr _default =
  asks (askArgument instr _default . instructions)

addInstruction :: Instr -> VM a -> VM a
addInstruction instr =
  local $ \vs -> vs { instructions = instr : instructions vs }

dropInstruction :: Drop -> VM a -> VM a
dropInstruction instr =
  local $ \vs -> vs { instructions = dropInstr instr $ instructions vs }


-- Markup reports (with exception handling)

reportBracketIO :: Position.T -> IO a -> IO a
reportBracketIO pos body = do
  Message.report pos Markup.running
  (res :: Either SomeException a) <- try body
  case res of
    Left e -> do
      Message.report pos Markup.failed
      Message.report pos Markup.finished
      throw e
    Right x -> do
      Message.report pos Markup.finished
      return x


-- Trackers

addToTimer :: Timer -> NominalDiffTime -> VM ()
addToTimer timer time =
  modifyRState $ \rs -> rs{trackers = Timer timer time : trackers rs}

addToCounter :: Counter -> Int -> VM ()
addToCounter counter increment =
  modifyRState $ \rs -> rs{trackers = Counter counter increment : trackers rs}

incrementCounter :: Counter -> VM ()
incrementCounter counter = addToCounter counter 1

-- Time proof tasks.
timeWith :: Timer -> VM a -> VM a
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


guardInstruction :: Flag -> Bool -> VM ()
guardInstruction instr _default =
  askInstructionBool instr _default >>= guard

guardNotInstruction :: Flag -> Bool -> VM ()
guardNotInstruction instr _default =
  askInstructionBool instr _default >>= guard . not

whenInstruction :: Flag -> Bool -> VM () -> VM ()
whenInstruction instr _default action =
  askInstructionBool instr _default >>= \b -> when b action

-- explicit failure management

setFailed :: VM ()
setFailed = modifyRState (\st -> st {failed = True})

ifFailed :: VM a -> VM a -> VM a
ifFailed alt1 alt2 = do
  failed <- readRState failed
  if failed then alt1 else alt2

-- local checking support

setChecked :: Bool -> VM ()
setChecked b = modifyRState (\st -> st {alreadyChecked = b})


-- common messages

reasonLog :: BYTES a => Message.Kind -> Position.T -> a -> VM ()
reasonLog kind pos = justIO . Message.outputReasoner kind pos

thesisLog :: BYTES a => Message.Kind -> Position.T -> Int -> a -> VM ()
thesisLog kind pos indent msg =
  justIO (Message.outputThesis kind pos (Bytes.spaces (3 * indent) <> make_bytes msg))

simpLog :: BYTES a => Message.Kind -> Position.T -> a -> VM ()
simpLog kind pos = justIO . Message.outputSimplifier kind pos

translateLog :: BYTES a => Message.Kind -> Position.T -> a -> VM ()
translateLog kind pos = justIO . Message.outputTranslate kind pos



retrieveContext :: Position.T -> Set.Set Text -> VM [Context]
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


initGuards :: DT.DisTree Bool
initGuards = foldr (`DT.insert` True) DT.empty [
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
getDef :: Formula -> VM DefEntry
getDef term = do
  defs <- asks definitions
  let mbDef = Map.lookup (trmId term) defs
  guard $ isJust mbDef
  return $ fromJust mbDef
