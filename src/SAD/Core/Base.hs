{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018)

Verifier state monad and common functions.
-}

{-# LANGUAGE PolymorphicComponents #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}


module SAD.Core.Base
  ( RState(..), CRM
  , askRS
  , updateRS
  , justIO
  , (<|>)
  , runRM

  , retrieveContext
  , makeInitialVState
  , defForm
  , getDef

  , setFailed
  , ifAskFailed
  , unsetChecked
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
import Data.IORef
import Data.Maybe (isJust, fromJust)
import Data.Text.Lazy (Text)
import Data.Time (NominalDiffTime, getCurrentTime, diffUTCTime)

import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.Text.Lazy as Text

import SAD.Core.SourcePos
import SAD.Data.Definition
import SAD.Data.Formula
import SAD.Data.Instr
import SAD.Data.Rules (Rule)
import SAD.Data.Text.Block (Block, ProofText)
import SAD.Data.Text.Context (Context(Context))
import SAD.Export.Base

import qualified SAD.Core.Message as Message
import qualified SAD.Data.Structures.DisTree as DT
import qualified SAD.Data.Text.Context as Context (name)



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

data VState = VS
  { thesisMotivated :: Bool
  , rewriteRules    :: [Rule]
  , evaluations     :: DT.DisTree Evaluation -- (low level) evaluation rules
  , currentThesis   :: Context
  , currentBranch   :: [Block] -- branch of the current block
  , currentContext  :: [Context]
  , definitions     :: Definitions
  , guards          :: Guards -- tracks which atomic formulas appear as guard
  , instructions    :: [Instr]
  , provers         :: [Prover]
  , restProofText   :: [ProofText]
  }

makeInitialVState :: [Prover] -> [ProofText] -> VState
makeInitialVState provers text = VS
  { thesisMotivated = False
  , rewriteRules    = []
  , evaluations     = DT.empty
  , currentThesis   = Context Bot []
  , currentBranch   = []
  , currentContext  = []
  , definitions     = initialDefinitions
  , guards          = initialGuards
  , instructions    = []
  , provers         = provers
  , restProofText   = text
  }

type VM = ReaderT VState CRM

justRS :: VM (IORef RState)
justRS = lift $ CRM $ \ s _ k -> k s


justIO :: IO a -> VM a
justIO m = lift $ CRM $ \ _ _ k -> m >>= k

-- State management from inside the verification monad

askRS :: (RState -> a) -> VM a
askRS f = justRS >>= (justIO . fmap f . readIORef)

updateRS :: (RState -> RState) -> VM ()
updateRS f = justRS >>= (justIO . flip modifyIORef f)

askInstructionInt :: Limit -> Int -> VM Int
askInstructionInt instr _default =
  fmap (askLimit instr _default) $ asks instructions

askInstructionBool :: Flag -> Bool -> VM Bool
askInstructionBool instr _default =
  fmap (askFlag instr _default) $ asks instructions

askInstructionText :: Argument -> Text -> VM Text
askInstructionText instr _default =
  fmap (askArgument instr _default) $ asks instructions

addInstruction :: Instr -> VM a -> VM a
addInstruction instr =
  local $ \vs -> vs { instructions = instr : instructions vs }

dropInstruction :: Drop -> VM a -> VM a
dropInstruction instr =
  local $ \vs -> vs { instructions = dropInstr instr $ instructions vs }


-- Trackers

addToTimer :: Timer -> NominalDiffTime -> VM ()
addToTimer timer time =
  updateRS $ \rs -> rs{trackers = Timer timer time : trackers rs}

addToCounter :: Counter -> Int -> VM ()
addToCounter counter increment =
  updateRS $ \rs -> rs{trackers = Counter counter increment : trackers rs}

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
setFailed = updateRS (\st -> st {failed = True})

ifAskFailed :: VM a -> VM a -> VM a
ifAskFailed alt1 alt2 = do
  failed <- askRS failed
  if failed then alt1 else alt2

-- local checking support

setChecked, unsetChecked :: VM ()
setChecked = updateRS (\st -> st {alreadyChecked = True})
unsetChecked = updateRS (\st -> st {alreadyChecked = False})


-- common messages

reasonLog :: Message.Kind -> SourcePos -> Text -> VM ()
reasonLog kind pos = justIO . Message.outputReasoner kind pos . Text.unpack

thesisLog :: Message.Kind -> SourcePos -> Int -> Text -> VM ()
thesisLog kind pos indent msg =
  justIO (Message.outputThesis kind pos (replicate (3 * indent) ' ' ++ Text.unpack msg))

simpLog :: Message.Kind -> SourcePos -> Text -> VM ()
simpLog kind pos = justIO . Message.outputSimplifier kind pos . Text.unpack

translateLog :: Message.Kind -> SourcePos -> Text -> VM ()
translateLog kind pos = justIO . Message.outputTranslate kind pos . Text.unpack



retrieveContext :: Set.Set Text -> VM [Context]
retrieveContext names = do
  globalContext <- asks currentContext
  let (context, unfoundSections) = runState (retrieve globalContext) names

  unless (Set.null unfoundSections) $
    reasonLog Message.WARNING noSourcePos $
      "Could not find sections " <> Text.unwords (map (Text.pack . show) $ Set.elems unfoundSections)
  return context
  where
    retrieve [] = return []
    retrieve (context:restContext) =
      let name = Context.name context in
        gets (Set.member name) >>= \p ->
          if p
          then modify (Set.delete name) >> fmap (context:) (retrieve restContext)
          else retrieve restContext




-- Definition management

-- initial definitions
initialDefinitions :: Definitions
initialDefinitions = Map.fromList [
  (EqualityId,  equality),
  (LessId,  less),
  (FunctionId,  function),
  (ApplicationId,  functionApplication),
  (DomainId,  domain),
  (SetId,  set),
  (ElementId,  elementOf),
  (PairId, pair) ]

hole0, hole1 :: VariableName
hole0 = VarHole "0"
hole1 = VarHole "1"

equality :: DefEntry
equality  = DE [] Top Signature (mkEquality (mkVar hole0) (mkVar hole1)) [] []

less :: DefEntry
less = DE [] Top Signature (mkLess (mkVar hole0) (mkVar hole1)) [] []

set :: DefEntry
set = DE [] Top Signature (mkSet $ mkVar hole0) [] []

elementOf :: DefEntry
elementOf = DE [mkSet $ mkVar hole1] Top Signature
  (mkElem (mkVar hole0) (mkVar hole1)) [] [[mkSet $ mkVar hole1]]

function :: DefEntry
function  = DE [] Top Signature (mkFun $ mkVar hole0) [] []

domain :: DefEntry
domain = DE [mkFun $ mkVar hole0] (mkSet ThisT) Signature
  (mkDom $ mkVar hole0) [mkSet ThisT] [[mkFun $ mkVar hole0]]

pair :: DefEntry
pair = DE [] Top Signature (mkPair (mkVar hole0) (mkVar hole1)) [] []

functionApplication :: DefEntry
functionApplication =
  DE [mkFun $ mkVar hole0, mkElem (mkVar $ hole1) $ mkDom $ mkVar hole0] Top Signature
    (mkApp (mkVar hole0) (mkVar hole1)) []
    [[mkFun $ mkVar hole0],[mkElem (mkVar $ hole1) $ mkDom $ mkVar hole0]]


initialGuards :: DT.DisTree Bool
initialGuards = foldr (\f -> DT.insert f True) (DT.empty) [
  mkSet $ mkVar hole1,
  mkFun $ mkVar hole0,
  mkElem (mkVar $ hole1) $ mkDom $ mkVar hole0]

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
