{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018)

Verifier state monad and common functions.
-}

{-# LANGUAGE PolymorphicComponents #-}
{-# LANGUAGE FlexibleContexts #-}


module Alice.Core.Base (
  RState (..), RM,
  askRS, updateRS,
  justIO,
  (<|>),
  runRM,

  GState (..), GM,
  askGlobalState, updateGlobalState,
  addGlobalContext, insertMRule,
  retrieveContext,
  initialGlobalState,
  defForm, getDef, getLink, addGroup,

  VState (..), VM,

  Counter (..), TimeCounter (..), IntCounter (..),
  accumulateIntCounter, accumulateTimeCounter, maximalTimeCounter,
  showTimeDiff,
  timer,

  askInstructionInt, askInstructionBin, askInstructionString,
  addInstruction, dropInstruction,
  addTimeCounter, addIntCounter, incrementIntCounter,
  guardInstruction, guardNotInstruction, whenInstruction,

  trimLine, MessageKind (..), putMessage,
  reasonerLog, simpLog, simpLog0, thesisLog, thesisLog0,
  blockLabel
) where

import Control.Monad
import Data.IORef
import Data.List
import Data.Time
import qualified Control.Applicative as App
import qualified Data.IntMap.Strict as IM
import Data.Maybe
import qualified Data.Map as M
import qualified Data.Set as Set
import Control.Monad.State
import Control.Monad.Reader

import Alice.Data.Formula
import Alice.Data.Instr
import Alice.Data.Text.Block (Block(..), Text, file)
import Alice.Data.Text.Context
import Alice.Data.Definition
import Alice.Data.Rules (Rule)
import Alice.Data.Evaluation
import Alice.Export.Base
import qualified Alice.Data.Structures.DisTree as DT
import Alice.Parser.Position

import Debug.Trace

-- Reasoner state

data RState = RState {
  instructions :: [Instr],
  counters     :: [Counter],
  provers      :: [Prover] }


{- the global proof state containing:
  ~ All definitions so far
  ~ positive and negative MESON rules for ontological checking
  ~ groupings of theorem identifiers
  ~ the global context
  ~ a counter for the identifier for skolem constants
-}

data GState = GL {
  definitions      :: Definitions,
  mesonPositives   :: DT.DisTree MRule,
  mesonNegatives   :: DT.DisTree MRule,
  identifierGroups :: M.Map String (Set.Set String),
  globalContext    :: [Context],
  skolemCounter    :: Int }



-- All of these counters are for gathering statistics to print out later

data Counter  =
    TimeCounter TimeCounter NominalDiffTime
  | IntCounter IntCounter Int

data TimeCounter  =
    ProofTime
  | SuccessTime  -- succesful prove time
  | SimplifyTime
  deriving Eq

data IntCounter  =
    Sections
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
  deriving Eq


-- CPS IO Maybe monad

type CRMC a b = IORef RState -> IO a -> (b -> IO a) -> IO a
newtype CRM b = CRM { runCRM :: forall a . CRMC a b }

instance Functor CRM where
  fmap = liftM

instance App.Applicative CRM where
  pure = return
  (<*>) = ap

instance Monad CRM where
  return r  = CRM $ \ _ _ k -> k r
  m >>= n   = CRM $ \ s z k -> runCRM m s z (\ r -> runCRM (n r) s z k)

instance App.Alternative CRM where
  empty = mzero
  (<|>) = mplus

instance MonadPlus CRM where
  mzero     = CRM $ \ _ z _ -> z
  mplus m n = CRM $ \ s z k -> runCRM m s (runCRM n s z k) k





type RM = CRM
runRM :: RM a -> IORef RState -> IO (Maybe a)
runRM m s = runCRM m s (return Nothing) (return . Just)

infixl 0 <|>
{-# INLINE (<|>) #-}
(<|>) :: (MonadPlus m) => m a -> m a -> m a
(<|>) = mplus


data VState = VS {
  thesisMotivated :: Bool,
  rewriteRules    :: [Rule],
  evaluations     :: DT.DisTree Eval, -- (low level) evaluation rules
  currentThesis   :: Context,
  currentBranch   :: [Block],         -- branch of the current block
  currentContext  :: [Context],
  restText        :: [Text] }



type GM = StateT GState CRM
type VM = ReaderT VState GM

justRS :: VM (IORef RState)
justRS = lift $ lift $ CRM $ \ s _ k -> k s


justIO :: IO a -> VM a
justIO m = lift $ lift $ CRM $ \ _ _ k -> m >>= k

-- State management from inside the verification monad

askRS f     = justRS >>= (justIO . fmap f . readIORef)
updateRS f  = justRS >>= (justIO . flip modifyIORef f)

askInstructionInt    instr _default =
  fmap (askII instr _default) (askRS instructions)
askInstructionBin    instr _default =
  fmap (askIB instr _default) (askRS instructions)
askInstructionString instr _default =
  fmap (askIS instr _default) (askRS instructions)

addInstruction  instr =
  updateRS $ \rs -> rs { instructions = instr : instructions rs }
dropInstruction instr =
  updateRS $ \rs -> rs { instructions = dropI instr $ instructions rs }
addTimeCounter counter time =
  updateRS $ \rs -> rs { counters = TimeCounter counter time : counters rs }
addIntCounter  counter time =
  updateRS $ \rs -> rs { counters = IntCounter  counter time : counters rs }
incrementIntCounter counter = addIntCounter counter 1

-- time proof tasks
timer counter task = do
  begin  <- justIO $ getCurrentTime
  result <- task
  end    <- justIO $ getCurrentTime
  addTimeCounter counter $ diffUTCTime end begin
  return result

guardInstruction instr _default =
  askInstructionBin instr _default >>= guard
guardNotInstruction instr _default =
  askInstructionBin instr _default >>= guard . not
whenInstruction instr _default action =
  askInstructionBin instr _default >>= \ b -> when b action

-- Counter management

fetchIntCounter  counterList counter =
  [ value | IntCounter  kind value <- counterList, counter == kind ]
fetchTimeCounter counterList counter =
  [ value | TimeCounter kind value <- counterList, counter == kind ]

accumulateIntCounter  counterList startValue =
  foldr (+) startValue . fetchIntCounter counterList
accumulateTimeCounter counterList startValue =
  foldr addUTCTime startValue . fetchTimeCounter counterList
maximalTimeCounter counterList = foldr max 0 . fetchTimeCounter counterList

showTimeDiff t
  | hours == 0 =
      format minutes ++ ':' : format restSeconds ++ '.' : format restCentis
  | True    =
      format hours   ++ ':' : format restMinutes ++ ':' : format restSeconds
  where
    format n = if n < 10 then '0':show n else show n
    centiseconds = truncate $ t * 100
    (seconds, restCentis)  = divMod centiseconds 100
    (minutes, restSeconds) = divMod seconds 60
    (hours  , restMinutes) = divMod minutes 60


-- IO management (print functions for the log)

trimLine :: String -> String
trimLine line =
  case reverse line of
    '\n' : '\r' : rest -> reverse rest
    '\n' : rest -> reverse rest
    _ -> line

data MessageKind = Normal | Warning | Error
instance Show MessageKind where
  show Normal = ""
  show Warning = "Warning"
  show Error = "Error"

makeMessage :: String -> MessageKind -> SourcePos -> String -> String
makeMessage origin kind pos msg =
  (if null origin then "" else "[" ++ origin ++ "] ") ++
  (case show kind of "" -> "" ; s -> s ++ ": ") ++
  (case show pos of "" -> ""; s -> s ++ "\n") ++ msg

putMessage :: String -> MessageKind -> SourcePos -> String -> VM ()
putMessage channel kind pos msg =
  justIO $ putStrLn $ makeMessage channel kind pos msg

reasonerLog :: MessageKind -> SourcePos -> String -> VM ()
reasonerLog = putMessage "Reason"

thesisLog0 :: MessageKind -> SourcePos -> String -> VM ()
thesisLog0 = putMessage "Thesis"

thesisLog kind indent block msg = do
  fileName <- askInstructionString ISfile ""
  thesisLog0 kind noPos $
    blockLabel fileName block ++ replicate (3 * indent) ' ' ++ msg

simpLog0 :: MessageKind -> SourcePos -> String -> VM ()
simpLog0 = putMessage "Simp"

simpLog kind context msg = do
  fileName <- askInstructionString ISfile ""
  simpLog0 kind noPos $ blockLabel fileName (cnHead context) ++ msg

blockLabel fileName block =
  let blockFile = file block; blockPos = position block
      line = sourceLine blockPos; column = sourceLine blockPos
  in  (if fileName == blockFile then "" else blockFile)
        ++ format (show (line, column)) ++ ": "
  where
    format string =
      let l = length string
      in  if l < 9 then string ++ replicate (9 - l) ' ' else string



-- GlobalState management

askGlobalState    = lift . gets
updateGlobalState = lift . modify

insertMRule :: [MRule] -> VM ()
insertMRule rules = updateGlobalState (add rules)
  where
    add [] globalState = globalState
    add (rule@(MR _ conclusion):rules) gs
      | isNot conclusion =
          let negatives     = mesonNegatives gs
              negConclusion = ltNeg conclusion
          in  add rules $
                gs {mesonNegatives = DT.insert negConclusion rule negatives}
      | otherwise  =
          let positives = mesonPositives gs
          in  add rules $
                gs {mesonPositives = DT.insert conclusion rule positives}

initialGlobalState = GL initialDefinitions DT.empty DT.empty M.empty [] 0

addGlobalContext cn =
  updateGlobalState (\st -> st {globalContext = cn : globalContext st})



retrieveContext names = do
  globalContext <- askGlobalState globalContext
  let (context, unfoundSections) = runState (retrieve globalContext) names
  -- warn a user if some sections could not be found
  unless (Set.null unfoundSections) $ warn unfoundSections
  return context
  where
    warn unfoundSections =
      reasonerLog Warning noPos $
        "Could not find sections " ++ unwords (map show $ Set.elems unfoundSections)
    retrieve [] = return []
    retrieve (context:restContext) = let name = cnName context in
      gets (Set.member name) >>= \p -> if p
      then modify (Set.delete name) >> fmap (context:) (retrieve restContext)
      else retrieve restContext




-- Definition management

-- initial definitions
initialDefinitions = IM.fromList [
  (-1,  equality),
  (-2,  less),
  (-4,  function),
  (-5,  functionApplication),
  (-6,  domain),
  (-7,  set),
  (-8,  elementOf),
  (-10, pair) ]

equality  = DE [] Top Signature (zEqu (zVar "?0") (zVar "?1")) [] []
less      = DE [] Top Signature (zLess (zVar "?0") (zVar "?1")) [] []
set       = DE [] Top Signature (zSet $ zVar "?0") [] []
elementOf = DE [zSet $ zVar "?1"] Top Signature
  (zElem (zVar "?0") (zVar "?1")) [] [[zSet $ zVar "?1"]]
function  = DE [] Top Signature (zFun $ zVar "?0") [] []
domain    = DE [zFun $ zVar "?0"] (zSet ThisT) Signature
  (zDom $ zVar "?0") [zSet ThisT] [[zFun $ zVar "?0"]]
pair      = DE [] Top Signature (zPair (zVar "?0") (zVar "?1")) [] []
functionApplication =
  DE [zFun $ zVar "?0", zElem (zVar $ "?1") $ zDom $ zVar "?0"] Top Signature
    (zApp (zVar "?0") (zVar "?1")) []
    [[zFun $ zVar "?0"],[zElem (zVar $ "?1") $ zDom $ zVar "?0"]]


-- retrieve definitional formula of a term
defForm :: IM.IntMap DefEntry -> Formula -> Maybe Formula
defForm definitions term = do
  def <- IM.lookup (trId term) definitions
  guard $ dfSign def
  sb <- match (dfTerm def) term
  return $ sb $ dfForm def


-- retrieve definition of a symbol (monadic)
getDef :: Formula -> VM DefEntry
getDef term = do
  defs <- askGlobalState definitions
  let mbDef = IM.lookup (trId term) defs
  guard $ isJust mbDef
  return $ fromJust mbDef

-- groupings

-- get the section identifiers grouped by a group identifier
getLink :: [String] -> VM (Set.Set String)
getLink link = do
  groups <- askGlobalState identifierGroups
  return $ Set.unions $
    map (\l -> M.findWithDefault (Set.singleton l) l groups) link

-- add group identifier
addGroup :: [String] -> VM ()
addGroup [] = return ()
addGroup [name] = reasonerLog Warning noPos $ "empty group: " ++ show name
addGroup (name:identifiers) =
  getLink identifiers >>= \link -> updateGlobalState
    (\st -> st {identifierGroups = M.insert name link $ identifierGroups st})
