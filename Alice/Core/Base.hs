{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018)

Verifier state monad and common functions.
-}

module Alice.Core.Base where

import Control.Monad
import Data.IORef
import Data.List
import Data.Time
import Control.Applicative
import qualified Data.IntMap.Strict as IM
import Data.Maybe
import qualified Data.Map as M
import qualified Data.Set as Set
import Control.Monad.State
import Control.Monad.Reader

import Alice.Data.Base
import Alice.Data.Kit
import Alice.Data.Instr
import Alice.Data.Text
import Alice.Export.Base
import Alice.Data.Formula
import qualified Alice.Data.DisTree as DT

import Debug.Trace

-- Reasoner state

data RState = RState {  rsInst :: [Instr],
                        rsCntr :: [Count],
                        rsPrdb :: [Prover] }


{- the global proof state containing:
  ~ All definitions so far
  ~ positive and negative MESON rules for ontological checking
  ~ groupings of theorem identifiers
  ~ the global context
  ~ a counter for the identifier for skolem constants
-}

data GState = GL {gsDefs :: Definitions,
                  gsGlps :: DT.DisTree MRule,
                  gsGlng :: DT.DisTree MRule,
                  gsGrup :: M.Map String (Set.Set String),
                  gsCtxt :: [Context],
                  gsSklm :: Int}



-- All of these counters are for gathering statistics to print out later

data Count  = CntrT CntrT NominalDiffTime
            | CntrI CntrI Int

data CntrT  = CTprov -- total proof time
            | CTprvy -- succesful prove time
            | CTsimp -- total simplifier time
            deriving Eq

data CntrI  = CIsect -- number of sections
            | CIgoal -- number of goals
            | CIfail -- number of failed proof tasks
            | CIsubt -- number of subtasks (not used at the moment)
            | CIprvy -- number off successful proof tasks
            | CIsymb -- number of symbols
            | CIchkt -- number of trivial checks
            | CIchkh -- number of hard checks
            | CIchky -- number of succesful checks
            | CIunfl -- number of unfoldings
            | CIeqtn -- number of equations
            | CIeqfl -- number of failed equations
            deriving Eq


-- CPS IO Maybe monad

type CRMC a b = IORef RState -> IO a -> (b -> IO a) -> IO a
newtype CRM b = CRM { runCRM :: forall a . CRMC a b }

instance Monad CRM where
  return r  = CRM $ \ _ _ k -> k r
  m >>= n   = CRM $ \ s z k -> runCRM m s z (\ r -> runCRM (n r) s z k)

instance MonadPlus CRM where
  mzero     = CRM $ \ _ z _ -> z
  mplus m n = CRM $ \ s z k -> runCRM m s (runCRM n s z k) k




-- Standard declaration to prevent compiler errors

instance Functor CRM where
    fmap = liftM

instance Applicative CRM where
    pure = return
    (<*>) = ap

instance Alternative CRM where
    empty = mzero
    (<|>) = mplus
---------------------------

type RM = CRM
runRM :: RM a -> IORef RState -> IO (Maybe a)
runRM m s = runCRM m s (return Nothing) (return . Just)

infixl 0 <>
(<>) :: (MonadPlus m) => m a -> m a -> m a
(<>) = mplus


data VState = VS { vsMotv :: Bool,       -- if the current thesis is motivated
                   vsRuls :: [Rule],     -- rewrite rules
                   vsEval :: DT.DisTree Eval, -- (low level) evaluation rules
                   vsThes :: Context,    -- current thesis
                   vsBran :: [Block],    -- branch of the current block
                   vsCtxt :: [Context],  -- context
                   vsText :: [Text] }    -- the remaining text}



type GM = StateT GState CRM
type VM = ReaderT VState GM

justRS :: VM (IORef RState)
justRS      = lift $ lift $ CRM $ \ s _ k -> k s


justIO :: IO a -> VM a
justIO m    = lift $ lift $ CRM $ \ _ _ k -> m >>= k

-- State management from inside the verification monad

getRS       = justRS >>= (justIO . readIORef)          -- retrieve state
askRS f     = justRS >>= (justIO . fmap f . readIORef) -- retrieve some component of the state
setRS r     = justRS >>= (justIO . flip writeIORef r)  -- set state
updateRS f  = justRS >>= (justIO . flip modifyIORef f) -- update state

askRSII i d = liftM (askII i d) (askRS rsInst) -- retrieve instructions
askRSIB i d = liftM (askIB i d) (askRS rsInst)
askRSIS i d = liftM (askIS i d) (askRS rsInst)

addRSIn ins = updateRS $ \ rs -> rs { rsInst = ins : rsInst rs } -- add/drop/modify instructions
drpRSIn ind = updateRS $ \ rs -> rs { rsInst = dropI ind $ rsInst rs }
addRSTI c i = updateRS $ \ rs -> rs { rsCntr = CntrT c i : rsCntr rs }
addRSCI c i = updateRS $ \ rs -> rs { rsCntr = CntrI c i : rsCntr rs }
incRSCI c   = addRSCI c 1

timer c a   = do  b <- justIO $ getCurrentTime -- time proof tasks
                  r <- a
                  e <- justIO $ getCurrentTime
                  addRSTI c $ diffUTCTime e b
                  return r

guardIB i d     = askRSIB i d >>= guard -- manage conditions set by instructions
guardNotIB i d  = askRSIB i d >>= guard . not
whenIB i d a    = askRSIB i d >>= \ b -> when b a
unlessIB i d a  = askRSIB i d >>= \ b -> unless b a


-- Counter management

fetchCI c cs  = [ i | CntrI d i <- cs, c == d ]
fetchCT c cs  = [ i | CntrT d i <- cs, c == d ]

cumulCI c t = foldr (+) t . fetchCI c
cumulCT c t = foldr addUTCTime t . fetchCT c
maximCT c   = foldr max 0 . fetchCT c

showTimeDiff t
  | th == 0 = dsh mn ++ ':' : dsh ss ++ '.' : dsh cs
  | True    = dsh th ++ ':' : dsh mn ++ ':' : dsh ss
  where
    dsh n   = if n < 10 then '0':show n else show n
    tc      = truncate $ t * 100
    (ts,cs) = divMod tc 100
    (tm,ss) = divMod ts 60
    (th,mn) = divMod tm 60


-- IO management (print functions for the log)

printRM :: Show a => a -> VM ()

putStrLnRM  = justIO . putStrLn
putStrRM    = justIO . putStr
printRM     = justIO . print

rlog0 tx = putStrLnRM $ "[Reason] " ++ tx

rlog bl tx = do tfn <- askRSIS ISfile ""
                rlog0 $ blLabl tfn bl ++ tx

tlog0 tx = putStrLnRM $ "[Thesis] " ++ tx

tlog n bl tx = do tfn <- askRSIS ISfile ""
                  tlog0 $ blLabl tfn bl ++take (3*n) (repeat ' ')++ tx

blLabl tf bl =
  let fl = blFile bl
  in  (if fl == tf then "" else fl) ++ fill (show (blLnCl bl)) ++ ": "
  where
    fill s =
      let l = length s
      in  if l < 9 then s ++ take (9 - l) (repeat ' ') else s



-- GlobalState management

askGS    = lift . gets
updateGS = lift . modify

getGlC :: VM (DT.DisTree MRule, DT.DisTree MRule)
getGlC = liftM2 (,) (askGS gsGlps) (askGS gsGlng) -- retrieve MESON rules
                                                  -- for onto checking
insertGl :: [MRule] -> VM () -- insert new MESON rules into the global context
insertGl rls = updateGS (add rls)
  where
    add [] gs = gs
    add (rl@(MR asm conc):rls) gs | isNot conc = add rls $ gs {gsGlng = DT.insert (ltNeg conc) rl (gsGlng gs) }
                                  | otherwise  = add rls $ gs {gsGlps = DT.insert conc rl (gsGlps gs) }

    ltNeg (Not f) = f
    ltNeg f = f

initGS = GL defs DT.empty DT.empty M.empty [] 0 --initial global state

addGlCn cn = updateGS (\st -> st {gsCtxt = cn : gsCtxt st}) -- add global context

retrieveCn nms = -- retrieve the context with the identifiers in nms
  do gCt <- askGS gsCtxt; let (nct, st) = runState (retrieve gCt) nms
     unless (Set.null st) $ warn st; return nct -- warn a user if some sections could not be found
  where
    warn st = rlog0 $ "Warning: Could not find sections " ++ unwords (map show $ Set.elems st)



class Named a where
  name :: a -> String

instance Named Context where name = cnName
instance Named Rule    where name = rlLabl

retrieve [] = return []
retrieve (c:cnt) = ifM (gets $ Set.member nm) (del >> liftM (c:) (retrieve cnt)) (retrieve cnt) -- if a name matches, delete
  where                                                                             -- it from the set
    nm = name c
    del = modify $ Set.delete nm

retrieveMN _ [] = return []
retrieveMN s (c:cnt) = if Set.member nm s then del >> liftM (c:) (retrieveMN s cnt) else retrieveMN s cnt
  where
    nm = name c
    del = modify $ Set.delete nm



-- Definition management

-- initial definitions
defs = IM.fromList [(-1, eq),(-2, less), (-4, fun),(-5,app),
                    (-6,dom),(-7,set),(-8,elmnt), (-10, pair)]

  -- equality
eq = DE [] Top Signature (zEqu (zVar "?0") (zVar "?1")) [] []
  -- well-founded ordering
less = DE [] Top Signature (zLess (zVar "?0") (zVar "?1")) [] []
  -- set
set = DE [] Top Signature (zSet $ zVar "?0") [] []
  -- element
elmnt = DE [zSet $ zVar "?1"] Top Signature (zElem (zVar "?0") (zVar "?1")) [] [[zSet $ zVar "?1"]]
  -- function
fun = DE [] Top Signature (zFun $ zVar "?0") [] []
  -- function application
app = DE [zFun $ zVar "?0", zElem (zVar $ "?1") $ zDom $ zVar "?0"] Top Signature (zApp (zVar "?0") (zVar "?1")) [] [[zFun $ zVar "?0"],[zElem (zVar $ "?1") $ zDom $ zVar "?0"]]
 -- domain of a function
dom = DE [zFun $ zVar "?0"] (zSet ThisT) Signature (zDom $ zVar "?0") [zSet ThisT] [[zFun $ zVar "?0"]]

pair = DE [] Top Signature (zPair (zVar "?0") (zVar "?1")) [] []


defForm :: IM.IntMap DefEntry -> Formula -> Maybe Formula -- retrieve the definitional formula of a term
defForm dfs t = do df <- IM.lookup (trId t) dfs           -- return Nothing in case of a SigExt
                   guard $ dfSign df
                   sb <- match (dfTerm df) t
                   return $ sb $ dfForm df


getDef :: Formula -> VM DefEntry -- retrieve the definition of a symbol
getDef t = do defs <- askGS gsDefs
              let lu = IM.lookup (trId t) defs
              guard $ isJust lu
              return $ fromJust lu


printDefs = askGS gsDefs >>= rlog0 . unlines . map show . IM.assocs
  -- print all definitions to the screen (only for debugging)

-- groupings

-- get the section identifiers grouped by a group identifier
getLink :: [String] -> VM (Set.Set String)
getLink ln = do
  grps <- askGS gsGrup
  return $ Set.unions $
    map (\l -> M.findWithDefault (Set.singleton l) l grps) ln

addGroup [] = return () -- add a group identifier
addGroup [nm] = rlog0 $ "Warning: empty group: " ++ show nm
addGroup (nm:ps) =
  getLink ps >>=
    \ln -> updateGS (\st -> st {gsGrup = M.insert nm ln $ gsGrup st})
