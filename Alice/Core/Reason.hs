{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018)

Reasoning methods and export to an external prover.
-}

module Alice.Core.Reason where

import Control.Monad
import Data.Char
import Data.List
import Data.Maybe
import System.Timeout
import Control.Exception
import Data.Monoid (Sum, getSum)
import qualified Data.IntMap.Strict as IM
import qualified Control.Monad.Writer as W
import qualified Data.Set as Set
import qualified Data.Map as M
import Control.Monad.State
import Control.Monad.Reader

import Alice.Data.Base
import Alice.Core.Base
import Alice.Data.Formula
import Alice.Data.Kit
import Alice.Data.Instr
import Alice.Data.Text
import Alice.Export.Prover
import Alice.ForTheL.Base
import Alice.Prove.MESON
import qualified Alice.Data.DisTree as DT

import Debug.Trace


-- *Fix Me* I deleted the splitG and replaced its use by singleton lists. This should be done more adequately.

-- Reasoner

reason tc = local (\st -> st {vsThes = tc}) prvThs
withGoal fn g   = local (\st -> st { vsThes = setForm (vsThes st) g}) fn
withCtxt fn cnt = local (\st -> st { vsCtxt = cnt }) fn

thesis = asks vsThes; context = asks vsCtxt


prvThs :: VM ()
prvThs = do  n <- askRSII IIdpth 3 ; guard $ n > 0       -- query whether the user has given a reasoning depth
             filt_context $ (splitG >>= goalseq n 0)-- split goals and start reasoning

goalseq :: Int -> Int -> [Formula] -> VM ()
goalseq n m (f:fs) = do  (trv <|> lnc <|> dlp) `withGoal` rfr
                         goalseq n m fs
  where
    rfr = reduce f           -- reduce f in view of evidences

    trv = sbg >> guard (isTop rfr)>> when (not . isTop $ f) (incRSCI CIsubt)  -- check if f is trivially true
    lnc = launch m                                                            -- launch the prover with the given context and the reduced goal formula

    dlp | n == 1  = rde >> mzero
        | True    = do  tsk <- unfold            -- unfold definitions, while unfolding the goal formula must be treated with opposite polarities as the rest. Hence the not
                        let Context {cnForm = Not nfr} : nct = tsk
                        goalseq (pred n) (succ m) [nfr] `withCtxt` nct  -- start reasoning process again

    rde = whenIB IBPrsn False $ rlog0 $ "reasoning depth exceeded"
    sbg = when (not . isTop $ f) $ whenIB IBPrsn False $ rlog0 $ tri ++ show f
    tri = if (isTop rfr) then "trivial: " else "proving: "

goalseq  _ _ _ = return ()

splitG :: VM [Formula]
splitG = asks (spl_al . strip . cnForm . vsThes)
  where
    spl_al = spl . albet
    spl (All u f) = liftM (All u) (spl_al f)
    spl (And f g) = mplus (spl_al f) (spl_al $ Imp f g) -- when splitting a conjuction we can add earlier
    spl (Or f g)  = liftM (zOr f) (spl_al g)            -- formulas as antecedents to later goals
    spl fr         = return fr


-- Call prover

launch :: Int -> VM ()
launch m = do  red <- askRSIB IBOnto False          -- ask if ontological reduction is enabled
               whenIB IBPtsk False (debug red)      -- print prover taks if the option is enabled
               prd <- askRS rsPrdb ; ins <- askRS rsInst
               tc <- thesis; cnt <- context
               let ext = justIO $ export red m prd ins cnt tc -- this is the monadic action for exporting the task
               ext >>= timer CTprov . justIO >>= guard        -- do it, keep track of the time, then check if it was succesfull
               CntrT _ td <- liftM head $ askRS rsCntr
               addRSTI CTprvy td ; incRSCI CIprvy
  where
    debug red = do  rlog0 "prover task:"
                    tlb <- asks $ map (if red then cnRedu else cnForm) . reverse . vsCtxt
                    mapM_ ((putStrRM "  " >>) . printRM) tlb
                    putStrRM "  |- " ; thesis >>= printRM . cnForm


callown :: VM ()
callown = do   tc <- thesis; cnt <- context
               n <- askGS gsSklm; ps <- askGS gsGlps; ng <- askGS gsGlng-- print prover taks if the option is enable
               let loc = takeWhile cnLowL cnt
                   prv = prove n loc ps ng tc
                   ext = timeout (10^4) $ evaluate $  prv    -- set timelimit to 10^4 (usually not necessary as max proof depth is limited)
               res <- justIO ext; guard (res == Just True)   -- try to solve



-- Context filtering

{- if an explicit list of theorems is given, we set the context to that plus all definitions/sigexts
   (as they usually import type information that is easily forgotten) and the low level context.
   Otherwise the whole context is selected. -}
filt_context :: VM a -> VM a
filt_context fn =
  do ln <- asks (cnLink . vsThes) >>= getLink; cnt <- asks vsCtxt;
     if Set.null ln then fn `withCtxt` (map rephead $ filter (not .isTop . cnRedu) cnt)
       else let (low,dfs) = deflow cnt in
      retrieveCn ln >>= \nct -> fn `withCtxt` (low ++ nct ++ dfs)
  where
    deflow cnt = let (low,top) = span cnLowL cnt; dfs = map replacehead $ filter (\c -> (not . isTop . cnRedu $ c) && (defn c || sign c)) top
                  in (low,dfs)
    defn = (==) Defn . blType . cnHead; sign = (==) Sign . blType . cnHead

    replacehead c = setForm c $ dive 0 $ cnForm c
    dive n (All _ (Imp (Tag DHD Trm {trName = "=", trArgs = [_, t]}) f)) = subst t "" $ inst "" f
    dive n (All _ (Iff (Tag DHD eq@Trm {trName = "=", trArgs = [_, t]}) f))
      = And (subst t "" $ inst "" f) (All "" $ Imp f eq)
    dive n (All _ (Imp (Tag DHD Trm{}) Top)) = Top
    dive n (All v f) = bool $ All v $ bind (show n) $ dive (succ n) $ inst (show n) f
    dive n (Imp f g) = bool $ Imp f $ dive n g
    dive _ f = f

    rephead c | defn c || sign c = replacehead c
              | otherwise = c


-- Service stuff

isDefn (Iff (Tag DHD _) _)  = True
isDefn (All _ f)            = isDefn f
isDefn (Imp _ f)            = isDefn f
isDefn _                    = False

isSign (Imp (Tag DHD _) _)  = True
isSign (All _ f)            = isSign f
isSign (Imp _ f)            = isSign f
isSign _                    = False

isUnit (Not f)              = isUnit f                          -- tests if a formula is a literal
isUnit f                    = isTrm f || isTop f || isBot f

isSort Trm {trArgs = _:ts}     = all ground ts      -- a predicate whose parameters are constants is viewed as a sort
isSort Trm {trName = 'a':_}   = True               -- notions are sorts
isSort (Not Trm {trName = "="})  = True               -- ?? not yet sure about this one
isSort f                    = isTop f || isBot f

ground Var{}            = False
ground f                    = allF ground f

noFree Var { trName = '?':_ } = False
noFree f = allF noFree f


-- reduction by collected info

rapid :: Formula -> Bool
rapid f = isTop $ reduce f

reduce :: Formula -> Formula
reduce t@Trm{trName = "="} = t -- leave equality untouched
reduce l | isLtrl l = fromMaybe l $ msum $ map (lookFor l) (trArgs $ predSymb l)
reduce f = bool $ mapF reduce $ bool f -- round through the formula


{-lookFor the right evidence-}
lookFor :: Formula -> Formula -> Maybe Formula
lookFor _ Ind{} = Nothing
lookFor l (Tag _ t) = lookFor l t
lookFor l trm =
  let tId = trId (predSymb l); negl = albet $ Not l
  in  checkFor l negl $ trInfo trm
  where
    checkFor l negl [] = Nothing
    checkFor l negl (pr:prds) | ltTwins l (replace trm ThisT pr) = Just Top
                              | ltTwins negl (replace trm ThisT pr) = Just Bot
                              | otherwise = checkFor l negl prds


-- unfolding of definitions

data UF = UF {dfs :: Definitions, evs :: DT.DisTree Eval, ufl :: Bool, ufs :: Bool}

-- the booleans are user parameters that control what is unfolded

unfold :: VM [Context]
unfold = do  ths <- thesis; cnt <- context
             let tsk = setForm ths (Not $ cnForm ths) : cnt
             dfs <- askGS gsDefs; dt <- asks vsEval
             ugen  <- askRSIB IBUnfl True; ulow  <- askRSIB IBUfdl True;
             usgen <- askRSIB IBUnfs True; uslow <- askRSIB IBUfds False
             guard (ugen || usgen)
             let ((gl:tun), rst) = span cnLowL tsk
                 (nloc, num) = W.runWriter $ flip runReaderT (UF dfs dt (ugen && ulow) (usgen && uslow)) $
                   liftM2 (:) (local (\st -> st {ufl = ugen, ufs = usgen}) $ unfoldC gl) (mapM unfoldC tun) --actual unfolding, writer monad records the number of unfolds
             unf nloc; when (num == 0) $ ntu >> mzero; addRSCI CIunfl (getSum num) -- report what has been unfolded or that nothing has been unfolded (-> fail)
             return $ nloc ++  rst
  where
    ntu         = whenIB IBPunf False $ rlog0 $ "nothing to unfold" -- only write messages if printunfold is turned on
    unf (tc:lc) = whenIB IBPunf False $ rlog0 $ "unfold to:\n"
                    ++ unlines (reverse $ map ((++) "  " . show . cnForm) lc)
                    ++ "  |- " ++ show (neg $ cnForm tc)


{-
unfoldC provides the recursive skeleton for unfolding everything in a (contexted) formula.
The actual unfolding of specific instances is then done by unfoldA.

The subfunction fill makes its round through the formula and expands everything that
has been marked before. Notice That we do not use the local context (fc) generated by
fill, but that it has to be included here because roundF generates it automatically.

fc -> formula context, sg -> signum
-}


unfoldC :: Context -> ReaderT UF (W.Writer (Sum Int)) Context
unfoldC cx | decl cx = return cx
           | otherwise = liftM (setForm cx) $ fill [] (Just True) 0 $ cnForm cx               -- unfold conservatively
  where
    fill fc sg n f | hasDMK f = return f                                 -- if nothing is to be unfolded, leave f be
                   | isTrm f  =  liftM reduce $ unfoldA (fromJust sg) f  -- else if f is also a Term then unfold its definition
    fill fc sg n (Iff f g)    = fill fc sg n $ zIff f g           -- Iff must be changed to double implication so that every position has a non neutral polarity
    fill fc sg n f            = roundFM 'u' fill fc sg n f         -- round through the formula (note that the local premises fc are not needed for unfolding )

    decl = ((==) Declare) . blType . cnHead

unfoldA sg fr =
  do nbs <- liftM (\f -> foldr (if sg then And else Or ) wip f) $ expA fr
     nfr <- liftM (\f -> foldr (if sg then And else Imp) nbs f) $ expS fr
     return nfr
  where
    wip = Tag DMK fr -- we mark the term so that it does not get unfolded again in subsequent iterations

    expS (Tag DMK _) = return []              -- do not expand marked terms
    expS h  = foldFM expT h                   -- get Definition expansion for subterms
    expT h  = liftM2 (++) (expS h) (expA h)   -- get all Definition expansions of the term and subterms
    expA h  = getExp h                        -- get what is expanded

    getExp (Tag DMK _) = return []
    getExp Trm {trName = "=", trArgs = [l,r]}
      = liftM3 (\a b c -> a ++ b ++ c) (deq l r) (deq r l) (setExt l r)
  -- we combine definitional information for l, for r and if
  -- we have set equality we also throw in extensionality for sets and if
  -- we have functions we throw in function extensionality

    getExp t | isApp t || isElem t = setfun_deq t
             | otherwise = deq t t

    deq f g = do
      dfs <- asks dfs
      let ls = maybeToList $ do
            mId <- mbId f; df <- IM.lookup (mId) dfs;
            guard (sg || dfSign df)
        -- only unfold a definitions or (a sigext in a positive position)
            sb <- match (dfTerm df) f
            let dq = replace (Tag DMK g) ThisT $ sb $ dfForm df
        -- substitute the (marked) term
            guard (not . isTop $ dq); return dq
      unfGuard ufl $ unless (null ls) (lift $ W.tell 1) >> return ls
        -- increase the counter by 1 and return what we got

    setExt f g = let ls =
                      (do guard (setType f && setType g); let v = zVar "" -- set extensionality
                          return $ zAll "" $ Iff (zElem v f) (zElem v g))
                      `mplus`
                      (do guard (funType f && funType g); let v = zVar "" -- function extensionality
                          return $ And (domEqu (zDom f) (zDom g)) $ zAll "" (Imp (zElem v $ zDom f) $ zEqu (zApp f v) (zApp g v)))
                  in lift (W.tell 1) >> return ls

    domEqu = if sg then zEqu else sEqu -- depending on the sign we choose the more convenient form of set equality

    setfun_deq t =
      do dt <- asks evs
         let ls = maybeToList $ DT.lookup t dt >>= msum . map findev
         unfGuard ufs $ unless (null ls) (lift $ W.tell 1) >> return ls
       where
         findev ev = do
           sb <- match (evTerm ev) t
           guard (all rapid $ map sb $ evCond ev)
           return $ replace (Tag DMK t) ThisT $ sb $
             if sg then evPos ev else evNeg ev

    unfGuard qu fn = ifM (asks qu) fn (return [])

hasDMK (Tag DMK _ ) = True
hasDMK _ = False

setType f | hasInfo f = any (infoTwins ThisT $ zSet ThisT) $ trInfo f
setType _ = False

funType f | hasInfo f = any (infoTwins ThisT $ zFun ThisT) $ trInfo f
funType _ = False

hasInfo f = isTrm f || isVar f
