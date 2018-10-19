{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018)

Well-definedness check and evidence collection.
-}

module Alice.Core.Check (fillDef) where

import Control.Monad
import Data.Maybe
import Data.Either (lefts,rights, isRight)
import Data.List
import qualified Data.IntMap.Strict as IM
import Control.Monad.State
import Control.Monad.Trans.Class
import Control.Monad.Reader

import Alice.Data.Base
import Alice.Data.Formula
import Alice.Data.Kit
import Alice.Data.Instr
import Alice.Data.Text
import Alice.Core.Base
import Alice.Core.Reason
import Alice.Prove.Normalize
import Alice.Prove.MESON
import Alice.Core.Reduction
import Alice.Core.Functions
import qualified Alice.Data.DisTree as DT

{-
fillDef checks for well-definedness and fortifies terms. Furthermore it returns
the term identifiers of newly introduced terms. this is only important for the
experimental support for constructed notions.

The fill subfunction makes its round through the formula. The first boolean (pr) tells us whether the
term in question is a predicate (True) or a term (False). The second boolean (nw)
tells us whether the symbol in question is introduced in that spot (True) or should be known (False).
The (at the beginning empty) list (fc) will accumulate the local premises of a position in the formula.
The Maybe Bool (sg) indicates the polarity of the position we are at (Just True -> positive, Just False -> negative,
Nothing -> neutral). The integer keeps track of quantification depth.

pr -> predicate, nw -> new word, fc -> formula context, sg -> signum

-}
--

fillDef :: Context -> VM Formula
fillDef cx
    = fill True False [] (Just True) 0 $ cnForm cx
  where
    fill pr nw fc sg n (Tag tg f)
      | tg == DHD = liftM (Tag DHD) $ fill pr True fc sg n f --newly introduced symbols
      | fnTag tg  =  liftM cnForm thesis >>= getMacro cx tg -- macros in function delcarations
      | otherwise = liftM (Tag tg) $ fill pr nw fc sg n f -- ignore every other tag
    fill _ _ _ _ _ t  | isThesis t = thesis >>= return . cnForm
    fill _ _ fc _ _ v | isVar v = do
      uin <- askRSIB IBinfo True  -- see if user has disables info collection
      nct <- cnRaise cx fc
      sinfo uin v `withCtxt` nct   -- fortify the term
    fill pr nw fc sg n tr@Trm {trName = t, trArgs = ts, trInfo = is, trId = tId}
      = do
        uin <- askRSIB IBinfo True
        nts <- mapM (fill False nw fc sg n) ts;        --fortify subterms
        nct <- cnRaise cx fc
        ntr <- setDef nw cx tr { trArgs = nts } `withCtxt` nct
        sinfo (not pr && uin) ntr `withCtxt` nct        -- fortify term
    fill pr nw fc sg n f = roundFM 'w' (fill pr nw) fc sg n f                 -- round trough the formula

    sinfo uin trm -- set info (we only do this for terms and if info collection is enabled)
      | uin   = setInfo trm
      | True  = return trm

    cnRaise cx fs = context >>= return . flip (foldr $ (:) . setForm cx) fs




setDef :: Bool -> Context -> Formula -> VM Formula
setDef nw cx trm@Trm{trName = t, trId = tId}  = incRSCI CIsymb >>
    (   guard nw >> return trm        -- if the symbol is newly introduced, no def must be checked
    <|>  findDef trm >>= testDef cx trm -- try to verify the symbols domain conditions
    <|>  out >> mzero )                           -- failure message
  where
    out = rlog (cnHead cx) $ "unrecognized: " ++ showsPrec 2 trm ""


-- Find relevant definitions and test them

type DefDuo = ([Formula], Formula)
  -- the list contains the guards, the formula is the term, fortified with definitional evidence


findDef :: Formula -> VM DefDuo -- retrieve definition of a symbol and prepare
findDef trm@Trm{trArgs = ts} = -- for ontological check
  do def <- getDef trm
     sb  <- match (dfTerm def) trm
     let ngs = map (infoSub sb) $ dfGrds def  -- instantiate definition guards
         nev = map sb $ dfEvid def -- definitional evidence
         nt  = trm { trInfo = nev } -- fortified term
     return (ngs, nt)
  where
    add nev t = t {trInfo = nev ++ trInfo t}

{-
testDef does what the name suggests and tests a definition. if the use has disabled
ontological checking we just assume that the definition fits, else we check it.
setup and cleanup take care of the special proof times that we allow an ontological
 check. easy is the triviality check (i.e. simplification with evidence or build in MESON),
 It passes any guard that could not be proved to the hard check, which calls the external ATP -}



testDef :: Context -> Formula -> DefDuo -> VM Formula
testDef cx trm (gs, nt)
    = do chk <- askRSIB IBchck True; if chk then setup >> easy >>= hard >> return nt else return nt
  where
    easy     = mapM triv gs
    hard hgs | all isRight hgs = incRSCI CIchkt >> whdchk ("trivial " ++ header rights hgs) >> cleanup
             | otherwise =
               do incRSCI CIchkh >> whdchk (header lefts hgs ++ thead (rights hgs));
                  mapM (reason . setForm ccx) (lefts hgs) >> incRSCI CIchky >> cleanup <|> cleanup >> mzero

    setup    = do  askRSII IIchtl 1 >>= addRSIn . InInt IItlim
                   askRSII IIchdp 3 >>= addRSIn . InInt IIdpth
                   askRSIB IBOnch False >>= addRSIn. InBin IBOnto


    cleanup  = do  drpRSIn $ IdInt IItlim
                   drpRSIn $ IdInt IIdpth
                   drpRSIn $ IdBin IBOnto

    ccx = let bl:bs = cnBran cx in cx { cnBran = bl { blLink = [] } : bs }


    header sel gs = "check: " ++ showsPrec 2 trm " vs " ++ grds (sel gs) --output printcheck messages
    thead [] = ""; thead gs = "(trivial: " ++ grds gs ++ ")"
    grds  gs = if null gs then " - " else unwords . map show $ gs
    whdchk = whenIB IBPchk False . rlog (head $ cnBran cx)



    triv g = if rapid g
               then  return $ Right g  -- triviality check
               else callown `withGoal` g >> return (Right g)
                 <|> return (Left g)


-- Info heuristic

{- moves through the low level context and collects typings of a given term. In
   case of equality we also add the typings of the equated term -}
typings :: (MonadPlus m) => [Context] -> Formula -> m [Formula]
typings [] _ = mzero
typings (c:cnt) t = dive (cnForm c) `mplus` typings cnt t
  where
    dive = dive2 . albet
    dive2 tr | isLtrl tr = comp [] $ ltArgs tr -- if we encounter a literal, then compare its arguments to t
      where
        comp _ [] = mzero
        comp ls (arg:rs) =
          let nt = mbNot tr; prd = predSymb tr
           in (do match t arg
                  return $ nt prd {trArgs = reverse ls ++ (ThisT : rs)} : ntnEvid ls prd ++ trInfo arg
              `mplus` comp (arg:ls) rs)

    dive2 e@Trm {trName = "=", trArgs = [l,r]} = if twins l t
                                      then return $ joinTps t (trInfo l) (trInfo r)
                                      else if twins r t
                                        then return $ joinTps t (trInfo r) (trInfo l)
                                        else mzero
    dive2 (And f g) = dive g `mplus` dive f
    dive2 (Tag _ f) = dive f
    dive2 _         = mzero

    ntnEvid [] prd | isNtn prd = trInfo prd
    ntnEvid _ _ = []



setInfo :: Formula -> VM Formula
setInfo t = do
  cnt <- asks vsCtxt
  let loc = takeWhile cnLowL cnt; lev = fromMaybe [] $ typings loc t
  return $ t {trInfo = trInfo t ++ lev}

joinTps t ls rs = filter (\l -> all (not . infoTwins t l) rs) ls ++ rs
