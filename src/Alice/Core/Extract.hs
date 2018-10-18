{-
Authors: Steffen Frerix (2017 - 2018)

Extraction of various information from formulas: definitions,
function evaluations, elementhood conditions for sets
-}
{-# LANGUAGE FlexibleContexts #-}

module Alice.Core.Extract where

import Alice.Data.Base
import Alice.Data.Formula
import Alice.Data.Kit
import Alice.Core.Base
import Alice.Core.Reduction
import Alice.Prove.Normalize
import qualified Alice.Data.DisTree as DT

import qualified Data.IntMap as IM
import Data.List
import Data.Maybe
import Control.Monad.State
import Control.Monad.Reader

import Debug.Trace


-- Definition extraction


{- extract definition from f and add it to the global state -}
addDef f = do dfs <- askGS gsDefs; let ndf = extrDef dfs f
              updateGS (\rs -> rs {gsDefs = add ndf (gsDefs rs)})
    where
      add df@DE {dfTerm = t} im = IM.insert (trId t) df im

{- extract definition. Multiple entries will only be extracted in the case of constructed notions (experimental).
   dive moves through the formula until it encounters the head term. Then guards, formula, term and type of the
   definition  are returned.
   evs collects definitional evidence. mkDef puts everything together. Type-likes for ontological reduction as well
   as definitional evidence closure are added later.-}
extrDef :: Definitions -> Formula -> DefEntry
extrDef dfs = closeEvid dfs . addTpLikes dfs . mkDef . dive [] 0
  where
    dive gs _ (All _ (Iff (Tag DHD Trm {trName = "=", trArgs = [_, t]}) f))         -- function definition
      = (gs, instWith ThisT f, Definition, t)
    dive gs _ (All _ (Imp (Tag DHD Trm {trName = "=", trArgs = [_, t]}) f))         -- function sigext
      = (gs, instWith ThisT f, Signature, t)
    dive gs _ (Iff (Tag DHD t) f) = (gs, f, Definition, t)          -- predicate definition
    dive gs _ (Imp (Tag DHD t) f) = (gs, f, Signature,t)    -- predicate sigext


    dive gs n (All _ f) = dive gs (succ n) $ inst ('?':show n) f   -- make universal quant matchable
    dive gs n (Imp g f) = dive (gs ++ deAnd g) n f
    mkDef (gs, form, dtyp, term) =  DE {dfGrds = gs, dfForm = form, dfType = dtyp, dfTerm = term, dfEvid = evs term form, dfTplk = []}

    evs term form | isNtn term = filter (isJust . find (twins ThisT) . ltArgs) . filter isLtrl . deAnd $ replace ThisT (head $ trArgs term) form
                  | otherwise = getEv form

getEv form =
  filter (isJust . find (twins ThisT) . ltArgs) . filter isLtrl . deAnd $ form

{- computes and adds type-likes for ontological reduction to a definition.-}
addTpLikes :: Definitions -> DefEntry -> DefEntry
addTpLikes dfs df = df {dfTplk = tp_likes $ dfGrds df}
  where
    tp_likes fs = rn_classes [] $ filter (\g -> isTrm g && no_sklm g && type_like dfs g fs) fs

    rn_classes _ [] = []
    rn_classes cl (t:ts) =
      case break (\t' -> trId t' == trId t) ts of
        (pre,[])      -> (t:cl): rn_classes [] pre
        (pre,t':post) -> rn_classes (t':cl) (t:pre ++ post)

    no_sklm Var{} = True
    no_sklm Trm {trName = 't':'s':'k':_} = False
    no_sklm f = allF no_sklm f


{- downward closure for definitional evidence. Example: if we have "natural c= rational c= real" then we do not only know that
   a natural number is rational, but also add the info that it is real.-}
closeEvid :: Definitions -> DefEntry -> DefEntry
closeEvid dfs df@DE{dfEvid = evs} = df { dfEvid = newEvid }
  where
    newEvid = nubBy twins $ evs ++ concatMap evids evs
    evids t@Trm {trId = n} =
      let def = fromJust $ IM.lookup n dfs
          sb  = fromJust $ match (dfTerm def) $ fromTo '?' 'u' t
      in  map (fromTo 'u' '?' . sb) $ dfEvid def
    evids _ = []



-- Evaluation for functions and sets

addEval dt f = foldr (\ev -> DT.insert (evTerm ev) ev) dt $ extrEval dt f

extrEval :: DT.DisTree Eval -> Formula -> [Eval]
extrEval dt f = flip runReaderT (0, dt) . dive $ f
  where
    dive (All _ (Iff (Tag DHD Trm {trName = "=", trArgs = [_, t]}) f))
      = extr $ instWith t f
    dive (All _ f) = freshV dive f
    dive (Imp f g) = dive g
    dive f = extr f

    extr f = extractEv id [] f

extractEv c gs f = extrFun c gs f `mplus` extrSet c gs f

freshV fn f = do n <- asks fst; local (\(m,dt) -> (succ m, dt)) $ fn $ inst ('?':show n) f


extrFun :: (Formula -> Formula) -> [Formula] -> Formula
        -> ReaderT (Int, DT.DisTree Eval) [] Eval
extrFun c gs (And g@(Tag DDM _ ) h) = extrSet c gs g `mplus` extrFun c gs h
extrFun c gs (And f g) = extrFun c gs g
extrFun c gs f = dive c gs f
  where
    dive c gs (Imp _ g) = dive c gs g -- ignore ontological assumptions
    dive c gs (Tag DCD (Imp f g)) = dive c (f:gs) g -- but add case distinctions
    dive c gs (All _ f) = freshV (dive c gs) f
    dive c gs (And f g) = dive c gs f `mplus` dive c gs g
    dive c gs (Tag DEV f@Trm{ trName = "=", trArgs = [tr,vl]} ) =
      let nf = c f {trArgs = [ThisT, vl] }
      in  return $ EV tr nf nf gs
    dive c gs (Exi x (And (Tag DEF f) (Tag DEV Trm {trName = "=", trArgs = [tr, Ind n]})))
      | n == 0 = extractEv c gs $ dec $ instWith tr f
    dive c gs (Exi x (And f g)) = dive (c . zExi x . And f) gs $ inst x g
    dive _ _ _ = mzero

    deConj (And f g) = deConj f ++ deConj g; deConj f = [f]

extrSet :: (Formula -> Formula) -> [Formula]-> Formula
        -> ReaderT (Int, DT.DisTree Eval) [] Eval
extrSet c gs (And f g) = extrSet c gs f `mplus` extrSet c gs g
extrSet c gs (Tag _ f) = extrSet c gs f
extrSet c gs (All _ (Iff g@Trm{trArgs = [_,t]} f ))
  | isElem g = do
      (n, dt) <- ask; let nm = '?':show n; nf = elemsimp dt $ strip $ inst nm f
      return $ EV (zElem (zVar nm) t) (mkPos $ c $ Tag DEV nf)(c nf) gs
extrSet _ _ f = mzero


elemsimp dt = dive
  where
    dive f@Trm {trArgs = [x,t]} | isElem f = fromMaybe f $ simp f
    dive f@Trm{} = f
    dive f = mapF dive f

    simp f = do
      ev <- DT.lookup f dt >>= single; guard (null $ evCond ev)
      sb <- match (evTerm ev) f; return $ sb $ evNeg ev

    single [x] = return x; single l = mzero

mkPos = dive
  where
    dive (Exi x f)   = All x $ dive f
    dive (Tag DEV f) = f
    dive (And f g) = Imp f $ dive g


instWith t = subst t "" . inst ""
