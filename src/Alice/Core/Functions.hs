{-
Authors: Steffen Frerix (2017 - 2018)

Generation of proof tasks.
-}


module Alice.Core.Functions (prfTask, getMacro) where

import Alice.Data.Base
import Alice.Data.Formula
import Alice.Data.Kit
import Alice.Data.Text
import Alice.Prove.Normalize
import Alice.Core.Base

import qualified Control.Monad.Writer as W
import Data.List
import Control.Monad
import Data.Maybe
import Debug.Trace
import Control.Monad.State


{- generate proof task associated with a block -}

prfTask Select vs fr = foldr mbExi fr vs
prfTask Declare _ fr
    | funDcl fr = funTask fr
    | setDcl fr = setTask fr
prfTask _ _ fr = fr

funDcl (And (And f _) _) = trId f == funId
funDcl _                 = False
setDcl (And f _)         = trId f == setId

setTask (And _ (All x (Iff _ (Tag DRP f)))) = rep x f -- replacement schema
setTask (And _ (All _ (Iff _ f))) = sep f -- separation schema
funTask h@(And (And _ g) f) =
  let c = dmcnd g
  in  domain g `blAnd` c (choices f `blAnd` existence f `blAnd` uniqueness f)

domain (Tag DDM (All _ (Iff _ f))) = Tag FDM $ sep f
domain (Tag DDM (Trm{trName = "=", trArgs = [_,t]})) = Tag FDM $ zSet t




choices f = Tag FCH . dive $ f
  where
    dive (Tag DEV _) = Top
    dive (Tag _ f) = dive f
    dive (Exi x (And (Tag DEF f) g)) =
      (prfTask Declare [] $ dec $ inst x $ f) `blAnd`
      (dec $ inst x $ f `blImp` dive g)
    dive (All x f) =  blAll x $ dive f
    dive (Imp f g) = f `blImp` dive g
    dive (Exi x f) = blExi x $ dive $ inst x f
    dive (And f g) = dive f `blAnd` dive g
    dive f = f


existence  = Tag FEX . dive 0
  where
    dive n (All x f) = let nn = 'c':show n in blAll nn $ dive (n + 1)$ inst nn f
    dive n (Imp f g) = blImp f $ dive n g
    dive _ f = let y = zVar "y" in zExi "y" $ devRep y $ describe_exi f



sep (And f g) = sep f
sep t = dec $ zSet $ last $ trArgs t -- we know that in this case t is the term zElem(. , .), where the second argument is the term whose sethood we have to show

rep x f = fromJust $ dive [] f `mplus` _default
  where
    dive vs (Exi x f) = dive (x:vs) f
    dive vs (And f g)
      | not $ null vs =
          let vs2 = map ((:) 'c') vs
          in  return $ foldr mbExi (sets vs2 `blAnd` foldr mbAll (f `blImp` elms vs vs2) vs) vs2
    dive _ _ = mzero
    _default =
      let x2 = 'c':x; xv = zVar x; x2v = zVar x2
      in  return $ zAll x $ Imp f $ zExi x2 $ zSet x2v `And` (xv `zElem` x2v)

    sets = foldr blAnd Top . map (zSet . zVar)
    elms (v1:vs) (v2:vs2) = zElem (zVar v1) (zVar v2) `blAnd` elms vs vs2
    elms _ _ = Top


uniqueness :: Formula -> Formula
uniqueness f = dive f
  where
    dive (All x f) = All x $ dive f
    dive (Imp f g) = f `blImp` dive g
    dive f =
      let y = zVar "y"; cy = zVar "cy"; df = describe f
          yf = devRep y df; cyf = devRep cy df
      in  Imp (yf `And` cyf) $ zEqu y cy



describe (And f g) = describe f `Or` describe g
describe (Tag DCD (And f g)) = And f $ deExi g
describe f = deExi f

describe_exi (And f g) = describe_exi f `Or` describe_exi g
describe_exi (Tag DCD (And f g)) = And f $ impExi g
describe_exi f = impExi f

deExi (Exi x (And f g)) = dec $ And (inst x f) (deExi $ inst x g)
deExi f = f

impExi (Exi x (And f g)) = dec $ Imp (inst x f) (impExi $ inst x g)
impExi f = f

devRep y (Tag DEV eq@Trm {trName = "=", trArgs = [_, t]}) = eq {trArgs = [y,t]}
devRep y f = mapF (devRep y) f


dmcnd (Tag _ (All _ (Iff Trm {trArgs = [_,dm]} g))) = dive
  where
    dive Trm {trId = tId, trArgs = [x,d]}
      | tId == elmId && twins d dm = subst x "" $ inst "" g
    dive f = mapF dive f
dmcnd (Tag _ Trm {trName = "=", trArgs = [dm,g]}) = dive
  where
    dive Trm {trId = tId, trArgs = [x,d]}
      | tId == elmId && twins d dm = zElem x g
    dive f = mapF dive f




-- notice that this takes place in the FM monad, therefore some lifts to get actions from the RM monad
getMacro cx tg = liftM (Tag tg . pd ) . either err return . dive
  where
    dive (And f g) = dive f `mplus` dive g
    dive (Imp f g) = liftM (Imp f) $ dive g
    dive (Tag tg' f) | tg == tg' = return f
    dive _ = Left $ "Warning: could not unfold macro: " ++ mcr tg

    err s = rlog (cnHead cx) s >> return Top

    pd (Imp f g) = Imp (Tag DIH f) g
    pd f = f                             -- so that an author may instantiate quantified variables

    mcr FDM = "domain"; mcr FEX = "existence"
    mcr FUQ = "uniqueness"; mcr FCH = "choices"
