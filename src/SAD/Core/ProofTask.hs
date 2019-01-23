{-
Authors: Steffen Frerix (2017 - 2018)

Generation of proof tasks.
-}


module SAD.Core.ProofTask (generateProofTask) where

import SAD.Data.Formula
import SAD.Data.Text.Block (Section(..))
import qualified SAD.Data.Text.Block as Block (position)
import SAD.Data.Text.Context (Context)
import qualified SAD.Data.Text.Context as Context
import SAD.Prove.Normalize
import SAD.Core.Base
import qualified SAD.Core.Message as Message

import qualified Control.Monad.Writer as W
import Data.List
import Control.Monad
import Data.Maybe
import Debug.Trace
import Control.Monad.State
import Control.Monad.Trans.Reader

import qualified SAD.Data.Text.Decl as Decl


{- generate proof task associated with a block -}

generateProofTask :: Section -> [String] -> Formula -> Formula
generateProofTask Selection vs f = foldr mbExi f vs
generateProofTask LowDefinition _ f
  | funDcl f = funTask f
  | setDcl f = setTask f
generateProofTask _ _ f = f

{- Check whether a formula is a set or function defintion -}
funDcl, setDcl :: Formula -> Bool
funDcl (And (And f _) _) = trId f == functionId
funDcl _ = False
setDcl (And f _) = trId f == setId
setDcl _ = error "SAD.Core.ProofTask.setDcl: misformed definition"

setTask :: Formula -> Formula
setTask (And _ (All x (Iff _ (Tag Replacement f)))) =
  replacement (Decl.name x) f
setTask (And _ (All _ (Iff _ f))) = separation f
setTask _ = error "SAD.Core.ProofTask.setTask: misformed definition"

{- generate separation proof task -}
separation :: Formula -> Formula
separation (And f g) = separation f
separation t | isElem t = dec $ zSet $ last $ trArgs t
separation _ = error "SAD.Core.ProofTask.separation: misformed argument"

{- generate replacement proof task -}
replacement :: String -> Formula -> Formula
replacement x f = fromJust $ dive [] f `mplus` _default
  where
    dive vs (Exi x f) = dive (Decl.name x:vs) f
    dive vs (And f g) | not $ null vs =
      let vsAlt  = map ((:) 'c') vs
          startF =
            sets vsAlt `blAnd` foldr mbAll (f `blImp` elements vs vsAlt) vs
      in  return $ foldr mbExi startF vsAlt
    dive _ _ = mzero
    _default =
      let x2 = 'c':x; xv = zVar x; x2v = zVar x2
      in  return $ zAll x $ Imp f $ zExi x2 $ zSet x2v `And` (xv `zElem` x2v)

    sets = foldr blAnd Top . map (zSet . zVar)
    elements (v1:vs) (v2:vs2) =
      zElem (zVar v1) (zVar v2) `blAnd` elements vs vs2
    elements _ _ = Top


funTask :: Formula -> Formula
funTask h@(And (And _ g) f) =
  let c = domainCondition g
  in  domain g `blAnd` c (choices f `blAnd` existence f `blAnd` uniqueness f)
funTask _ = error "SAD.Core.ProofTask.funTask: misformed definition"

domain :: Formula -> Formula
domain (Tag Domain (All _ (Iff _ f))) = Tag DomainTask $ separation f
domain (Tag Domain Trm{trName = "=", trArgs = [_,t]}) = Tag DomainTask $ zSet t
domain _ = error "SAD.Core.ProofTask.domain: misformed definition"


{- extract choice tasks -}
choices :: Formula -> Formula
choices = Tag ChoiceTask . dive
  where
    dive (Tag Evaluation _) = Top
    dive (Tag _ f) = dive f
    dive (Exi dcl (And (Tag Defined f) g)) = let x = Decl.name dcl in 
      (generateProofTask LowDefinition [] $ dec $ inst x $ f) `blAnd`
      (dec $ inst x $ f `blImp` dive g)
    dive (All x f) = dBlAll x $ dive f
    dive (Imp f g) = f `blImp` dive g
    dive (Exi x f) = dBlExi x $ dive f
    dive (And f g) = dive f `blAnd` dive g
    dive f = f

{- extract existence task -}
existence :: Formula -> Formula
existence  = Tag ExistenceTask . dive 0
  where
    dive n (All x f) = let nn = 'c':show n in zAll nn $ dive (n + 1)$ inst nn f
    dive n (Imp f g) = blImp f $ dive n g
    dive _ f = let y = zVar "y" in zExi "y" $ devReplace y $ describe_exi f



{- extract uniqueness task -}
uniqueness :: Formula -> Formula
uniqueness = Tag UniquenessTask . dive
  where
    dive (All x f) = All x $ dive f
    dive (Imp f g) = f `blImp` dive g
    dive f =
      let y = zVar "y"; cy = zVar "cy"; df = describe f
          yf = devReplace y df; cyf = devReplace cy df
      in  zAll "y" $ zAll "cy" $ inc $ inc $ Imp (yf `And` cyf) $ zEqu y cy

{- output a description of a function in the form 
  (condition_1 /\ evaluation_1) \/ ... \/ (condition_n /\ evaluation_n)
  choices are expressed by choice operator rather than throuth an existentially
  quantified formula -}
describe :: Formula -> Formula
describe (And f g) = describe f `Or` describe g
describe (Tag Condition (Imp f g)) = And f $ deExi g
describe f = deExi f

deExi (Exi dcl (And f g)) = let x = Decl.name dcl in 
  dec $ And (inst x f) (deExi $ inst x g)
deExi f = f

{- like 'describe' above, but choices are assumed instead of stated -}
describe_exi :: Formula -> Formula
describe_exi (And f g) = describe_exi f `Or` describe_exi g
describe_exi (Tag Condition (Imp f g)) = Imp f $ impExi g
describe_exi f = impExi f

impExi (Exi dcl (And f g)) = let x = Decl.name dcl in
  dec $ Imp (inst x f) (impExi $ inst x g)
impExi f = f

{- a certain normalization of the term marked with Evaluation -}
devReplace :: Formula -> Formula -> Formula
devReplace y (Tag Evaluation eq@Trm {trName = "=", trArgs = [_, t]}) =
  eq {trArgs = [y,t]}
devReplace y f = mapF (devReplace y) f

{- compute domain conditions of functions -}
domainCondition :: Formula -> Formula -> Formula
domainCondition (Tag _ (All _ (Iff Trm {trArgs = [_,dm]} g))) = dive
  where
    dive Trm {trId = tId, trArgs = [x,d]}
      | tId == elementId && twins d dm = subst x "" $ inst "" g
    dive f = mapF dive f
domainCondition (Tag _ Trm {trName = "=", trArgs = [dm,g]}) = dive
  where
    dive Trm {trId = tId, trArgs = [x,d]}
      | tId == elementId && twins d dm = zElem x g
    dive f = mapF dive f
domainCondition _ =
  error "SAD.Core.ProofTask.domainCondition: misformed argument"
