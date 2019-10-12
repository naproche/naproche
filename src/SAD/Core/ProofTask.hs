{-
Authors: Steffen Frerix (2017 - 2018)

Generation of proof tasks.
-}

{-# LANGUAGE OverloadedStrings #-}

module SAD.Core.ProofTask (generateProofTask) where

import SAD.Data.Formula

import SAD.Data.Text.Block (Section(..))
import SAD.Prove.Normalize

import qualified Data.Text.Lazy as Text

import Data.Maybe

import SAD.Data.Text.Decl


{- generate proof task associated with a block -}

generateProofTask :: Section -> [VariableName] -> Formula -> Formula
generateProofTask Selection vs f = foldr mbExi f vs
generateProofTask LowDefinition _ f
  | funDcl f = funTask f
  | setDcl f = setTask f
generateProofTask _ _ f = f

{- Check whether a formula is a set or function defintion -}
funDcl, setDcl :: Formula -> Bool
funDcl (And (And f _) _) = trmId f == FunctionId
funDcl _ = False
setDcl (And f _) = trmId f == SetId
setDcl _ = error "SAD.Core.ProofTask.setDcl: misformed definition"

setTask :: Formula -> Formula
setTask (And _ (All x (Iff _ (Tag Replacement f)))) =
  replacement (declName x) f
setTask (And _ (All _ (Iff _ f))) = separation f
setTask _ = error "SAD.Core.ProofTask.setTask: misformed definition"

{- generate separation proof task -}
separation :: Formula -> Formula
separation (And f g) = separation f
separation t | isElem t = dec $ zSet $ last $ trmArgs t
separation _ = error "SAD.Core.ProofTask.separation: misformed argument"

{- generate replacement proof task -}
replacement :: VariableName -> Formula -> Formula
replacement x f = fromMaybe _default $ dive [] f
  where
    dive vs (Exi x f) = dive (declName x:vs) f
    dive vs (And f g) | not $ null vs =
      let vsAlt  = map VarTask vs
          startF = sets vsAlt `blAnd` foldr mbAll (f `blImp` elements vs vsAlt) vs
      in  Just $ foldr mbExi startF vsAlt
    dive _ _ = Nothing
    _default =
      let x2 = VarTask x; xv = zVar x; x2v = zVar x2
      in  zAll x $ Imp f $ zExi x2 $ zSet x2v `And` (xv `zElem` x2v)

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
domain (Tag Domain Trm{trmName = TermEquality, trmArgs = [_,t]}) = Tag DomainTask $ zSet t
domain _ = error "SAD.Core.ProofTask.domain: misformed definition"


{- extract choice tasks -}
choices :: Formula -> Formula
choices = Tag ChoiceTask . dive
  where
    dive (Tag Evaluation _) = Top
    dive (Tag _ f) = dive f
    dive (Exi dcl (And (Tag Defined f) g)) = let x = declName dcl in
      (generateProofTask LowDefinition [] $ dec $ inst x $ f) `blAnd`
      (dec $ inst x $ f `blImp` dive g)
    dive (All x f) = bool $ All x $ dive f
    dive (Imp f g) = f `blImp` dive g
    dive (Exi x f) = bool $ Exi x $ dive f
    dive (And f g) = dive f `blAnd` dive g
    dive f = f

{- extract existence task -}
existence :: Formula -> Formula
existence  = Tag ExistenceTask . dive 0
  where
    dive :: Int -> Formula -> Formula
    dive n (All x f) = let nn = VarTask $ VarDefault $ Text.pack $ show n in zAll nn $ dive (n + 1) $ inst nn f
    dive n (Imp f g) = blImp f $ dive n g
    dive _ f = let y = zVar (VarDefault "y") in zExi (VarDefault "y") $ devReplace y $ describe_exi f



{- extract uniqueness task -}
uniqueness :: Formula -> Formula
uniqueness = Tag UniquenessTask . dive
  where
    dive (All x f) = All x $ dive f
    dive (Imp f g) = f `blImp` dive g
    dive f =
      let y = zVar $ VarDefault "y"; cy = zVar $ VarTask $ VarDefault "y"; df = describe f
          yf = devReplace y df; cyf = devReplace cy df
      in  zAll (VarDefault "y") $ zAll (VarTask $ VarDefault "y") $ inc $ inc $ Imp (yf `And` cyf) $ zEqu y cy

{- output a description of a function in the form
  (condition_1 /\ evaluation_1) \/ ... \/ (condition_n /\ evaluation_n)
  choices are expressed by choice operator rather than throuth an existentially
  quantified formula -}
describe :: Formula -> Formula
describe (And f g) = describe f `Or` describe g
describe (Tag Condition (Imp f g)) = And f $ deExi g
describe f = deExi f

deExi :: Formula -> Formula
deExi (Exi dcl (And f g)) = let x = declName dcl in
  dec $ And (inst x f) (deExi $ inst x g)
deExi f = f

{- like 'describe' above, but choices are assumed instead of stated -}
describe_exi :: Formula -> Formula
describe_exi (And f g) = describe_exi f `Or` describe_exi g
describe_exi (Tag Condition (Imp f g)) = Imp f $ impExi g
describe_exi f = impExi f

impExi :: Formula -> Formula
impExi (Exi dcl (And f g)) = let x = declName dcl in
  dec $ Imp (inst x f) (impExi $ inst x g)
impExi f = f

{- a certain normalization of the term marked with Evaluation -}
devReplace :: Formula -> Formula -> Formula
devReplace y (Tag Evaluation eq@Trm {trmName = TermEquality, trmArgs = [_, t]}) =
  eq {trmArgs = [y,t]}
devReplace y f = mapF (devReplace y) f

{- compute domain conditions of functions -}
domainCondition :: Formula -> Formula -> Formula
domainCondition (Tag _ (All _ (Iff Trm {trmArgs = [_,dm]} g))) = dive
  where
    dive Trm {trmId = tId, trmArgs = [x,d]}
      | tId == ElementId && twins d dm = subst x VarEmpty $ inst VarEmpty g
    dive f = mapF dive f
domainCondition (Tag _ Trm {trmName = TermEquality, trmArgs = [dm,g]}) = dive
  where
    dive Trm {trmId = tId, trmArgs = [x,d]}
      | tId == ElementId && twins d dm = zElem x g
    dive f = mapF dive f
domainCondition _ =
  error "SAD.Core.ProofTask.domainCondition: misformed argument"
