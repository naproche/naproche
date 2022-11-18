-- |
-- Authors: Steffen Frerix (2017 - 2018)
--
-- Generation of proof tasks for low-level map and class definitions and choices.


{-# LANGUAGE OverloadedStrings #-}

module SAD.Core.ProofTask (generateProofTask) where

import Data.Set (Set)
import Data.Text.Lazy qualified as Text

import SAD.Data.Formula
import SAD.Data.Text.Block (Section(..))
import SAD.Prove.Normalize
import SAD.Data.Text.Decl


-- * Proof tasks

-- Generate proof task associated with a block
generateProofTask :: Section -> Set VariableName -> Formula -> Formula
generateProofTask Choice vs f = foldr mbExi f vs
generateProofTask LowDefinition _ f
  | mapDcl f = mapTask f
  | classDcl f = classTask f
generateProofTask _ _ f = f

-- Check whether a formula is a map definition
mapDcl :: Formula -> Bool
mapDcl ((f `And` _) `And` _) = trmId f == MapId
mapDcl _ = False

-- Check whether a formula is a class definition
classDcl :: Formula -> Bool
classDcl (Trm{trId = id} `And` _) = id == SetId || id == ClassId
classDcl (f `And` _) = classDcl f
classDcl f = error $ "SAD.Core.ProofTask.classDcl: misformed definition: " ++ show f


-- ** Proof tasks for classes

classTask :: Formula -> Formula
-- {x_1, ..., x_n}
classTask (_ `And` (All x (_ `Iff` (Trm{trId = ObjectId} `And` _)))) = Top
-- {t(x_1, ..., x_n) | ...}
classTask (_ `And` (All x (_ `Iff` (Tag Replacement f)))) = Top
-- {t(x_1,...,x_n) in X | ...}
classTask (_ `And` (All _ (_ `Iff` f))) = Top
-- Anything else
classTask f = error $ "SAD.Core.ProofTask.classTask: misformed definition: " ++ show f


-- ** Proof tasks for maps

-- Takes a statement of the form
-- @(aMap(F) and (Domain :: ...)) and ...@
mapTask :: Formula -> Formula
mapTask h@((_ `And` g) `And` f) =
  let c = domainCondition g
  in  domainTask g `blAnd` c (choiceTask f `blAnd` existenceTask f `blAnd` uniquenessTask f)
mapTask _ = error "SAD.Core.ProofTask.mapTask: misformed definition"

-- Takes a statement of one of the following forms:
--
--  1. @Domain :: forall v0 (aElementOf(v0,Dom(F)) iff f@
--     if the domain of @F@ is defined via a comprehension term @{x | f}@
--
--  2. @Domain :: Dom(F) = t@
--     when the domain of @F@ is defined via a term @t@
domainTask :: Formula -> Formula
domainTask (Tag Domain (All _ (_ `Iff` f))) = Tag DomainTask $ separation f
domainTask (Tag Domain Trm{trmName = TermEquality, trmArgs = [_,t]}) = Tag DomainTask $ mkClass t
domainTask _ = error "SAD.Core.ProofTask.domainTask: misformed definition"

choiceTask :: Formula -> Formula
choiceTask = Tag ChoiceTask . dive
  where
    dive (Tag Evaluation _) = Top
    dive (Tag _ f) = dive f
    dive (Exi dcl ((Tag Defined f) `And` g)) = let x = declName dcl in
      generateProofTask LowDefinition mempty (dec $ inst x f) `blAnd`
      dec (inst x $ f `blImp` dive g)
    dive (All x f) = bool $ All x $ dive f
    dive (f `Imp` g) = f `blImp` dive g
    dive (Exi x f) = bool $ Exi x $ dive f
    dive (f `And` g) = dive f `blAnd` dive g
    dive f = f

existenceTask :: Formula -> Formula
existenceTask  = Tag ExistenceTask . dive 0
  where
    dive :: Int -> Formula -> Formula
    dive n (All x f) = let nn = VarTask $ VarDefault $ Text.pack $ show n in
      mkAll nn $ dive (n + 1) $ inst nn f
    dive n (f `Imp` g) = f `blImp` dive n g
    dive _ f = let y = mkVar (VarDefault "y") in
      mkExi (VarDefault "y") (mkObject y `And` devReplace y (describe_exi f))

uniquenessTask :: Formula -> Formula
uniquenessTask = Tag UniquenessTask . dive
  where
    dive (All x f) = All x $ dive f
    dive (f `Imp` g) = f `blImp` dive g
    dive f =
      let y = mkVar $ VarDefault "y"
          cy = mkVar $ VarTask $ VarDefault "y"
          df = describe f
          yf = devReplace y df
          cyf = devReplace cy df
      in  mkAll (VarDefault "y") $ mkAll (VarTask $ VarDefault "y") $
        inc $ inc $ (yf `And` cyf) `Imp` mkEquality y cy


-- * Misc

separation :: Formula -> Formula
separation (f `And` g) = separation f
separation t | isElem t = dec $ mkClass $ last $ trmArgs t
separation f = error $ "SAD.Core.ProofTask.separation: misformed argument: " ++ show f

-- output a description of a map in the form
-- @(condition_1 /\ evaluation_1) \/ ... \/ (condition_n /\ evaluation_n)@
-- choices are expressed by choice operator rather than throuth an existentially
-- quantified formula
describe :: Formula -> Formula
describe (f `And` g) = describe f `Or` describe g
describe (Tag Condition (f `Imp` g)) = f `And` deExi g
describe f = deExi f

deExi :: Formula -> Formula
deExi (Exi dcl (f `And` g)) = let x = declName dcl in
  dec $ inst x f `And` deExi (inst x g)
deExi f = f

-- Like 'describe' above, but choices are assumed instead of stated
describe_exi :: Formula -> Formula
describe_exi (f `And` g) = describe_exi f `Or` describe_exi g
describe_exi (Tag Condition (f `Imp` g)) = f `Imp` impExi g
describe_exi f = impExi f

impExi :: Formula -> Formula
impExi (Exi dcl (f `And` g)) = let x = declName dcl in
  dec $ inst x f `Imp` impExi (inst x g)
impExi f = f

-- A certain normalization of the term marked with Evaluation
devReplace :: Formula -> Formula -> Formula
devReplace y (Tag Evaluation eq@Trm {trmName = TermEquality, trmArgs = [_, t]}) =
  eq {trmArgs = [y,t]}
devReplace y f = mapF (devReplace y) f

-- Compute domain conditions of maps
domainCondition :: Formula -> Formula -> Formula
domainCondition (Tag _ (All _ (Trm {trmArgs = [_,dm]} `Iff` g))) = dive
  where
    dive Trm {trId = tId, trmArgs = [x,d]}
      | tId == ElementId && twins d dm = subst x VarEmpty $ inst VarEmpty g
    dive f = mapF dive f
domainCondition (Tag _ Trm {trmName = TermEquality, trmArgs = [dm,g]}) = dive
  where
    dive Trm {trId = tId, trmArgs = [x,d]}
      | tId == ElementId && twins d dm = mkElem x g
    dive f = mapF dive f
domainCondition _ =
  error "SAD.Core.ProofTask.domainCondition: misformed argument"
