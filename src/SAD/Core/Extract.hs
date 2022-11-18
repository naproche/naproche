-- |
-- Authors: Steffen Frerix (2017 - 2018)
--
-- Extraction of various information from formulas: definitions,
-- map evaluations, elementhood conditions for classes


{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NamedFieldPuns #-}

module SAD.Core.Extract (
  addDefinition,
  addEvaluation,
  extractRewriteRule
) where

import qualified Data.Map as Map
import Data.List
import Data.Maybe
import Control.Monad.State
import Control.Monad.Reader
import qualified Data.Text.Lazy as Text

import SAD.Data.Formula
import SAD.Data.Definition
import SAD.Data.Text.Context (Context)
import qualified SAD.Data.Text.Context as Context (formula, name)
import SAD.Data.Rules (Rule(Rule))
import qualified SAD.Data.Rules as Rule
import SAD.Prove.Normalize
import SAD.Data.Structures.DisTree (DisTree)
import qualified SAD.Data.Structures.DisTree as DisTree
import SAD.Data.Text.Decl


-- Definition extraction

{- extract definition from f and add it to the global state -}
addDefinition :: (Definitions, Guards) -> Formula -> (Definitions, Guards)
addDefinition (defs, grds) f = let newDef = extractDefinition defs f in
  (addD newDef defs, addG newDef grds)
  where
    addD df@DefEntry {defTerm = t} = Map.insert (trmId t) df
    addG df@DefEntry {defGuards = grd} grds = foldr add grds $ filter isTrm grd

    add guard grds =
      if   case DisTree.find guard grds of [] -> False; (x:_) -> x
      then grds
      else DisTree.insert guard True grds

{- Extract definition from a formula. Evidence closure is computed afterwards -}
extractDefinition :: Definitions -> Formula -> DefEntry
extractDefinition defs =
  closeEvidence defs . makeDefinition . dive [] 0
  where
    dive :: [Formula] -> Int -> Formula -> ([Formula], Formula, DefType, Formula)
    dive guards _ (All _ (Iff (Tag HeadTerm Trm {trmName = TermEquality, trmArgs = [_, t]}) f))
      = (guards, instWith ThisT f, Definition, t) -- function definition
    dive guards _ (All _ (Imp (Tag HeadTerm Trm {trmName = TermEquality, trmArgs = [_, t]}) f))
      = (guards, instWith ThisT f, Signature, t)  -- function signature extension
    dive guards _ (Iff (Tag HeadTerm t) f)
      = (guards, f, Definition, t)                -- predicate definition
    dive guards _ (Imp (Tag HeadTerm t) f)
      = (guards, f, Signature,t)                  -- predicate sigext

    -- make a universal quant matchable
    dive guards n (All _ f) = dive guards (succ n) $ inst (VarHole $ Text.pack $ show n) f
    dive guards n (Imp g f) = dive (guards ++ splitConjuncts g) n f
    makeDefinition (guards, formula, kind, term) = DefEntry {
      defGuards = guards, defFormula = formula,
      defKind = kind, defTerm = term,
      defEvidence = extractEvidences term formula,
      defTypeLikes = []}


{- get evidence for a defined term from a definitional formula -}
extractEvidences :: Formula -> Formula -> [Formula]
extractEvidences t =
  filter (isJust . find (twins ThisT) . trmArgs . ltAtomic) . filter isLiteral . splitConjuncts .
    if   isNotion t -- notion evidence concerns the first argument.
    then replace ThisT (head $ trmArgs t)
    else id


{- downward closure for definitional evidence. Example:
if we have "natural c= rational c= real" then we do not only know that
a natural number is rational, but also add the info that it is real.-}
closeEvidence :: Definitions -> DefEntry -> DefEntry
closeEvidence dfs def@DefEntry {defEvidence = evidence} = def { defEvidence = newEvidence }
  where
    newEvidence = nubBy twins $ evidence ++ concatMap definitionalEvidence evidence
    definitionalEvidence t@Trm {trId = n} =
      let def = fromJust $ Map.lookup n dfs
          sb  = fromJust $ match (defTerm def) $ fromTo makeU t
      in  map (fromTo fromU . sb) $ defEvidence def
    definitionalEvidence _ = []

    fromTo :: (VariableName -> VariableName) -> Formula -> Formula
    fromTo fn v@Var {varName = vn} = v {varName = fn vn}
    fromTo fn f = mapF (fromTo fn) f

    makeU :: VariableName -> VariableName
    makeU (VarHole nm) = VarU nm
    makeU v = v

    fromU :: VariableName -> VariableName
    fromU (VarU nm) = VarHole nm
    fromU v = v


-- Extraction of Rewrite Rules


extractRewriteRule :: Context -> [Rule]
extractRewriteRule c =
  map (\rl -> rl {Rule.label = Context.name c}) $ dive 0 [] $ Context.formula c
  where
    dive :: Int -> [Formula] -> Formula -> [Rule]
    -- if HeadTerm is reached, discard all collected conditions
    dive n gs (All _ (Iff (Tag HeadTerm Trm {trmName = TermEquality, trmArgs = [_,t]}) f )) =
      dive n gs $ subst t VarEmpty $ inst VarEmpty f
    dive n gs (All _ (Imp (Tag HeadTerm Trm {trmName = TermEquality, trmArgs = [_, t]}) f)) =
      dive n gs $ subst t VarEmpty $ inst VarEmpty f
    -- make universal quantifier matchable
    dive n gs (All _ f) = let nn = VarHole $ Text.pack $ show n in dive (succ n) gs $ inst nn f
    dive n gs (Imp f g) = dive n (splitConjuncts f ++ gs) g -- record conditions
    dive n gs (Tag _ f) = dive n gs f -- ignore tags
    dive n gs (And f g) = dive n gs f ++ dive n gs g
    -- we do not allow rules where the left side is a variable
    dive n gs Trm {trmName = TermEquality, trmArgs = [l@Var{varName},r]} | not (isVarHole varName)
      = return $ Rule l r gs undefined -- the name is filled in later
    dive n gs Trm {trmName = TermEquality, trmArgs = [l@Trm{},r]}
      = return $ Rule l r gs undefined -- the name is filled in later
    dive n gs (Not Trm{}) = mzero
    dive n gs f | isNot f = dive n gs $ albet f -- pushdown negation
    dive _ _ _ = mzero

-- Evaluation for maps and classes

addEvaluation :: DisTree Evaluation -> Formula -> DisTree Evaluation
addEvaluation evaluations f =
  foldr (\eval -> DisTree.insert (evaluationTerm eval) eval) evaluations $
  extractEvaluation evaluations f

extractEvaluation :: DisTree Evaluation -> Formula -> [Evaluation]
extractEvaluation dt = flip runReaderT (0, dt) . dive
  where
    dive (All _ (Iff (Tag HeadTerm Trm {trmName = TermEquality, trmArgs = [_, t]}) f))
      = extractEv id [] $ instWith t f
    dive (All _ f) = freshV dive f
    dive (Imp f g) = dive g
    dive f = extractEv id [] f

extractEv :: (Formula -> Formula)
             -> [Formula]
             -> Formula
             -> ReaderT (Int, DisTree Evaluation) [] Evaluation
extractEv c gs f = extractMapEval c gs f `mplus` extractClassEval c gs f

freshV :: (MonadReader (a, b1) m, Enum a, Show a) =>
          (Formula -> m b2) -> Formula -> m b2
freshV fn f = do -- generate fresh variables
  n <- asks fst; local (\(m,dt) -> (succ m, dt)) $ fn $ inst (VarHole $ Text.pack $ show n) f


extractMapEval :: (Formula -> Formula) -> [Formula] -> Formula
  -> ReaderT (Int, DisTree Evaluation) [] Evaluation
extractMapEval c gs (And g@(Tag Domain _ ) h) =
  extractClassEval c gs g `mplus` extractMapEval c gs h
extractMapEval c gs (And f g) = extractMapEval c gs g
extractMapEval c gs f = dive c gs f
  where
    dive c gs (Imp _ g) = dive c gs g -- ignore ontological assumptions
    dive c gs (Tag Condition (Imp f g)) = dive c (f:gs) g --but add case distinctions
    dive c gs (All _ f) = freshV (dive c gs) f
    dive c gs (And f g) = dive c gs f `mplus` dive c gs g
    dive c gs (Tag Evaluation f@Trm{ trmName = TermEquality, trmArgs = [tr,vl]} ) =
      let nf = c f {trmArgs = [ThisT, vl] }
      in  return $ EV tr nf nf gs
    dive c gs (Exi x (And (Tag Defined f)
      (Tag Evaluation Trm {trmName = TermEquality, trmArgs = [tr, Ind {indIndex = n}]})))
        | n == 0 = extractEv c gs $ dec $ instWith tr f
    dive c gs (Exi x (And f g)) =
      dive (c . dExi x . And f) gs $ inst (declName x) g
    dive _ _ _ = mzero

extractClassEval :: (Formula -> Formula) -> [Formula]-> Formula
  -> ReaderT (Int, DisTree Evaluation) [] Evaluation
extractClassEval c gs (And f g) =
  extractClassEval c gs f `mplus` extractClassEval c gs g
extractClassEval c gs (Tag _ f) = extractClassEval c gs f
extractClassEval c gs (All _ (Iff g@Trm{trmArgs = [_,t]} f )) | isElem g = do
  (n, evals) <- ask
  let nm = VarHole $ Text.pack $ show n; nf = simplifyElementCondition evals $ strip $ inst nm f
  return $ EV (mkElem (mkVar nm) t) (mkPos $ c $ Tag Evaluation nf)(c nf) gs
extractClassEval _ _ f = mzero


simplifyElementCondition :: DisTree Evaluation -> Formula -> Formula
simplifyElementCondition evals = dive
  where
    dive f@Trm {trmArgs = [x,t]} | isElem f = fromMaybe f $ simp f
    dive f@Trm{} = f
    dive f = mapF dive f

    simp f = do
      ev <- DisTree.lookup f evals >>= single; guard (null $ evaluationConditions ev)
      sb <- match (evaluationTerm ev) f; return $ sb $ evaluationNegatives ev

    single [x] = return x; single l = mzero

mkPos :: Formula -> Formula
mkPos = dive
  where
    dive (Exi x f)   = All x $ dive f
    dive (Tag Evaluation f) = f
    dive (And f g) = Imp f $ dive g


instWith :: Formula -> Formula -> Formula
instWith t = subst t VarEmpty . inst VarEmpty
