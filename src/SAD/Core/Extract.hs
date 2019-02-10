{-
Authors: Steffen Frerix (2017 - 2018)

Extraction of various information from formulas: definitions,
function evaluations, elementhood conditions for sets
-}
{-# LANGUAGE FlexibleContexts #-}

module SAD.Core.Extract (
  addDefinition,
  addEvaluation,
  extractRewriteRule
) where

import SAD.Data.Formula
import SAD.Data.Definition (DefEntry(DE), Definitions, DefType(..), Guards)
import qualified SAD.Data.Definition as Definition
import SAD.Data.Evaluation (Evaluation(EV))
import qualified SAD.Data.Evaluation as Evaluation
import SAD.Data.Text.Context (Context)
import qualified SAD.Data.Text.Context as Context (formula, name)
import SAD.Data.Rules (Rule(Rule))
import qualified SAD.Data.Rules as Rule
import SAD.Core.Base
import SAD.Core.Reduction
import SAD.Prove.Normalize
import qualified SAD.Data.Structures.DisTree as DT
import qualified SAD.Data.Text.Decl as Decl

import qualified Data.IntMap as IM
import Data.List
import Data.Maybe
import Control.Monad.State
import Control.Monad.Reader

import Debug.Trace


-- Definition extraction


{- extract definition from f and add it to the global state -}
addDefinition :: (Definitions, Guards) -> Formula -> (Definitions, Guards)
addDefinition (defs, grds) f = let newDef = extractDefinition defs f in
  (addD newDef defs, addG newDef grds)
  where
    addD df@DE {Definition.term = t} = IM.insert (trId t) df
    addG df@DE {Definition.guards = grd} grds = foldr add grds $ filter isTrm grd

    add guard grds =
      if   head $ fromMaybe [False] $ DT.lookup guard grds
      then grds
      else DT.insert guard True grds

{- Extract definition from a formula. Evidence closure is computed afterwards -}
extractDefinition :: Definitions -> Formula -> DefEntry
extractDefinition defs =
  closeEvidence defs . makeDefinition . dive [] 0
  where
    dive guards _ (All _ (Iff (Tag HeadTerm Trm {trName = "=", trArgs = [_, t]}) f))
      = (guards, instWith ThisT f, Definition, t) -- function definition
    dive guards _ (All _ (Imp (Tag HeadTerm Trm {trName = "=", trArgs = [_, t]}) f))
      = (guards, instWith ThisT f, Signature, t)  -- function sigext
    dive guards _ (Iff (Tag HeadTerm t) f)
      = (guards, f, Definition, t)                -- predicate definition
    dive guards _ (Imp (Tag HeadTerm t) f)
      = (guards, f, Signature,t)                  -- predicate sigext

    -- make a universal quant matchable
    dive guards n (All _ f) = dive guards (succ n) $ inst ('?':show n) f
    dive guards n (Imp g f) = dive (guards ++ deAnd g) n f
    makeDefinition (guards, formula, kind, term) = DE {
      Definition.guards = guards, Definition.formula = formula,
      Definition.kind = kind, Definition.term = term,
      Definition.evidence = extractEvidences term formula,
      Definition.typeLikes = []}


{- get evidence for a defined term from a definitional formula -}
extractEvidences :: Formula -> Formula -> [Formula]
extractEvidences t =
  filter (isJust . find (twins ThisT) . ltArgs) . filter isLiteral . deAnd .
    if   isNotion t -- notion evidence concerns the first argument.
    then replace ThisT (head $ trArgs t)
    else id


{- downward closure for definitional evidence. Example:
if we have "natural c= rational c= real" then we do not only know that
a natural number is rational, but also add the info that it is real.-}
closeEvidence :: Definitions -> DefEntry -> DefEntry
closeEvidence dfs def@DE{Definition.evidence = evidence} = def { Definition.evidence = newEvidence }
  where
    newEvidence = nubBy twins $ evidence ++ concatMap defEvidence evidence
    defEvidence t@Trm {trId = n} =
      let def = fromJust $ IM.lookup n dfs
          sb  = fromJust $ match (Definition.term def) $ fromTo '?' 'u' t
      in  map (fromTo 'u' '?' . sb) $ Definition.evidence def
    defEvidence _ = []


-- Extraction of Rewrite Rules


extractRewriteRule :: Context -> [Rule]
extractRewriteRule c =
  map (\rl -> rl {Rule.label = Context.name c}) $ dive 0 [] $ Context.formula c
  where
    -- if HeadTerm is reached, discard all collected conditions
    dive n gs (All _ (Iff (Tag HeadTerm Trm {trName = "=", trArgs = [_,t]}) f )) =
      dive n gs $ subst t "" $ inst "" f
    dive n gs (All _ (Imp (Tag HeadTerm Trm {trName = "=", trArgs = [_, t]}) f)) =
      dive n gs $ subst t "" $ inst "" f
    -- make universal quantifier matchable
    dive n gs (All _ f) = let nn = '?' : show n in dive (succ n) gs $ inst nn f
    dive n gs (Imp f g) = dive n (deAnd f ++ gs) g -- record conditions
    dive n gs (Tag _ f) = dive n gs f -- ignore tags
    dive n gs (And f g) = dive n gs f ++ dive n gs g
    -- we do not allow rules where the left side is a variable
    dive n gs Trm {trName = "=", trArgs = [l,r]} | head (trName l) /= '?'
      = return $ Rule l r gs undefined -- the name is filled in later
    dive n gs (Not Trm{}) = mzero
    dive n gs f | isNot f = dive n gs $ albet f -- pushdown negation
    dive _ _ _ = mzero

-- Evaluation for functions and sets

addEvaluation evaluations f =
  foldr (\eval -> DT.insert (Evaluation.term eval) eval) evaluations $
  extractEvaluation evaluations f

extractEvaluation :: DT.DisTree Evaluation -> Formula -> [Evaluation]
extractEvaluation dt = flip runReaderT (0, dt) . dive
  where
    dive (All _ (Iff (Tag HeadTerm Trm {trName = "=", trArgs = [_, t]}) f))
      = extractEv id [] $ instWith t f
    dive (All _ f) = freshV dive f
    dive (Imp f g) = dive g
    dive f = extractEv id [] f

extractEv c gs f = extractFunctionEval c gs f `mplus` extractSetEval c gs f

freshV fn f = do -- generate fresh variables
  n <- asks fst; local (\(m,dt) -> (succ m, dt)) $ fn $ inst ('?':show n) f


extractFunctionEval :: (Formula -> Formula) -> [Formula] -> Formula
  -> ReaderT (Int, DT.DisTree Evaluation) [] Evaluation
extractFunctionEval c gs (And g@(Tag Domain _ ) h) =
  extractSetEval c gs g `mplus` extractFunctionEval c gs h
extractFunctionEval c gs (And f g) = extractFunctionEval c gs g
extractFunctionEval c gs f = dive c gs f
  where
    dive c gs (Imp _ g) = dive c gs g -- ignore ontological assumptions
    dive c gs (Tag Condition (Imp f g)) = dive c (f:gs) g --but add case distinctions
    dive c gs (All _ f) = freshV (dive c gs) f
    dive c gs (And f g) = dive c gs f `mplus` dive c gs g
    dive c gs (Tag Evaluation f@Trm{ trName = "=", trArgs = [tr,vl]} ) =
      let nf = c f {trArgs = [ThisT, vl] }
      in  return $ EV tr nf nf gs
    dive c gs (Exi x (And (Tag Defined f)
      (Tag Evaluation Trm {trName = "=", trArgs = [tr, Ind {trIndx = n}]})))
        | n == 0 = extractEv c gs $ dec $ instWith tr f
    dive c gs (Exi x (And f g)) =
      dive (c . dExi x . And f) gs $ inst (Decl.name x) g
    dive _ _ _ = mzero

    deConj (And f g) = deConj f ++ deConj g; deConj f = [f]

extractSetEval :: (Formula -> Formula) -> [Formula]-> Formula
  -> ReaderT (Int, DT.DisTree Evaluation) [] Evaluation
extractSetEval c gs (And f g) =
  extractSetEval c gs f `mplus` extractSetEval c gs g
extractSetEval c gs (Tag _ f) = extractSetEval c gs f
extractSetEval c gs (All _ (Iff g@Trm{trArgs = [_,t]} f )) | isElem g = do
  (n, evals) <- ask
  let nm = '?':show n; nf = simplifyElementCondition evals $ strip $ inst nm f
  return $ EV (zElem (zVar nm) t) (mkPos $ c $ Tag Evaluation nf)(c nf) gs
extractSetEval _ _ f = mzero


simplifyElementCondition evals = dive
  where
    dive f@Trm {trArgs = [x,t]} | isElem f = fromMaybe f $ simp f
    dive f@Trm{} = f
    dive f = mapF dive f

    simp f = do
      ev <- DT.lookup f evals >>= single; guard (null $ Evaluation.conditions ev)
      sb <- match (Evaluation.term ev) f; return $ sb $ Evaluation.negatives ev

    single [x] = return x; single l = mzero

mkPos = dive
  where
    dive (Exi x f)   = All x $ dive f
    dive (Tag Evaluation f) = f
    dive (And f g) = Imp f $ dive g


instWith t = subst t "" . inst ""
