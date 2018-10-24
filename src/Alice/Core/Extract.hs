{-
Authors: Steffen Frerix (2017 - 2018)

Extraction of various information from formulas: definitions,
function evaluations, elementhood conditions for sets
-}
{-# LANGUAGE FlexibleContexts #-}

module Alice.Core.Extract (
  addDefinition,
  addEvaluation,
  extractRewriteRule
) where

import Alice.Data.Base
import Alice.Data.Formula
import Alice.Data.Kit
import Alice.Data.Text
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
addDefinition f = do
  defs <- askGlobalState definitions; let newDef = extractDefinition defs f
  updateGlobalState (\rs -> rs {definitions = add newDef (definitions rs)})
  where
    add df@DE {dfTerm = t} = IM.insert (trId t) df

{- Extract definition from a formula. Evidence closure and type-likes are
computed afterwards -}
extractDefinition :: Definitions -> Formula -> DefEntry
extractDefinition defs =
  closeEvidence defs . addTypeLikes defs . makeDefinition . dive [] 0
  where
    dive guards _ (All _ (Iff (Tag DHD Trm {trName = "=", trArgs = [_, t]}) f))
      = (guards, instWith ThisT f, Definition, t) -- function definition
    dive guards _ (All _ (Imp (Tag DHD Trm {trName = "=", trArgs = [_, t]}) f)) 
      = (guards, instWith ThisT f, Signature, t)  -- function sigext
    dive guards _ (Iff (Tag DHD t) f)
      = (guards, f, Definition, t)                -- predicate definition
    dive guards _ (Imp (Tag DHD t) f)
      = (guards, f, Signature,t)                  -- predicate sigext

    -- make a universal quant matchable
    dive guards n (All _ f) = dive guards (succ n) $ inst ('?':show n) f 
    dive guards n (Imp g f) = dive (guards ++ deAnd g) n f
    makeDefinition (guards, formula, kind, term) = DE {
      dfGrds = guards, dfForm = formula,
      dfType = kind, dfTerm = term,
      dfEvid = extractEvidences term formula,
      dfTplk = []}


{- get evidence for a defined term from a definitional formula -}
extractEvidences :: Formula -> Formula -> [Formula]
extractEvidences t = 
  filter (isJust . find (twins ThisT) . ltArgs) . filter isLtrl . deAnd .
    if   isNtn t -- notion evidence concerns the first argument.
    then replace ThisT (head $ trArgs t)
    else id

{- computes and adds type-likes for ontological reduction to a definition.-}
addTypeLikes :: Definitions -> DefEntry -> DefEntry
addTypeLikes dfs def = def {dfTplk = tp_likes $ dfGrds def}
  where
    tp_likes fs =
      rn_classes [] $ 
        filter (\g -> isTrm g && no_sklm g && type_like dfs g fs) fs

    rn_classes _ [] = []
    rn_classes cl (t:ts) = case break (\t' -> trId t' == trId t) ts of
      (pre,[])      -> (t:cl): rn_classes [] pre
      (pre,t':post) -> rn_classes (t':cl) (t:pre ++ post)

    no_sklm Var{} = True
    no_sklm Trm {trName = 't':'s':'k':_} = False
    no_sklm f = allF no_sklm f


{- downward closure for definitional evidence. Example:
if we have "natural c= rational c= real" then we do not only know that
a natural number is rational, but also add the info that it is real.-}
closeEvidence :: Definitions -> DefEntry -> DefEntry
closeEvidence dfs def@DE{dfEvid = evidence} = def { dfEvid = newEvidence }
  where
    newEvidence = nubBy twins $ evidence ++ concatMap defEvidence evidence
    defEvidence t@Trm {trId = n} =
      let def = fromJust $ IM.lookup n dfs
          sb  = fromJust $ match (dfTerm def) $ fromTo '?' 'u' t
      in  map (fromTo 'u' '?' . sb) $ dfEvid def
    defEvidence _ = []


-- Extraction of Rewrite Rules


extractRewriteRule :: Context -> [Rule]
extractRewriteRule c = 
  map (\rl -> rl {rlLabl = cnName c}) $ dive 0 [] $ cnForm c
  where
    -- if DHD is reached, discard all collected conditions
    dive n gs (All _ (Iff (Tag DHD Trm {trName = "=", trArgs = [_,t]}) f )) 
      = dive n gs $ subst t "" $ inst "" f
    dive n gs (All _ (Imp (Tag DHD Trm {trName = "=", trArgs = [_, t]}) f))
      = dive n gs $ subst t "" $ inst "" f
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

addEvaluation dt f = 
  foldr (\eval -> DT.insert (evTerm eval) eval) dt $ extractEvaluation dt f

extractEvaluation :: DT.DisTree Eval -> Formula -> [Eval]
extractEvaluation dt = flip runReaderT (0, dt) . dive
  where
    dive (All _ (Iff (Tag DHD Trm {trName = "=", trArgs = [_, t]}) f))
      = extractEv id [] $ instWith t f
    dive (All _ f) = freshV dive f
    dive (Imp f g) = dive g
    dive f = extractEv id [] f

extractEv c gs f = extractFunctionEval c gs f `mplus` extractSetEval c gs f

freshV fn f = do -- generate fresh variables
  n <- asks fst; local (\(m,dt) -> (succ m, dt)) $ fn $ inst ('?':show n) f


extractFunctionEval :: (Formula -> Formula) -> [Formula] -> Formula
  -> ReaderT (Int, DT.DisTree Eval) [] Eval
extractFunctionEval c gs (And g@(Tag DDM _ ) h) =
  extractSetEval c gs g `mplus` extractFunctionEval c gs h
extractFunctionEval c gs (And f g) = extractFunctionEval c gs g
extractFunctionEval c gs f = dive c gs f
  where
    dive c gs (Imp _ g) = dive c gs g -- ignore ontological assumptions
    dive c gs (Tag DCD (Imp f g)) = dive c (f:gs) g --but add case distinctions
    dive c gs (All _ f) = freshV (dive c gs) f
    dive c gs (And f g) = dive c gs f `mplus` dive c gs g
    dive c gs (Tag DEV f@Trm{ trName = "=", trArgs = [tr,vl]} ) =
      let nf = c f {trArgs = [ThisT, vl] }
      in  return $ EV tr nf nf gs
    dive c gs (Exi x (And (Tag DEF f) 
      (Tag DEV Trm {trName = "=", trArgs = [tr, Ind n]})))
        | n == 0 = extractEv c gs $ dec $ instWith tr f
    dive c gs (Exi x (And f g)) = dive (c . zExi x . And f) gs $ inst x g
    dive _ _ _ = mzero

    deConj (And f g) = deConj f ++ deConj g; deConj f = [f]

extractSetEval :: (Formula -> Formula) -> [Formula]-> Formula
  -> ReaderT (Int, DT.DisTree Eval) [] Eval
extractSetEval c gs (And f g) =
  extractSetEval c gs f `mplus` extractSetEval c gs g
extractSetEval c gs (Tag _ f) = extractSetEval c gs f
extractSetEval c gs (All _ (Iff g@Trm{trArgs = [_,t]} f )) | isElem g = do
  (n, evals) <- ask
  let nm = '?':show n; nf = simplifyElementCondition evals $ strip $ inst nm f
  return $ EV (zElem (zVar nm) t) (mkPos $ c $ Tag DEV nf)(c nf) gs
extractSetEval _ _ f = mzero


simplifyElementCondition evals = dive
  where
    dive f@Trm {trArgs = [x,t]} | isElem f = fromMaybe f $ simp f
    dive f@Trm{} = f
    dive f = mapF dive f

    simp f = do
      ev <- DT.lookup f evals >>= single; guard (null $ evCond ev)
      sb <- match (evTerm ev) f; return $ sb $ evNeg ev

    single [x] = return x; single l = mzero

mkPos = dive
  where
    dive (Exi x f)   = All x $ dive f
    dive (Tag DEV f) = f
    dive (And f g) = Imp f $ dive g


instWith t = subst t "" . inst ""
