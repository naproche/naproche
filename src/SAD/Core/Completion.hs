{-
Author: Annika Hennes (2019)

Executes Knuth-Bendix completion on a term rewriting system
-}

{-# LANGUAGE OverloadedStrings #-}

module SAD.Core.Completion
  (Equation(..), toFormula, completeAndSimplify, isConfluent, rewriter
  , allCriticalPairs
  ) where

import SAD.Data.Formula
import SAD.Core.Rewrite
import SAD.Prove.Unify


import SAD.Helpers

import Data.List
import Data.Maybe
import Data.Function (on)
import qualified Data.Map as Map
import Data.Text.Lazy (Text)
import qualified Data.Text.Lazy as Text

data Equation = Equation Formula Formula
  deriving (Eq, Ord)

instance Show Equation where
    show (Equation l r) = show l ++ " = " ++ show r

toFormula :: Equation -> Formula
toFormula (Equation lhs rhs) = Trm TermEquality [lhs, rhs] [] EqualityId


{-adding rules respecting a given ordering-}
normalizeAndOrient :: (Formula -> Formula -> Bool)
                     -> [Equation]
                     -> Equation
                     -> Maybe (Formula, Formula)
normalizeAndOrient ord rules (Equation s t) =
  let nfs = rewriter rules s
      nft = rewriter rules t
  in if (ord nfs nft) then return (nfs,nft)
                      else if (ord nft nfs) then return (nft,nfs)
                                            else Nothing


{-help function for updating the three lists in complete-}
updateTrip :: Maybe (Formula,Formula)
           -> ([Equation],[Equation],[Equation])
           -> ([Equation],[Equation],[Equation])
updateTrip (Just (s,t)) (eqs,def,eq:ocrits)
  | twins s t = (eqs,def,ocrits)
  | otherwise =
      let eq' = Equation s t
          eqs' = eq':eqs
      in (eqs',def,ocrits ++ foldr ((++) . (criticalPairs  eq')) [] eqs')
updateTrip _ (eqs,def,eq:ocrits) = (eqs,eq:def,ocrits)
updateTrip _ _ = error "updateTrip: no critical pairs"


{-basic completion of a term rewriting system-}
complete :: (Formula -> Formula -> Bool)
         -> ([Equation], [Equation], [Equation])
         -> [Equation]
complete ord (eqs,def,eq:ocrits) =
  let st = normalizeAndOrient ord eqs eq
      trip = updateTrip st (eqs,def,eq:ocrits)
  in complete ord trip
complete ord (eqs,def,_)
  | def == [] = eqs
  | otherwise =
      let e = maybeToList (find (isJust . normalizeAndOrient ord eqs) def)
      in if e == [] then error "complete: non-orientable equation" --prevent infinite loop
                    else complete ord (eqs, (nub def) \\ e,e)


{-removing redundant rules from a completed term rewriting system-}
interreduce :: [Equation] -> [Equation]
interreduce = dive []
  where
    dive dun eqs = case eqs of
        (Equation l r):oeqs ->
            let dun' = if twins (rewriter (dun ++ oeqs) l) l
                        then (Equation l (rewriter (dun ++ eqs) r)):dun
                        else dun
            in dive dun' oeqs
        [] -> reverse dun


{-gets a list of strings as weights (descending weights) and completes and interreduces a term rewriting system-}
completeAndSimplify :: [Text] -> [Equation] -> [Equation]
completeAndSimplify wts eqs = (interreduce . (complete ord)) (eqs',[], allCriticalPairs eqs')
  where
    ord = lpoGe (weight wts)
    eqs' = catMaybes $ map help_normalize eqs
    help_normalize fml = normalizeAndOrient ord [] fml >>= pure . uncurry Equation


{-tests whether the critical pairs in a term rewriting system are joinable-}
confluence_crit_pairs :: [Equation] -> [Equation] -> Bool
confluence_crit_pairs cp trs = all (\(Equation l r) -> ((==) `on` (rewriter trs)) l r) cp


{-tests whether a terminating term rewriting system is confluent-}
isConfluent :: [Equation] -> Bool
isConfluent trs = confluence_crit_pairs (allCriticalPairs trs) trs


{-tests whether x occurs strictly before y in list-}
earlier :: Ord a => [a] -> a -> a -> Bool
earlier lst = let m = Map.fromList $ zip lst [(0::Int)..]
  in \a b -> case Map.lookup a m of
    Nothing -> False
    Just n -> case Map.lookup b m of
        Nothing -> True
        Just m -> n < m


{-order of precedence in a list-}
weight :: Ord a => [a] -> a -> a -> Bool
weight lis f g = earlier lis g f


----Rewriting

--modified unification algorithm
--instantiating left-hand side of a formula to a term

{-updating substitution function-}
term_match :: Maybe (Formula -> Maybe Formula)
           -> [(Formula, Formula)]
           -> Maybe (Formula -> Maybe Formula)
term_match env [] = env
term_match env ((a,b):oth) =
  case (a,b) of
    (Trm {trmName = f, trmArgs = fargs}, Trm {trmName = g, trmArgs = gargs})
      -> if f == g && length fargs == length gargs
           then term_match env $ zip fargs gargs ++ oth
           else Nothing
    (Var {varName = vn} ,t) | case vn of VarHole _ -> True; VarU _ -> True; _ -> False
      -> case env of
           Just env'
             -> case env' a of
                  Nothing -> term_match
                    (Just (\c -> if c == a then Just t else env' c)) oth
                  Just b -> if b == t then term_match env oth
                                      else Nothing
           Nothing -> Nothing
    _ -> Nothing


{-term substitution-}
tsubst :: (Formula -> Maybe Formula)
       -> Formula
       -> Formula
tsubst sfn tm =
  case tm of
    Var {varName = vn} | case vn of VarHole _ -> True; VarU _ -> True; _ -> False
      -> case sfn tm of
           Just sub -> sub
           _-> tm
    Trm {trmName = f, trmArgs = args, trmId = n}
      -> zTrm n f (map (tsubst sfn) args)
    _ -> error "tsubst: input is not a term"


{-tries to find a rewrite rule in eqs that can be applied at the first position of some term t-}
rewrite1 :: [Equation] -> Formula -> Maybe Formula
rewrite1 eqs t =
  case eqs of
  (Equation l r):oeqs ->
    let trmM = term_match (Just (\ a -> Nothing)) [(l,t)]
    in case trmM of
         Just fn -> Just (tsubst fn r)
         Nothing -> rewrite1 oeqs t
  _ -> Nothing


{-rewriting of arbitrary terms-}
rewriter :: [Equation] -> Formula -> Formula
rewriter eqs tm = case rewrite1 eqs tm of
    Just r -> rewriter eqs r
    Nothing -> case tm of
        Trm {trmName = f, trmArgs = args, trmId = n} ->
            let newArgs = map (rewriter eqs) args
                tm' = zTrm n f newArgs
            in if tm' == tm then tm else rewriter eqs tm'
        _ -> tm


{-rename variables occurring in two terms such that they have no free variables in common-}
renamepair :: Equation -> Equation -> (Equation, Equation)
renamepair (Equation l1 r1) (Equation l2 r2) =
  let freeVars1 = fvToVarList $ allFree [] l1 <> allFree [] r1
      freeVars2 = fvToVarList $ allFree [] l2 <> allFree [] r2
      (nms1,nms2) = splitAt (length freeVars1)
        $ map (\n -> zVar (VarHole $ Text.pack $ 'a' : show n))
          [0..(length freeVars1 + length freeVars2 - 1)]
      l1' = substs l1 freeVars1 nms1
      r1' = substs r1 freeVars1 nms1
      l2' = substs l2 freeVars2 nms2
      r2' = substs r2 freeVars2 nms2
  in (Equation l1' r1', Equation l2' r2')


--computing all critical pairs

{-finds all critical overlaps between a left-hand side of a rule and another term-}
overlaps :: (Formula, Formula)
         -> Formula
         -> (Maybe (Formula -> Formula) -> Formula -> Maybe Formula)
         -> [Formula]
overlaps (l,r) = dive
  where
    dive tm@(Trm _ args _ _) rfn = listcases (\i a -> rfn i $ tm {trmArgs = a}) args
                                ++ (maybeToList $ rfn (unify l tm) r)
    dive _ _ = []

    listcases _ [] = []
    listcases rfn (h:t) = dive h (\i h' -> rfn i $ h':t)
                       ++ listcases (\i t' -> rfn i $ h:t') t


crit1 :: Equation -> Equation -> [Formula]
crit1 (Equation l1 r1) (Equation l2 r2) =
  overlaps (l1,r1) l2 (\ unifct t ->  unifct <*> pure (zEqu t r2))


{-computes all critical pairs of two formulas-}
criticalPairs :: Equation -> Equation -> [Equation]
criticalPairs fma fmb = map fromFormula $
  let (fm1,fm2) = renamepair fma fmb in
  if twins (toFormula fma) (toFormula fmb)
    then crit1 fm1 fm2
    else union (crit1 fm1 fm2) (crit1 fm2 fm1)
  where
    fromFormula (Trm TermEquality [l,r] _ EqualityId) = Equation l r
    fromFormula _ = error "fromFormula: cannot happen"


{-computes all critical pairs of a term rewriting system-}
allCriticalPairs :: [Equation] -> [Equation]
allCriticalPairs trs = nubOrd $ concat $ [criticalPairs a b | (a:rest) <- tails trs, b <- (a:rest)]