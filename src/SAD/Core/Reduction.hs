{-
Authors: Steffen Frerix (2017 - 2018)

Ontological reduction.
-}

module SAD.Core.Reduction (ontoReduce) where

import SAD.Data.Formula
import SAD.Data.Definition (DefEntry(DE), Definitions, Guards, isGuard)
import qualified SAD.Data.Definition as Definition
import SAD.Core.Base
import SAD.Prove.Normalize

import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IM
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Data.List
import Data.Maybe
import Control.Monad.Trans.Class
import Control.Monad.State
import Control.Monad.Trans.Maybe

{- the names used in this implementation direclty correspond to the concepts
occuring in the description and correctness proof of the algorithm. -}

type Position = [Int]
{- We are only interested in atomic positions, therefore a position here only records
the path we take at a binary operator. Unary operators (Not, All, Exi) are not reflected
in the position.-}

ontoReduce dfs grds skolem f =
  let (conjuncts, newSkolem) = ontoPrep skolem f
      reducedConjuncts = map (boolSimp . ontoRed dfs grds) conjuncts
      reducedFormula = uClose [] $ foldr blAnd Top reducedConjuncts
  in (reducedFormula, newSkolem)

{- Ontologically reduces a given formula f. Notice that by virtue of preparation with
SAD.Prove.Normalize.ontoPrep, we may assume the following for the given formula:
  * And, Or, Not, Trm and Var are the only formula constructors appearing in f (in particular no quantifiers can appear)
  * negation only appears on the literal level-}
ontoRed :: Definitions -> Guards -> Formula -> Formula
ontoRed dfs grds f = dive [] f
  where
    dive position (And g h) =
      And (dive (0:position) g) (dive (1:position) h)
    dive position (Or g h) =
      Or (dive (0:position) g) (dive (1:position) h)
    dive position (Not t@Trm{})
      | isGuard t grds = Not $ tryEliminating t position
    dive _ f = f
    
    tryEliminating t position
      | t `isEliminableAt` reverse position = Top
      | otherwise = t


    isEliminableAt t position =
      let relevantPositions = filter (/= position) atomicPositions
      in  all (\g -> t `isEliminableFor` g || g `isEliminableFor` t) $
            map (dereference f) relevantPositions

    isEliminableFor g h =
      let gFreeVars = freeVars g
          relevantPositions = map fst $ filter (\(pos, name) -> Set.member name gFreeVars) $
            directArgumentPositions h
          subParticleCondition = all (\k -> isEliminableFor g k) $ subParticles h
          thisParticleCondition =
            null relevantPositions ||
            (h `satisfiesDisjointnessConditionFor` g &&
              all (\pos -> isCoveredByIn pos g h) relevantPositions)
      in  thisParticleCondition && subParticleCondition

    isCoveredByIn position g h = -- disjointness condition is already checked above
      let generalPosGuards = generalPositionGuards position h
          allPosGuards = allPositionGuards position h
          differentFromG = filter (not . hasSameSyntacticStructureAs g) allPosGuards
          relevantAtoms = concatMap atoms differentFromG
      in  g `isElemOf` generalPosGuards &&
            all (\g' -> g `isEliminableFor` g' || g' `isEliminableFor` g) relevantAtoms

    satisfiesDisjointnessConditionFor h g =
      let relevantGuards = filter (hasSameSyntacticStructureAs g) $ generalGuards h
          relevantSets = map freeVars relevantGuards
      in  checkDisjointness relevantSets
      where
        checkDisjointness [] = True
        checkDisjointness (g:rst) =
          all (Set.null . Set.intersection g) rst && checkDisjointness rst


    atomicPositions = atomicPos f

    --- extracting guards

    allGuards h
      | isSkolem h = []
      | otherwise =
          let def = fromJust $ IM.lookup (trId h) dfs
              sb  = fromJust $ match (Definition.term def) h
          in  map sb $ Definition.guards def
    
    generalGuards h
      | isSkolem h = []
      | otherwise =
          let def = fromJust $ IM.lookup (trId h) dfs
              zipped = zip (allGuards h) (Definition.guards def)
          in  map fst $ filter (uncurry hasSameSyntacticStructureAs) zipped

    allPositionGuards pos h
      | isSkolem h = []
      | otherwise =
          let def = fromJust $ IM.lookup (trId h) dfs
              posName = trName $ ((trArgs $ Definition.term def)!!pos)
          in  filter (Set.member posName . freeVars) $ Definition.guards def

    generalPositionGuards pos h
      | isSkolem h = []
      | otherwise =
          let def = fromJust $ IM.lookup (trId h) dfs
              positionGuards = allPositionGuards pos h
              sb = fromJust $ match (Definition.term def) h
              zipped = zip (map sb positionGuards) positionGuards
          in  map fst $ filter (uncurry hasSameSyntacticStructureAs) zipped


--- auxiliary functions

atomicPos :: Formula -> [Position]
atomicPos = map reverse . dive []
  where
    dive pos (And f g) = dive (0:pos) f ++ dive (1:pos) g
    dive pos (Or f g) = dive (0:pos) f ++ dive (1:pos) g
    dive pos (Iff f g) = dive (0:pos) f ++ dive (1:pos) g
    dive pos (Imp f g) = dive (0:pos) f ++ dive (1:pos) g
    dive pos Trm{} = [pos]
    dive pos Top = [pos]
    dive pos Bot = [pos]
    dive pos f = foldF (dive pos) f

directArgumentPositions :: Formula -> [(Int, String)]
directArgumentPositions = dive 0 . arguments
  where
    dive _ [] = []
    dive pos (x:xs) = case x of
      Var{trName = name} -> (pos, name) : dive (succ pos) xs
      _ -> dive (succ pos) xs
  
dereference :: Formula -> Position -> Formula
dereference = dive
  where
    dive (And f g) pos = binary pos f g
    dive (Imp f g) pos = binary pos f g
    dive (Iff f g) pos = binary pos f g
    dive (Or f g) pos = binary pos f g
    dive t@Trm{} [] = t
    dive (All _ f) pos = dive f pos
    dive (Exi _ f) pos = dive f pos
    dive (Not f) pos = dive f pos
    dive (Tag _ f) pos = dive f pos
    dive Top [] = Top
    dive Bot [] = Bot

    binary (0:pos) f g = dive f pos
    binary (1:pos) f g = dive g pos

subParticles :: Formula -> [Formula]
subParticles = filter isTrm . arguments


freeVars :: Formula -> Set String
freeVars Var {trName = name} = Set.singleton name
freeVars f = foldF freeVars f

atoms :: Formula -> [Formula]
atoms f@Trm{} = [f]
atoms f = foldF atoms f

hasSameSyntacticStructureAs :: Formula -> Formula -> Bool
hasSameSyntacticStructureAs f g = evalState (dive f g) Map.empty
  where
    dive :: Formula -> Formula -> State (Map String String) Bool
    dive Var{trName = name1} Var{trName = name2} = do
      value <- gets $ Map.lookup name1
      case value of
        Nothing -> do
          isInjective <- gets $ notElem name2 . map snd . Map.assocs
          modify (Map.insert name1 name2) >> return isInjective
        Just name -> if name == name2 then return True else return False
    dive Trm{trId = id1, trArgs = args1} Trm{trId = id2, trArgs = args2}
      | id1 == id2 = pairs args1 args2
    dive _ _ = return False
    pairs [] [] = return True
    pairs (arg1:rst1) (arg2:rst2) = liftM2 (&&) (dive arg1 arg2) (pairs rst1 rst2)

-- special elementhood predicate for guards

isElemOf :: Formula -> [Formula] -> Bool
isElemOf g [] = False
isElemOf g (h:hs) = g `twins` h || isElemOf g hs


-- generalization of term arguments

arguments :: Formula -> [Formula]
arguments Top = []; arguments Bot = []
arguments f = trArgs f 