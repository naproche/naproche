{-
Authors: Steffen Frerix (2017 - 2018)

Ontological reduction.
-}

module SAD.Core.Reduction (ontoReduce) where

import SAD.Data.Formula
import SAD.Data.Definition (DefEntry(DE), Definitions)
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

import Debug.Trace


{- some notes :

      * We are only interested in atomic positions, therefore a position here only records
        the path we take at a binary operator. Unary operators (Not, All, Exi) are not reflected
        in the position.

-}
type Position = [Int]


ontoReduce dfs skolem f =
  let (conjuncts, nsk) = ontoPrep skolem f; inter = map (boolSimp . ontoRed dfs) conjuncts; red = uClose [] $ foldr blAnd Top inter
  in (red, nsk)

{- takes a list of formulas that represents a disjuction of formulas. If a
disjunct is a literal, we check whether it is eliminable for the rest. All
eliminable literals are deleted and the universal closure is formed. -}
ontoRed :: Definitions -> Formula -> Formula
ontoRed dfs f = {-trace ("\nreducing " ++ show f) $-} dive [] f
  where
    dive position (And g h) =
      And (dive (0:position) g) (dive (1:position) h)
    dive position (Or g h) =
      Or (dive (0:position) g) (dive (1:position) h)
    dive position (Not t@Trm{}) = Not $ tryEliminating t position
    dive _ f = f
    
    tryEliminating t position
      | t `isEliminableAt` reverse position = Top
      | otherwise = t


    isEliminableAt t position =
      let relevantPositions = filter (/= position) atomicPositions
          res = all (\g -> t `isEliminableFor` g || g `isEliminableFor` t) $
            map (dereference f) relevantPositions
      in  {-trace ("check eliminability of " ++ show t ++ " yielded " ++ show res)-} res

    isEliminableFor g h =
      let gFreeVars = freeVars g
          relevantPositions = map fst $ filter (\(pos, name) -> Set.member name gFreeVars) $
            directArgumentPositions h
          subParticleCondition = all (\k -> isEliminableFor g k) $ subParticles h
          thisParticleCondition =
            if   null relevantPositions
            then True
            else h `satisfiesDisjointnessConditionFor` g &&
                 all (\pos -> isCoveredByIn pos g h) relevantPositions
          res = thisParticleCondition && subParticleCondition
      in  {-trace ("check eliminability of " ++ show g ++ " for " ++ show h ++ " yielded " ++ show res)-} res

    isCoveredByIn position g h = -- disjointness condition is already checked above
      let generalPosGuards = generalPositionGuards position h
          allPosGuards = allPositionGuards position h
          differentFromG = filter (not . hasSameSyntacticStructureAs g) allPosGuards
          res1 = g `isElemOf` generalPosGuards
          res2 = all (\g' -> g `isEliminableFor` g' || g' `isEliminableFor` g) differentFromG
          res  = res1 && res2
      in {-trace ("check " ++ show position ++ " is covered by " ++ show g ++ " in " ++ show h ++ " is " ++ show res ++ "\n    " ++ show g ++ " is guard " ++ show res1 ++ "; guards are " ++ show generalPosGuards)-} res

    satisfiesDisjointnessConditionFor h g =
      let relevantGuards = filter (hasSameSyntacticStructureAs g) $ generalGuards h
          relevantSets = map freeVars relevantGuards
          res = checkDisjointness relevantSets
      in  {-trace ("disjointness condition for " ++ show g ++ " is satisfied by " ++ show h ++ " is " ++ show res)-} res
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
          in  {-trace ("posName of " ++ show pos ++ " is " ++ show posName) $-} filter (Set.member posName . freeVars) $ Definition.guards def

    generalPositionGuards pos h
      | isSkolem h = []
      | otherwise =
          let def = fromJust $ IM.lookup (trId h) dfs
              positionGuards = allPositionGuards pos h
              sb = fromJust $ match (Definition.term def) h
              zipped = zip (map sb positionGuards) positionGuards
          in  {-trace ("allPosguards for " ++ show h ++ " at " ++ show pos ++ " are " ++ show positionGuards) $-} map fst $ filter (uncurry hasSameSyntacticStructureAs) zipped

  



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
directArgumentPositions f = dive 0 . arguments $ f
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

subParticles f = filter isTrm . arguments $ f


freeVars :: Formula -> Set String
freeVars Var {trName = name} = Set.singleton name
freeVars f = foldF freeVars f

hasSameSyntacticStructureAs :: Formula -> Formula -> Bool
hasSameSyntacticStructureAs f g = fst $ runState (dive f g) Map.empty
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