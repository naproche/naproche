{-
Authors: Steffen Frerix (2017 - 2018)

Discrimination tree data structure.
-}

module Alice.Data.Structures.DisTree (
  DisTree,
  empty,
  insert,
  lookup,
  find
  ) where

-- Discrimination tree for unification

import Alice.Data.Formula (Formula(..), isTrm)

import Prelude hiding (lookup)
import qualified Data.List as L hiding (lookup)
import Control.Monad
import Data.Maybe
import Debug.Trace

data DTree a = Node {struct :: Struct, children :: [DTree a]} | Leaf {stored :: a}

newtype DisTree a = DT [DTree [a]]

empty = DT []


-- a structure element is a variable or a function symbol with identifier and arity or a generalized constant
data Struct = Vr | Fun {fId :: Int, ar :: Int} | GC String deriving Show

isLeaf (Leaf _) = True
isLeaf _ = False

{- arity generalized for variables -}
arity :: Struct -> Int
arity Vr = 0
arity (GC _) = 0
arity (Fun n m) = m

{- move to the next argument by jumping the arity of the current argument -}
jump :: DTree [a] -> [DTree [a]]
jump (Leaf a) = [Leaf a]
jump (Node st chld) = concatMap (jmp (arity st)) chld
  where
    jmp 0 nd = [nd]
    jmp ar (Node st chld) = concatMap (jmp (ar + arity st - 1)) chld

structMatch :: Formula -> Struct -> Bool
structMatch Var{trName = '?':_} Vr = True
structMatch Var{trName = 'x':nm} (GC s) = nm == s
structMatch (Trm{trId = m}) (Fun n _) = n == m
structMatch _ _ = False

retrMatch :: Formula -> Struct -> Bool
retrMatch _ Vr = True
retrMatch f g = structMatch f g


toStruct :: Formula -> Struct
toStruct Var {trName = '?':_ } = Vr
toStruct Var {trName = 'x':nm} = GC nm
toStruct Trm {trId = m, trArgs = ts} = Fun m (length ts)

{- arguments generalized for variables -}
args :: Formula -> [Formula]
args Ind{} = []
args Var{} = []
args Trm{trArgs = ts} = ts

{- insert an element into the tree -}
insert :: Formula -> a -> DisTree a -> DisTree a
insert f _ t | not $ isTrm f = t
insert f a (DT nds) = DT $ dive nds [f]
  where
    dive nds ls@(f:fs) = case break (structMatch f . struct) nds of
      (_ , [])  -> dtree ls a ++ nds
      (pre, nd : post) -> pre ++ (nd {children = dive (children nd) (args f ++ fs)} : post)
    dive [Leaf as] [] = [Leaf (a:as)]

{- build a tree from a list of formulas -}
dtree :: [Formula] -> a -> [DTree [a]]
dtree [Top] _ = []
dtree [Bot] _ = []
dtree fs a = tr fs
  where
    tr (f:fs) = [Node (toStruct f) (tr $ args f ++ fs)]
    tr []     = [Leaf [a]]

{- lookup an element from the tree. The key for the lookup is the structure of the
   formula f -}
lookup :: Formula -> DisTree a -> Maybe [a]
lookup f (DT nds) = mbConcat $ dive nds [f]
  where
    dive nds (Var{trName = '?':_}:fs)
      = let (lfs, nnds) = L.partition isLeaf $ concatMap jump nds
         in map stored lfs `mplus` dive nnds fs
    dive nds ls@(f:fs) = case dropWhile (not . retrMatch f . struct) nds of
      []  -> mzero
      nd:rst -> dive (children nd) (mbArgs (struct nd) f ++ fs) `mplus` dive rst ls
    dive [Leaf as] [] = return as
    dive [] [] = return []

    mbArgs Vr = const []; mbArgs _ = args

    mbConcat [] = Nothing; mbConcat lst = Just $ concat lst

find f = fromMaybe [] . lookup f

{- only for debugging: transform a tree into a readable format -}

showTree :: Show a => DisTree a -> String
showTree (DT []) = ""
showTree (DT [Leaf a]) = "Leaf " ++ show a
showTree (DT (nd:nds)) = "\n" ++ unlines (recursor (nd:nds))
  where
    recursor [] = []
    recursor [Leaf a] = ["L " ++ show a]
    recursor (nd:nds) = helper nd ++ recursor nds
    helper (Node st chld) = let ([hd],str) = splitAt 1 $ recursor chld; sn = show st; l = length sn in (sn ++ space (4-l) ++ hd) : map ((++) (space 4)) str

    space n = take n $ repeat ' '
