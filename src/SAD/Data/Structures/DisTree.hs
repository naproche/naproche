{-
Authors: Steffen Frerix (2017 - 2018)

Discrimination tree data structure.
-}

module SAD.Data.Structures.DisTree (
  DisTree,
  empty,
  insert, insertBy,
  lookup,
  find
  ) where

-- Discrimination tree for unification

import SAD.Data.Formula (Formula(..), isTrm)

import Prelude hiding (lookup, head)
import qualified Data.List as L hiding (lookup)
import Control.Monad
import Data.Maybe

data DTree a =
  Node {struct :: Struct, children :: [DTree a]} |
  Leaf {stored :: a}

newtype DisTree a = DT [DTree [a]]

empty :: DisTree a
empty = DT []


{- a sucture element is a variable or a function symbol with identifier and
arity or a generalized constant (i.e. non-matchable free variable) -}
data Struct =
  Variable |
  Function {symbolId :: Int, symbolArity :: Int} |
  GeneralizedConstant String
  deriving Show

isLeaf :: DTree a -> Bool
isLeaf (Leaf _) = True
isLeaf _ = False

{- arity generalized for variables -}
arity :: Struct -> Int
arity Variable = 0
arity (GeneralizedConstant _) = 0
arity (Function _ m) = m

{- move to the next argument by jumping the arity of the current argument -}
jump :: DTree [a] -> [DTree [a]]
jump (Leaf value) = [Leaf value]
jump (Node struct children) = concatMap (jmp (arity struct)) children
  where
    jmp 0 node = [node]
    jmp ar (Node struct children) =
      concatMap (jmp (ar + arity struct - 1)) children

{- test whether a given formula matches a given structure -}
structMatch :: Formula -> Struct -> Bool
structMatch Var{trName = '?':_} Variable = True
structMatch Var{trName = 'x':nm} (GeneralizedConstant s) = nm == s
structMatch Trm{trId = m} (Function n _) = n == m
structMatch _ _ = False

{- during retrieval everything matches a variable -}
retrieveMatch :: Formula -> Struct -> Bool
retrieveMatch _ Variable = True
retrieveMatch f g = structMatch f g

{- compute the structure of a formula -}
toStruct :: Formula -> Struct
toStruct Var {trName = '?':_ } = Variable
toStruct Var {trName = 'x':nm} = GeneralizedConstant nm
toStruct Trm {trId = m, trArgs = ts} = Function m (length ts)

{- arguments generalized for variables -}
args :: Formula -> [Formula]
args Ind{} = []
args Var{} = []
args Trm{trArgs = ts} = ts

{- insert an element into the tree -}
insert :: Formula -> a -> DisTree a -> DisTree a
insert key _ tree | not $ isTrm key = tree
insert key value (DT nodes) = DT $ dive nodes [key]
  where
    dive nodes keylist@(key:ks) = case break (structMatch key . struct) nodes of
      -- if nothing matches -> creat a whole new branch with value at the end
      (_ , [])  -> buildTree keylist value ++ nodes
      (unmatchedNodes, matchedNode : rest) -> unmatchedNodes ++ (
        matchedNode {children = dive (children matchedNode) (args key ++ ks)} :
        rest)
    -- if we reach a leaf -> add the value
    dive [Leaf values] [] = [Leaf (value:values)]

{- build a tree from a list of formulas -}
buildTree :: [Formula] -> a -> [DTree [a]]
buildTree [Top] _ = []
buildTree [Bot] _ = []
buildTree keys value = dtree keys
  where
    dtree (k:ks) = [Node (toStruct k) (dtree $ args k ++ ks)]
    dtree []     = [Leaf [value]]

{- lookup values in a tree. The key for the lookup is the structure of
the given formula. Multiple leafs may match the key. lookup returns all of
their values. -}
lookup :: Formula -> DisTree a -> Maybe [a]
lookup key (DT nodes) = mbConcat $ dive nodes [key]
  where
    dive nodes (Var{trName = '?':_}:ks)
      = let (leafs, newNodes) = L.partition isLeaf $ concatMap jump nodes
         in map stored leafs `mplus` dive newNodes ks
    dive nodes keylist@(k:ks) =
      case dropWhile (not . retrieveMatch k . struct) nodes of
        []  -> mzero -- nothing matches -> key is not in the tree
        matchedNode:rest ->
          dive (children matchedNode) (mbArgs (struct matchedNode) k ++ ks)
          `mplus` dive rest keylist
    dive [Leaf values] [] = return values
    dive [] [] = return []

    mbArgs Variable = const []; mbArgs _ = args

    mbConcat [] = Nothing; mbConcat lst = Just $ concat lst

find :: Formula -> DisTree a -> [a]
find f = fromMaybe [] . lookup f


insertBy :: (a -> Formula) -> a -> DisTree a -> DisTree a
insertBy keyFunction value = insert (keyFunction value) value

{- only for debugging: transform a tree into a readable format -}

showTree :: Show a => DisTree a -> String
showTree (DT []) = ""
showTree (DT [Leaf value]) = "Leaf " ++ show value
showTree (DT (node:rest)) = "\n" ++ unlines (recursor (node:rest))
  where
    recursor [] = []
    recursor [Leaf value] = ["L " ++ show value]
    recursor (node:rest) = helper node ++ recursor rest
    helper (Node struct children) =
      let ([head],stringChildren) = splitAt 1 $ recursor children
          sn = show struct; l = length sn
      in  (sn ++ space (4-l) ++ head) : map ((space 4) ++ ) stringChildren

    space n = replicate n ' '
