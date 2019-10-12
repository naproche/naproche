{-
Authors: Steffen Frerix (2017 - 2018)

Discrimination tree data structure.
-}

{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}

module SAD.Data.Structures.DisTree (
  DisTree,
  empty,
  insert, insertBy,
  lookup,
  find,
  showTree
  ) where

-- Discrimination tree for unification

import SAD.Data.Formula (Formula(..))

import Prelude hiding (lookup, head)
import qualified Data.List as L
import Data.Maybe
import SAD.Data.Terms (TermId)
import SAD.Data.VarName
import Data.Text.Lazy (Text)

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
  Function {symbolId :: TermId, symbolArity :: Int} |
  GeneralizedConstant Text
  deriving Show

{- move to the next argument by jumping the arity of the current argument -}
jump :: DTree [a] -> [DTree [a]]
jump (Leaf value) = [Leaf value]
jump (Node struct children) = children >>= jmp (arity struct)
  where
    jmp 0 node = [node]
    jmp ar (Node struct children) = children >>= jmp (ar + arity struct - 1)
    jmp _ (Leaf _) = error "Inconsistency in DisTree"

    arity Variable = 0
    arity (GeneralizedConstant _) = 0
    arity (Function _ m) = m

{- test whether a given formula matches a given structure -}
structMatch :: Formula -> Struct -> Bool
structMatch Var{varName = VarHole _} Variable = True
structMatch Var{varName = VarConstant nm} (GeneralizedConstant s) = nm == s
structMatch Trm{trmId = m} (Function n _) = n == m
structMatch _ _ = False

{- during retrieval everything matches a variable -}
retrieveMatch :: Formula -> Struct -> Bool
retrieveMatch _ Variable = True
retrieveMatch f g = structMatch f g

{- arguments generalized for variables -}
args :: Formula -> [Formula]
args Trm{trmArgs = ts} = ts
args _ = []

{- insert a term into the tree -}
insert :: Formula -> a -> DisTree a -> DisTree a
insert key@(Trm{}) value (DT nodes) = DT $ dive nodes [key]
  where
    dive nodes keylist@(k:ks) = case break (structMatch k . struct) nodes of
      -- if nothing matches -> create a whole new branch with value at the end
      (_ , [])  -> buildTree keylist value ++ nodes
      (unmatchedNodes, matchedNode : rest) -> unmatchedNodes ++ (
        matchedNode {children = dive (children matchedNode) (args k ++ ks)} :
        rest)
    -- if we reach a leaf -> add the value
    dive [Leaf values] [] = [Leaf (value:values)]

insert _ _ tree = tree

insertBy :: (a -> Formula) -> a -> DisTree a -> DisTree a
insertBy keyFunction value = insert (keyFunction value) value

{- build a tree from a list of formulas -}
buildTree :: [Formula] -> a -> [DTree [a]]
buildTree [Top] _ = []
buildTree [Bot] _ = []
buildTree keys value = [dtree keys]
  where
    dtree (k:ks) = Node (toStruct k) [dtree $ args k ++ ks]
    dtree []     = Leaf [value]

    toStruct Var {varName = VarHole _} = Variable
    toStruct Var {varName = VarConstant nm} = GeneralizedConstant nm
    toStruct Trm {trmId = m, trmArgs = ts} = Function m (length ts)
    toStruct _ = error "DisTree: Formula has no representation."

{- lookup values in a tree. The key for the lookup is the structure of
the given formula. Multiple leafs may match the key. lookup returns all of
their values. -}
lookup :: Formula -> DisTree a -> Maybe [a]
lookup key (DT nodes) = mbConcat $ dive nodes [key]
  where
    dive :: [DTree [a]] -> [Formula] -> [[a]]
    dive nodes (Var{varName = VarHole _}:ks)
      = let (leafs, newNodes) = L.partition isLeaf $ concatMap jump nodes
         in map stored leafs ++ dive newNodes ks
    dive nodes keylist@(k:ks) =
      case dropWhile (not . retrieveMatch k . struct) nodes of
        []  -> [] -- nothing matches -> key is not in the tree
        matchedNode:rest ->
          dive (children matchedNode) (mbArgs (struct matchedNode) k ++ ks)
          ++ dive rest keylist
    dive [Leaf values] [] = [values]
    dive [] [] = [[]]

    mbArgs Variable = const []; 
    mbArgs _ = args

    mbConcat [] = Nothing; 
    mbConcat lst = Just $ concat lst

    isLeaf (Leaf _) = True
    isLeaf _ = False

find :: Formula -> DisTree a -> [a]
find f = fromMaybe [] . lookup f

{- only for debugging: transform a tree into a readable format -}
showTree :: Show a => DisTree a -> String
showTree (DT []) = ""
showTree (DT [Leaf value]) = "Leaf " ++ show value -- this shouldn't occur
showTree (DT xs) = "\n" ++ unlines (recursor xs)
  where
    recursor [] = []
    recursor [Leaf value] = ["L " ++ show value]
    recursor (node:rest) = helper node ++ recursor rest
    
    helper (Node struct children) =
      let ([head],stringChildren) = splitAt 1 $ recursor children
          sn = show struct; l = length sn
      in  (sn ++ space (4-l) ++ head) : map ((space 4) ++ ) stringChildren

    space n = replicate n ' '
