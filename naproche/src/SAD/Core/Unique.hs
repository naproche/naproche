{-# LANGUAGE OverloadedStrings #-}

-- | This module generates unique identifiers.
-- It provides a 'newIdent' function that takes an identifier
-- and then returns either this identifier or the identifier appended
-- by a unique number (to ensure it does not overlap with any other idents).
-- By using 'newIdent' throughout, we can ensure that all names are globally
-- unique in the type-checking and simplification phases.

-- Traditionally, the unique number appended will not depend on the ident
-- passed to 'newIdent', but rather be incremented each time the function is called.
-- That is quite efficient but also means that the numbers will be quite large.
-- Instead we keep a map from an "alpha-prefix" of each identifier
-- (the longest prefix such that the last character is not a number)
-- to an integer that will be added to that identifier.

module SAD.Core.Unique 
  ( UniqueT(..), Unique, runUnique, evalUnique
  , HasUnique(..)
  , identSet, identClass, identElement, identObject, identHole, identEmpty
  ) where

import Control.Monad.Identity (Identity)
import Control.Monad.State
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Map (Map)
import qualified Data.Map as Map

import SAD.Data.Identifier
import Data.Char (isNumber)

onLast :: (Text -> Text) -> [Text] -> [Text]  
onLast f xs = case xs of
  [] -> [f ""]
  [x] -> [f x]
  [x, ""] -> [f x, ""]
  [x, "", ""] -> [f x, "", ""]
  (x:xs) -> x : onLast f xs

alphaPrefixOf :: Identifier -> Identifier
alphaPrefixOf n = case n of
  NormalIdent n' -> NormalIdent $ Text.dropWhileEnd isNumber n'
  SymbolIdent ns -> SymbolIdent $ onLast (Text.dropWhileEnd isNumber) ns

appendNum :: Identifier -> Int -> Identifier
appendNum n x = case n of
  NormalIdent n' -> NormalIdent $ n' <> Text.pack (show x)
  SymbolIdent ns -> SymbolIdent $ onLast (<> Text.pack (show x)) ns

newtype PrefixUniqueMap = PrefixUniqueMap
  { fromPrefixUniqueMap :: Map Identifier Int }

newtype UniqueT m a = UniqueT { fromUnique :: StateT PrefixUniqueMap m a }
  deriving (Functor, Applicative, Monad, MonadTrans, MonadState PrefixUniqueMap)

instance MonadIO m => MonadIO (UniqueT m) where
  liftIO action = lift $ liftIO action

identSet, identClass, identElement, identObject, identHole, identEmpty :: Ident
initialPrefixUniqueMap :: PrefixUniqueMap
((identSet, identClass, identElement, identObject, identHole, identEmpty), initialPrefixUniqueMap)
  = flip runState (PrefixUniqueMap Map.empty) . fromUnique $ do
      identSet <- newIdent identifierSet
      identClass <- newIdent identifierClass
      identElement <- newIdent identifierElement
      identObject <- newIdent identifierObject
      identHole <- newIdent identifierHole
      identEmpty <- newIdent identifierEmpty
      pure (identSet, identClass, identElement, identObject, identHole, identEmpty)

runUnique :: UniqueT m a -> m (a, PrefixUniqueMap)
runUnique = flip runStateT initialPrefixUniqueMap . fromUnique

evalUnique :: Monad m => UniqueT m a -> m a
evalUnique = flip evalStateT initialPrefixUniqueMap . fromUnique

type Unique a = UniqueT Identity

lookupAndIncrement :: Monad m => Identifier -> UniqueT m Int
lookupAndIncrement n = do
  m <- get
  let m' = fromPrefixUniqueMap m
  let x = Map.findWithDefault 0 n m'
  put $ PrefixUniqueMap $ Map.insertWith (+) n 1 m'
  pure x

class Monad m => HasUnique m where
  newIdent :: Identifier -> m Ident

instance Monad m => HasUnique (UniqueT m) where
  newIdent n = do
    let n' = alphaPrefixOf n
    x <- lookupAndIncrement n'
    pure $ Ident (appendNum n' x) n