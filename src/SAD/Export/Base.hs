{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018)

Construct prover database.
-}

module SAD.Export.Base (Prover(..),Format(..),readProverDatabase) where

import qualified Data.Char as Char
import System.IO
import System.IO.Error
import Control.Exception
import qualified SAD.Core.Message as Message
import SAD.Core.SourcePos
import qualified Isabelle.File as File

data Prover = Prover {
  name           :: String,
  label          :: String,
  path           :: String,
  arguments      :: [String],
  format         :: Format,
  successMessage :: [String],
  failureMessage :: [String],
  unknownMessage :: [String] }

data Format = TPTP | DFG

initPrv l = Prover l "Prover" "" [] TPTP [] [] []


-- Database reader

{- parse the prover database in provers.dat -}
readProverDatabase :: String -> IO [Prover]
readProverDatabase file = do
  input <- catch (File.read file) $ err . ioeGetErrorString
  let dropWS = dropWhile Char.isSpace
      trimWS = reverse . dropWS . reverse . dropWS
      ls = map trimWS $ lines input
  case readProvers 1 Nothing ls of
    Left e  ->  err e
    Right d ->  return d
  where
    err = Message.errorExport (fileOnlyPos file)


readProvers :: Int -> Maybe Prover -> [String] -> Either String [Prover]

readProvers n mbp ([]:ls)      = readProvers (succ n) mbp ls
readProvers n mbp (('#':_):ls) = readProvers (succ n) mbp ls
readProvers n _ ([_]:_)        = Left $ show n ++ ": empty value"

readProvers n Nothing (('P':l):ls)
  = readProvers (succ n) (Just $ initPrv l) ls
readProvers n (Just pr) (('P':l):ls)
  = fmap2 (:) (validate pr) $ readProvers (succ n) (Just $ initPrv l) ls
readProvers n (Just pr) (('L':l):ls)
  = readProvers (succ n) (Just pr { label = l }) ls
readProvers n (Just pr) (('Y':l):ls)
  = readProvers (succ n) (Just pr { successMessage = l : successMessage pr }) ls
readProvers n (Just pr) (('N':l):ls)
  = readProvers (succ n) (Just pr { failureMessage = l : failureMessage pr }) ls
readProvers n (Just pr) (('U':l):ls)
  = readProvers (succ n) (Just pr { unknownMessage = l : unknownMessage pr }) ls
readProvers n (Just pr) (('C':l):ls)
  = let (p:a) = if null l then ("":[]) else words l
    in  readProvers (succ n) (Just pr { path = p, arguments = a }) ls
readProvers n (Just pr) (('F':l):ls)
  = case l of
      "tptp" ->  readProvers (succ n) (Just pr { format = TPTP }) ls
      "dfg"  ->  readProvers (succ n) (Just pr { format = DFG  }) ls
      _      ->  Left $ show n ++ ": unknown format: " ++ l

readProvers n (Just _)  ((c:_):_)  = Left $ show n ++ ": invalid tag: "   ++ [c]
readProvers n Nothing ((c:_):_)    = Left $ show n ++ ": misplaced tag: " ++ [c]

readProvers _ (Just pr) [] = fmap1 (:[]) $ validate pr
readProvers _ Nothing []   = Right []


validate :: Prover -> Either String Prover
validate Prover { name = n, path = "" }
  = Left $ " prover '" ++ n ++ "' has no command line"
validate Prover { name = n, successMessage = [] }
  = Left $ " prover '" ++ n ++ "' has no success responses"
validate Prover { name = n, failureMessage = [], unknownMessage = [] }
  = Left $ " prover '" ++ n ++ "' has no failure responses"
validate r = Right r


-- Service stuff

fmap1 :: (a -> b) -> Either e a -> Either e b
fmap1 f (Right a) = Right (f a)
fmap1 _ (Left e)  = Left e

fmap2 :: (a -> b -> c) -> Either e a -> Either e b -> Either e c
fmap2 _ (Left e) _          = Left e
fmap2 _ _ (Left e)          = Left e
fmap2 f (Right a) (Right b) = Right (f a b)
