{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018)

Construct prover database.
-}

module Alice.Export.Base (Prover(..),Format(..),readPrDB) where

import Data.Char
import Data.List
import System.Exit
import System.IO
import System.IO.Error
import Control.Exception
import Alice.Core.Message
import Alice.Core.Position

data Prover = Prover {
  prName :: String,    -- prover name
  prLabl :: String,    -- prover identifier
  prPath :: String,    -- path to call the prover
  prArgs :: [String],  -- comline flags
  prFrmt :: Format,    -- format that the prover reads
  prSucc :: [String],  -- prover's success message
  prFail :: [String],  -- prover's failure message
  prUnkn :: [String] } -- prover's unkown message

data Format = TPTP | DFG

initPrv l = Prover l "Prover" "" [] TPTP [] [] []


-- Database reader

{- parse the prover database in provers.dat -}
readPrDB :: String -> IO [Prover]
readPrDB file = do
  inp <- catch (readFile file) $ die . ioeGetErrorString
  let dws = dropWhile isSpace
      cln = reverse . dws . reverse . dws
      lns = map cln $ lines inp
  case readPrvs 1 Nothing lns of
    Left e  ->  die e
    Right d ->  return d
  where
    die e = outputExport NORMAL (fileOnlyPos file) e >> exitFailure


readPrvs :: Int -> Maybe Prover -> [String] -> Either String [Prover]

readPrvs n mbp ([]:ls)      = readPrvs (succ n) mbp ls
readPrvs n mbp (('#':_):ls) = readPrvs (succ n) mbp ls
readPrvs n _ ([_]:_)        = Left $ show n ++ ": empty value"

readPrvs n (Nothing) (('P':l):ls)
  = readPrvs (succ n) (Just $ initPrv l) ls
readPrvs n (Just pr) (('P':l):ls)
  = fmap2 (:) (validate pr) $ readPrvs (succ n) (Just $ initPrv l) ls
readPrvs n (Just pr) (('L':l):ls)
  = readPrvs (succ n) (Just pr { prLabl = l }) ls
readPrvs n (Just pr) (('Y':l):ls)
  = readPrvs (succ n) (Just pr { prSucc = l : prSucc pr }) ls
readPrvs n (Just pr) (('N':l):ls)
  = readPrvs (succ n) (Just pr { prFail = l : prFail pr }) ls
readPrvs n (Just pr) (('U':l):ls)
  = readPrvs (succ n) (Just pr { prUnkn = l : prUnkn pr }) ls
readPrvs n (Just pr) (('C':l):ls)
  = let (p:a) = if null l then ("":[]) else words l
    in  readPrvs (succ n) (Just pr { prPath = p, prArgs = a }) ls
readPrvs n (Just pr) (('F':l):ls)
  = case l of
      "tptp"  ->  readPrvs (succ n) (Just pr { prFrmt = TPTP }) ls
      "dfg"   ->  readPrvs (succ n) (Just pr { prFrmt = DFG  }) ls
      _       ->  Left $ show n ++ ": unknown format: " ++ l

readPrvs n (Just _)  ((c:_):_)  = Left $ show n ++ ": invalid tag: "   ++ [c]
readPrvs n (Nothing) ((c:_):_)  = Left $ show n ++ ": misplaced tag: " ++ [c]

readPrvs _ (Just pr) [] = fmap1 (:[]) $ validate pr
readPrvs _ (Nothing) [] = Right []


validate :: Prover -> Either String Prover
validate (Prover { prName = n, prPath = "" })
  = Left $ " prover '" ++ n ++ "' has no command line"
validate (Prover { prName = n, prSucc = [] })
  = Left $ " prover '" ++ n ++ "' has no success responses"
validate (Prover { prName = n, prFail = [], prUnkn = [] })
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
