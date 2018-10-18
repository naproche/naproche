{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018)

Core functios on formulas.
-}

module Alice.Data.Formula where

import Debug.Trace

import Alice.Data.Base

import Control.Monad
import Data.Maybe
import qualified Data.Monoid as Monoid
import qualified Data.IntMap.Strict as IM
import qualified Data.Traversable as Traverse

-- Traversing functions

{- map a function over the next structure level of a formula -}
mapF :: (Formula -> Formula) -> Formula -> Formula
mapF fn (All v f)       = All v (fn f)
mapF fn (Exi v f)       = Exi v (fn f)
mapF fn (Iff f g)       = Iff (fn f) (fn g)
mapF fn (Imp f g)       = Imp (fn f) (fn g)
mapF fn (Or  f g)       = Or  (fn f) (fn g)
mapF fn (And f g)       = And (fn f) (fn g)
mapF fn (Tag a f)       = Tag a (fn f)
mapF fn (Not f)         = Not (fn f)
mapF _  (Top)           = Top
mapF _  (Bot)           = Bot
mapF fn (Trm t ts ss n) = Trm t (map fn ts) ss n
mapF fn (Var v ss)      = Var v ss
mapF fn (Ind v)      = Ind v
mapF fn ThisT           = ThisT

{- map a monadic action over the next structure level of a formula -}
mapFM :: (Monad m) => (Formula -> m Formula) -> Formula -> m Formula
mapFM fn (All v f)      = liftM (All v) (fn f)
mapFM fn (Exi v f)      = liftM (Exi v) (fn f)
mapFM fn (Iff f g)      = liftM2 Iff (fn f) (fn g)
mapFM fn (Imp f g)      = liftM2 Imp (fn f) (fn g)
mapFM fn (Or  f g)      = liftM2 Or  (fn f) (fn g)
mapFM fn (And f g)      = liftM2 And (fn f) (fn g)
mapFM fn (Tag a f)      = liftM (Tag a) (fn f)
mapFM fn (Not f)        = liftM  Not (fn f)
mapFM _  (Top)          = return Top
mapFM _  (Bot)          = return Bot
mapFM fn (Trm t ts ss n )= liftM (\ts -> Trm t ts ss n) (mapM fn ts)
mapFM fn (Var v ss)     = return $ Var v ss
mapFM fn (Ind v)        = return $ Ind v
mapFM fn ThisT          = return ThisT


-- Logical traversing
{- same as roundFM but without the monadic action. At the moment not in use
   in the code. -}
roundF :: Char -> ([Formula] -> Maybe Bool -> Int -> Formula -> Formula)  --- compare directed local image
               ->  [Formula] -> Maybe Bool -> Int -> Formula -> Formula   --- [Formula] -> list of premises
roundF c fn cn sg n = dive                                                --- Maybe Bool -> polarity (Nothing menas neutral)
  where                                                                   --- Int counts quantification depth
    dive (All u f)  = let nf = fn cn sg (succ n); nn = c:show n
                      in  All u $ bind nn $ nf $ inst nn f
    dive (Exi u f)  = let nf = fn cn sg (succ n); nn = c:show n
                      in  Exi u $ bind nn $ nf $ inst nn f
    dive (Iff f g)  = let nf = fn cn Nothing n f
                      in  Iff nf $ fn cn Nothing n g
    dive (Imp f g)  = let nf = fn cn (liftM not sg) n f
                      in  Imp nf $ fn (nf:cn) sg n g
    dive (Or  f g)  = let nf = fn cn sg n f
                      in  Or nf $ fn (Not nf:cn) sg n g
    dive (And f g)  = let nf = fn cn sg n f
                      in  And nf $ fn (nf:cn) sg n g
    dive (Not f)    = Not $ fn cn (liftM not sg) n f
    dive f          = mapF (fn cn sg n) f

{- traverse the structure of a formula with a monadic action all while keeping track of
   local premises (fn), polarity (sg) and quantification depth (n). A unique identifying
   char (c) is provided to shape the instantiations.-}
roundFM :: (Monad m) =>
          Char -> ([Formula] -> Maybe Bool -> Int -> Formula -> m Formula)
               ->  [Formula] -> Maybe Bool -> Int -> Formula -> m Formula
roundFM c fn cn sg n  = dive
  where
    dive (All u f)  = do  let nf = fn cn sg (succ n); nn = c:show n
                          liftM (All u . bind nn) $ nf $ inst nn f
    dive (Exi u f)  = do  let nf = fn cn sg (succ n); nn = c:show n
                          liftM (Exi u . bind nn) $ nf $ inst nn f
    dive (Iff f g)  = do  nf <- fn cn Nothing n f
                          liftM (Iff nf) $ fn cn Nothing n g
    dive (Imp f g)  = do  nf <- fn cn (liftM not sg) n f
                          liftM (Imp nf) $ fn (nf:cn) sg n g
    dive (Or  f g)  = do  nf <- fn cn sg n f
                          liftM (Or nf) $ fn (Not nf:cn) sg n g
    dive (And f g)  = do  nf <- fn cn sg n f
                          liftM (And nf) $ fn (nf:cn) sg n g
    dive (Not f)    = liftM Not $ fn cn (liftM not sg) n f
    dive f          = mapFM (fn cn sg n) f


-- Folding

{- map a collection function over the next structure level of a formula -}
foldF :: (Monoid.Monoid a) => (Formula -> a) -> Formula -> a
foldF fn (All _ f)      = fn f
foldF fn (Exi _ f)      = fn f
foldF fn (Iff f g)      = Monoid.mappend (fn f) (fn g)
foldF fn (Imp f g)      = Monoid.mappend (fn f) (fn g)
foldF fn (Or  f g)      = Monoid.mappend (fn f) (fn g)
foldF fn (And f g)      = Monoid.mappend (fn f) (fn g)
foldF fn (Tag _ f)      = fn f
foldF fn (Not f)        = fn f
foldF _  (Top)          = Monoid.mempty
foldF _  (Bot)          = Monoid.mempty
foldF fn Trm {trArgs = ts} = Monoid.mconcat $ map fn $ ts
foldF fn Var{}          = Monoid.mempty
foldF fn Ind{}          = Monoid.mempty
foldF fn ThisT          = Monoid.mempty

{- tests whether a predicate holds for all formulas on the next structure level
   of a formula -}
allF :: (Formula -> Bool) -> Formula -> Bool
allF fn = Monoid.getAll . foldF (Monoid.All . fn)

{- tests whether a predicate holds for any formula on the next structure level
   of a formula -}
anyF :: (Formula -> Bool) -> Formula -> Bool
anyF fn = Monoid.getAny . foldF (Monoid.Any . fn)

{- sums up a numeric function over the next structure level of a formula -}
sumF :: (Num a) => (Formula -> a) -> Formula -> a
sumF fn = Monoid.getSum . foldF (Monoid.Sum . fn)


{- map a monadic collection over the next structure level of a formula -}
foldFM :: (Monoid.Monoid a, Monad m) => (Formula -> m a) -> Formula -> m a
foldFM fn (All _ f) = fn f
foldFM fn (Exi _ f) = fn f
foldFM fn (Iff f g) = liftM2 Monoid.mappend (fn f) (fn g)
foldFM fn (Imp f g) = liftM2 Monoid.mappend (fn f) (fn g)
foldFM fn (And f g) = liftM2 Monoid.mappend (fn f) (fn g)
foldFM fn (Or  f g) = liftM2 Monoid.mappend (fn f) (fn g)
foldFM fn (Tag _ f) = fn f
foldFM fn (Not f)   = fn f
foldFM _ Top        = return Monoid.mempty
foldFM _ Bot        = return Monoid.mempty
foldFM fn Trm {trArgs = ts} = liftM Monoid.mconcat $ mapM fn $ ts
foldFM fn Var{}    = return Monoid.mempty
foldFM fn Ind{}    = return Monoid.mempty

-- Bind, inst, subst

{- check for closedness in the sense that the formula contains no non-bound
   de Bruijn index. -}
closed :: Formula -> Bool
closed  = dive 0
  where
    dive n (All _ g)    = dive (succ n) g
    dive n (Exi _ g)    = dive (succ n) g
    dive n (Trm t ts _ _) = all (dive n) ts
    dive n (Var _ _)    = True
    dive n (Ind v)      = v < n
    dive n f            = allF (dive n) f

{- bind a variable with name v in a formula. This also affects any info stored. -}
bind :: String -> Formula -> Formula
bind v  = dive 0
  where
    dive n (All u g)  = All u $ dive (succ n) g
    dive n (Exi u g)  = Exi u $ dive (succ n) g
    dive n (Var u _) | u == v
                      = Ind n
    dive n (Trm t ts is m) = Trm t (map (dive n) ts) (map (dive n) is) m
    dive n (Ind m )   = Ind m
    dive n f          = mapF (dive n) f

{- instantiate a formula with a variable with name v. This also affects any info stored. -}
inst :: String -> Formula -> Formula
inst v  = dive 0
  where
    dive n (All u g)  = All u $ dive (succ n) g
    dive n (Exi u g)  = Exi u $ dive (succ n) g
    dive n (Ind m) | m == n
                      = Var v []
    dive n (Trm t ts is m) = let d = dive n
                              in Trm t (map d ts) (map d is) m
    dive n (Var x ss) = let d = dive n in Var x (map d ss)
    dive n f          = mapF (dive n) f

{- substitute a formula t for a variable with name v. Does not affect info. -}
subst :: Formula -> String -> Formula -> Formula
subst t v = dive
  where
    dive (Var u _)    | u == v  = t
    dive f            = mapF dive f

{- multiple substitutions at the same time. Does not affect info. -}
substs :: Formula -> [String] -> [Formula] -> Formula
substs f vs ts = dive f
  where
    dive (Var u ss)  = fromMaybe (Var u ss) (lookup u zvt)
    dive f            = mapF dive f
    zvt               = zip vs ts

{- instantiate a formula with the placeholder token ThisT -}
instThisT :: Formula -> Formula
instThisT = dive 0
  where
    dive n (All u g)  = All u $ dive (succ n) g
    dive n (Exi u g)  = Exi u $ dive (succ n) g
    dive n (Ind m) | m == n = ThisT
    dive n (Trm t ts is m) = let d = dive n
                              in Trm t (map d ts) is m
    dive n (Var x ss) = let d = dive n in Var x ss
    dive n f          = mapF (dive n) f


-- Compare and replace

{- check for syntactic equality of terms/atomic formulas. Always yields False
   for compound formulas. -}
twins :: Formula -> Formula -> Bool
twins (Ind u )    (Ind v )    = u == v
twins (Var u _ )    (Var v _ )    = u == v
twins (Trm  p ps _ n ) (Trm q qs _ m ) | n == m  = pairs ps qs
  where
    pairs (p:ps) (q:qs) = twins p q && pairs ps qs
    pairs [] []         = True
    pairs _ _           = False
twins ThisT ThisT = True
twins _ _         = False

-- made these change to occurs because it should be a syntactical check and have
-- nothing to do with info

{- replace the term s by the term t. Does not affect info. -}
replace :: Formula -> Formula -> Formula -> Formula
replace t s = dive
  where
    dive f  | twins s f = t
            | otherwise = dive_aux f
    dive_aux (Trm t ts is n) = Trm t (map dive ts) is n
    dive_aux (Var x ss) = Var x ss
    dive_aux (Ind n)   = Ind n
    dive_aux f = mapF dive f
