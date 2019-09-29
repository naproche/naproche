{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018)

Core functions on formulas.
-}

module SAD.Data.Formula.Base where

import Data.Maybe
import qualified Data.Monoid as Monoid
import Control.Monad.Identity
import Control.Applicative

import SAD.Data.Tag (Tag)
import SAD.Core.SourcePos (SourcePos)
import SAD.Data.TermId

import SAD.Data.Text.Decl (Decl)

data Formula =
  All Decl Formula        | Exi Decl Formula |
  Iff Formula Formula     | Imp Formula Formula     |
  Or  Formula Formula     | And Formula Formula     |
  Tag Tag Formula         | Not Formula             |
  Top                     | Bot                     |
  Trm { trmName :: String   , trmArgs :: [Formula],
        trmInfo :: [Formula], trmId   :: TermId}         |
  Var { varName :: String, varInfo :: [Formula], varPosition :: SourcePos } |
  Ind { indIndex :: Int, indPosition :: SourcePos }   | ThisT
  deriving (Eq, Ord)

trInfo :: Formula -> [Formula]
trInfo Trm {trmInfo = xs} = xs
trInfo Var {varInfo = xs} = xs
trInfo _ = error "Formula.Base.trInfo: Partial function"

showTrName :: Formula -> ShowS
showTrName (Trm {trmName = s}) = showString $ filter (/= ':') s
showTrName (Var {varName = s}) = showString $ filter (/= ':') s
showTrName _ = id

-- Traversing functions

-- | Map a function over the next structure level of a formula
mapF :: (Formula -> Formula) -> Formula -> Formula
mapF fn = runIdentity . mapFM (Identity . fn)

-- | Map a monadic action over the next structure level of a formula
mapFM :: (Applicative m) => (Formula -> m Formula) -> Formula -> m Formula
mapFM fn (All v f) = All v <$> fn f
mapFM fn (Exi v f) = Exi v <$> fn f
mapFM fn (Iff f g) = liftA2 Iff (fn f) (fn g)
mapFM fn (Imp f g) = liftA2 Imp (fn f) (fn g)
mapFM fn (Or f g) = liftA2 Or (fn f) (fn g)
mapFM fn (And f g) = liftA2 And (fn f) (fn g)
mapFM fn (Tag a f) = Tag a <$> fn f
mapFM fn (Not f) = Not <$> fn f
mapFM fn t@Trm{} = (\args -> t {trmArgs = args}) <$> (traverse fn $ trmArgs t)
mapFM _ f = pure f

-- Logical traversing
-- | Same as roundFM but without the monadic action.
roundF :: Char -> ([Formula] -> Maybe Bool -> Int -> Formula -> Formula)
               -> [Formula] -> Maybe Bool -> Int -> Formula -> Formula
roundF c fn l p n f = runIdentity $ roundFM c (\w x y z -> Identity $ fn w x y z) l p n f

{- traverse the structure of a formula with a monadic action all while keeping 
track of local premises, polarity and quantification depth. A unique identifying
char is provided to shape the instantiations.-}
roundFM :: (Monad m) =>
          Char -> ([Formula] -> Maybe Bool -> Int -> Formula -> m Formula)
               -> [Formula] -> Maybe Bool -> Int -> Formula -> m Formula
roundFM char traversalAction localContext polarity n = dive
  where
    dive (All u f) = do
      let action = traversalAction localContext polarity (succ n)
          nn = char:show n
      All u . bind nn <$> (action $ inst nn f)
    dive (Exi u f) = do
      let action = traversalAction localContext polarity (succ n)
          nn = char:show n
      Exi u . bind nn <$> (action $ inst nn f)
    dive (Iff f g) = do
      nf <- traversalAction localContext Nothing n f
      Iff nf <$> traversalAction localContext Nothing n g
    dive (Imp f g) = do
      nf <- traversalAction localContext (not <$> polarity) n f
      Imp nf <$> traversalAction (nf:localContext) polarity n g
    dive (Or f g) = do
      nf <- traversalAction localContext polarity n f
      Or nf  <$> traversalAction (Not nf:localContext) polarity n g
    dive (And f g) = do
      nf <- traversalAction localContext polarity n f
      And nf <$> traversalAction (nf:localContext) polarity n g
    dive (Not f) = Not <$> traversalAction localContext (not <$> polarity) n f
    dive f = mapFM (traversalAction localContext polarity n) f

-- | Map a collection function over the next structure level of a formula
foldF :: (Monoid.Monoid a) => (Formula -> a) -> Formula -> a
foldF fn = runIdentity . foldFM (Identity . fn)

{- | tests whether a predicate holds for all formulas on the next structure level
   of a formula. Returns 'True' if there is none. -}
allF :: (Formula -> Bool) -> Formula -> Bool
allF predicate = Monoid.getAll . foldF (Monoid.All . predicate)

{- | tests whether a predicate holds for any formula on the next structure level
   of a formula. Returns 'False' if there is none. -}
anyF :: (Formula -> Bool) -> Formula -> Bool
anyF predicate = Monoid.getAny . foldF (Monoid.Any . predicate)

{- sums up a numeric function over the next structure level of a formula -}
sumF :: (Num a) => (Formula -> a) -> Formula -> a
sumF fn = Monoid.getSum . foldF (Monoid.Sum . fn)


{- map a monadic collection over the next structure level of a formula -}
foldFM :: (Monoid.Monoid a, Applicative m) => (Formula -> m a) -> Formula -> m a
foldFM fn (All _ f) = fn f
foldFM fn (Exi _ f) = fn f
foldFM fn (Iff f g) = liftA2 Monoid.mappend (fn f) (fn g)
foldFM fn (Imp f g) = liftA2 Monoid.mappend (fn f) (fn g)
foldFM fn (And f g) = liftA2 Monoid.mappend (fn f) (fn g)
foldFM fn (Or f g) = liftA2 Monoid.mappend (fn f) (fn g)
foldFM fn (Tag _ f) = fn f
foldFM fn (Not f) = fn f
foldFM fn t@Trm{} = fmap Monoid.mconcat $ traverse fn $ trmArgs t
foldFM _ _ = pure Monoid.mempty


-- Bind, inst, subst

{- check for closedness in the sense that the formula contains no non-bound
   de Bruijn index. -}
closed :: Formula -> Bool
closed  = dive 0
  where
    dive n (All _ g) = dive (succ n) g
    dive n (Exi _ g) = dive (succ n) g
    dive n t@Trm{} = all (dive n) $ trmArgs t
    dive _ Var{} = True
    dive n Ind {indIndex = v} = v < n
    dive n f = allF (dive n) f

{- checks whether the non-compound formula t occurs anywhere in the formula f -}
occurs :: Formula -> Formula -> Bool
occurs t f = twins t f || anyF (occurs t) f

-- | Bind a variable with name v in a formula.
-- This also affects any info stored.
bind :: String -> Formula -> Formula
bind v = dive 0
  where
    dive n (All u g) = All u $ dive (succ n) g
    dive n (Exi u g) = Exi u $ dive (succ n) g
    dive n Var {varName = u, varPosition = pos}
      | u == v = Ind n pos
    dive n t@Trm{} = t {
      trmArgs = map (dive n) $ trmArgs t,
      trmInfo = map (dive n) $ trmInfo t}
    dive _ i@Ind{} = i
    dive n f = mapF (dive n) f

-- | Instantiate a formula with a variable with name v.
-- This also affects any info stored.
inst :: String -> Formula -> Formula
inst x = dive 0
  where
    dive n (All u g) = All u $ dive (succ n) g
    dive n (Exi u g) = Exi u $ dive (succ n) g
    dive n Ind {indIndex = m, indPosition = pos}
      | m == n = Var x [] pos
    dive n t@Trm{} = t {
      trmArgs = map (dive n) $ trmArgs t,
      trmInfo = map (dive n) $ trmInfo t }
    dive n v@Var{} = v {varInfo = map (dive n) $ varInfo v}
    dive n f = mapF (dive n) f

{- substitute a formula t for a variable with name v. Does not affect info. -}
subst :: Formula -> String -> Formula -> Formula
subst t v = dive
  where
    dive Var {varName = u} | u == v = t
    dive f = mapF dive f

{- multiple substitutions at the same time. Does not affect info. -}
substs :: Formula -> [String] -> [Formula] -> Formula
substs f vs ts = dive f
  where
    dive v@Var {varName = u, varInfo = ss} = fromMaybe v (lookup u zvt)
    dive f = mapF dive f
    zvt = zip vs ts



-- Compare and replace

{- check for syntactic equality of terms/atomic formulas. Always yields False
for compound formulas. -}
twins :: Formula -> Formula -> Bool
twins u@Ind{} v@Ind{} = indIndex u == indIndex v
twins Var {varName = u} Var {varName = v} = u == v
twins t@Trm{} s@Trm{}
  | trmId t == trmId s = pairs (trmArgs t) (trmArgs s)
  where
    pairs (p:ps) (q:qs) = twins p q && pairs ps qs
    pairs [] [] = True
    pairs _ _ = False
twins ThisT ThisT = True
twins _ _ = False

-- made these change to occurs because it should be a syntactical check and have
-- nothing to do with info

{- replace the term s by the term t. Does not affect info. -}
replace :: Formula -> Formula -> Formula -> Formula
replace t s = dive
  where
    dive f
      | twins s f = t
      | otherwise = dive_aux f
    dive_aux t@Trm{} = t {trmArgs = map dive $ trmArgs t}
    dive_aux v@Var{} = v
    dive_aux i@Ind{} = i
    dive_aux f = mapF dive f

syntacticEquality :: Formula -> Formula -> Bool
syntacticEquality = dive
  where
    dive (And f1 g1) (And f2 g2) = dive f1 f2 && dive g1 g2
    dive (Or f1 g1) (Or f2 g2) = dive f1 f2 && dive g1 g2
    dive (Imp f1 g1) (Imp f2 g2) = dive f1 f2 && dive g1 g2
    dive (Iff f1 g1) (Iff f2 g2) = dive f1 f2 && dive g1 g2
    dive (All _ f) (All _ g) = dive f g
    dive (Exi _ f) (Exi _ g) = dive f g
    dive (Tag t1 f) (Tag t2 g) = t1 == t2 && dive f g
    dive (Not f) (Not g) = dive f g
    dive Top Top = True
    dive Bot Bot = True
    dive ThisT ThisT = True
    dive t1@Trm{} t2@Trm{} = twins t1 t2
    dive Var {varName = v1} Var {varName = v2} = v1 == v2
    dive _ _ = False