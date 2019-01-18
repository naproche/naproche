{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018)

Core functions on formulas.
-}

module SAD.Data.Formula.Base where

import Control.Monad
import Data.Maybe
import qualified Data.Monoid as Monoid

import SAD.Data.Tag (Tag)
import SAD.Core.SourcePos (SourcePos, noPos)

import SAD.Data.Text.Decl (Decl)
import qualified SAD.Data.Text.Decl as Decl


data Formula =
  All Decl Formula        | Exi Decl Formula |
  Iff Formula Formula     | Imp Formula Formula     |
  Or  Formula Formula     | And Formula Formula     |
  Tag Tag Formula         | Not Formula             |
  Top                     | Bot                     |
  Trm { trName :: String   , trArgs :: [Formula],
        trInfo :: [Formula], trId   :: Int}         |
  Var { trName :: String   , trInfo :: [Formula], trPosition :: SourcePos } |
  Ind { trIndx :: Int, trPosition :: SourcePos }   | ThisT


-- Traversing functions

{- map a function over the next structure level of a formula -}
mapF :: (Formula -> Formula) -> Formula -> Formula
mapF fn (All v f) = All v (fn f)
mapF fn (Exi v f) = Exi v (fn f)
mapF fn (Iff f g) = Iff (fn f) (fn g)
mapF fn (Imp f g) = Imp (fn f) (fn g)
mapF fn (Or f g) = Or (fn f) (fn g)
mapF fn (And f g) = And (fn f) (fn g)
mapF fn (Tag a f) = Tag a (fn f)
mapF fn (Not f) = Not (fn f)
mapF fn t@Trm{} = t {trArgs = map fn $ trArgs t}
mapF _ f = f

{- map a monadic action over the next structure level of a formula -}
mapFM :: (Monad m) => (Formula -> m Formula) -> Formula -> m Formula
mapFM fn (All v f) = All v <$> fn f
mapFM fn (Exi v f) = Exi v <$> fn f
mapFM fn (Iff f g) = liftM2 Iff (fn f) (fn g)
mapFM fn (Imp f g) = liftM2 Imp (fn f) (fn g)
mapFM fn (Or f g) = liftM2 Or (fn f) (fn g)
mapFM fn (And f g) = liftM2 And (fn f) (fn g)
mapFM fn (Tag a f) = Tag a <$> fn f
mapFM fn (Not f) = Not <$> fn f
mapFM fn t@Trm{} = do
  newArgs <- mapM fn $ trArgs t; return t {trArgs = newArgs}
mapFM _ f = return f



-- Logical traversing
{- same as roundFM but without the monadic action. -}
roundF :: Char -> ([Formula] -> Maybe Bool -> Int -> Formula -> Formula)
               -> [Formula] -> Maybe Bool -> Int -> Formula -> Formula
roundF char traversalFunction localContext polarity n = dive
  where
    dive (All u f) =
      let function = traversalFunction localContext polarity (succ n)
          nn = char:show n
      in  All u $ bind nn $ function $ inst nn f
    dive (Exi u f) =
      let function = traversalFunction localContext polarity (succ n)
          nn = char:show n
      in  Exi u $ bind nn $ function $ inst nn f
    dive (Iff f g) =
      let nf = traversalFunction localContext Nothing n f
      in  Iff nf $ traversalFunction localContext Nothing n g
    dive (Imp f g) =
      let nf = traversalFunction localContext (not <$> polarity) n f
      in  Imp nf $ traversalFunction (nf:localContext) polarity n g
    dive (Or f g) =
      let nf = traversalFunction localContext polarity n f
      in  Or nf $ traversalFunction (Not nf:localContext) polarity n g
    dive (And f g) =
      let nf = traversalFunction localContext polarity n f
      in  And nf $ traversalFunction (nf:localContext) polarity n g
    dive (Not f) = Not $ traversalFunction localContext (not <$> polarity) n f
    dive f = mapF (traversalFunction localContext polarity n) f

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


-- Folding

{- map a collection function over the next structure level of a formula -}
foldF :: (Monoid.Monoid a) => (Formula -> a) -> Formula -> a
foldF fn (All _ f) = fn f
foldF fn (Exi _ f) = fn f
foldF fn (Iff f g) = Monoid.mappend (fn f) (fn g)
foldF fn (Imp f g) = Monoid.mappend (fn f) (fn g)
foldF fn (Or f g) = Monoid.mappend (fn f) (fn g)
foldF fn (And f g) = Monoid.mappend (fn f) (fn g)
foldF fn (Tag _ f) = fn f
foldF fn (Not f) = fn f
foldF fn t@Trm{} = Monoid.mconcat $ map fn $ trArgs t
foldF _ _ = Monoid.mempty

{- tests whether a predicate holds for all formulas on the next structure level
   of a formula -}
allF :: (Formula -> Bool) -> Formula -> Bool
allF predicate = Monoid.getAll . foldF (Monoid.All . predicate)

{- tests whether a predicate holds for any formula on the next structure level
   of a formula -}
anyF :: (Formula -> Bool) -> Formula -> Bool
anyF predicate = Monoid.getAny . foldF (Monoid.Any . predicate)

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
foldFM fn (Or f g) = liftM2 Monoid.mappend (fn f) (fn g)
foldFM fn (Tag _ f) = fn f
foldFM fn (Not f) = fn f
foldFM fn t@Trm{} = fmap Monoid.mconcat $ mapM fn $ trArgs t
foldFM _ _ = return Monoid.mempty


-- Bind, inst, subst

{- check for closedness in the sense that the formula contains no non-bound
   de Bruijn index. -}
closed :: Formula -> Bool
closed  = dive 0
  where
    dive n (All _ g) = dive (succ n) g
    dive n (Exi _ g) = dive (succ n) g
    dive n t@Trm{} = all (dive n) $ trArgs t
    dive _ Var{} = True
    dive n Ind {trIndx = v} = v < n
    dive n f = allF (dive n) f

{- checks whether the formula t occurs anywhere in the formula f -}
occurs :: Formula -> Formula -> Bool
occurs t f = twins t f || anyF (occurs t) f

{- bind a variable with name v in a formula.
This also affects any info stored. -}
bind :: String -> Formula -> Formula
bind v = dive 0
  where
    dive n (All u g) = All u $ dive (succ n) g
    dive n (Exi u g) = Exi u $ dive (succ n) g
    dive n Var {trName = u, trPosition = pos}
      | u == v = Ind n pos
    dive n t@Trm{} = t {
      trArgs = map (dive n) $ trArgs t,
      trInfo = map (dive n) $ trInfo t}
    dive _ i@Ind{} = i
    dive n f = mapF (dive n) f

{- instantiate a formula with a variable with name v.
This also affects any info stored. -}
inst :: String -> Formula -> Formula
inst x = dive 0
  where
    dive n (All u g) = All u $ dive (succ n) g
    dive n (Exi u g) = Exi u $ dive (succ n) g
    dive n Ind {trIndx = m, trPosition = pos}
      | m == n = Var x [] pos
    dive n t@Trm{} = t {
      trArgs = map (dive n) $ trArgs t,
      trInfo = map (dive n) $ trInfo t }
    dive n v@Var{} = v {trInfo = map (dive n) $ trInfo v}
    dive n f = mapF (dive n) f

{- substitute a formula t for a variable with name v. Does not affect info. -}
subst :: Formula -> String -> Formula -> Formula
subst t v = dive
  where
    dive Var {trName = u} | u == v = t
    dive f = mapF dive f

{- multiple substitutions at the same time. Does not affect info. -}
substs :: Formula -> [String] -> [Formula] -> Formula
substs f vs ts = dive f
  where
    dive v@Var {trName = u, trInfo = ss} = fromMaybe v (lookup u zvt)
    dive f = mapF dive f
    zvt = zip vs ts



-- Compare and replace

{- check for syntactic equality of terms/atomic formulas. Always yields False
for compound formulas. -}
twins :: Formula -> Formula -> Bool
twins u@Ind{} v@Ind{} = trIndx u == trIndx v
twins Var {trName = u} Var {trName = v} = u == v
twins t@Trm{} s@Trm{}
  | trId t == trId s = pairs (trArgs t) (trArgs s)
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
    dive_aux t@Trm{} = t {trArgs = map dive $ trArgs t}
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
    dive Var {trName = v1} Var {trName = v2} = v1 == v2
    dive _ _ = False