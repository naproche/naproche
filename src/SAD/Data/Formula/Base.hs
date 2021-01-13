{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018)

Core functions on formulas.
-}

module SAD.Data.Formula.Base
  ( Formula(..), Tag(..), AllEq(..)
  , occursIn, isClosed, subst, substs, bind, mapF, foldF, replace
  , Decl(..), newDecl, positionedDecl
  ) where

import Data.Maybe
import qualified Data.Monoid as Monoid
import Control.Monad.Identity
import Control.Applicative

import SAD.Core.SourcePos (SourcePos, noSourcePos)
import SAD.Data.Terms
import SAD.Data.VarName

import qualified Data.Map as Map

data Formula =
  All Decl Formula        | Exi Decl Formula |
  Class Decl Formula      |
  Iff Formula Formula     | Imp Formula Formula     |
  Or  Formula Formula     | And Formula Formula     |
  Tag Tag Formula         | Not Formula             |
  Top                     | Bot                     |
  Trm { trmName :: TermName, trmArgs :: [Formula],
        trmInfo :: [Formula], trmId  :: AllEq TermId}    |
  -- | Free variables 'Var'.
  Var { varName :: VarName, varInfo :: [Formula], varPosition :: SourcePos } |
  -- | This is used for representing bound variables through de Brujin indices.
  -- @Ind n indPosition@ tells us that the variable corresponding
  -- to this index has been quantified over at the @n@th quantifier one meets if one
  -- traverses the formula from the inside to the outside.
  Ind { indIndex :: Int, indPosition :: SourcePos } | ThisT
  deriving (Eq, Ord, Show)

data AllEq a = AllEq { fromAllEq :: a }
  deriving (Show)

instance Eq (AllEq a) where (==) _ _ = True
instance Ord (AllEq a) where (<=) _ _ = True

data Tag =
  Dig | DigMultiSubject | DigMultiPairwise | HeadTerm |
  InductionHypothesis | CaseHypothesisTag | EqualityChain |
  -- Tags to mark certain parts of function definitions
  GenericMark | Evaluation | Condition | Defined | Domain | Replacement |
  -- Tags to mark parts in function proof tasks
  DomainTask | ExistenceTask | UniquenessTask | ChoiceTask | CoercionTag
  deriving (Eq, Ord, Show)

-- | >0, with 0 as undefined
type Serial = Int

-- | A variable declaration.
data Decl = Decl {
  declName :: VarName,
  declPosition :: SourcePos,
  declSerial :: Serial
} deriving (Eq, Ord, Show)

{- a declaration that has no representation in the input text -}
newDecl :: VarName -> Decl
newDecl v = Decl v noSourcePos 0

{- a declaration that has a representation in the input text but has not been
generated during parsing -}
positionedDecl :: PosVar -> Decl
positionedDecl (PosVar nm pos) = Decl nm pos 0

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

-- | check for closedness in the sense that the formula contains no non-bound
-- de Bruijn index.
isClosed :: Formula -> Bool
isClosed  = dive 0
  where
    dive n (All _ g) = dive (succ n) g
    dive n (Exi _ g) = dive (succ n) g
    dive n t@Trm{} = all (dive n) $ trmArgs t
    dive _ Var{} = True
    dive n Ind {indIndex = v} = v < n
    dive n f = allF (dive n) f

{- checks whether the non-compound formula t occurs anywhere in the formula f -}
occursIn :: Formula -> Formula -> Bool
t `occursIn` f = twins t f || anyF (t `occursIn`) f

-- | @bind v f@ bind the variable @v@ in the formula @f@. This means that the variable gets
-- replaced by a corresponding de Brujin index. To ensure the term is closed, one
-- needs to quantify over it after calling this function. This also affects any info stored.
bind :: VarName -> Formula -> Formula
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

-- | @subst t v f@ substitutes all occurrences of the free variable @v@ inside the formula @f@ by the formula @t@. Does not affect info.
subst :: Formula -> VarName -> Formula -> Formula
subst t v f = substs f [v] [t]

-- | @substs f v ts@ substitutes all occurrences of the free variables @vs@ inside the formula @f@ by the corresponding formulas @ts@. Does not affect info.
substs :: Formula -> [VarName] -> [Formula] -> Formula
substs f vs ts = dive f
  where
    dive v@Var {varName = u} = fromMaybe v (Map.lookup u zvt)
    dive f = mapF dive f
    zvt = Map.fromList $ zip vs ts



-- Compare and replace

{- check for syntactic equality of terms/atomic formulas. Always yields False
for compound formulas. -}
twins :: Formula -> Formula -> Bool
twins u@Ind{} v@Ind{} = indIndex u == indIndex v
twins Var {varName = u} Var {varName = v} = u == v
twins t@Trm{} s@Trm{}
  | fromAllEq (trmId t) == fromAllEq (trmId s) = pairs (trmArgs t) (trmArgs s)
  where
    pairs (p:ps) (q:qs) = twins p q && pairs ps qs
    pairs [] [] = True
    pairs _ _ = False
twins ThisT ThisT = True
twins _ _ = False

-- made these change to occurs because it should be a syntactical check and have
-- nothing to do with info

-- | @replace t s f@ replace the term @s@ by the term @t@ in @f@. Does not affect info.
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