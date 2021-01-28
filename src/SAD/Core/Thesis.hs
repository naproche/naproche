{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018)

Maintain the current thesis.
-}

{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}

module SAD.Core.Thesis (inferNewThesis) where


import SAD.Core.Base
import SAD.Core.Reason
import SAD.Data.Definition (Definitions)
import SAD.Data.Formula

import SAD.Data.Text.Context (Context)
import SAD.Helpers (notNull)
import qualified Data.Text.Lazy as Text
import qualified SAD.Data.Text.Context as Context

import Control.Applicative
import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.State
import Data.List
import Data.Maybe
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set


-- Infer new thesis


{- Infer the newThesis. Also report whether it is motivated and whether it has
changed at all -}
inferNewThesis :: Definitions -> [Context] -> Context -> (Bool, Bool, Context)
inferNewThesis definitions wholeContext@(context:_) thesis
  | isFunctionMacro context = functionTaskThesis context thesis
  | otherwise = (motivated, changed, newThesis)
  where
    -- a thesis can only become unmotivated through an assumption
    motivated = notAnAssumption || isJust usefulVariation
    newThesis = Context.setFormula thesis $ reduceWithEvidence $ getObj postReductionThesis
    changed = hasChanged postReductionThesis
    postReductionThesis
      | notAnAssumption = -- enable destruction of defined symbols in this case
          reduceThesis definitions (Context.formula context) preReductionThesis
      | otherwise =
          reductionInViewOf (Context.formula context) preReductionThesis
    preReductionThesis
      | notAnAssumption = thesisFormula
      | otherwise = fromMaybe thesisFormula usefulVariation
    usefulVariation = findUsefulVariation definitions wholeContext thesisFormula
    thesisFormula = strip $ Context.formula thesis
    notAnAssumption = not $ Context.isAssumption context


-- Reduce f in view of g

{- contraction in view of a set of formulae -}
reductionInViewOf :: Formula -> Formula -> ChangeInfo Formula
reductionInViewOf g = reduce
  where
    hs = externalConjuncts g
    reduce f
      | isTop f = return Top
      | isBot f = return Bot
      | any (equivalentTo f) hs = changed Top
      | any (equivalentTo $ Not f) hs = changed Bot
      | isExi f && f `hasInstantiationIn` hs = changed Top
      | isAll f && (albet $ Not f) `hasInstantiationIn` hs = changed Bot
      | isTrm f = return f
      | isIff f = reduce $ albet f
      | otherwise = bool <$> mapFM reduce f

{- the equivalence test used here is quite crude, but cheap:
syntactic equality modulo alpha-beta normalization -}
equivalentTo :: Formula -> Formula -> Bool
equivalentTo = normalizedCheck 0
  where
    normalizedCheck :: Int -> Formula -> Formula -> Bool
    normalizedCheck n f g = check n (albet f) (albet g)
    check n (All _ a) (All _ b) = let freshVariable = VarDefault $ Text.pack $ show n in
      normalizedCheck (succ n) (inst freshVariable a) (inst freshVariable b)
    check n (Exi _ a) (Exi _ b) = let freshVariable = VarDefault $ Text.pack $ show n in
      normalizedCheck (succ n) (inst freshVariable a) (inst freshVariable b)
    check n (And a b) (And c d) = normalizedCheck n a c && normalizedCheck n b d
    check n (Or a b) (Or c d)   = normalizedCheck n a c && normalizedCheck n b d
    check n (Not a) (Not b)     = normalizedCheck n a b
    check n (Tag _ a) b         = normalizedCheck n a b
    check n a (Tag _ b)         = normalizedCheck n a b
    check _ Top Top             = True
    check _ Bot Bot             = True
    check _ a b                 = twins a b


{- checks whether an instantitation of f (modulo local properties collected)
can be patched together from the hs. Important to be able to reduce an
existential thesis. -}
hasInstantiationIn:: Formula -> [Formula] -> Bool
hasInstantiationIn (Exi _ f) = notNull . listOfInstantiations f

type Instantiation = Map.Map VariableName Formula
{- the actual process of finding an instantiation. -}
listOfInstantiations :: Formula -> [Formula] -> [Instantiation]
listOfInstantiations f = instantiations 1 Map.empty (albet $ inst (VarAssume 0) f)

{- worker function for SAD.Core.Thesis.listOfInstantiations -}
-- FIXME This functions needs a better way to generate free variables. The
--       explicit parameter passing is inadequate.
instantiations :: Int -> Instantiation -> Formula -> [Formula] -> [Instantiation]
instantiations n currentInst f hs =
  [ newInst | h <- hs, newInst <- extendInstantiation currentInst f h ] ++
  patchTogether (albet f)
  where
    patchTogether :: Formula -> [Instantiation]
    patchTogether (And f g) = -- find instantiation of g then extend them to f
      [ fInst | gInst <- instantiations n currentInst (albet g) hs,
                fInst <- instantiations n gInst (albet f) $
                  subInfo gInst (pred n) ++ hs ]--add collected local properties
    patchTogether (Exi _ f) =
      instantiations (succ n) currentInst (albet $ inst (VarAssume n) f) hs
    patchTogether _ = []

    subInfo :: Instantiation -> Int -> [Formula]
    subInfo sub n =
      let sub' = applySub sub $ mkVar $ VarAssume n
      in  map (replace sub' ThisT) $ varInfo $ sub'


{- finds an instantiation to make a formula equal to a second formula.
An initial instantiation is given which is then tried to be extended.
Result is returned within the list monad. -}
extendInstantiation :: Instantiation -> Formula -> Formula -> [Instantiation]
extendInstantiation sb f g = snd <$> runStateT (normalizedDive 0 f g) sb
  where
    normalizedDive :: Int -> Formula -> Formula -> StateT (Map.Map VariableName Formula) [] ()
    normalizedDive n f g = dive n (albet f) (albet g)
    dive n (All _ f) (All _ g)
      = let nn = VarDefault $ Text.pack $ show n in normalizedDive (succ n) (inst nn f) (inst nn g)
    dive n (Exi _ f) (Exi _ g)
      = let nn = VarDefault $ Text.pack $ show n in normalizedDive (succ n) (inst nn f) (inst nn g)
    dive n (And f1 g1) (And f2 g2) =
      normalizedDive n f1 f2 >> normalizedDive n g1 g2
    dive n (Or  f1 g1) (Or  f2 g2) =
      normalizedDive n f1 f2 >> normalizedDive n g1 g2
    dive n (Not f) (Not g) = dive n f g
    dive n Trm {trId = t1, trmArgs = ts1} Trm {trId = t2, trmArgs = ts2}
      = lift (guard $ t1 == t2) >> mapM_ (uncurry $ dive n) (zip ts1 ts2)
    dive _ v@Var {varName = s@(VarAssume _)} t = do
      mp <- get; case Map.lookup s mp of
        Nothing -> modify (Map.insert s t)
        Just t' -> lift $ guard (twins t t')
    dive _ v@Var{} w@Var{} = lift $ guard (twins v w)
    dive _ _ _ = lift mzero

-- External conjuncts

{- find all external conjuncts of a formula -}
externalConjuncts :: Formula -> [Formula]
externalConjuncts = normalizedDive
  where
    normalizedDive = dive . albet
    dive h@(And f g) = h : (normalizedDive f ++ normalizedDive g)
    dive h@(Exi _ f) = h : filter isClosed (normalizedDive f)
    dive h@(All _ f) = h : filter isClosed (normalizedDive f)
    dive (Tag _ f)   = normalizedDive f
    dive f           = [f]


{- find a useful variation of the thesis (with respect to a given assumption)-}
findUsefulVariation :: Definitions -> [Context] -> Formula -> Maybe Formula
findUsefulVariation definitions (assumption:restContext) thesis =
  find useful variations
  where
    variations = map snd $
      runVM (generateVariations definitions thesis) $ Context.declaredNames assumption
    useful variation = isTop $ getObj $
      reductionInViewOf (Not variation) $ Context.formula assumption
findUsefulVariation _ _ _ =
  error "SAD.Core.Thesis.findUsefulVariation: empty context"

--- improved reduction

{- reduce the thesis and possibly look behind symbol definitions. Only one
layer of definition can be stripped away. -}
reduceThesis :: Definitions -> Formula -> Formula -> ChangeInfo Formula
reduceThesis definitions affirmation thesis =
  let reducedThesis = reductionInViewOf affirmation thesis
      expandedThesis = expandSymbols thesis
      reducedExpandedThesis =
        reductionInViewOf affirmation expandedThesis
  in  if   (not . hasChanged) reducedThesis -- if reduction does not work
      then if   (not . hasChanged) reducedExpandedThesis--try it after expansion
           then return thesis -- if it still does nothing -> give up
           else reducedExpandedThesis
      else reducedThesis
  where
    expandSymbols t@Trm{}= fromMaybe t $ defForm definitions t
    expandSymbols f = mapF expandSymbols f







-- Find possible variations

{- Generate all possible variations-}
generateVariations :: Definitions -> Formula -> VariationMonad Formula
generateVariations definitions = pass [] (Just True) (0 :: Int)
  where
    pass localContext sign n = dive
      where
        dive h@(All _ f) = case sign of
          Just True   -> liberateVariableIn f `mplus` roundThrough h
          _           -> return h
        dive h@(Exi _ f) = case sign of
          Just False  -> liberateVariableIn f `mplus` roundThrough h
          _           -> return h
        dive h@Trm{}     = return h `mplus` lookBehindDefinition h
        dive h@(And f g) = case sign of
          Just True   -> And f <$> pass (f:localContext) sign n g
          _           -> roundThrough h
        dive h@(Or  f g) = case sign of
          Just False  -> Or f  <$> pass (Not f:localContext) sign n g
          _           -> roundThrough h
        dive h@(Imp f g) = case sign of
          Just False  -> Imp f <$> pass (f:localContext) sign n g
          _           -> roundThrough h
        dive (Tag GenericMark f) = return f
        dive h           = roundThrough h

        liberateVariableIn f = generateInstantiations f >>= dive
        roundThrough = roundFM VarZ pass localContext sign n
        lookBehindDefinition t = mconcat . map (dive . reduceWithEvidence .
          markRecursive  (trmId t)) . maybeToList . defForm definitions $ t

{- mark symbols that are recursively defined in their defining formula, so that
   the definition is not infinitely expanded -}
markRecursive :: TermId -> Formula -> Formula
markRecursive n t@Trm{trId = m}
  | n == m = Tag GenericMark t
  | otherwise = t
markRecursive n f = mapF (markRecursive n) f

{- generate all instantiations with as of yet unused variables -}
generateInstantiations :: Formula -> VariationMonad Formula
generateInstantiations f = VM tryAllVars
  where
    tryAllVars vs = map go $ Set.elems vs
      where
        go v = (Set.delete v vs, inst v f)

-- Variation monad


{- monad to do bookkeeping during the search for a variation, i.e. keep track
of which variables have already been used for an instantiation -}
newtype VariationMonad res =
  VM { runVM :: Set VariableName -> [(Set VariableName, res)] }

instance Ord a => Semigroup (VariationMonad a) where
  a <> b = VM $ \s -> runVM a s <> runVM b s

instance Ord a => Monoid (VariationMonad a) where
  mempty = VM $ \s -> []

instance Functor VariationMonad where
  fmap = liftM

instance Applicative VariationMonad where
  pure  = return
  (<*>) = ap

instance Monad VariationMonad where
  return r = VM $ \ s -> [(s, r)]
  m >>= k  = VM $ \ s -> concatMap apply (runVM m s)
    where apply (s, r) = runVM (k r) s

instance Alternative VariationMonad where
  empty = mzero
  (<|>) = mplus

instance MonadPlus VariationMonad where
  mzero     = VM $ \ _ -> []
  mplus m k = VM $ \ s -> runVM m s ++ runVM k s

-- special reduction of function thesis

isFunctionMacro :: Context -> Bool
isFunctionMacro = isMacro . Context.formula
  where
    isMacro (Tag tg _ ) = fnTag tg
    isMacro _ = False

functionTaskThesis :: Context -> Context -> (Bool, Bool, Context)
functionTaskThesis context thesis = (True, changed, newThesis)
  where
    newThesis = Context.setFormula thesis $ getObj reducedThesis
    changed = hasChanged reducedThesis
    thesisFormula = Context.formula thesis
    reducedThesis = reduceFunctionTask (Context.formula context) thesisFormula

reduceFunctionTask :: Formula -> Formula -> ChangeInfo Formula
reduceFunctionTask (Tag tg _) = fmap boolSimp . dive
  where
    dive (Tag tg' _) | tg' == tg = changed Top
    dive f = mapFM dive f

-- Change Monad

{- a simple monad to keep track of whether a function has changed its
   input or returns it unchanged -}
-- FIXME This bookkeeping monad is superfluous. A simple syntactic equality
--       check to determine the changedness status should suffice and should
--       not be noticable performancewise.
data ChangeInfo a = Change {getObj :: a, hasChanged :: Bool}

instance Functor ChangeInfo where
  fmap = liftM

instance Applicative ChangeInfo where
  pure = return
  (<*>) = ap

instance Monad ChangeInfo where
  return a = Change a False
  Change a p >>= f = let Change b q = f a in Change b (p || q)

changed :: a -> ChangeInfo a -- declare a change to an object
changed a = Change a True
