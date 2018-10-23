{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018)

Maintain the current thesis.
-}

module Alice.Core.Thesis (new_thesis) where 
import Control.Monad
import Data.List
import Data.Maybe
import Control.Applicative
import Control.Monad.Trans.State
import Control.Monad.Trans.Class

import Alice.Data.Base
import Alice.Data.Formula
import Alice.Data.Kit
import Alice.Data.Text
import Alice.Core.Base
import Alice.Core.Reason

import Debug.Trace
import qualified Data.IntMap.Strict as IM
import qualified Data.Map as M



-- Infer new thesis

{- infer the new thesis. return whether the new thesis is motivated (nmt),
   whether the thesis has changed at all (chng) and what the new thesis
   actually is (ntc). -}

new_thesis :: IM.IntMap DefEntry -> [Context] -> Context -> (Bool, Bool, Context)
new_thesis dfs cnt@(ct:_) tc | fnMacro ct = fn_thesis ct tc
                         | otherwise = (nmt, chng, ntc)
  where
    nmt = nas || isJust ith -- a thesis can only become unmotivated through an assumption
    ntc = setForm tc $ reduceWithEvidence lth
    lth = getObj kth
    chng = hasChanged kth
    kth | nas = thsReduce dfs (cnForm ct) jth -- if not an assumption, enable destruction of defined symbols
        | otherwise = tmWipe (cjs 0 $ cnForm ct) jth -- else the usual "reduction in sight of"
    jth | nas = ths
        | otherwise = fromMaybe ths ith
    ith = tmInst dfs cnt ths -- find instantiations
    ths = strip $ cnForm tc
    nas = not $ isAssm ct -- true iff the statement in question is not an assumption



-- Reduce f in sight of hs

{- contraction in view of a set of formulae -}
tmWipe :: [Formula] -> Formula -> ChangeInfo Formula
tmWipe hs f    | isTop f = return Top
               | isBot f = return Bot
               | any (tmComp 0 $ f) hs     = changed Top
               | any (tmComp 0 $ Not f) hs = changed Bot
               | isExi f && instExi f hs  = changed Top
               | isAll f && instExi (Not f) hs = changed Bot
               | isTrm f                   = return f
               | isIff f                   = tmWipe hs $ albet f
               | otherwise                 = liftM bool $ mapFM (tmWipe hs) f

tmComp n f g  = cmp (albet f) (albet g) -- tmComp compares two formulas syntactically after alpha-beta normalizing them
  where
    cmp (All _ a) (All _ b) = tmComp (succ n) (inst nvr a) (inst nvr b)  -- cmp is the syntactic comparison of two formulas
    cmp (Exi _ a) (Exi _ b) = tmComp (succ n) (inst nvr a) (inst nvr b)
    cmp (And a b) (And c d) = tmComp n a c && tmComp n b d
    cmp (Or a b) (Or c d)   = tmComp n a c && tmComp n b d
    cmp (Not a) (Not b)     = tmComp n a b
    cmp (Tag _ a) b         = tmComp n a b
    cmp a (Tag _ b)         = tmComp n a b
    cmp Top Top             = True
    cmp Bot Bot             = True
    cmp a b                 = twins a b

    nvr = show n

{- checks whether an instantitation of f can be patched together from the hs.
   Important to be able to reduceWithEvidence an existential thesis. -}
instExi (Exi _ f) hs = not . null $ instList 1 M.empty (albet $ inst "i0" f) hs
instExi (Not f) hs = instExi (albet (Not f)) hs

{- the actual process of finding an instantiation. Most conveniently expressed
   within the list monad. -}
instList n sb f hs = [ s | h <- hs, s <- instanc sb f h] `mplus` cmp (albet f)
        where -- if f is an instance of one of the hs -> done; else try to patch f together from the hs
          cmp (And f g) = [ sbs | s   <- instList n sb (albet g) hs,
                                  sbs <- instList n s (albet f) (subInfo s (pred n) ++ hs)] -- by processing g first and adding certain
          cmp (Exi _ f) = instList (succ n) sb (albet $ inst ('i':show n) f) hs             -- Info to hs, we can more conveniently deal
          cmp _ = []                                                                        -- with the typings encountered in existential
                                                                                            -- statements; it is not necessary though
          subInfo sb n = let sub = applySb sb $ zVar $ 'i':show n
                          in map (replace sub ThisT) $ trInfo $ sub
-- instance checking

{- finds an instantiation to make a formula equal to a second formula. An instantiation can be given
   which is then tried to be extended -}
instanc sb f g = liftM snd $ runStateT (dive_al 0 f g) sb
  where
    dive_al n f g = dive n (albet f) (albet g)
    dive n (All _ f) (All _ g)
      = let nn = show n in dive_al (succ n) (inst nn f) (inst nn g)
    dive n (Exi _ f) (Exi _ g)
      = let nn = show n in dive_al (succ n) (inst nn f) (inst nn g)
    dive n (And f1 g1) (And f2 g2) = dive_al n f1 f2 >> dive_al n g1 g2
    dive n (Or  f1 g1) (Or  f2 g2) = dive_al n f1 f2 >> dive_al n g1 g2
    dive n (Not f) (Not g) = dive n f g
    dive n Trm {trId = t1, trArgs = ts1} Trm {trId = t2, trArgs = ts2}
      = lift (guard $ t1 == t2) >> mapM_ (uncurry $ dive n) (zip ts1 ts2)
    dive _ v@Var {trName = s@('i':_)} t
     = do mp <- get; case M.lookup s mp of
            Nothing -> modify (M.insert s t)
            Just t' -> lift $ guard (twins t t')
    dive _ x@Var{} y@Var{} = lift $ guard (twins x y)
    dive _ _ _ = lift mzero

-- External conjucnts

{- find all external conjuncts of a formula. Usually used for "reduction in view of"-}
cjs :: Int -> Formula -> [Formula]
cjs n = acc . albet
  where
    acc h@(And f g) = h : (cjs n f ++ cjs n g)
    acc h@(Exi _ f) = h : (cjs (succ n) $ inst nvr f)
    acc h@(All _ f) = h : (cjs (succ n) $ inst nvr f)
    acc h@(Or f g)  = [h]
    acc (Tag _ f)   = cjs n f
    acc f         = [f]

    nvr = '.' : show n

-- Instantiate f with vs in sight of h

tmInst dfs (ct:cnt) ths = find gut insts
  where
    insts =  map snd $ runTM (tmPass dfs ths) $ cnDecl ct
    gut g = isTop $ getObj $  tmWipe (cjs 0 $ Not g) $ cnForm ct

--- improved reduction
{- this function enables *affirmations* to reduceWithEvidence defined symbols
   before (instead of only assumptions). Only one layer of definition
   can be stripped away at a time. -}

thsReduce :: IM.IntMap DefEntry -> Formula -> Formula -> ChangeInfo Formula
thsReduce dfs fr jth = let njth = tmWipe (cjs 0 fr) jth
                           expj = expand jth
                           nexj = tmWipe (cjs 0 fr) expj
                        in
                        if (not . hasChanged) njth                   -- if reduction had no effect
                           then
                           if (not . hasChanged) nexj                -- we check whether expanding the formula lets us reduceWithEvidence further
                              then return jth                        -- if not, we cannot detect changes to the thesis
                              else nexj                        -- if yes, we take the reduced expanded formula
                           else njth
    where
      expand t@Trm{}= fromMaybe t $ defForm dfs t
      expand f = mapF expand f







-- Find possible instantiations

{- Generate all possible instantiations-}
tmPass dfs  = pass [] (Just True) 0
  where
    pass fc sg n  = dive
      where
        dive h@(All u f)    = case sg of
                Just True   -> qua u f `mplus` rnd h
                _           -> return h                 -- do not instantitate beneath a quantifier of wrong polarity
        dive h@(Exi u f)    = case sg of
                Just False  -> qua u f `mplus` rnd h
                _           -> return h                 -- do not instantiate beneath a quantifier of wront polarity
        dive h@Trm{}  = return h `mplus` def h
        ---------- the following lines exclude formulas that are
        ---------- theoretically impossible as useful variations
        dive h@(And f g)    = case sg of
                Just True   -> liftM (And f) $ pass (f:fc) sg n g
                _           -> rnd h
        dive h@(Or  f g)    = case sg of
                Just False  -> liftM (Or f) $ pass (Not f:fc) sg n g
                _           -> rnd h
        dive h@(Imp f g)    = case sg of
                Just False  -> liftM (Imp f) $ pass (f:fc) sg n g
                _           -> rnd h
        ------------------------------------------------------------------
        dive (Tag DMK f)    = return f                   -- identify recursively defined symbols that have already been explored
        dive h              = rnd h

        qua u f = tmVars u f >>= dive
        rnd h = roundFM 'z' pass fc sg n h
        def t = msum . map (dive . reduceWithEvidence . markRec  (trId t)) . maybeToList . defForm dfs $ t -- look behind the definition of symbols
                                                                                                  -- to find an instantiation

{- mark symbols that are recursively defined in their defining formula, so that
   the definition is not infinitely expanded -}
markRec n t@Trm{trId = m} | n == m = Tag DMK t
                          | otherwise = t
markRec n f = mapF (markRec n) f

{- manage which variables have already been used for an instantiation-}
tmVars u f  = TM (vrs [])
  where
    vrs ov (v:vs) = (ov ++ vs, inst v f) : vrs (v:ov) vs
    vrs _ [] = []

-- Thesis monad


{- an easy monad to handle the search for an instantiation, i.e. keep track of
   which variables have not yet been used and conveniently explore all possibilities
   in the search tree. -}
newtype TM res = TM { runTM :: [String] -> [([String], res)] }

instance Monad TM where
  return r  = TM $ \ s -> [(s, r)]
  m >>= k   = TM $ \ s -> concatMap apply (runTM m s)
    where apply (s, r) = runTM (k r) s

instance MonadPlus TM where
  mzero     = TM $ \ _ -> []
  mplus m k = TM $ \ s -> runTM m s ++ runTM k s


-- standard declarations to prevent compiler error

instance Functor TM where
    fmap = liftM

instance Applicative TM where
    pure = return
    (<*>) = ap

instance Alternative TM where
    empty = mzero
    (<|>) = mplus





-- special reduction of function thesis

fnMacro = mcr . cnForm
  where
    mcr (Tag tg _ ) = fnTag tg
    mcr _ = False

fn_thesis ct tc = (True, chngd, ntc)
  where
    ntc = setForm tc $ getObj kth
    chngd = hasChanged kth
    ths = cnForm tc
    kth = fn_red (cnForm ct) ths

fn_red (Tag tg _) = liftM bool_simp . dive
  where
    dive (Tag tg' _) | tg' == tg = changed Top
    dive f = mapFM dive f


-- Change Monad

{- a simple monad to keep track of whether a function has changed its
   input or returns it unchanged -}

data ChangeInfo a = Change (a, Bool)

instance Monad ChangeInfo where
  return a = Change (a, False)
  Change (a, p) >>= f = let Change (b, q) = f a in Change (b, p || q)

hasChanged :: ChangeInfo a -> Bool -- extranct the change information
hasChanged (Change (a, p)) = p

getObj :: ChangeInfo a -> a -- extract the object
getObj (Change (a, p)) = a

changed :: a -> ChangeInfo a -- declare a change to an object
changed a = Change (a, True)


instance (Show a) => Show (ChangeInfo a) where
  show (Change (a, b)) = show a
-- standard declarations to prevent compiler error

instance Applicative ChangeInfo where
  pure = return
  (<*>) = ap

instance Functor ChangeInfo where
  fmap = liftM
