{-
Authors: Steffen Frerix (2017 - 2018)

Term rewriting: extraction of rules and proof of equlities.
-}



module Alice.Core.Rewrite (eqReason, extractRule, printrules) where


import Alice.Data.Base
import Alice.Data.Formula
import Alice.Data.Kit
import Alice.Data.Text
import Alice.Core.Base
import Alice.Data.Instr
import Alice.Core.Thesis
import Alice.Core.Reason



import Data.List
import Data.Maybe
import qualified Data.IntMap.Strict as IM
import qualified Data.Set as Set
import Control.Monad.State
import Data.Either
import Control.Monad.Reader

import Debug.Trace
import Control.Monad



type Weighting = String -> String -> Bool


-- Lexicographic path ordering

{- standard implementation of LPO -}
lpoGe :: Weighting -> Formula -> Formula -> Bool
lpoGe w t s = twins t s || lpoGt w t s

lpoGt :: Weighting -> Formula -> Formula -> Bool
lpoGt w tr@Trm {trName = t, trArgs = ts} sr@Trm {trName = s, trArgs = ss} =
     any (\ti -> lpoGe w ti sr) ts
  || (all (lpoGt w tr) ss
  && ((t == s && lexord (lpoGt w) ts ss)
  || w t s))
lpoGt w Trm { trName = t, trArgs = ts} v@Var {trName = x} = w t x || any (\ti -> lpoGe w ti v) ts
lpoGt w v@Var {trName = x} Trm {trName = t, trArgs = ts} = w x t && all (lpoGt w v) ts
lpoGt w Var{trName = x} Var {trName = y} = w x y
lpoGt _ _ _ = False

lexord :: (Formula -> Formula -> Bool) -> [Formula] -> [Formula] -> Bool
lexord ord (x:xs) (y:ys) | ord x y = length xs == length ys
                         | otherwise = twins x y && lexord ord xs ys
lexord _ _ _ = False


-- simplification

{- performs one simplification step. We always try to simplify in a leftmost-bottommost fashion
   with respect to the term structure -}


type SI = ([Formula], String)



simpstep :: [Rule] -> Weighting -> Formula -> [(Formula, SI)]
simpstep rls w = flip runStateT undefined . dive -- dive :: StateT SI Maybe Formula
  where
    dive t@Trm {trName = tr, trArgs = ts} = (try ts [] >>= \nts -> return t {trArgs = nts}) `mplus` app t
    dive v@Var{} = app v

    try [] _ = mzero
    try (t:ts) rs = (dive t >>= \nt -> return $ reverse rs ++ (nt:ts)) `mplus` try ts (t:rs)

    app t = do (f, cnd, rl) <- lift (app_l True t `mplus` app_l False t); put (cnd, rlLabl rl); return f

    app_l p t = do rl <- rls; let (l,r) = if p then (rlLeft rl, rlRght rl) else (rlRght rl, rlLeft rl);
                   sbs <- match l t; guard $ full (sbs r) && check sbs l r; return (sbs r, map sbs $ rlCond rl, rl)

    check sbs l r = lpoGt w (sbs l) (sbs r); full Var {trName = '?':_} = False; full f = allF full f






findnf :: [Rule] -> Weighting -> Formula -> [[(Formula, SI)]]
findnf rls w f = map (reverse . (:) (f, (pure Top, ""))) $ dive f
  where
    dive f = case simpstep rls w f of [] -> return []; smps -> do (t,gs) <- smps; liftM ((:) (t,gs)) $ dive t



findp :: Bool -> [Rule] -> Weighting -> Formula -> Formula -> VM [SI]
findp verb rls w l r = let ls = findnf rls w l; rs = findnf rls w r; pths = paths ls rs
                        in if null pths then (out ls rs >> mzero)
                            else let (sl, sr) = head pths in showpath sl >> showpath sr >> return (map snd $ sl ++ sr)
  where
    paths ls rs = do lp@((l, _):_) <- ls; rp@((r, _):_) <- rs; guard (twins l r); return (reverse lp, reverse rp)
    out ls rs = when verb $
                      do slog0 $ "no matching normal forms found"; showpath (head ls); showpath (head rs)
    showpath ((f,_):ls) = when verb $ slog0 (show f) >> mapM_ (\(f,gs) -> slog0 $ " --> " ++ show f ++ conditions gs) ls
    conditions (gs, nm) = annote nm (" by " ++ nm ++ ",") ++  annote gs (" conditions: " ++ unwords (intersperse "," $ map show gs))
    annote s str = if null s then "" else str



{- apply simplification steps until a normal form is reached. If verbose mode is
   active, also print a log of the simplifications performed -}
simplify :: Bool -> [Rule] -> Weighting -> Formula -> VM Formula
simplify verb rls w f = return Top



{- applies computational reasoning to an equality chain -}
eqReason :: Context -> VM ()
eqReason ths | body = do whenIB IBPrsn False $ rlog0 $ "eqchain concluded"
                         return ()
             | (not . null) (link) = do frl <- retrieveRl link; comp frl $ strip $ cnForm ths -- get the referenced rewrite rules and call comp for rewriting
             | otherwise = do rls <- rules; comp rls $ strip $ cnForm ths -- if no link is provided, take all rules
    where
      link = cnLink ths
      body = (not .null) $ blBody . head . cnBran $ ths -- this is true for the overaching block of the EC

retrieveRl :: [String] -> VM [Rule]
retrieveRl ln = do rls <- rules; nln <- getLink ln; let (nrl, st) = runState (retrieveMN nln rls) nln
                   unless (Set.null st) $ warn st; return nrl
  where
    warn st = slog0 $ "Warning: Could not find rules " ++ unwords (map show $ Set.elems st)


rules = asks vsRuls


{- applies rewriting and compares the resulting normal forms -}
comp :: [Rule] -> Formula -> VM ()
comp rls Trm {trName = "=", trArgs = [l,r]}=
  do verb <- askRSIB IBPsmp False -- check if printsimp is on
     gs <- findp verb rls (>) l r; cx <- thesis
     mapM_ (solve_gs cx verb) $ map fst gs
     return ()


solve_gs cx verb gs = setup >> easy >>= hard
  where
    easy     = mapM triv gs
    hard hgs | all isRight hgs = whdt hgs >> cleanup
             | otherwise = whd (header lefts hgs ++ thead (rights hgs))
                          >> (mapM (reason . setForm ccx) (lefts hgs) >> cleanup) <|> (cleanup >> mzero)


    setup    = do  askRSII IIchtl 1 >>= addRSIn . InInt IItlim
                   askRSII IIchdp 3 >>= addRSIn . InInt IIdpth
                   addRSIn $ InBin IBOnto False


    cleanup  = do  drpRSIn $ IdInt IItlim
                   drpRSIn $ IdInt IIdpth
                   drpRSIn $ IdBin IBOnto

    header sel gs = "condition: " ++ grds (sel gs)
    thead [] = ""; thead gs = "(trivial: " ++ grds gs ++ ")"
    grds  gs = if null gs then " - " else unwords . intersperse "," . map show $ reverse gs
    whd = when verb . slog cx
    whdt hgs = if all isTop $ rights hgs then return () else whd ("trivial " ++ header rights hgs)

    ccx = let bl:bs = cnBran cx in cx { cnBran = bl { blLink = [] } : bs }

    triv g = if rapid g
               then return $ Right g  -- triviality check
               else callown `withGoal` g >> return (Right g)
                 <|> return (Left g)




-- extraction of rewrite rules

{- extracts eligible rewrite rules from a formula.
   dive moves though the formula and collects conditions
   for a rewrite rule to be applicable. Only conditions that
   are made clear by implication can be detected. -}
extractRule :: Context -> [Rule]
extractRule c = map (\rl -> rl {rlLabl = cnName c}) $ dive 0 [] $ cnForm c
  where
    dive n gs (All _ (Iff (Tag DHD Trm {trName = "=", trArgs = [_,t]}) f )) -- if a DHD is reached, discard all collected guards (they must always be true locally)
      = dive n gs $ subst t "" $ inst "" f
    dive n gs (All _ (Imp (Tag DHD Trm {trName = "=", trArgs = [_, t]}) f))                 -- -"-
      = dive n gs $ subst t "" $ inst "" f
    dive n gs (All _ f) = let nn = '?' : show n in dive (succ n) gs $ inst nn f -- instantiate universal quant
    dive n gs (Imp f g) = dive n (deAnd f ++ gs) g            -- record conditions
    dive n gs (Tag _ f) = dive n gs f                -- ignore tags
    dive n gs (And f g) = dive n gs f ++ dive n gs g -- search for rewrite rules separately in the conjuncts
    dive n gs Trm {trName = "=", trArgs = [l,r]} | head (trName l) /= '?' --check that the left side is not simply a variable
      = return $ Rule l r gs undefined
    dive n gs (Not Trm{}) = mzero
    dive n gs f | isNot f = dive n gs $ albet f -- pushdown negation
    dive _ _ _ = mzero




-- show instances and user communication

instance Show Rule where
  show rl = show (rlLeft rl) ++ " = " ++ show (rlRght rl) ++ ", Cond: " ++ show (rlCond rl) ++ ", Label: " ++ show (rlLabl rl)

printrules :: [Rule] -> String
printrules = unlines . map show

slog0 tx = putStrLnRM $ "[Simplf] " ++ tx

slog cx tx = do tfn <- askRSIS ISfile ""
                slog0 $ blLabl tfn (cnHead cx) ++ tx
