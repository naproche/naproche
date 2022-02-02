{-
Authors: Steffen Frerix (2017 - 2018)

Term rewriting: extraction of rules and proof of equlities.
-}

{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}

module SAD.Core.Rewrite (equalityReasoning, lpoGe) where

import SAD.Core.Base
import SAD.Core.Reason
import SAD.Data.Formula
import SAD.Data.Instr
import SAD.Data.Rules (Rule)
import SAD.Data.Text.Context (Context)
import SAD.Helpers (notNull)

import SAD.Export.Representation

import qualified SAD.Core.Message as Message
import qualified SAD.Data.Rules as Rule
import qualified SAD.Data.Text.Block as Block (body, link, position)
import qualified SAD.Data.Text.Context as Context

import Data.List
import qualified Data.Set as Set
import Control.Monad.State
import Data.Either
import Control.Monad.Reader
import Data.Text.Lazy (Text)
import qualified Data.Text.Lazy as Text
import Isabelle.Library ()
import qualified Isabelle.Position as Position


-- Lexicographic path ordering

{- a weighting to parametrize the LPO -}
type Weighting = Text -> Text -> Bool


{- standard implementation of LPO -}
lpoGe :: Weighting -> Formula -> Formula -> Bool
lpoGe w t s = twins t s || lpoGt w t s


lpoGt :: Weighting -> Formula -> Formula -> Bool
lpoGt w tr@Trm {trmName = t, trmArgs = ts} sr@Trm {trmName = s, trmArgs = ss} =
   any (\ti -> lpoGe w ti sr) ts
    || (all (lpoGt w tr) ss
    && ((t == s && lexord (lpoGt w) ts ss)
    || w (toLazyText $ represent t) (toLazyText $ represent s)))
lpoGt w Trm { trmName = t, trmArgs = ts} v@Var {varName = x} =
  w (toLazyText $ represent t) (toLazyText $ represent x) || any (\ti -> lpoGe w ti v) ts
lpoGt w v@Var {varName = x} Trm {trmName = t, trmArgs = ts} =
  w (toLazyText $ represent x) (toLazyText $ represent t) && all (lpoGt w v) ts
lpoGt w Var{varName = x} Var {varName = y} = w (toLazyText $ represent x) (toLazyText $ represent y)
lpoGt _ _ _ = False


lexord :: (Formula -> Formula -> Bool) -> [Formula] -> [Formula] -> Bool
lexord ord (x:xs) (y:ys)
  | ord x y = length xs == length ys
  | otherwise = twins x y && lexord ord xs ys
lexord _ _ _ = False


-- simplification

{- type to record conditions and intermediate steps during simplification -}
type SimpInfo = ([Formula], Text)


{- performs one simplification step. We always try to simplify in a
leftmost-bottommost fashion with respect to the term structure -}
simpstep :: [Rule] -> Weighting -> Formula -> [(Formula, SimpInfo)]
simpstep rules w = flip runStateT undefined . dive
  where
    dive t@Trm {trmName = tName, trmArgs = tArgs} =
      (do newArgs <- try tArgs; return t {trmArgs = newArgs}) `mplus` applyRule t
    dive v@Var{} = applyRule v

    try [] = mzero
    try (t:ts) = (dive t >>= \nt -> return (nt:ts)) `mplus` fmap (t :) (try ts)

    applyRule t = do
      (f, cnd, rl) <- lift (applyLeftToRight t `mplus` applyRightToLeft t)
      put (cnd, Rule.label rl); return f

    applyLeftToRight = applyRuleDirected True
    applyRightToLeft = applyRuleDirected False

    applyRuleDirected p t = do
      rule <- rules
      let (l,r) =
            if   p
            then (Rule.left rule, Rule.right rule)
            else (Rule.right rule, Rule.left rule)
      sbs <- match l t; let nr = sbs r
      guard $ full nr && lpoGt w (sbs l) nr -- simplified term must be lighter
      return (sbs r, map sbs $ Rule.condition rule, rule)

    full Var {varName = VarHole _} = False; full f = allF full f


{- finds ALL normalforms and their corresponding simplification paths -}
findNormalform :: [Rule] -> Weighting -> Formula -> [[(Formula, SimpInfo)]]
findNormalform rules w t = map (reverse . (:) (t, trivialSimpInfo)) $ dive t
  where
    trivialSimpInfo = (pure Top, mempty)
    dive t = case simpstep rules w t of
      [] -> return []
      simplifications -> do
        (simplifiedTerm, simpInfo) <- simplifications
        (:) (simplifiedTerm, simpInfo) <$> dive simplifiedTerm


{- finds two matching normalforms and outputs all conditions accumulated
during their rewriting -}
generateConditions ::
  Position.T -> Bool -> [Rule] -> Weighting -> Formula -> Formula -> VerifyMonad [SimpInfo]
generateConditions pos verbositySetting rules w l r =
  let leftNormalForms  = findNormalform rules w l
      rightNormalForms = findNormalform rules w r
      paths = simpPaths leftNormalForms rightNormalForms
  in  if   null paths
      then log (head leftNormalForms) (head rightNormalForms) >> mzero
      else let (leftPath, rightPath) = head paths
            in showPath leftPath >> showPath rightPath >>
               return (map snd $ leftPath ++ rightPath)
  where
    -- check for matching normalforms and output the paths to them
    simpPaths leftNormalForms rightNormalForms = do
      leftPath@ ((simplifiedLeft , _):_) <- leftNormalForms
      rightPath@((simplifiedRight, _):_) <- rightNormalForms
      guard (twins simplifiedLeft simplifiedRight)
      return (reverse leftPath, reverse rightPath)

    -- logging and user communication
    log leftNormalForm rightNormalForm = when verbositySetting $ do
      simpLog Message.WRITELN pos "no matching normal forms found"
      showPath leftNormalForm; showPath rightNormalForm
    showPath ((t,_):rest) = when verbositySetting $ do
      simpLog Message.WRITELN pos (show t)
      mapM_ (simpLog Message.WRITELN pos . format) rest
    -- formatting of paths
    format (t, simpInfo) = " --> " <> show t <> conditions simpInfo
    conditions (conditions, name) =
      (if Text.null name then "" else " by " <> Text.unpack name <> ",") <>
      (if null conditions then "" else " conditions: " <>
        unwords (intersperse "," $ map show conditions))


{- applies computational reasoning to an equality chain -}
equalityReasoning :: Position.T -> Context -> VerifyMonad ()
equalityReasoning pos thesis
  | body = whenInstruction printreasonParam $ reasonLog Message.WRITELN pos "equality chain concluded"
  | notNull link = getLinkedRules pos link >>= rewrite pos equation
  | otherwise = rules >>= rewrite pos equation -- if no link is given -> all rules
  where
    equation = strip $ Context.formula thesis
    link = Context.link thesis
    -- body is true for the EC section containing the equlity chain
    body = notNull $ Block.body . head . Context.branch $ thesis


getLinkedRules :: Position.T -> [Text] -> VerifyMonad [Rule]
getLinkedRules pos link = do
  rules <- rules; let setLink = Set.fromList link
  let (linkedRules, unfoundRules) = runState (retrieve setLink rules) setLink
  unless (Set.null unfoundRules) $ warn unfoundRules
  return linkedRules
  where
    warn st =
      simpLog Message.WARNING pos $
        "Could not find rules " <> unwords (map show $ Set.elems st)

    retrieve _ [] = return []
    retrieve s (c:cnt) = let nm = Rule.label c in
      if   Set.member nm s
      then modify (Set.delete nm) >> fmap (c:) (retrieve s cnt)
      else retrieve s cnt


{- fetch all rewrite rules from the global state -}
rules :: VerifyMonad [Rule]
rules = asks rewriteRules


{- applies rewriting to both sides of an equation
and compares the resulting normal forms -}
rewrite :: Position.T -> Formula -> [Rule] -> VerifyMonad ()
rewrite pos Trm {trmName = TermEquality, trmArgs = [l,r]} rules = do
  verbositySetting <- askInstructionParam printsimpParam
  conditions <- generateConditions pos verbositySetting rules (>) l r;
  mapM_ (dischargeConditions pos verbositySetting . fst) conditions
rewrite _ _ _ = error "SAD.Core.Rewrite.rewrite: non-equation argument"


{- dischargeConditions accumulated during rewriting -}
dischargeConditions :: Position.T -> Bool -> [Formula] -> VerifyMonad ()
dischargeConditions pos verbositySetting conditions =
  setup $ easy >>= hard
  where
    easy = mapM trivialityCheck conditions
    hard hardConditions
      | all isRight hardConditions =
          if all isTop $ rights hardConditions
          then return ()
          else log $ "trivial " <> header rights hardConditions
      | otherwise = do
          log (header lefts hardConditions <> thead (rights hardConditions))
          thesis <- asks currentThesis
          mapM_ (proveThesis' pos . Context.setFormula (wipeLink thesis)) (lefts hardConditions)

    setup :: VerifyMonad a -> VerifyMonad a
    setup action = do
      timelimit <- SetInt timelimitParam <$> askInstructionParam checktimeParam
      depthlimit <- SetInt depthlimitParam <$> askInstructionParam checkdepthParam
      addInstruction timelimit $ addInstruction depthlimit action

    header select conditions = "condition: " <> format (select conditions)
    thead [] = ""; thead conditions = "(trivial: " <> format conditions <> ")"
    format conditions =
      if   null conditions
      then " - "
      else unwords . intersperse "," . map show $ reverse conditions
    log msg =
      when verbositySetting $ asks currentThesis >>=
        flip (simpLog Message.WRITELN . Block.position . Context.head) msg

    wipeLink thesis =
      let block:restBranch = Context.branch thesis
      in  thesis {Context.branch = block {Block.link = []} : restBranch}
