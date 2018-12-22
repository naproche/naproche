{-
Authors: Andrei Paskevich (2001 - 2008)

Print proof task in DFG syntax.
-}

module SAD.Export.DFG (output) where

import Data.List
import qualified Data.IntMap.Strict as IM

import SAD.Data.Formula
import SAD.Data.Text.Block (Block(Block))
import  qualified SAD.Data.Text.Block as Block
import SAD.Data.Text.Context as Context (Context(..))
import SAD.Export.Base

output :: Bool -> Prover -> Int -> [Context] -> Context -> String
output red _ _ cn gl = (hdr . sym . axm . cnj . eop) ""
  where
    hdr = showString "begin_problem(A).list_of_descriptions.name({*EA*})."
        . showString "author({*EA*}).status(unknown).description({*EA*})."
        . eol

    sym = showString "list_of_symbols.\n" . dfgSLS (gl:cn) . eol

    axm = showString "list_of_formulae(axioms).\n" . axs . eol
    cnj = showString "list_of_formulae(conjectures).\n" . gll . eol

    eol = showString "end_of_list.\n"
    eop = showString "end_problem.\n"

    axs = foldr (flip (.) . dfgForm red) id cn
    gll = dfgForm red gl


-- Formula print

dfgForm :: Bool -> Context -> ShowS
dfgForm red (Context fr (Block { Block.name = m } : _) _ g)
        = let f = if red then g else fr in
          showString "formula(" . dfgTerm 0 f .
          (if null m || m == "__" then id else showChar ',' . showString m) .
          showString ").\n"

dfgTerm :: Int -> Formula -> ShowS
dfgTerm d = dive
  where
    dive (All _ f)  = showString "forall" . showParen True (binder f)
    dive (Exi _ f)  = showString "exists" . showParen True (binder f)
    dive (Iff f g)  = showString "equiv" . showArgumentsWith dive [f,g]
    dive (Imp f g)  = showString "implies" . showArgumentsWith dive [f,g]
    dive (Or  f g)  = showString "or" . showArgumentsWith dive [f,g]
    dive (And f g)  = showString "and" . showArgumentsWith dive [f,g]
    dive (Tag _ f)  = dive f
    dive (Not f)    = showString "not" . showArgumentsWith dive [f]
    dive Top        = showString "true"
    dive Bot        = showString "false"
    dive t| isEquality t = showString "equal" . showArgumentsWith dive (trArgs t)
          | isTrm t = showTrName t . showArgumentsWith dive (trArgs t)
          | isVar t = showTrName t
          | isInd t = showChar 'W' . shows (d - 1 - trIndx t)

    binder f  = showChar '[' . dfgTerm (succ d) (Ind 0 undefined)
              . showString "]," . dfgTerm (succ d) f

showTrName = showString . filter (/= ':') . trName


-- Symbol count

dfgSLS :: [Context] -> ShowS
dfgSLS tsk  = sls "functions" fns . sls "predicates" pds
  where
    sls s (hd:tl) = showString s . showChar '[' . shs hd
                  . showTailWith shs tl . showString "].\n"
    sls _ _ = id

    shs (s, a)  = showParen True $ stn s . showChar ',' . shows a
    stn = showString . filter (/= ':')

    pds = [ (s, a) | (True,  s, a) <- sms ]
    fns = [ (s, a) | (False, s, a) <- sms ]
    sms = foldr (union . nub . dfgSyms True . Context.formula) [] tsk

dfgSyms :: Bool -> Formula -> [(Bool, String, Int)]
dfgSyms s f | isEquality f   = concatMap (dfgSyms False) $ trArgs f
dfgSyms s Trm {trName = t, trArgs = ts} = (s, t, length ts) : concatMap (dfgSyms False) ts
dfgSyms s Var {trName = v}     = [(s, v, 0)]
dfgSyms s Ind{}     = []
dfgSyms s f             = foldF (dfgSyms s) f
