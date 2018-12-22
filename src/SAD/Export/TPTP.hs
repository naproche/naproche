{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018)

Print proof task in TPTP syntax.
-}

module SAD.Export.TPTP (output) where


import qualified Data.IntMap.Strict as IM

import SAD.Data.Formula
import SAD.Data.Text.Block (Block(Block))
import qualified SAD.Data.Text.Block as Block
import SAD.Data.Text.Context (Context(..))
import SAD.Export.Base

import Debug.Trace

output :: Bool -> Prover -> Int -> [Context] -> Context -> String
output red _ _ cn gl = (axs . cnj) ""
  where
    axs = foldr (flip (.) . tptpForm red ",hypothesis,") id cn
    cnj = tptpForm red ",conjecture," gl


-- Formula print

tptpForm :: Bool -> String -> Context -> ShowS
tptpForm red s (Context fr (Block { Block.name = m } : _) _ g)
          = let f = if red then g else fr in
            showString "fof(m"
          . showString (if null m then "_" else m)
          . showString s . tptpTerm 0 f . showString ").\n"

tptpTerm :: Int -> Formula -> ShowS
tptpTerm d = dive
  where
    dive (All _ f)  = showParen True $ showString " ! " . binder f
    dive (Exi _ f)  = showParen True $ showString " ? " . binder f
    dive (Iff f g)  = sinfix " <=> " f g
    dive (Imp f g)  = sinfix " => " f g
    dive (Or  f g)  = sinfix " | " f g
    dive (And f g)  = sinfix " & " f g
    dive (Tag _ f)  = dive f
    dive (Not f)    = showParen True $ showString " ~ " . dive f
    dive Top        = showString "$true"
    dive Bot        = showString "$false"
    dive t| isEquality t = let [l, r] = trArgs t in sinfix " = " l r
          | isTrm t = showTrName t . showArgumentsWith dive (trArgs t)
          | isVar t = showTrName t
          | isInd t = showChar 'W' . shows (d - 1 - trIndx t)

    sinfix o f g  = showParen True $ dive f . showString o . dive g

    binder f  = showChar '[' . tptpTerm (succ d) (Ind 0 undefined)
              . showString "] : " . tptpTerm (succ d) f

showTrName = showString . filter (/= ':') . trName
