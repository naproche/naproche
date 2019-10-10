{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018)

Print proof task in TPTP syntax.
-}

module SAD.Export.TPTP (output) where

import SAD.Data.Formula (Formula(..), isEquality, showTrName, showArgumentsWith)
import SAD.Data.Text.Block (Block(Block))
import qualified SAD.Data.Text.Block as Block
import SAD.Data.Text.Context (Context(..))

output :: Bool -> [Context] -> Context -> String
output red contexts goal = concat
  [ concatMap (tptpForm red ",hypothesis,") $ reverse contexts
  , tptpForm red ",conjecture," goal
  ]

-- Formula print
tptpForm :: Bool -> String -> Context -> String
tptpForm red s (Context fr (Block { Block.name = m } : _) _ g) = concat
  [ "fof(m"
  , (if null m then "_" else m)
  , s, tptpTerm 0 fr "", ").\n"
  ]
tptpForm _ _ _ = ""

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
    dive t@Trm {} | isEquality t = let [l, r] = trmArgs t in sinfix " = " l r
    dive t@Trm {}   = showTrName t . showArgumentsWith dive (trmArgs t)
    dive v@Var {}   = showTrName v
    dive i@Ind {}   = showChar 'W' . shows (d - 1 - indIndex i)
    dive ThisT      = error "SAD.Export.TPTP: Didn't expect ThisT here"

    sinfix o f g  = showParen True $ dive f . showString o . dive g

    binder f  = showChar '[' . tptpTerm (succ d) (Ind 0 undefined)
              . showString "] : " . tptpTerm (succ d) f