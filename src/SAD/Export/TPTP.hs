{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018)

Print proof task in TPTP syntax.
-}

{-# LANGUAGE OverloadedStrings #-}

module SAD.Export.TPTP (output) where

import SAD.Data.Formula (Formula(..), showTrName, TermName(..))
import Data.Text (Text)
import qualified Data.Text as Text
import SAD.Export.Representation
import SAD.Core.SourcePos (noSourcePos)

output :: [(Text, Formula)] -> (Text, Formula) -> Text
output contexts goal = 
  mconcat (map (tptpForm ",hypothesis,") $ reverse contexts)
  <> tptpForm ",conjecture," goal

-- Formula print
tptpForm :: Text -> (Text, Formula) -> Text
tptpForm s (name, fr) =
  "fof(m"
  <> (if Text.null name then "_" else  name)
  <> s <> tptpTerm 0 fr <> ").\n"

tptpTerm :: Int -> Formula -> Text
tptpTerm d = dive
  where
    dive (All _ f)  = buildParens $ " ! " <> binder f
    dive (Exi _ f)  = buildParens $ " ? " <> binder f
    dive (Iff f g)  = sinfix " <=> " f g
    dive (Imp f g)  = sinfix " => " f g
    dive (Or  f g)  = sinfix " | " f g
    dive (And f g)  = sinfix " & " f g
    dive (Tag _ f)  = dive f
    dive (Not f)    = buildParens $ " ~ " <> dive f
    dive Top        = "$true"
    dive Bot        = "$false"
    dive t@Trm {trmName = TermEquality} = let [l, r] = trmArgs t in sinfix " = " l r
    dive t@Trm {}   =  (showTrName t) <> buildArgumentsWith dive (trmArgs t)
    dive v@Var {}   =  (showTrName v)
    dive i@Ind {}   = "W" <> (Text.pack (show (d - 1 - indIndex i)))
    dive ThisT      = error "SAD.Export.TPTP: Didn't expect ThisT here"

    sinfix o f g  = buildParens $ dive f <> o <> dive g

    binder f  = "[" <> tptpTerm (succ d) (Ind 0 noSourcePos) <> "] : " <> tptpTerm (succ d) f