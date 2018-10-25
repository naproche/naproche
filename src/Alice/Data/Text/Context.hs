module Alice.Data.Text.Context where

import Alice.Data.Text.Block
import Alice.Data.Formula (Formula)

data Context  = Context { cnForm :: Formula,  -- formula of the context
                          cnBran :: [Block],  -- branch of the context
                          cnMESN :: [MRule],  -- MESON rules extracted from the formula
                          cnRedu :: Formula } -- ontologically reduced formula

data MRule = MR { asm :: [Formula], -- assumptions of the rule
                  conc :: Formula } -- conclusion of the rule
                    deriving Show



-- Context utilities

cnHead  = head . cnBran
cnTail  = tail . cnBran
cnTopL  = null . cnTail                     -- Top Level context
cnLowL  = not  . cnTopL                     -- Low Level context

cnSign  = blSign . cnHead
cnDecl  = blDecl . cnHead
cnName  = blName . cnHead
cnLink  = blLink . cnHead



isAssm = (==) Assume . blType . cnHead

setForm :: Context -> Formula -> Context
setForm cx fr = cx { cnForm = fr }

setRedu :: Context -> Formula -> Context
setRedu cx fr = cx { cnRedu = fr }


instance Show Context where
  show = show . cnForm