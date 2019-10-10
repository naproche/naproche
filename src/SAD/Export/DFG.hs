{-
Authors: Andrei Paskevich (2001 - 2008)

Print proof task in DFG syntax.
-}

module SAD.Export.DFG (output) where

import Data.List

import SAD.Data.Formula
import SAD.Data.Text.Block (Block(Block))
import qualified SAD.Data.Text.Block as Block
import SAD.Data.Text.Context as Context (Context(..))
import SAD.Helpers
import SAD.Data.TermId

output :: Bool -> [Context] -> Context -> String
output red contexts goal = concat
  [ "begin_problem(A).list_of_descriptions.name({*EA*})."
  , "author({*EA*}).status(unknown).description({*EA*})."
  , endOfList
  , "list_of_symbols.\n"
  , dfgSLS (goal:contexts)
  , endOfList
  , "list_of_formulae(axioms).\n"
  , concatMap (formatContext red) $ reverse $ contexts
  , endOfList
  , "list_of_formulae(conjectures).\n"
  , formatContext red goal
  , endOfList
  , "end_problem.\n"
  ]
  where
    endOfList = "end_of_list.\n"

-- Formula print

formatContext :: Bool -> Context -> String
formatContext red (Context fr (Block { Block.name = m } : _) _ g) = concat
  [ "formula(" ++ formatFormula 0 (if red then g else fr) ""
  , if null m || m == "__" then "" else "," ++ m
  , ").\n" 
  ]
formatContext _ _ = ""

formatFormula :: Int -> Formula -> ShowS
formatFormula d = dive
  where
    dive (All _ f)  = showString "forall" . showParen True (binder f)
    dive (Exi _ f)  = showString "exists" . showParen True (binder f)
    dive (Iff f g)  = showString "equiv" . showArgumentsWith dive [f,g]
    dive (Imp f g)  = showString "implies" . showArgumentsWith dive [f,g]
    dive (Or  f g)  = showString "or" . showArgumentsWith dive [f,g]
    dive (And f g)  = showString "and" . showArgumentsWith dive [f,g]
    dive (Tag _ f)  = dive f
    dive (Not f)    = showString "not" . showParen True (dive f)
    dive Top        = showString "true"
    dive Bot        = showString "false"
    dive t@Trm {} | isEquality t = showString "equal" . showArgumentsWith dive (trmArgs t)
    dive t@Trm {}   = showTrName t
    dive v@Var {}   = showTrName v
    dive i@Ind {}   = showChar 'W' . shows (d - 1 - indIndex i)
    dive ThisT      = error "SAD.Export.DFG: Didn't expect ThisT here"

    binder f  = showChar '[' . formatFormula (succ d) (Ind 0 undefined)
              . showString "]," . formatFormula (succ d) f

-- | Symbol count
dfgSLS :: [Context] -> String
dfgSLS tasks  = sls "functions" functions ++ sls "predicates" predicates
  where
    sls _ [] = ""
    sls s ls = s ++ "[" ++ (commaSeparated shs ls) "" ++ "].\n"

    shs (s, a)  = showParen True $ stn s . showChar ',' . shows a
    stn = showString . filter (/= ':')

    predicates = [ (s, a) | (True,  s, a) <- sms ]
    functions = [ (s, a) | (False, s, a) <- sms ]
    sms = foldr (union . nubOrd . findSymbols True . Context.formula) [] tasks


-- | Find symbols returning Name, Arity and whether it is top-level.
findSymbols :: Bool -> Formula -> [(Bool, String, Int)]
findSymbols s t@Trm {trmId = EqualityId}      = concatMap (findSymbols False) $ trmArgs t
findSymbols s Trm {trmName = t, trmArgs = ts} = (s, t, length ts) : concatMap (findSymbols False) ts
findSymbols s Var {varName = v}               = [(s, show v, 0)]
findSymbols s Ind{}                           = []
findSymbols s f                               = foldF (findSymbols s) f