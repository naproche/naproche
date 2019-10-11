{-
Authors: Andrei Paskevich (2001 - 2008)

Print proof task in DFG syntax.
-}

{-# LANGUAGE OverloadedStrings #-}

module SAD.Export.DFG (output) where

import Data.List

import SAD.Data.Formula hiding (commaSeparated)
import SAD.Data.Text.Block (Block(Block))
import qualified SAD.Data.Text.Block as Block
import SAD.Data.Text.Context as Context (Context(..))
import SAD.Helpers
import SAD.Data.TermId
import Data.Text.Lazy (Text)
import SAD.Core.SourcePos (noSourcePos)
import qualified Data.Text.Lazy as Text
import Data.Text.Lazy.Builder (Builder)
import qualified Data.Text.Lazy.Builder as Builder
import SAD.Export.Representation

output :: Bool -> [Context] -> Context -> Text
output red contexts goal = forceBuilder $ mconcat $
  [ "begin_problem(A).list_of_descriptions.name({*EA*})."
  , "author({*EA*}).status(unknown).description({*EA*})."
  , endOfList
  , "list_of_symbols.\n"
  , dfgSLS (goal:contexts)
  , endOfList
  , "list_of_formulae(axioms).\n"
  ] ++ (map (formatContext red) $ reverse $ contexts) ++
  [ endOfList
  , "list_of_formulae(conjectures).\n"
  , formatContext red goal
  , endOfList
  , "end_problem.\n"
  ]
  where
    endOfList = "end_of_list.\n"

formatContext :: Bool -> Context -> Builder
formatContext red (Context fr (Block { Block.name = m } : _) _ g) = mconcat
  [ "formula(", formatFormula 0 (if red then g else fr)
  , if Text.null m || m == "__" then "" else "," <> (Builder.fromLazyText m)
  , ").\n" 
  ]
formatContext _ _ = ""

formatFormula :: Int -> Formula -> Builder
formatFormula d = dive
  where
    dive :: Formula -> Builder
    dive (All _ f)  = "forall"  <> buildParens (binder f)
    dive (Exi _ f)  = "exists"  <> buildParens (binder f)
    dive (Iff f g)  = "equiv"   <> buildArgumentsWith dive [f,g]
    dive (Imp f g)  = "implies" <> buildArgumentsWith dive [f,g]
    dive (Or  f g)  = "or"      <> buildArgumentsWith dive [f,g]
    dive (And f g)  = "and"     <> buildArgumentsWith dive [f,g]
    dive (Tag _ f)  = dive f
    dive (Not f)    = "not"     <> buildParens (dive f)
    dive Top        = "true"
    dive Bot        = "false"
    dive t@Trm {} | isEquality t = "equal" <> buildArgumentsWith dive (trmArgs t)
    dive t@Trm {}   = Builder.fromLazyText $ showTrName t
    dive v@Var {}   = Builder.fromLazyText $ showTrName v
    dive i@Ind {}   = "W" <> (Builder.fromString $ show (d - 1 - indIndex i))
    dive ThisT      = error "SAD.Export.DFG: Didn't expect ThisT here"

    binder f = "[" <> formatFormula (succ d) (Ind 0 noSourcePos) <> "]," <> formatFormula (succ d) f

-- | Symbol count
dfgSLS :: [Context] -> Builder
dfgSLS tasks  = sls "functions" functions <> sls "predicates" predicates
  where
    sls _ [] = ""
    sls s ls = s <> "[" <> (commaSeparated shs ls) <> "].\n"

    shs (s, a)  = buildParens $ (Builder.fromLazyText $ Text.filter (/= ':') $ forceBuilder s) <> "," <> (Builder.fromString (show a))

    predicates = [ (s, a) | (True,  s, a) <- sms ]
    functions = [ (s, a) | (False, s, a) <- sms ]
    sms = foldr (union . nubOrd . findSymbols True . Context.formula) [] tasks


-- | Find symbols returning Name, Arity and whether it is top-level.
findSymbols :: Bool -> Formula -> [(Bool, Builder, Int)]
findSymbols s t@Trm {trmId = EqualityId}      = concatMap (findSymbols False) $ trmArgs t
findSymbols s Trm {trmName = t, trmArgs = ts} = (s, Builder.fromLazyText t, length ts) : concatMap (findSymbols False) ts
findSymbols s Var {varName = v}               = [(s, represent v, 0)]
findSymbols s Ind{}                           = []
findSymbols s f                               = foldF (findSymbols s) f