{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}

module SAD.Structures.StructureTree where

import SAD.Data.Formula as Formula
import qualified SAD.Structures.Formula as F
import qualified SAD.Structures.Export as E
import qualified SAD.Structures.Translate as T
import SAD.Data.Text.Block
import Data.Text.Lazy (Text)
import qualified Data.Text.Lazy as T
import Data.Tree
import qualified Data.Text.Lazy as Text
import SAD.Data.Text.Decl
import SAD.Core.Message (show_position)
import Data.List (foldl')

data ForthelExpr = ForthelExpr
  { forthelName :: Text
  , forthelAssumptions :: [Formula]
  , forthelTopLevel :: Bool
  , forthelNeedsProof :: Bool
  , forthelCanDeclare :: Bool
  , forthelFormula :: Formula
  } deriving (Eq, Show)

extractBlocks :: ProofText -> Forest ForthelExpr 
extractBlocks (ProofTextBlock b) = 
  [ Node (ForthelExpr (name b) [] (isTopLevel b) (needsProof b) (canDeclare (kind b)) (formula b))
    (concatMap extractBlocks (body b))]
extractBlocks (ProofTextRoot t) = concatMap extractBlocks t
extractBlocks _ = []

toStatement :: Tree ForthelExpr -> Either Text ForthelExpr
toStatement (Node e xs) = (\(b, x, xs) -> e {forthelNeedsProof = b, forthelFormula = x, forthelAssumptions = xs}) <$> go xs
  where
    go :: Forest ForthelExpr -> Either Text (Bool, Formula, [Formula])
    go [] = Left "Empty theorem."
    go xs = let (ys,y) = unsnoc xs 
      in if any (forthelNeedsProof . rootLabel) ys 
        then Left "Multiple statements in a theorem are not supported!" 
        else Right $
          ( forthelNeedsProof $ rootLabel y
          , forthelFormula $ rootLabel y
          , map (forthelFormula . rootLabel) ys)
    unsnoc xs = (init xs, last xs)

pattern (:\/), (:/\), (:->), (:<->), (:==) :: Formula -> Formula -> Formula
pattern a :\/ b = Or a b
pattern a :/\ b = And a b
pattern a :-> b = Imp a b
pattern a :<-> b = Iff a b
pattern a :== b <- Trm _ [a, b] _ EqualityId

-- TODO: By removing the de-brujin indices,
-- we might end up with wrong bindings of variables.
toDeclaration :: ForthelExpr -> F.Declaration
toDeclaration (ForthelExpr {..}) =
  let work = go []
      go xs (All d f) = let v = T.pack $ show $ declName d 
        in F.All v (go (v:xs) f)
      go xs (Exi d f) = let v = T.pack $ show $ declName d
        in F.Exists v (go (v:xs) f)
      go xs (Iff f g) = (go xs f) F.:<-> (go xs g)
      go xs (Imp f g) = (go xs f) F.:-> (go xs g)
      go xs (Or f g) = (go xs f) F.:\/ (go xs g)
      go xs (And f g) = (go xs f) F.:/\ (go xs g)
      go xs (Tag _ f) = go xs f
      go xs (Not f) = (F.Const "not") F.:@ (go xs f)
      go xs Top = F.Top
      go xs Bot = F.Bot
      go xs (Trm _ [f, g] _ EqualityId) = (go xs f) F.:== (go xs g)
      go xs (Trm (TermNotion name) args info id) =
        foldl' (F.:@) (F.TyPredicate name) (map (go xs) args)
      go xs (Trm (TermUnaryAdjective name) args info id) =
        foldl' (F.:@) (F.Predicate name) (map (go xs) args)
      go xs (Trm (TermMultiAdjective name) args info id) =
        foldl' (F.:@) (F.Predicate name) (map (go xs) args)
      go xs (Trm name args info id) =
        foldl' (F.:@) (F.Const (termToText name)) (map (go xs) args)
      go xs (Var name info pos) = F.Variable (varToText name)
      go xs (Ind idx pos) = F.Variable (xs !! idx)
      go xs ThisT = F.Const "ThisT"
  in case forthelNeedsProof of
    True -> F.Conjecture forthelName (map work forthelAssumptions) (work forthelFormula)
    False -> F.Hypothesis forthelName (map work (forthelAssumptions ++ [forthelFormula]))

varToText :: VariableName -> Text
varToText (VarConstant t) = t
varToText v = T.pack $ show v

termToText :: TermName -> Text
termToText (TermName t) = t
termToText (TermSymbolic t) = t
termToText (TermNotion t) = t
termToText (TermThe t) = t
termToText (TermUnaryAdjective t) = t
termToText (TermMultiAdjective t) = t
termToText (TermUnaryVerb t) = t
termToText (TermMultiVerb t) = t
termToText t = T.pack $ show t

toLeanCode :: [ForthelExpr] -> Text
toLeanCode fs = "axiom omitted {p : Prop} : p\n\n" 
  <> E.export (T.translateDoc $ F.Document (map toDeclaration fs))

ppForthelExpr :: ForthelExpr -> String
ppForthelExpr (ForthelExpr {..}) = 
  (if forthelNeedsProof then "T " else "A ") 
  ++ Text.unpack forthelName ++ ": " ++ show (foldr Imp forthelFormula forthelAssumptions)

debugShow :: Formula -> String
debugShow (All d f) = "All " ++ show d ++ " " ++ parens (debugShow f)
debugShow (Exi d f) = "Exi " ++ show d ++ " " ++ parens (debugShow f)
debugShow (Iff f g) = parens (debugShow f) ++ " <=> " ++ parens (debugShow g)
debugShow (Imp f g) = parens (debugShow f) ++ " => " ++ parens (debugShow g)
debugShow (Or f g) = parens (debugShow f) ++ " or " ++ parens (debugShow g)
debugShow (And f g) = parens (debugShow f) ++ " and " ++ parens (debugShow g)
debugShow (Tag t f) = "(Tag: " ++ show t ++ ") " ++ parens (debugShow f)
debugShow (Not f) = "not " ++ debugShow f
debugShow Top = "true"
debugShow Bot = "false"
debugShow (Trm name args info id) = show name ++ "(args: " 
  ++ (concatMap (parens . debugShow) args) ++ ") (info: "
  ++ (concatMap (parens . debugShow) info) ++ ") (id: " ++ show id ++ ")"
debugShow (Var name info pos) = show name ++ "(info: " ++ (concatMap (parens . debugShow) info)
  ++ ") (pos: " ++ show_position pos ++ ")"
debugShow (Ind idx pos) = show idx ++ "(pos: " ++ show_position pos ++ ")"
debugShow ThisT = "ThisT"

parens :: String -> String
parens s = "(" ++ s ++ ")"

-- TODO:
-- Fix -> Top in Prime no square, tenth hypothesis
-- Statement after fails to translate
