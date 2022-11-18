-- |
-- Authors: Steffen Frerix (2018),
--          Makarius Wenzel (2018)
--
-- PIDE markup reports for ForTheL text elements.


{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}

module SAD.ForTheL.Reports (
  addMarkup,
  markupToken,
  markupTokenOf,
  getMarkupToken,
  getMarkupTokenOf,
  or,
  neitherNor,
  conjunctiveAnd,
  whenWhere,
  ifThen,
  macroLet,
  synonymLet,
  addDropReport,
  addInstrReport,
  addPretypingReport,
  addMacroReport,
  addBlockReports,
  sectionHeader,
  lowlevelHeader,
  proofStart,
  byAnnotation,
  proofEnd
) where

import Prelude hiding (or)
import Control.Monad.State.Class (modify)
import Data.List hiding (or)
import Data.Set (Set)

import SAD.Helpers (nubOrd)
import SAD.ForTheL.Base
import SAD.Data.Text.Block (Block)
import SAD.Data.Text.Block qualified as Block
import SAD.Data.Text.Decl
import Data.Text.Lazy (Text)
import SAD.Data.Formula
import SAD.Parser.Base
import SAD.Parser.Primitives

import Isabelle.Library (make_bytes)
import Isabelle.Markup qualified as Markup
import Isabelle.Position qualified as Position

import Naproche.Program qualified as Program


addReports :: [Position.Report] -> FTL ()
addReports newRep = modify (\st ->
  if Program.is_pide (program st) then
    seq newRep $ st {reports = newRep ++ reports st}
  else st)


-- markup tokens while parsing

-- | Adds markup to a parser.
addMarkup :: Markup.T -> FTL a -> FTL a
addMarkup markup parser = do
  pos <- getPos
  content <- parser
  addReports [(pos, markup)]
  return content

markupToken :: Markup.T -> Text -> FTL ()
markupToken markup = addMarkup markup . token'

markupTokenOf :: Markup.T -> [Text] -> FTL ()
markupTokenOf markup = addMarkup markup . tokenOf'

getMarkupToken :: Markup.T -> Text -> FTL Text
getMarkupToken markup = addMarkup markup . getToken'

getMarkupTokenOf :: Markup.T -> [Text] -> FTL Text
getMarkupTokenOf markup = addMarkup markup . getTokenOf'


-- formula and variable reports

variableReport :: Bool -> Decl -> Position.T -> [Position.Report]
variableReport def decl pos =
  case declName decl of
    VarConstant name ->
      [(pos,
        Position.make_entity_markup def (declSerial decl) "variable" (make_bytes name, declPosition decl))]
    _ -> []

formulaReports :: Set Decl -> Formula -> [Position.Report]
formulaReports decls = nubOrd . dive
  where
    dive Var {varName = name, varPosition = pos} =
      (pos, Markup.free) : entity
      where
        entity =
          case find (\decl -> declName decl == name) decls of
            Nothing -> []
            Just decl -> variableReport False decl pos
    dive (All decl f) = quantDive decl f
    dive (Exi decl f) = quantDive decl f
    dive f = foldF dive f

    quantDive decl f = let pos = declPosition decl in
      (pos, Markup.bound) : variableReport True decl pos ++
      boundReports decl f ++
      dive f

boundReports :: Decl -> Formula -> [Position.Report]
boundReports decl = dive 0
  where
    dive n (All _ f) = dive (n + 1) f
    dive n (Exi _ f) = dive (n + 1) f
    dive n Ind {indIndex = i, indPosition = pos} | i == n =
      (pos, Markup.bound) : variableReport False decl pos
    dive n f = foldF (dive n) f


-- add reports during parsing

addBlockReports :: Block -> FTL ()
addBlockReports bl = addReports $ let decls = Block.declaredVariables bl in
  map (Block.position bl,) [Markup.cartouche, Markup.expression "text block"] ++
  formulaReports decls (Block.formula bl) ++
  concatMap (\decl -> variableReport True decl $ declPosition decl) decls

addInstrReport :: Position.T -> FTL ()
addInstrReport pos = addReports $
  map (pos,) [Markup.comment2, Markup.expression "text instruction"]

addDropReport :: Position.T -> FTL ()
addDropReport pos = addReports $
  map (pos,) [Markup.comment2, Markup.expression "drop text instruction"]

addPretypingReport :: Position.T -> [Position.T] -> FTL ()
addPretypingReport pos ps = addReports $
  map (pos,) [Markup.cartouche, Markup.expression "variable pretyping"] ++
  map (, Markup.free) ps

addMacroReport :: Position.T -> FTL ()
addMacroReport pos =
  addReports $ map (pos,) [Markup.cartouche, Markup.expression "macro definition"]


-- specific markup

synonymLet :: Markup.T
synonymLet = Markup.keyword3
macroLet :: Markup.T
macroLet = Markup.keyword3
sectionHeader :: Markup.T
sectionHeader = Markup.keyword1
lowlevelHeader :: Markup.T
lowlevelHeader = Markup.keyword2
proofStart :: Markup.T
proofStart = Markup.keyword3
proofEnd :: Markup.T
proofEnd = Markup.keyword3
byAnnotation :: Markup.T
byAnnotation = Markup.keyword2
ifThen :: Markup.T
ifThen = Markup.keyword2
conjunctiveAnd :: Markup.T
conjunctiveAnd = Markup.keyword2 -- as opposed to listing "and"
neitherNor :: Markup.T
neitherNor = Markup.keyword2
whenWhere :: Markup.T
whenWhere = Markup.keyword2
or :: Markup.T
or = Markup.keyword2
