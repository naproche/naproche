{-
Authors: Steffen Frerix (2018), Makarius Wenzel (2018)

PIDE markup reports for ForTheL text elements.
-}

{-# LANGUAGE TupleSections #-}

module SAD.ForTheL.Reports
  ( markupToken
  , markupTokenOf
  , or
  , neitherNor
  , conjunctiveAnd
  , whenWhere
  , ifThen
  , macroLet
  , synonymLet
  , addDropReport
  , addInstrReport
  , addPretypingReport
  , addMacroReport
  , addBlockReports
  , topsectionHeader
  , lowlevelHeader
  , proofStart
  , byAnnotation
  , proofEnd
  ) where

import Prelude hiding (or)
import Control.Monad.State.Class (modify)
import Data.List hiding (or)
import SAD.Helpers (nubOrd)
import Data.Set (Set)
import PIDE (PIDE)
import qualified PIDE
import PIDE.SourcePos
import SAD.ForTheL.Base

import SAD.Data.Text.Block (Block)
import qualified SAD.Data.Text.Block as Block
import SAD.Data.Text.Decl
import Data.Text (Text)
import qualified Data.Text as Text
import SAD.Data.Formula
import SAD.Data.Instr

import SAD.Parser.Base
import SAD.Parser.Primitives

addReports :: (PIDE -> [PIDE.Report]) -> FTL ()
addReports rep = modify (\st -> case pide st of
  Just pide -> let newRep = rep pide
               in  seq newRep $ st {reports = newRep ++ reports st}
  Nothing -> st)


-- markup tokens while parsing

markupToken :: PIDE.T -> Text -> FTL ()
markupToken markup s = do
  pos <- getPos; token' s; addReports $ const [(pos, markup)]

markupTokenOf :: PIDE.T -> [Text] -> FTL ()
markupTokenOf markup ss = do
  pos <- getPos; tokenOf' ss; addReports $ const [(pos, markup)]


-- formula and variable reports

variableReport :: PIDE -> Bool -> Decl -> SourcePos -> [PIDE.Report]
variableReport pide def decl pos =
  case declName decl of
    VarConstant name ->
      [(pos, PIDE.entityMarkup pide "variable" (Text.unpack name) def (declSerial decl) (declPosition decl))]
    _ -> []

formulaReports :: PIDE -> Set Decl -> Formula -> [PIDE.Report]
formulaReports pide decls = nubOrd . dive
  where
    dive Var {varName = name, varPosition = pos} =
      (pos, PIDE.free) : entity
      where
        entity =
          case find (\decl -> declName decl == name) decls of
            Nothing -> []
            Just decl -> variableReport pide False decl pos
    dive (All decl f) = quantDive decl f
    dive (Exi decl f) = quantDive decl f
    dive f = foldF dive f

    quantDive decl f = let pos = declPosition decl in
      (pos, PIDE.bound) : variableReport pide True decl pos ++
      boundReports pide decl f ++
      dive f

boundReports :: PIDE -> Decl -> Formula -> [PIDE.Report]
boundReports pide decl = dive 0
  where
    dive n (All _ f) = dive (succ n) f
    dive n (Exi _ f) = dive (succ n) f
    dive n Ind {indIndex = i, indPosition = pos} | i == n =
      (pos, PIDE.bound) : variableReport pide False decl pos
    dive n f = foldF (dive n) f


-- add reports during parsing

addBlockReports :: Block -> FTL ()
addBlockReports bl = addReports $ \pide -> let decls = Block.declaredVariables bl in
  (Block.position bl, PIDE.expression "text block") :
  formulaReports pide decls (Block.formula bl) ++
  concatMap (\decl -> variableReport pide True decl $ declPosition decl) decls

addInstrReport :: Pos -> FTL ()
addInstrReport pos = addReports $ const $
  map (position pos,) [PIDE.comment2, PIDE.expression "text instruction"]

addDropReport :: Pos -> FTL ()
addDropReport pos = addReports $ const $
  map (position pos,) [PIDE.comment2, PIDE.expression "drop text instruction"]

addPretypingReport :: SourcePos -> [SourcePos] -> FTL ()
addPretypingReport pos ps = addReports $ const $
  (pos, PIDE.expression "variable pretyping") : map (, PIDE.free) ps

addMacroReport :: SourcePos -> FTL ()
addMacroReport pos = addReports $ const [(pos, PIDE.expression "macro definition")]


-- specific markup

synonymLet :: PIDE.T
synonymLet = PIDE.keyword3
macroLet :: PIDE.T
macroLet = PIDE.keyword3
topsectionHeader :: PIDE.T
topsectionHeader = PIDE.keyword1
lowlevelHeader :: PIDE.T
lowlevelHeader = PIDE.keyword2
proofStart :: PIDE.T
proofStart = PIDE.keyword3
proofEnd :: PIDE.T
proofEnd = PIDE.keyword3
byAnnotation :: PIDE.T
byAnnotation = PIDE.keyword2
ifThen :: PIDE.T
ifThen = PIDE.keyword2
conjunctiveAnd :: PIDE.T
conjunctiveAnd = PIDE.keyword2 -- as opposed to listing "and"
neitherNor :: PIDE.T
neitherNor = PIDE.keyword2
whenWhere :: PIDE.T
whenWhere = PIDE.keyword2
or :: PIDE.T
or = PIDE.keyword2
