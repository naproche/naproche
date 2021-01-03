{-
Authors: Steffen Frerix (2018), Makarius Wenzel (2018)

PIDE markup reports for ForTheL text elements.
-}

{-# LANGUAGE TupleSections #-}

module SAD.ForTheL.Reports
  ( addMarkup
  , markupToken
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
  , sectionHeader
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
import SAD.Core.Message (PIDE)
import qualified SAD.Core.Message as Message
import SAD.Core.SourcePos
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


import qualified Isabelle.Markup as Markup

addReports :: (PIDE -> [Message.Report]) -> FTL ()
addReports rep = modify (\st -> case pide st of
  Just pide -> let newRep = rep pide
               in  seq newRep $ st {reports = newRep ++ reports st}
  Nothing -> st)


-- markup tokens while parsing

-- | Adds markup to a parser.
addMarkup :: Markup.T -> FTL a -> FTL a
addMarkup markup parser = do
  pos <- getPos
  content <- parser
  addReports $ const [(pos, markup)]
  return content

markupToken :: Markup.T -> Text -> FTL ()
markupToken markup = addMarkup markup . token'

markupTokenOf :: Markup.T -> [Text] -> FTL ()
markupTokenOf markup = addMarkup markup . tokenOf'


-- formula and variable reports

variableReport :: PIDE -> Bool -> Decl -> SourcePos -> [Message.Report]
variableReport pide def decl pos =
  case declName decl of
    VarConstant name ->
      [(pos, Message.entityMarkup pide "variable" (Text.unpack name) def (declSerial decl) (declPosition decl))]
    _ -> []

formulaReports :: PIDE -> Set Decl -> Formula -> [Message.Report]
formulaReports pide decls = nubOrd . dive
  where
    dive Var {varName = name, varPosition = pos} =
      (pos, Markup.free) : entity
      where
        entity =
          case find (\decl -> declName decl == name) decls of
            Nothing -> []
            Just decl -> variableReport pide False decl pos
    dive (All decl f) = quantDive decl f
    dive (Exi decl f) = quantDive decl f
    dive f = foldF dive f

    quantDive decl f = let pos = declPosition decl in
      (pos, Markup.bound) : variableReport pide True decl pos ++
      boundReports pide decl f ++
      dive f

boundReports :: PIDE -> Decl -> Formula -> [Message.Report]
boundReports pide decl = dive 0
  where
    dive n (All _ f) = dive (succ n) f
    dive n (Exi _ f) = dive (succ n) f
    dive n Ind {indIndex = i, indPosition = pos} | i == n =
      (pos, Markup.bound) : variableReport pide False decl pos
    dive n f = foldF (dive n) f


-- add reports during parsing

addBlockReports :: Block -> FTL ()
addBlockReports bl = addReports $ \pide -> let decls = Block.declaredVariables bl in
  (Block.position bl, Markup.expression "text block") :
  formulaReports pide decls (Block.formula bl) ++
  concatMap (\decl -> variableReport pide True decl $ declPosition decl) decls

addInstrReport :: Pos -> FTL ()
addInstrReport pos = addReports $ const $
  map (position pos,) [Markup.comment2, Markup.expression "text instruction"]

addDropReport :: Pos -> FTL ()
addDropReport pos = addReports $ const $
  map (position pos,) [Markup.comment2, Markup.expression "drop text instruction"]

addPretypingReport :: SourcePos -> [SourcePos] -> FTL ()
addPretypingReport pos ps = addReports $ const $
  (pos, Markup.expression "variable pretyping") : map (, Markup.free) ps

addMacroReport :: SourcePos -> FTL ()
addMacroReport pos = addReports $ const [(pos, Markup.expression "macro definition")]


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
