
{-# LANGUAGE TupleSections #-}
module SAD.ForTheL.Reports where

import Control.Monad
import qualified Control.Monad.State.Class as MS
import Data.List

import SAD.Core.Message (PIDE)
import qualified SAD.Core.Message as Message
import SAD.Core.SourcePos
import SAD.ForTheL.Base

import SAD.Data.Text.Block (Text(..), Block)
import qualified SAD.Data.Text.Block as Block
import SAD.Data.Text.Decl (Decl)
import qualified SAD.Data.Text.Decl as Decl
import SAD.Data.Formula
import qualified SAD.Data.Instr as Instr

import SAD.Parser.Base
import SAD.Parser.Primitives




import Isabelle.Markup as Markup

addReports :: (PIDE -> [Message.Report]) -> FTL ()
addReports rep = MS.modify (\st -> st {reports = \pide -> rep pide ++ reports st pide})

-- markup tokens while parsing

markupToken :: Markup.T -> String -> FTL ()
markupToken markup s = do
  pos <- getPos; wdToken s; addReports $ const [(pos, markup)]

markupTokenOf :: Markup.T -> [String] -> FTL ()
markupTokenOf markup ss = do
  pos <- getPos; wdTokenOf ss; addReports $ const [(pos, markup)]

-- formula and variable reports

entityReport :: PIDE -> Bool -> Decl -> SourcePos -> [Message.Report]
entityReport pide def decl pos =
  case Decl.name decl of
    'x' : name ->
      [(pos, Message.entityMarkup pide "variable" name def (Decl.serial decl) (Decl.position decl))]
    _ -> []

formulaReports :: PIDE -> [Decl] -> Formula -> [Message.Report]
formulaReports pide decls = nub . dive
  where
    dive Var {trName = name, trPosition = pos} =
      (pos, Markup.free) : entity
      where
        entity =
          case find (\decl -> Decl.name decl == name) decls of
            Nothing -> []
            Just decl -> entityReport pide False decl pos
    dive (All dcl f) = quantDive dcl f
    dive (Exi dcl f) = quantDive dcl f
    dive f = foldF dive f

    quantDive dcl f = let pos = Decl.position dcl in
      (pos, Markup.bound) : entityReport pide True dcl pos ++
      boundReports pide dcl f ++
      foldF dive f

boundReports :: PIDE -> Decl -> Formula -> [Message.Report]
boundReports pide dcl = dive 0
  where
    dive n (All _ f) = dive (succ n) f
    dive n (Exi _ f) = dive (succ n) f
    dive n Ind {trIndx = i, trPosition = pos} | i == n =
      (pos, Markup.bound) : entityReport pide False dcl pos
    dive n f = foldF (dive n) f


-- add reports during parsing

addBlockReports :: Block -> FTL ()
addBlockReports bl = addReports $ \pide -> let decls = Block.declaredVariables bl in
  (Block.position bl, Markup.expression "text block") :
  formulaReports pide decls (Block.formula bl) ++
  concatMap (\decl -> entityReport pide True decl $ Decl.position decl) decls

addInstrReport :: Instr.Pos -> FTL ()
addInstrReport pos = addReports $ const $
  map (Instr.position pos,) [Markup.comment2, Markup.expression "text instruction"]

addDropReport :: Instr.Pos -> FTL ()
addDropReport pos = addReports $ const $
  map (Instr.position pos,) [Markup.comment2, Markup.expression "drop text instruction"]

addSynonymReport :: Instr.Pos -> FTL ()
addSynonymReport pos = addReports $ const $
  map (Instr.position pos,) [Markup.comment3, Markup.expression "text synonyms"]

addPretypingReport :: SourcePos -> [SourcePos] -> FTL ()
addPretypingReport pos ps = addReports $ const $
  (pos, Markup.expression "variable pretyping") : map ( ,Markup.free) ps

addMacroReport :: SourcePos -> FTL ()
addMacroReport pos = addReports $ const [(pos, Markup.expression "macro definition")]

-- markups used

synonymLet = Markup.keyword3
macroLet = Markup.keyword3
topsectionHeader = Markup.keyword1
lowlevelHeader = Markup.keyword2
proofStart = Markup.keyword3
proofEnd = Markup.keyword3
byAnnotation = Markup.keyword2