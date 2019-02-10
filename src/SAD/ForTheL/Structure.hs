{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018)

Syntax of ForTheL sections.
-}

{-# LANGUAGE NamedFieldPuns #-}

module SAD.ForTheL.Structure (forthel) where

import Data.List
import Data.Maybe
import Data.Char (isAlphaNum)
import Control.Monad
import qualified Data.Char as Char
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Control.Monad.State.Class as MS

import SAD.ForTheL.Base
import SAD.ForTheL.Statement
import SAD.ForTheL.Extension
import SAD.ForTheL.Instruction
import SAD.ForTheL.Reports

import SAD.Parser.Base
import SAD.Parser.Combinators
import SAD.Parser.Token
import SAD.Parser.Primitives

import SAD.Core.SourcePos

import qualified SAD.Data.Instr as Instr
import SAD.Data.Text.Block (Block(Block), Text(..), Section(..))
import qualified SAD.Data.Text.Block as Block
import SAD.Data.Formula
import qualified SAD.Data.Tag as Tag
import SAD.Data.Text.Decl (Decl(Decl))
import qualified SAD.Data.Text.Decl as Decl

import Debug.Trace

forthel :: FTL [Text]
forthel = section <|> macroOrPretype <|> bracketExpression <|> endOfFile
  where
    section = liftM2 ((:) . TextBlock) topsection forthel
    macroOrPretype = liftM2 (:) (introduceMacro </> pretypeVariable) forthel
    endOfFile = eof >> return []


bracketExpression = topInstruction >>= procParseInstruction
  where
    topInstruction =
      fmap (uncurry TextDrop) instrDrop </>
      fmap (uncurry TextInstr) (instr </> instrExit </> instrRead)

procParseInstruction text = case text of
  TextInstr _ (Instr.String Instr.Read _) -> return [text]
  TextInstr _ (Instr.Command Instr.EXIT) -> return []
  TextInstr _ (Instr.Command Instr.QUIT) -> return []
  TextInstr _ (Instr.Strings Instr.Synonym syms) -> addSynonym syms >> fmap ((:) text) forthel
  _ -> fmap ((:) text) forthel
  where
    addSynonym :: [String] -> FTL ()
    addSynonym syms 
      | null syms || null (tail syms) = return ()
      | otherwise = MS.modify $ \st -> st {strSyms = syms : strSyms st}

topsection = signature <|> definition <|> axiom <|> theorem

--- generic topsection parsing

genericTopsection kind header endparser = do
  pos <- getPos; inp <- getInput; nm <- header;
  toks <- getTokens inp; bs <- body
  let bl = Block.makeBlock zHole bs kind nm [] pos toks
  addBlockReports bl; return bl
  where
    body = assumption <|> endparser
    assumption = topAssume `pretypeBefore` body
    topAssume = pretypeSentence Assumption (asmH >> statement) assumeVars noLink

--- generic header parser

header titles = finish $ markupTokenOf topsectionHeader titles >> optLL1 "" topIdentifier


-- topsections

signature =
  let sigext = pretype $ pretypeSentence Posit sigExtend defVars noLink
  in  genericTopsection Signature sigH sigext
definition =
  let define = pretype $ pretypeSentence Posit defExtend defVars noLink
  in  genericTopsection Definition defH define
axiom =
  let posit = pretype $
        pretypeSentence Posit (affH >> statement) affirmVars noLink
  in  genericTopsection Axiom axmH posit
theorem = 
  let topAffirm = pretypeSentence Affirmation (affH >> statement) affirmVars link
  in  genericTopsection Theorem thmH (topProof topAffirm)
    

sigH = header ["signature"]
defH = header ["definition"]
axmH = header ["axiom"]
thmH = header ["theorem", "lemma", "corollary", "proposition"]


-- low-level
choose = sentence Selection (chsH >> selection) assumeVars link
caseHypo = sentence Block.CaseHypothesis (casH >> statement) affirmVars link
affirm = sentence Affirmation (affH >> statement) affirmVars link </> eqChain
assume = sentence Assumption (asmH >> statement) assumeVars noLink
llDefn = sentence LowDefinition(ldfH >> setNotion </> functionNotion) llDefnVars noLink

-- Links and Identifiers
link = finish eqLink
  where
    identifiers = topIdentifier `sepByLL1` comma

topIdentifier = tokenPrim notSymb
  where
    notSymb t = case showToken t of
      [c] -> guard (isAlphaNum c) >> return [c]
      tk -> return tk

lowIdentifier = expar topIdentifier

noLink = finish $ return []

eqLink = optLL1 [] $ expar $ wdToken "by" >> identifiers
  where
    identifiers = topIdentifier `sepByLL1` comma

-- declaration management, typings and pretypings

updateDeclbefore :: FTL Text -> FTL [Text] -> FTL [Text]
updateDeclbefore blp p = do
  txt <- blp; case txt of
    TextBlock bl -> addDecl (Block.declaredNames bl) $ fmap (txt : ) p
    _ -> fmap (txt :) p

pretyping :: Block -> FTL Block
pretyping bl = do
  dvs <- getDecl; tvs <- getPretyped; pret dvs tvs bl

pret :: [String] -> [TVar] -> Block -> FTL Block
pret dvs tvs bl = do
  untyped <- mapM makeDecl $ freePositions (blockVars ++ dvs) (Block.formula bl)
  let typing =
        if null untyped
        then Top
        else foldl1 And $ map (`typeWith` tvs) $ map Decl.name untyped
  return $ assumeBlock {Block.formula = typing, Block.declaredVariables = untyped}
  where
    blockVars = Block.declaredNames bl
    assumeBlock = bl {Block.body = [], Block.kind = Assumption, Block.link = []}
    typeWith v = substHole (zVar v) . snd . fromJust . find (elem v . fst)

pretypeBefore :: FTL Block -> FTL [Text] -> FTL [Text]
pretypeBefore blp p = do
  bl <- blp; typeBlock <- pretyping bl; let pretyped = Block.declaredNames typeBlock
  pResult   <- addDecl (pretyped ++ Block.declaredNames bl) $ fmap (TextBlock bl : ) p
  return $ if null pretyped then pResult else TextBlock typeBlock : pResult

pretype :: FTL Block -> FTL [Text]
pretype p = p `pretypeBefore` return []


-- low-level header
hence = optLL1 () $ wdTokenOf ["then", "hence", "thus", "therefore"]
letUs = optLL1 () $ (mu "let" >> mu "us") <|> (mu "we" >> mu "can")
  where
    mu = markupToken lowlevelHeader

chsH = hence >> letUs >> markupTokenOf lowlevelHeader ["choose", "take", "consider"]
casH = markupToken lowlevelHeader "case"
affH = hence
asmH = lus </> markupToken lowlevelHeader "let"
  where
    lus = letUs >> markupTokenOf lowlevelHeader ["assume", "presume", "suppose"] >> optLL1 () that
ldfH = markupToken lowlevelHeader "define"


-- generic sentence parser

statementBlock kind p mbLink = do
  nm <- opt "__" lowIdentifier;
  pos <- getPos; inp <- getInput;
  fr <- p; link <- mbLink;
  toks <- getTokens inp;
  return $ Block.makeBlock fr [] kind nm link pos toks


pretypeSentence kind p wfVars mbLink = narrow $ do
  dvs <- getDecl; tvr <- fmap (concatMap fst) getPretyped
  bl <- wellFormedCheck (wf dvs tvr) $ statementBlock kind p mbLink
  newDecl <- bindings dvs $ Block.formula bl
  let nbl = if Block.canDeclare kind then bl {Block.declaredVariables = newDecl} else bl
  addBlockReports nbl; return nbl {Block.formula = removeObject $ Block.formula bl}
  where
    wf dvs tvr bl =
      let fr = Block.formula bl; nvs = intersect tvr $ free dvs fr
      in  wfVars (nvs ++ dvs) fr

sentence kind p wfVars mbLink = do
  dvs <- getDecl;
  bl <- wellFormedCheck (wfVars dvs . Block.formula) $ statementBlock kind p mbLink
  newDecl <- bindings dvs $ Block.formula bl
  let nbl = bl {Block.declaredVariables = newDecl}
  addBlockReports nbl; return nbl {Block.formula = removeObject $ Block.formula bl}

-- variable well-formedness checks

defVars, assumeVars, affirmVars :: [String] -> Formula -> Maybe String

defVars dvs f
  | null unusedVars = affirmVars dvs f
  | otherwise = return errorMsg
  where
    unusedVars = let fvs = free [] f in filter (`notElem` fvs) dvs
    errorMsg = "extra variables in the guard: " ++ varString
    varString = concatMap ((' ' :) . showVar) unusedVars

llDefnVars dvs f
  | x `elem` dvs = Just $ "Defined variable is already in use: " ++ showVar x
  | otherwise = affirmVars (x : dvs) f
  where
    [x] = declNames [] f

assumeVars dvs f = affirmVars (declNames dvs f ++ dvs) f

affirmVars = overfree


-- proofs

-- proof methods

data Scheme = None | Short | Raw | InS | InT Formula deriving Show

preMethod = optLLx None $ letUs >> dem >> after method that
  where
    dem = markupTokenOf lowlevelHeader ["prove", "show", "demonstrate"]
    that = markupToken lowlevelHeader "that"

postMethod = optLL1 None $ short <|> explicit
  where
    short = markupToken proofStart "indeed" >> return Short
    explicit = finish $ markupToken proofStart "proof" >> method

method = optLL1 Raw $ markupToken byAnnotation "by" >> (contradict <|> cases <|> induction)
  where
    contradict = wdToken "contradiction" >> return Raw
    cases = wdToken "case" >> wdToken "analysis" >> return Raw
    induction = wdToken "induction" >> optLL1 InS (wdToken "on" >> fmap InT sTerm)


--- creation of induction thesis

indThesis fr pre post = do
  it <- indScheme pre post >>= indTerm fr; dvs <- getDecl
  indFormula (freePositions dvs it) it fr
  where
    indScheme (InT _) (InT _) = failWF "conflicting induction schemes"
    indScheme m@(InT _) _ = return m; indScheme _ m@(InT _) = return m
    indScheme InS _ = return InS; indScheme _ m = return m

    indTerm _ (InT t) = return t
    indTerm (All v _) InS = return $ pVar (Decl.name v, Decl.position v)
    indTerm _ InS = failWF "invalid induction thesis"
    indTerm _ _ = return Top

    indFormula _ Top fr = return fr
    indFormula vs it fr = insertIndTerm it <$> indStatem vs fr

    indStatem vs (Imp g f) = (Imp g .) <$> indStatem vs f
    indStatem vs (All v f) = (dAll v .) <$> indStatem (deleteDecl v vs) f
    indStatem [] f = return (`Imp` f)
    indStatem _ _ = failWF $ "invalid induction thesis " ++ show fr

    insertIndTerm it cn = cn $ Tag InductionHypothesis $ substHole it $ cn $ zLess it zHole

    deleteDecl Decl{Decl.name, Decl.position} = deleteBy (\a b -> fst a == fst b) (name, position)



-- proof initiation

proof p = do
  pre <- preMethod; bl <- p; post <- postMethod;
  nf <- indThesis (Block.formula bl) pre post
  addBody pre post $ bl {Block.formula = nf}



topProof p = do
  pre <- preMethod; bl <- p; post <- postMethod; typeBlock <- pretyping bl;
  let pretyped = Block.declaredNames typeBlock
  nbl <- addDecl pretyped $ fmap TextBlock $ do
    nf <- indThesis (Block.formula bl) pre post
    addBody pre post $ bl {Block.formula = nf}
  return $ if null pretyped then [nbl] else [TextBlock typeBlock, nbl]

addBody None None = return -- no proof was given
addBody _ Short = proofSentence    -- a short proof was given
addBody _ _ = proofBody    -- a full proof was given



-- proof texts

proofSentence bl = do
  pbl <- narrow assume </> proof (narrow $ affirm </> choose) </> narrow llDefn
  return bl {Block.body = [TextBlock pbl]}

proofBody bl = do
  bs <- proofText; ls <- link
  return bl {Block.body = bs, Block.link = ls ++ Block.link bl}

proofText = 
  qed <|>
  (unfailing (fmap TextBlock lowtext <|> instruction) `updateDeclbefore` proofText)
  where
    lowtext =
      narrow assume </>
      proof (narrow $ affirm </> choose </> llDefn) </>
      caseDestinction
    qed = label "qed" $ markupTokenOf proofEnd ["qed", "end", "trivial", "obvious"] >> return []
    instruction =
      fmap (uncurry TextDrop) instrDrop </>
      fmap (uncurry TextInstr) instr

caseDestinction = do
  bl@Block { Block.formula = fr } <- narrow caseHypo
  proofBody $ bl { 
  Block.formula = Imp (Tag Tag.CaseHypothesis fr) zThesis}


-- equality Chain

eqChain = do
  dvs <- getDecl; nm <- opt "__" lowIdentifier; pos <- getPos; inp <- getInput
  body <- wellFormedCheck (chainVars dvs) $ sTerm >>= nextTerm
  toks <- getTokens inp
  let Tag EqualityChain Trm{trArgs = [t,_]} = Block.formula $ head body
      Tag EqualityChain Trm{trArgs = [_,s]} = Block.formula $ last body
      fr = Tag EqualityChain $ zEqu t s; tBody = map TextBlock body
  return $ Block.makeBlock fr tBody Affirmation nm [] pos toks
  where
    chainVars dvs = affirmVars dvs . foldl1 And . map Block.formula


eqTail t = nextTerm t </> (smTokenOf "." >> return [])

nextTerm :: Formula -> FTL [Block]
nextTerm t = do
  pos <- getPos; inp <- getInput
  symbol ".="; s <- sTerm; ln <- eqLink; toks <- getTokens inp
  ((:) $ Block.makeBlock (Tag EqualityChain $ zEqu t s)
    [] Affirmation "__" ln pos toks) <$> eqTail s

-- error handling

unfailing :: FTL Text -> FTL Text
unfailing p =
  inspectError p >>= either guardEOF return
  where
    guardEOF err = notEof >> jumpToNextUnit (return $ TextError err)

jumpToNextUnit :: FTL a -> FTL a
jumpToNextUnit = jumpWith nextUnit
  where
    nextUnit (t:tks)
      | isEOF t = [t]
      | tokenText t == "." && (null tks || isEOF (head tks) || tokenText (head tks) /= "=") = tks
      | otherwise = nextUnit tks
    nextUnit [] = []