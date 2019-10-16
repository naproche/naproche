{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018)

Syntax of ForTheL sections.
-}

{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}

module SAD.ForTheL.Structure (forthel) where

import Data.List
import Data.Maybe
import Data.Char (isAlphaNum)
import Control.Applicative
import Control.Monad
import Control.Monad.State.Class (modify)
import Data.Text.Lazy (Text)
import qualified Data.Text.Lazy as Text
import qualified Data.Set as Set
import Data.Set (Set)

import SAD.ForTheL.Base
import SAD.ForTheL.Statement
import SAD.ForTheL.Extension
import SAD.ForTheL.Instruction
import SAD.ForTheL.Reports

import SAD.Parser.Base
import SAD.Parser.Combinators
import SAD.Parser.Token
import SAD.Parser.Primitives

import SAD.Data.Instr
import SAD.Data.Text.Block (Block(Block), ProofText(..), Section(..))
import qualified SAD.Data.Text.Block as Block
import SAD.Data.Formula
import qualified SAD.Data.Tag as Tag
import SAD.Data.Text.Decl (Decl(Decl))
import SAD.Data.Text.Decl


forthel :: FTL [ProofText]
forthel = section <|> macroOrPretype <|> bracketExpression <|> endOfFile
  where
    section = liftM2 ((:) . ProofTextBlock) topsection forthel
    macroOrPretype = liftM2 (:) (introduceMacro </> pretypeVariable) forthel
    endOfFile = eof >> return []


bracketExpression :: FTL [ProofText]
bracketExpression = topInstruction >>= procParseInstruction
  where
    topInstruction =
      fmap (uncurry ProofTextDrop) instrDrop </>
      fmap (uncurry ProofTextInstr) (instr </> instrExit </> instrRead)

procParseInstruction :: ProofText -> FTL [ProofText]
procParseInstruction text = case text of
  ProofTextInstr _ (GetArgument Read _) -> return [text]
  ProofTextInstr _ (Command EXIT) -> return []
  ProofTextInstr _ (Command QUIT) -> return []
  ProofTextInstr _ (GetArguments Synonym syms) -> addSynonym syms >> fmap ((:) text) forthel
  _ -> fmap ((:) text) forthel
  where
    addSynonym :: [Text] -> FTL ()
    addSynonym syms
      | null syms || null (tail syms) = return ()
      | otherwise = modify $ \st -> st {strSyms = syms : strSyms st}

topsection :: FTL Block
topsection =
  -- We use backtracking alternative (</>) here since these environments
  -- all start with the same begin token.
  texSig </> texAxiom </> texDefinition
  <|> signature' <|> definition <|> axiom <|> theorem

--- generic topsection parsing

genericTopsection :: Section -> FTL Text -> FTL [ProofText] -> FTL Block
genericTopsection kind header content = do
  pos <- getPos
  inp <- getInput
  h <- header
  toks <- getTokens inp
  bs <- body
  let block = Block.makeBlock (zVar (VarHole "")) bs kind h [] pos toks
  addBlockReports block
  return block
  where
    body = assumption <|> content
    assumption = topAssume `pretypeBefore` body
    topAssume = pretypeSentence Assumption (beginAsm >> statement) assumeVars noLink

-- | @texTopsection kind env content@ parses an environment with the name @env@, followed by content
-- parsed by the specified @content@ parser. The result is combined into a block of kind @kind@.
texTopsection :: Section -> Text -> FTL [ProofText] -> FTL Block
texTopsection kind env content = do
  pos <- getPos
  inp <- getInput
  h <- texBegin env
  toks <- getTokens inp
  bs <- body
  texEnd env
  let block = Block.makeBlock (zVar (VarHole "")) bs kind h [] pos toks
  addBlockReports block
  return block
  where
    body = assumption <|> content
    assumption = topAssume `pretypeBefore` body
    topAssume = pretypeSentence Assumption (beginAsm >> statement) assumeVars noLink


--- generic header parser

header :: [Text] -> FTL Text
header titles = finish $ markupTokenOf topsectionHeader titles >> optLL1 "" topIdentifier


-- topsections

signature' :: FTL Block
signature' =
  let sigExt = pretype $ pretypeSentence Posit sigExtend defVars noLink
  in  genericTopsection Signature sigH sigExt

texSig :: FTL Block
texSig =
  let sigExt = pretype $ pretypeSentence Posit sigExtend defVars noLink
  in  texTopsection Signature "signature" sigExt

definition :: FTL Block
definition =
  let define = pretype $ pretypeSentence Posit defExtend defVars noLink
  in  genericTopsection Definition defH define

texDefinition :: FTL Block
texDefinition =
  let define = pretype $ pretypeSentence Posit defExtend defVars noLink
  in  texTopsection Definition "definition" define

axiom :: FTL Block
axiom =
  let posit = pretype $
        pretypeSentence Posit (beginAff >> statement) affirmVars noLink
  in  genericTopsection Axiom axmH posit

texAxiom :: FTL Block
texAxiom =
  let posit = pretype $ pretypeSentence Posit (beginAff >> statement) affirmVars noLink
  in  texTopsection Axiom "axiom" posit

theorem :: FTL Block
theorem =
  let topAffirm = pretypeSentence Affirmation (beginAff >> statement) affirmVars link
  in  genericTopsection Theorem thmH (topProof topAffirm)


sigH :: FTL Text
sigH = header ["signature"]
defH :: FTL Text
defH = header ["definition"]
axmH :: FTL Text
axmH = header ["axiom"]
thmH :: FTL Text
thmH = header ["theorem", "lemma", "corollary", "proposition"]


-- low-level
choose :: FTL Block
choose = sentence Selection (beginChoice >> selection) assumeVars link
caseHypo :: FTL Block
caseHypo = sentence Block.CaseHypothesis (beginCase >> statement) affirmVars link
affirm :: FTL Block
affirm = sentence Affirmation (beginAff >> statement) affirmVars link </> eqChain
assume :: FTL Block
assume = sentence Assumption (beginAsm >> statement) assumeVars noLink
llDefn :: FTL Block
llDefn = sentence LowDefinition(beginDef >> setNotion </> functionNotion) llDefnVars noLink

-- Links and Identifiers
link :: Parser st [Text]
link = finish eqLink

topIdentifier :: Parser st Text
topIdentifier = tokenPrim notSymb
  where
    notSymb t = case Text.uncons (showToken t) of
      Just (c, "") -> guard (isAlphaNum c) >> return (Text.singleton c)
      _ -> return (showToken t)

lowIdentifier :: Parser st Text
lowIdentifier = parenthesised topIdentifier

noLink :: Parser st [a]
noLink = finish $ return []

eqLink :: Parser st [Text]
eqLink = optLL1 [] $ parenthesised $ token' "by" >> identifiers
  where
    identifiers = topIdentifier `sepByLL1` comma

-- declaration management, typings and pretypings

updateDeclbefore :: FTL ProofText -> FTL [ProofText] -> FTL [ProofText]
updateDeclbefore blp p = do
  txt <- blp; case txt of
    ProofTextBlock bl -> addDecl (Block.declaredNames bl) $ fmap (txt : ) p
    _ -> fmap (txt :) p

pretyping :: Block -> FTL Block
pretyping bl = do
  dvs <- getDecl; tvs <- getPretyped; pret dvs tvs bl

pret :: Set VariableName -> [TVar] -> Block -> FTL Block
pret dvs tvs bl = do
  untyped <- makeDecls $ fvToVarSet $ excludeSet (allFree (Block.formula bl)) (blockVars <> dvs)
  let typing =
        if null untyped
        then Top
        else foldl1 And $ map (`typeWith` tvs) $ map declName $ Set.toList untyped
  return $ assumeBlock {Block.formula = typing, Block.declaredVariables = untyped}
  where
    blockVars = Block.declaredNames bl
    assumeBlock = bl {Block.body = [], Block.kind = Assumption, Block.link = []}
    typeWith v = subst (zVar v) (VarHole "") . snd . fromJust . find (elem v . fst)

pretypeBefore :: FTL Block -> FTL [ProofText] -> FTL [ProofText]
pretypeBefore blp p = do
  bl <- blp; typeBlock <- pretyping bl; let pretyped = Block.declaredNames typeBlock
  pResult   <- addDecl (pretyped <> Block.declaredNames bl) $ fmap (ProofTextBlock bl : ) p
  return $ if null pretyped then pResult else ProofTextBlock typeBlock : pResult

pretype :: FTL Block -> FTL [ProofText]
pretype p = p `pretypeBefore` return []


-- low-level header
hence :: Parser st ()
hence = optLL1 () $ tokenOf' ["then", "hence", "thus", "therefore"]
letUs :: FTL ()
letUs = optLL1 () $ (mu "let" >> mu "us") <|> (mu "we" >> mu "can")
  where
    mu = markupToken lowlevelHeader

beginChoice :: FTL ()
beginChoice = hence >> letUs >> markupTokenOf lowlevelHeader ["choose", "take", "consider"]
beginCase :: FTL ()
beginCase = markupToken lowlevelHeader "case"
beginAff :: Parser st ()
beginAff = hence
beginAsm :: FTL ()
beginAsm = lus </> markupToken lowlevelHeader "let"
  where
    lus = letUs >> markupTokenOf lowlevelHeader ["assume", "presume", "suppose"] >> optLL1 () that
beginDef :: FTL ()
beginDef = markupToken lowlevelHeader "define"


-- generic sentence parser

statementBlock :: Section
                  -> Parser st Formula -> Parser st [Text] -> Parser st Block
statementBlock kind p mbLink = do
  nm <- optLLx "__" lowIdentifier;
  pos <- getPos; inp <- getInput;
  fr <- p; link <- mbLink;
  toks <- getTokens inp;
  return $ Block.makeBlock fr [] kind nm link pos toks


pretypeSentence :: Section
                   -> FTL Formula
                   -> (Set VariableName -> Formula -> Maybe Text)
                   -> FTL [Text]
                   -> FTL Block
pretypeSentence kind p wfVars mbLink = narrow $ do
  dvs <- getDecl; tvr <- fmap (Set.unions . map fst) getPretyped
  bl <- wellFormedCheck (wf dvs tvr) $ statementBlock kind p mbLink
  newDecl <- bindings dvs $ Block.formula bl
  let nbl = if Block.canDeclare kind then bl {Block.declaredVariables = newDecl} else bl
  addBlockReports nbl; return nbl {Block.formula = removeObject $ Block.formula bl}
  where
    wf dvs tvr bl =
      let fr = Block.formula bl; nvs = Set.intersection tvr $ fvToVarSet $ excludeSet (free fr) dvs
      in  wfVars (nvs <> dvs) fr

sentence :: Section
            -> FTL Formula
            -> (Set VariableName -> Formula -> Maybe Text)
            -> FTL [Text]
            -> FTL Block
sentence kind p wfVars mbLink = do
  dvs <- getDecl;
  bl <- wellFormedCheck (wfVars dvs . Block.formula) $ statementBlock kind p mbLink
  newDecl <- bindings dvs $ Block.formula bl
  let nbl = bl {Block.declaredVariables = newDecl}
  addBlockReports nbl; return nbl {Block.formula = removeObject $ Block.formula bl}

-- variable well-formedness checks

defVars, assumeVars, affirmVars :: Set VariableName -> Formula -> Maybe Text

defVars dvs f
  | null unusedVars = affirmVars dvs f
  | otherwise = pure errorMsg
  where
    unusedVars = let fvs = fvToVarSet $ free f in dvs `Set.difference` fvs
    errorMsg = "extra variables in the guard: " <> varText
    varText = Text.concat $ map (Text.cons ' ' . showVar) $ Set.toList unusedVars

llDefnVars :: Set VariableName -> Formula -> Maybe Text
llDefnVars dvs f
  | x `elem` dvs = Just $ "Defined variable is already in use: " <> showVar x
  | otherwise = affirmVars (Set.insert x dvs) f
  where
    [x] = Set.elems $ declNames mempty f

assumeVars dvs f = affirmVars (declNames dvs f <> dvs) f

affirmVars = freeOrOverlapping


-- proofs

-- proof methods

data Scheme = None | Short | Raw | InS | InT Formula deriving Show

preMethod :: FTL Scheme
preMethod = optLLx None $ letUs >> dem >> after method that
  where
    dem = markupTokenOf lowlevelHeader ["prove", "show", "demonstrate"]
    that = markupToken lowlevelHeader "that"

postMethod :: FTL Scheme
postMethod = optLL1 None $ short <|> explicit
  where
    short = markupToken proofStart "indeed" >> return Short
    explicit = finish $ markupToken proofStart "proof" >> method

method :: FTL Scheme
method = optLL1 Raw $ markupToken byAnnotation "by" >> (contradict <|> cases <|> induction)
  where
    contradict = token' "contradiction" >> return Raw
    cases = token' "case" >> token' "analysis" >> return Raw
    induction = token' "induction" >> optLL1 InS (token' "on" >> fmap InT sTerm)


--- creation of induction thesis

indThesis :: Formula -> Scheme -> Scheme -> FTL Formula
indThesis fr pre post = do
  it <- indScheme pre post >>= indTerm fr; dvs <- getDecl
  indFormula (fvToVarSet $ excludeSet (free it) dvs) it fr
  where
    indScheme (InT _) (InT _) = failWF "conflicting induction schemes"
    indScheme m@(InT _) _ = return m; indScheme _ m@(InT _) = return m
    indScheme InS _ = return InS; indScheme _ m = return m

    indTerm _ (InT t) = return t
    indTerm (All v _) InS = return $ pVar $ PosVar (declName v) (declPosition v)
    indTerm _ InS = failWF "invalid induction thesis"
    indTerm _ _ = return Top

    indFormula _ Top fr = return fr
    indFormula vs it fr = insertIndTerm it <$> indStatem vs fr

    indStatem vs (Imp g f) = (Imp g .) <$> indStatem vs f
    indStatem vs (All v f) = (dAll v .) <$> indStatem (deleteDecl v vs) f
    indStatem vs f | Set.null vs = pure (`Imp` f)
    indStatem _ _ = failWF $ "invalid induction thesis " <> (Text.pack $ show fr)

    insertIndTerm it cn = cn $ Tag InductionHypothesis $ subst it (VarHole "") $ cn $ zLess it (zVar (VarHole ""))

    deleteDecl Decl{declName, declPosition} = Set.delete (PosVar declName declPosition)



-- proof initiation

proof :: FTL Block -> FTL Block
proof p = do
  pre <- preMethod; bl <- p; post <- postMethod;
  nf <- indThesis (Block.formula bl) pre post
  addBody pre post $ bl {Block.formula = nf}



topProof :: FTL Block -> FTL [ProofText]
topProof p = do
  pre <- preMethod; bl <- p; post <- postMethod; typeBlock <- pretyping bl;
  let pretyped = Block.declaredNames typeBlock
  nbl <- addDecl pretyped $ fmap ProofTextBlock $ do
    nf <- indThesis (Block.formula bl) pre post
    addBody pre post $ bl {Block.formula = nf}
  return $ if null pretyped then [nbl] else [ProofTextBlock typeBlock, nbl]

addBody :: Scheme -> Scheme -> Block -> FTL Block
addBody None None = return -- no proof was given
addBody _ Short = proofSentence    -- a short proof was given
addBody _ _ = proofBody    -- a full proof was given



-- proof texts

proofSentence :: Block -> FTL Block
proofSentence bl = do
  pbl <- narrow assume </> proof (narrow $ affirm </> choose) </> narrow llDefn
  return bl {Block.body = [ProofTextBlock pbl]}

proofBody :: Block -> FTL Block
proofBody bl = do
  bs <- proofProofText; ls <- link
  return bl {Block.body = bs, Block.link = ls ++ Block.link bl}

proofProofText :: FTL [ProofText]
proofProofText =
  qed <|>
  (unfailing (fmap ProofTextBlock lowtext <|> instruction) `updateDeclbefore` proofProofText)
  where
    lowtext =
      narrow assume </>
      proof (narrow $ affirm </> choose </> llDefn) </>
      caseDestinction
    qed = label "qed" $ markupTokenOf proofEnd ["qed", "end", "trivial", "obvious"] >> return []
    instruction =
      fmap (uncurry ProofTextDrop) instrDrop </>
      fmap (uncurry ProofTextInstr) instr

caseDestinction :: FTL Block
caseDestinction = do
  bl@Block { Block.formula = fr } <- narrow caseHypo
  proofBody $ bl {
  Block.formula = Imp (Tag Tag.CaseHypothesis fr) zThesis}


-- equality Chain

eqChain :: FTL Block
eqChain = do
  dvs <- getDecl; nm <- opt "__" lowIdentifier; pos <- getPos; inp <- getInput
  body <- wellFormedCheck (chainVars dvs) $ sTerm >>= nextTerm
  toks <- getTokens inp
  let Tag EqualityChain Trm{trmArgs = [t,_]} = Block.formula $ head body
      Tag EqualityChain Trm{trmArgs = [_,s]} = Block.formula $ last body
      fr = Tag EqualityChain $ zEqu t s; tBody = map ProofTextBlock body
  return $ Block.makeBlock fr tBody Affirmation nm [] pos toks
  where
    chainVars dvs = affirmVars dvs . foldl1 And . map Block.formula

eqTail :: Formula -> FTL [Block]
eqTail t = nextTerm t </> (token "." >> return [])

nextTerm :: Formula -> FTL [Block]
nextTerm t = do
  pos <- getPos; inp <- getInput
  symbol ".="; s <- sTerm; ln <- eqLink; toks <- getTokens inp
  ((:) $ Block.makeBlock (Tag EqualityChain $ zEqu t s)
    [] Affirmation "__" ln pos toks) <$> eqTail s

-- | Fail if @p@ failed with no or only @EOF@ input remaining
-- or continue with a @ProofTextError@ as a @ParseResult@.
unfailing :: FTL ProofText -> FTL ProofText
unfailing p = do
  res <- inspectError p
  case res of
    Right pr -> pure pr
    Left err -> do
      notEof
      jumpToNextUnit (pure $ ProofTextError err)

-- | Skip input until we encounter @EOF@ (keep) or a dot not followed by '=' (discard the dot).
jumpToNextUnit :: FTL a -> FTL a
jumpToNextUnit = mapInput nextUnit
  where
    nextUnit (t:tks)
      | isEOF t = [t]
      | tokenText t == "." && (null tks || isEOF (head tks) || tokenText (head tks) /= "=") = tks
      | otherwise = nextUnit tks
    nextUnit [] = []
