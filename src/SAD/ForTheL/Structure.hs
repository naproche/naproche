{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018)

Syntax of ForTheL sections.
-}

{-# LANGUAGE TupleSections #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}

module SAD.ForTheL.Structure (forthel, texForthel) where

import Data.List
import Data.Maybe
import Data.Char (isAlphaNum)
import Control.Applicative
import Control.Monad
import Control.Monad.State.Class (modify)
import Data.Text (Text)
import qualified Data.Text as Text
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
import SAD.Data.Text.Decl


-- | The old .ftl file parser.
forthel :: FTL [ProofText]
forthel = repeatUntil (pure <$> (
    makeFtlSection Signature signatureTags signature'
    <|> makeFtlSection Definition definitionTags definition
    <|> makeFtlSection Axiom axiomTags axiom
    <|> makeFtlSection Theorem theoremTags theorem
    <|> (bracketExpression >>= addSynonym)
    <|> try introduceMacro
    <|> pretypeVariable))
  (try (bracketExpression >>= exitInstruction) <|> (eof >> return []))

-- | Parses tex files.
texForthel :: FTL [ProofText]
texForthel = repeatUntil (pure <$> forthelStep) (try (bracketExpression >>= exitInstruction) <|> (eof >> return []))

-- | Parses one forthel construct with tex syntax for forthel sections.
forthelStep :: FTL ProofText
forthelStep = 
    makeSectionTexEnv Signature signatureTags signature'
    <|> makeSectionTexEnv Definition definitionTags definition
    <|> makeSectionTexEnv Axiom axiomTags axiom
    <|> addMetadata Theorem texTheorem
    <|> (bracketExpression >>= addSynonym)
    <|> try introduceMacro
    <|> pretypeVariable


-- | Parses a bracket expression without evaluating it.
bracketExpression :: FTL ProofText
bracketExpression = 
  fmap (uncurry ProofTextDrop) instrDrop
  </> fmap (uncurry ProofTextInstr) (instr </> instrExit </> instrRead)

-- | If ProofText has synonym instruction, it gets added.
addSynonym :: ProofText -> FTL ProofText
addSynonym text = case text of
  ProofTextInstr _ (GetArguments Synonym syms) -> addSynonym' syms >> return text
  _ -> return text
  where
    addSynonym' :: [Text] -> FTL ()
    addSynonym' syms
      | null syms || null (tail syms) = return ()
      | otherwise = modify $ \st -> st {strSyms = syms : strSyms st}

-- | Succeeds if the ProofText consists of an exit instruction.
exitInstruction :: ProofText -> FTL [ProofText]
exitInstruction text = case text of
  ProofTextInstr _ (GetArgument (Read _) _) -> return [text]
  ProofTextInstr _ (Command EXIT) -> return []
  ProofTextInstr _ (Command QUIT) -> return []
  _ -> failing (return ()) >> return [] -- Not sure how to properly throw an error.


-- | Creates a full forthel section parser for parsing tex envs.
makeSectionTexEnv :: Section -> [Text] -> FTL [ProofText] -> FTL ProofText
makeSectionTexEnv kind envType content =
  addMetadata kind $ texEnv envType content

-- | @texEnv envType labelParser parseContent@ is a tex environment parser
-- for forthel sections.
-- @envType@ parses the environment type specified in the environment declaration.
-- @content@ parses the insides of the environment.
texEnv :: [Text] -> FTL a -> FTL (a, Maybe Text)
texEnv envType content = do
  -- We use 'try' to backtrack if parsing the environment declaration fails.
  envType' <- try . texBegin . addMarkup sectionHeader $ getTokenOf envType
  envLabel <- optionalEnvLabel
  (, envLabel) <$> (content <* texEnd (markupToken sectionHeader envType'))


-- | Creates a full forthel section parser with its header included.
makeFtlSection :: Section -> [Text] -> FTL [ProofText] -> FTL ProofText
makeFtlSection kind titles content =
  addMetadata kind $ do
    label <- header $ markupTokenOf sectionHeader titles
    content' <- content
    return (content', label)
    where
      header :: FTL () -> FTL (Maybe Text)
      header title = finish $ title >> optLL1 Nothing (Just <$> topIdentifier)

-- | This is the last step when creating a proof text from a topsection. We take some metadata
-- and moreover read some metadata from the state and use it to make a `ProofText` out
-- of a parser that returns @ProofText@s and optional label information.
addMetadata :: Section -> FTL ([ProofText], Maybe Text) -> FTL ProofText
addMetadata kind content = do
  inp <- getInput
  (content', label) <- content
  tokens <- getTokens inp
  -- For some weird reason, if no label is present we must represent it as the empty string.
  let block = Block.makeBlock (mkVar (VarHole "")) content' kind (fromMaybe "" label) [] tokens
  addBlockReports block
  return $ ProofTextBlock block


-- Core parsers for the bodies of the forthel sections.

signature' :: FTL [ProofText]
signature' = addAssumptions $ pretype $ pretypeSentence Posit sigExtend defVars noLink

definition :: FTL [ProofText]
definition = addAssumptions $ pretype $ pretypeSentence Posit defExtend defVars noLink

axiom :: FTL [ProofText]
axiom = addAssumptions $ pretype $ pretypeSentence Posit (beginAff >> statement) affirmVars noLink

theorem :: FTL [ProofText]
theorem = addAssumptions $ topProof postMethod qed link $ pretypeSentence Affirmation (beginAff >> statement) affirmVars link

-- Parsing tex theorems has the additional difficulty over other environments, that it could consist of
-- two tex envs, a theorem env and a proof env.
texTheorem :: FTL ([ProofText], Maybe Text)
texTheorem = do
  envType <- try . texBegin . addMarkup sectionHeader $ getTokenOf theoremTags
  label <- optionalEnvLabel
  text <- addAssumptions . topProof texPostMethod texQed (return []) $
            pretypeSentence Affirmation (beginAff >> statement) affirmVars link <* texEnd (markupToken sectionHeader envType)
  return (text, label)


-- | Adds parser for parsing any number of assumptions before the passed content parser.
addAssumptions :: FTL [ProofText] -> FTL [ProofText]
addAssumptions content = body
  where
    body = assumption <|> content
    assumption = topAssume `pretypeBefore` body
    topAssume = pretypeSentence Assumption (beginAsm >> statement) assumeVars noLink

-- These are given in text format and not as a parser, because we want to later decide
-- whether they are parsed in a case-sensitive manner.
signatureTags, definitionTags, axiomTags, theoremTags :: [Text]
signatureTags = ["signature"]
definitionTags = ["definition"]
axiomTags = ["axiom"]
theoremTags = ["theorem", "lemma", "corollary", "proposition"]


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
llDefn = sentence LowDefinition (beginDef >> classNotion </> functionNotion) llDefnVars noLink


-- Tex labels
envLabel :: FTL Text
envLabel = do
  symbol "["
  label <- topIdentifier
  symbol "]"
  return label

optionalEnvLabel :: FTL (Maybe Text)
optionalEnvLabel = optLLx Nothing (Just <$> envLabel)

-- Links and Identifiers
link :: FTL [Text]
link = finish eqLink

topIdentifier :: FTL Text
topIdentifier = tokenPrim notSymb
  where
    notSymb t = case Text.uncons (showToken t) of
      Just (c, "") -> guard (isAlphaNum c) >> return (Text.singleton c)
      _ -> return (showToken t)

lowIdentifier :: FTL Text
lowIdentifier = parenthesised topIdentifier

noLink :: FTL [a]
noLink = finish $ return []

eqLink :: FTL [Text]
eqLink = optLL1 [] $ parenthesised $ token' "by" >> identifiers
  where
    identifiers = topIdentifier `sepByLL1` comma

-- declaration management, typings and pretypings

updateDeclbefore :: FTL ProofText -> FTL [ProofText] -> FTL [ProofText]
updateDeclbefore blp p = do
  txt <- blp
  case txt of
    ProofTextBlock bl -> addDecl (Block.declaredNames bl) $ fmap (txt : ) p
    _ -> fmap (txt :) p

pretyping :: Block -> FTL Block
pretyping bl = do
  dvs <- getDecl
  tvs <- getPretyped
  pret dvs tvs bl

pret :: Set VarName -> [TVar] -> Block -> FTL Block
pret dvs tvs bl = do
  untyped <- makeDecls $ fvToVarSet $ excludeSet (allFree (Block.formula bl)) (blockVars <> dvs)
  let typing =
        if null untyped
        then Top
        else foldl1 And $ fmap ((`typeWith` tvs) . declName) (Set.toList untyped)
  return $ assumeBlock {Block.formula = typing, Block.declaredVariables = untyped}
  where
    blockVars = Block.declaredNames bl
    assumeBlock = bl {Block.body = [], Block.kind = Assumption, Block.link = []}
    typeWith v = subst (mkVar v) (VarHole "") . snd . fromJust . find (elem v . fst)

pretypeBefore :: FTL Block -> FTL [ProofText] -> FTL [ProofText]
pretypeBefore blp p = do
  bl <- blp -- Runs ASSUMPTION BLOCK!!!
  typeBlock <- pretyping bl -- (not always) used block containing variable declarations for the assumption.
  let pretyped = Block.declaredNames typeBlock
  pResult <- addDecl (pretyped <> Block.declaredNames bl) $ fmap (ProofTextBlock bl : ) p -- runs p, in our case CONTENT!!
  return $ if null pretyped then pResult else ProofTextBlock typeBlock : pResult

-- | @pretype p@ prepends a @ProofText@ to @p@ that explicitly declares the pretypings and the variable
-- declarations contained in the parser state before running @p@. Moreover the this pretyping information
-- is also added as a @ProofText@.
pretype :: FTL Block -> FTL [ProofText]
pretype p = p `pretypeBefore` return []


-- low-level header
hence :: FTL ()
hence = optLL1 () $ tokenOf' ["then", "hence", "thus", "therefore"]
letUs :: FTL ()
letUs = optLL1 () $ (mu "let" >> mu "us") <|> (mu "we" >> mu "can")
  where
    mu = markupToken lowlevelHeader

beginChoice :: FTL ()
beginChoice = hence >> letUs >> markupTokenOf lowlevelHeader ["choose", "take", "consider"]
beginCase :: FTL ()
beginCase = markupToken lowlevelHeader "case"
beginAff :: FTL ()
beginAff = hence
beginAsm :: FTL ()
beginAsm = lus </> markupToken lowlevelHeader "let"
  where
    lus = letUs >> markupTokenOf lowlevelHeader ["assume", "presume", "suppose"] >> optLL1 () that
beginDef :: FTL ()
beginDef = markupToken lowlevelHeader "define"


-- generic sentence parser

statementBlock :: Section
                  -> FTL Formula -> FTL [Text] -> FTL Block
statementBlock kind p mbLink = do
  nm <- optLLx "__" lowIdentifier
  inp <- getInput
  fr <- p
  link <- mbLink
  toks <- getTokens inp
  return $ Block.makeBlock fr [] kind nm link toks


pretypeSentence :: Section
                   -> FTL Formula
                   -> (Set VarName -> Formula -> Maybe Text)
                   -> FTL [Text]
                   -> FTL Block
pretypeSentence kind p wfVars mbLink = narrow $ do
  dvs <- getDecl
  tvr <- fmap (Set.unions . map fst) getPretyped
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
            -> (Set VarName -> Formula -> Maybe Text)
            -> FTL [Text]
            -> FTL Block
sentence kind p wfVars mbLink = do
  dvs <- getDecl
  bl <- wellFormedCheck (wfVars dvs . Block.formula) $ statementBlock kind p mbLink
  newDecl <- bindings dvs $ Block.formula bl
  let nbl = bl {Block.declaredVariables = newDecl}
  addBlockReports nbl; return nbl {Block.formula = removeObject $ Block.formula bl}

-- variable well-formedness checks

defVars, assumeVars, affirmVars :: Set VarName -> Formula -> Maybe Text

defVars dvs f
  | null unusedVars = affirmVars dvs f
  | otherwise = pure errorMsg
  where
    unusedVars = let fvs = fvToVarSet $ free f in dvs `Set.difference` fvs
    errorMsg = "extra variables in the guard: " <> varText
    varText = Text.concat $ map (Text.cons ' ' . showVar) $ Set.toList unusedVars

llDefnVars :: Set VarName -> Formula -> Maybe Text
llDefnVars dvs f
  | x `elem` dvs = Just $ "Defined variable is already in use: " <> showVar x
  | otherwise = affirmVars (Set.insert x dvs) f
  where
    [x] = Set.elems $ declNames mempty f

assumeVars dvs f = affirmVars (declNames dvs f <> dvs) f

affirmVars = freeOrOverlapping


-- proofs

-- proof methods

data Scheme = None | Short | Raw | Contradiction | InS | InT Formula deriving (Eq, Ord, Show)

preMethod :: FTL Scheme
preMethod = optLLx None $ letUs >> dem >> after (optLL1 Raw method) that
  where
    dem = markupTokenOf lowlevelHeader ["prove", "show", "demonstrate"]
    that = markupToken lowlevelHeader "that"

postMethod :: FTL Scheme
postMethod = optLL1 None $ short <|> explicit
  where
    short = markupToken proofStart "indeed" >> return Short
    explicit = finish $ markupToken proofStart "proof" >> optLL1 Raw method

texPostMethod :: FTL Scheme
texPostMethod = optLLx None $ texBegin (markupToken proofStart "proof") >> (short <|> explicit)
  where
    short = markupToken proofStart "indeed" >> return Short
    explicit = optLL1 Raw . finish $ markupToken byAnnotation "proof" >> method

method :: FTL Scheme
method = markupToken byAnnotation "by" >> (contradict <|> cases <|> induction)
  where
    contradict = token' "contradiction" >> return Contradiction
    cases = token' "case" >> token' "analysis" >> return Raw
    induction = token' "induction" >> optLL1 InS (token' "on" >> fmap InT sTerm)

qed :: FTL ()
qed = label "qed" $ markupTokenOf proofEnd ["qed", "end", "trivial", "obvious"]

texQed :: FTL ()
texQed = label "qed" . texEnd $ markupToken proofEnd "proof"

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
    indStatem _ _ = failWF $ "invalid induction thesis " <> (Text.pack $ showFormula fr)

    insertIndTerm it cn = cn $ Tag InductionHypothesis $ subst it (VarHole "") $ cn $ mkLess it (mkVar (VarHole ""))

    deleteDecl Decl{declName, declPosition} = Set.delete (PosVar declName declPosition)



-- proof initiation

proof :: FTL Block -> FTL Block
proof p = do
  pre <- preMethod
  bl <- p
  post <- postMethod
  nf <- indThesis (Block.formula bl) pre post
  addBody qed link pre post $ bl {Block.formula = nf}



topProof :: FTL Scheme -> FTL () -> FTL [Text] -> FTL Block -> FTL [ProofText]
topProof postMethod qed link p = do
  pre <- preMethod
  bl <- p
  post <- postMethod
  typeBlock <- pretyping bl
  let pretyped = Block.declaredNames typeBlock
  nbl <- addDecl pretyped $ fmap ProofTextBlock $ do
    nf <- indThesis (Block.formula bl) pre post
    addBody qed link pre post $ bl {Block.formula = nf}
  return $ if null pretyped then [nbl] else [ProofTextBlock typeBlock, nbl]

-- Takes proof end parser @qed@ and the link @link@ to insert after the proof body as parameters.
addBody :: FTL () -> FTL [Text] -> Scheme -> Scheme -> Block -> FTL Block
addBody _ _ None None b = return b -- no proof was given
addBody _ _ _ Short b = proofSentence b   -- a short proof was given
addBody qed link pre post b = proofBody qed link $ b {Block.kind = kind}  -- a full proof was given
  where kind = if pre == Contradiction || post == Contradiction then ProofByContradiction else Block.kind b



-- proof texts

proofSentence :: Block -> FTL Block
proofSentence bl = do
  pbl <- narrow assume </> proof (narrow $ affirm </> choose) </> narrow llDefn
  return bl {Block.body = [ProofTextBlock pbl]}

-- Takes proof end parser @qed@ and the link @link@ to insert after the proof body as parameters.
proofBody :: FTL () -> FTL [Text] -> Block -> FTL Block
proofBody qed link bl = do
  bs <- proofText qed
  ls <- link
  return bl {Block.body = bs, Block.link = ls ++ Block.link bl}

-- Takes the proof end parser @qed@ as parameter.
proofText :: FTL () -> FTL [ProofText]
proofText qed =
  (qed >> return []) <|>
  (unfailing (fmap ProofTextBlock lowtext <|> instruction) `updateDeclbefore` proofText qed)
  where
    lowtext =
      narrow assume </>
      proof (narrow $ affirm </> choose </> llDefn) </>
      caseDestinction
    instruction =
      fmap (uncurry ProofTextDrop) instrDrop </>
      fmap (uncurry ProofTextInstr) instr

caseDestinction :: FTL Block
caseDestinction = do
  bl@Block { Block.formula = fr } <- narrow caseHypo
  proofBody qed link $ bl {
  Block.formula = Imp (Tag CaseHypothesisTag fr) mkThesis}


-- equality Chain

eqChain :: FTL Block
eqChain = do
  dvs <- getDecl; nm <- opt "__" lowIdentifier; inp <- getInput
  body <- wellFormedCheck (chainVars dvs) $ sTerm >>= nextTerm
  toks <- getTokens inp
  let Tag EqualityChain Trm{trmArgs = [t,_]} = Block.formula $ head body
      Tag EqualityChain Trm{trmArgs = [_,s]} = Block.formula $ last body
      fr = Tag EqualityChain $ mkEquality t s; tBody = map ProofTextBlock body
  return $ Block.makeBlock fr tBody Affirmation nm [] toks
  where
    chainVars dvs = affirmVars dvs . foldl1 And . map Block.formula

eqTail :: Formula -> FTL [Block]
eqTail t = nextTerm t </> (token "." >> return [])

nextTerm :: Formula -> FTL [Block]
nextTerm t = do
  inp <- getInput
  symbol ".="
  s <- sTerm
  ln <- eqLink
  toks <- getTokens inp
  (:) (Block.makeBlock (Tag EqualityChain $ mkEquality t s)
    [] Affirmation "__" ln toks) <$> eqTail s

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
