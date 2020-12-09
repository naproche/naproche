{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018)

Syntax of ForTheL sections.
-}

{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}

module SAD.ForTheL.Structure (forthel, texForthel) where

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
import SAD.Data.Text.Decl


-- | The old .ftl file parser.
forthel :: FTL [ProofText]
forthel = repeatM $
  continue <$> (topsection <|> introduceMacro </> pretypeVariable)
  <|> bracketExpression
  <|> (eof >> return abort)

-- | Parses tex files.
texForthel :: FTL [ProofText]
texForthel = repeatM $
  Continue <$> repeatInTexEnv' (token "forthel") forthelStep
  <|> (eof >> return abort)
  <|> consumeToken
  where
    consumeToken = anyToken >> return (Continue mempty)

-- | Parses one forthel construct with tex syntax for topsection.
forthelStep :: FTL (StepStatus [ProofText])
forthelStep = 
  (continue <$> (texTopsection <|> introduceMacro </> pretypeVariable))
  <|> bracketExpression

bracketExpression :: FTL (StepStatus [ProofText])
bracketExpression = topInstruction >>= procParseInstruction
  where
    topInstruction =
      fmap (uncurry ProofTextDrop) instrDrop </>
      fmap (uncurry ProofTextInstr) (instr </> instrExit </> instrRead)

procParseInstruction :: ProofText -> FTL (StepStatus [ProofText])
procParseInstruction text = case text of
  ProofTextInstr _ (GetArgument Read _) -> return (Abort [text])
  ProofTextInstr _ (Command EXIT) -> return abort
  ProofTextInstr _ (Command QUIT) -> return abort
  ProofTextInstr _ (GetArguments Synonym syms) -> addSynonym syms >> return (continue text)
  _ -> return (continue text)
  where
    addSynonym :: [Text] -> FTL ()
    addSynonym syms
      | null syms || null (tail syms) = return ()
      | otherwise = modify $ \st -> st {strSyms = syms : strSyms st}

topsection :: FTL ProofText
topsection = addHeader (header signatureTags) signature'
  <|> addHeader (header definitionTags) definition
  <|> addHeader (header axiomTags) axiom
  <|> addHeader (header theoremTags) theorem

texTopsection :: FTL ProofText
texTopsection = texEnv (labelParser signatureTags) optionalEnvLabel (giveTokens signature')
  <|> texEnv (labelParser definitionTags) optionalEnvLabel (giveTokens definition)
  <|> texEnv (labelParser axiomTags) optionalEnvLabel (giveTokens axiom)
  <|> texEnv (labelParser theoremTags) optionalEnvLabel (giveTokens theorem)
  where
    labelParser = markupTokenOf' topsectionHeader . tokenOf
    -- The topsection parsers have a parameter that tells them which tokens to specify when creating
    -- a block. In the case of tex environments, we will just read the tokens before applying the parser.
    giveTokens parser label = do
      inp <- getInput
      tokens <- getTokens inp
      parser tokens label


-- Helpers for constructing environments and adding headers.

-- | @texEnv envType labelParser parseContent@ parses a tex environment. @envType@ parses
-- then environment type specified in the environment declaration. @labelParser@ parses a
-- label declaration such as '[label]'. @content@ parses the insides of the environment,
-- while optionally being able to use the label information.
texEnv :: FTL () -> LabelParser label -> (label -> FTL content) -> FTL content
texEnv envType labelParser content = do
  -- We use 'try' to backtrack if parsing the environment declaration fails.
  try $ texBegin envType
  envLabel <- labelParser
  after (content envLabel) (texEnd envType)

-- | Repeats a parser until the end parser succeeds or the content parser aborts.
untilEnd :: Monoid a => FTL (StepStatus a) -> FTL () -> FTL a
untilEnd content end = repeatM $ (end >> return (Abort mempty)) <|> content

-- | Parses tex environment while iterating a parser inside it until '\end{...}' is parsed or abort instruction
-- is passed.
repeatInTexEnv :: Monoid content => FTL () -> LabelParser label -> (label -> FTL (StepStatus content)) -> FTL content
repeatInTexEnv envType labelParser content = do
  try $ texBegin envType
  envLabel <- labelParser
  untilEnd (content envLabel) (texEnd envType)

-- | Version of @repeatInTexEnv@ without label data.
repeatInTexEnv' :: Monoid content => FTL () -> FTL (StepStatus content) -> FTL content
repeatInTexEnv' envType = repeatInTexEnv envType noEnvLabel . const


-- | @addHeader header parseContent@ constructs a forthel topsection construct in the old
-- .ftl file format. @header@ parses the header and @parseContent@ parses the main body of
-- the construct. @parseContent@ is parameterized by a whole set of tokens included in the
-- construct(including the header) and moreover by an optional label.
addHeader :: FTL (Maybe Text) -> ([Token] -> Maybe Text -> FTL ProofText) -> FTL ProofText
addHeader header content = do
  inp <- getInput
  label <- header
  tokens <- getTokens inp
  content tokens label


-- generic topsection parsing

genericTopsection :: Section -> FTL [ProofText] -> [Token] -> Maybe Text -> FTL ProofText
genericTopsection kind content tokens header = do
  bs <- body
  -- For some weird reason, if no label is present we must represent it as the empty string.
  let block = Block.makeBlock (mkVar (VarHole "")) bs kind (fromMaybe "" header) [] tokens
  addBlockReports block
  return $ ProofTextBlock block
  where
    body = assumption <|> content
    assumption = topAssume `pretypeBefore` body
    topAssume = pretypeSentence Assumption (beginAsm >> statement) assumeVars noLink


-- generic header parser

header :: [Text] -> FTL (Maybe Text)
header titles = finish $ markupTokenOf topsectionHeader titles >> optLL1 Nothing (Just <$> topIdentifier)


-- Topsections. These are all parameterized by some metadata that gets embedded
-- into the block.

signature' :: [Token] -> Maybe Text -> FTL ProofText
signature' =
  let sigExt = pretype $ pretypeSentence Posit sigExtend defVars noLink
  in  genericTopsection Signature sigExt

definition :: [Token] -> Maybe Text -> FTL ProofText
definition =
  let define = pretype $ pretypeSentence Posit defExtend defVars noLink
  in  genericTopsection Definition define

axiom :: [Token] -> Maybe Text -> FTL ProofText
axiom =
  let posit = pretype $
        pretypeSentence Posit (beginAff >> statement) affirmVars noLink
  in  genericTopsection Axiom posit

theorem :: [Token] -> Maybe Text -> FTL ProofText
theorem =
  let topAffirm = pretypeSentence Affirmation (beginAff >> statement) affirmVars link
  in  genericTopsection Theorem (topProof topAffirm)

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
llDefn = sentence LowDefinition(beginDef >> setNotion </> functionNotion) llDefnVars noLink

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
        else foldl1 And $ fmap ((`typeWith` tvs) . declName) (Set.toList untyped)
  return $ assumeBlock {Block.formula = typing, Block.declaredVariables = untyped}
  where
    blockVars = Block.declaredNames bl
    assumeBlock = bl {Block.body = [], Block.kind = Assumption, Block.link = []}
    typeWith v = subst (mkVar v) (VarHole "") . snd . fromJust . find (elem v . fst)

pretypeBefore :: FTL Block -> FTL [ProofText] -> FTL [ProofText]
pretypeBefore blp p = do
  bl <- blp; typeBlock <- pretyping bl; let pretyped = Block.declaredNames typeBlock
  pResult   <- addDecl (pretyped <> Block.declaredNames bl) $ fmap (ProofTextBlock bl : ) p
  return $ if null pretyped then pResult else ProofTextBlock typeBlock : pResult

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

data Scheme = None | Short | Raw | Contradiction | InS | InT Formula deriving (Eq, Ord, Show)

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
    contradict = token' "contradiction" >> return Contradiction
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
    indStatem _ _ = failWF $ "invalid induction thesis " <> Text.pack (show fr)

    insertIndTerm it cn = cn $ Tag InductionHypothesis $ subst it (VarHole "") $ cn $ mkLess it (mkVar (VarHole ""))

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
addBody None None b = return b -- no proof was given
addBody _ Short b = proofSentence b   -- a short proof was given
addBody pre post b = proofBody $ b {Block.kind = kind}  -- a full proof was given
  where kind = if pre == Contradiction || post == Contradiction then ProofByContradiction else Block.kind b



-- proof texts

proofSentence :: Block -> FTL Block
proofSentence bl = do
  pbl <- narrow assume </> proof (narrow $ affirm </> choose) </> narrow llDefn
  return bl {Block.body = [ProofTextBlock pbl]}

proofBody :: Block -> FTL Block
proofBody bl = do
  bs <- proofText; ls <- link
  return bl {Block.body = bs, Block.link = ls ++ Block.link bl}

proofText :: FTL [ProofText]
proofText =
  qed <|>
  (unfailing (fmap ProofTextBlock lowtext <|> instruction) `updateDeclbefore` proofText)
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
  Block.formula = Imp (Tag Tag.CaseHypothesis fr) mkThesis}


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
