{-|
License     : GPL 3
Maintainer  : Andrei Paskevich (2001 - 2008),
              Steffen Frerix (2017 - 2018)

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
import SAD.Data.Text.Decl


-- * Parsing a ForTheL text

-- | Parse a @.ftl@ or @.ftl.tex@ document:
-- @{<topLevelBlock>} (<exitInstruction> | <EOF>)@
forthel :: ParserKind -> FTL [ProofText]
forthel dialect = repeatUntil (pure <$> topLevelBlock dialect)
  (try (bracketExpression >>= exitInstruction) <|> (eof >> return []))

-- | Parse a top-level block:
-- @<topLevelSection> | <instruction> | <macro> | <pretyping>@
topLevelBlock :: ParserKind -> FTL ProofText
topLevelBlock dialect =
      topLevelSection dialect
  <|> (bracketExpression >>= addSynonym)
  <|> try introduceMacro
  <|> pretypeVariable

-- | Parse a top-level section:
-- @<signature> | <definition> | <axiom> | <theorem>@
topLevelSection :: ParserKind -> FTL ProofText
topLevelSection dialect =
      signature dialect
  <|> definition dialect
  <|> axiom dialect
  <|> theorem dialect


-- * Top-level sections

-- | Parse a signature:
--
-- FTL:
-- @"signature" [<identifier>] "." <signatureBody>@
--
-- TEX:
-- @"\\begin" "{" "signature" "}" ["[" <name> "]"] [<label>] <signatureBody>
-- "\\end" "{" "signature" "}"@
signature :: ParserKind -> FTL ProofText
signature Ftl = do
  keyword <- markupToken sectionHeader "signature"
  label <- optLL1 Nothing (Just <$> identifier)
  dot
  content <- signatureBody
  addMetadata Signature content label
signature Tex = do
  keyword <- try . texBegin $ getMarkupToken sectionHeader "signature"
  label <- optionalEnvLabel
  content <- signatureBody
  texEnd (markupToken sectionHeader keyword)
  addMetadata Signature content label

-- | Parse a signature:
--
-- FTL:
-- @"definition" [<identifier>] "." <definitionBody>@
--
-- TEX:
-- @"\\begin" "{" "definition" "}" ["[" <name> "]"] [<label>] <definitionBody>
-- "\\end" "{" "definition" "}"@
definition :: ParserKind -> FTL ProofText
definition Ftl = do
  keyword <- markupToken sectionHeader "definition"
  label <- optLL1 Nothing (Just <$> identifier)
  dot
  content <- definitionBody
  addMetadata Definition content label
definition Tex = do
  keyword <- try . texBegin $ getMarkupToken sectionHeader "definition"
  label <- optionalEnvLabel
  content <- definitionBody
  texEnd (markupToken sectionHeader keyword)
  addMetadata Definition content label

-- | Parse a signature:
--
-- FTL:
-- @"axiom" [<identifier>] "." <axiomBody>@
--
-- TEX:
-- @"\\begin" "{" "axiom" "}" ["[" <name> "]"] [<label>] <axiomBody>
-- "\\end" "{" "axiom" "}"@
axiom :: ParserKind -> FTL ProofText
axiom Ftl = do
  keyword <- markupToken sectionHeader "axiom"
  label <- optLL1 Nothing (Just <$> identifier)
  dot
  content <- axiomBody
  addMetadata Axiom content label
axiom Tex = do
  keyword <- try . texBegin $ getMarkupToken sectionHeader "axiom"
  label <- optionalEnvLabel
  content <- axiomBody
  texEnd (markupToken sectionHeader keyword)
  addMetadata Axiom content label

-- | Parse a signature:
--
-- FTL:
-- @("theorem" | "proposition" | "lemma" | "corollary") [<identifier>] "."
-- <theoremBody>@
--
-- TEX:
-- @...@
theorem :: ParserKind -> FTL ProofText
theorem Ftl = do
  keyword <- markupTokenOf sectionHeader ["theorem", "proposition", "lemma", "corollary"]
  label <- optLL1 Nothing (Just <$> identifier)
  dot
  content <- theoremBody
  addMetadata Theorem content label
theorem Tex = do
  keyword <- try . texBegin $ getMarkupTokenOf sectionHeader ["theorem", "lemma", "corollary", "proposition"]
  label <- optionalEnvLabel
  content <- addAssumptions . texTopLevelProof $
             pretypeSentence Affirmation (affirmationHeader >> statement) affirmVars finishWithOptLink <* texEnd (markupToken sectionHeader keyword)
  addMetadata Theorem content label

-- | This is the last step when creating a proof text from a top-level section.
-- We take some metadata and moreover read some metadata from the state and use
-- it to make a 'ProofText' out of the content and (optional) label of a
-- top-level section.
addMetadata :: Section -> [ProofText] -> Maybe Text -> FTL ProofText
addMetadata kind content optLabel = do
  input <- getInput
  tokens <- getTokens input
  -- If there is no label, represent it by an empty string
  let label = fromMaybe "" optLabel
  let block = Block.makeBlock (mkVar (VarHole "")) content kind label [] tokens
  addBlockReports block
  return $ ProofTextBlock block


-- * Bracket expressions (aka instructions)

-- | Parses a bracket expression without evaluating it.
bracketExpression :: FTL ProofText
bracketExpression =
  fmap (uncurry ProofTextDrop) instrDrop
  </> fmap (uncurry ProofTextInstr) (instr </> instrExit </> instrRead)

-- | If ProofText has synonym instruction, it gets added.
addSynonym :: ProofText -> FTL ProofText
addSynonym text = case text of
  ProofTextInstr _ (Synonym syms) | length syms > 1 ->
    modify (\st -> st {strSyms = syms : strSyms st}) >> return text
  _ -> return text

-- | Succeeds if the ProofText consists of an exit instruction.
exitInstruction :: ProofText -> FTL [ProofText]
exitInstruction text = case text of
  ProofTextInstr _ (GetArgument (Read _) _) -> return [text]
  ProofTextInstr _ (Command Exit) -> return []
  _ -> failing (return ()) >> return [] -- Not sure how to properly throw an error.


-- * Top-level section bodies

signatureBody :: FTL [ProofText]
signatureBody = addAssumptions $ pretype $ pretypeSentence Posit sigExtend defVars finishWithoutLink

definitionBody :: FTL [ProofText]
definitionBody = addAssumptions $ pretype $ pretypeSentence Posit defExtend defVars finishWithoutLink

axiomBody :: FTL [ProofText]
axiomBody = addAssumptions $ pretype $ pretypeSentence Posit (affirmationHeader >> statement) affirmVars finishWithoutLink

theoremBody :: FTL [ProofText]
theoremBody = addAssumptions $ ftlTopLevelProof $ pretypeSentence Affirmation (affirmationHeader >> statement) affirmVars finishWithOptLink


-- | Adds parser for parsing any number of assumptions before the passed content
-- parser.
addAssumptions :: FTL [ProofText] -> FTL [ProofText]
addAssumptions content = body
  where
    body = assumption <|> content
    assumption = topAssume `pretypeBefore` body
    topAssume = pretypeSentence Assumption (assumptionHeader >> statement) assumeVars finishWithoutLink


-- * Low-level blocks

-- | Parse a choice expression.
choose :: FTL Block
choose = sentence Choice (choiceHeader >> choice) assumeVars finishWithOptLink

-- | Parse a case hypothesis.
caseHypothesis :: FTL Block
caseHypothesis = sentence Block.CaseHypothesis (caseHeader >> statement) affirmVars finishWithOptLink

-- | Parse an affirmation.
affirmation :: FTL Block
affirmation = sentence Affirmation (affirmationHeader >> statement) affirmVars finishWithOptLink </> eqChain

-- | Parse an assumption.
assumption :: FTL Block
assumption = sentence Assumption (assumptionHeader >> statement) assumeVars finishWithoutLink

-- | Parse a low-level definition.
lowLevelDefinition :: FTL Block
lowLevelDefinition = sentence LowDefinition (lowLevelDefinitionHeader >> classNotion </> mapNotion) llDefnVars finishWithoutLink


-- * Identifiers, links, labels

-- ** Identifiers

-- | Parse an identifier, i.e. a sequence of alphanumeric tokens and underscores.
identifier :: FTL Text
identifier = Text.toCaseFold . Text.concat <$> many (tokenPrim notSymb)
  where
    notSymb t = case Text.uncons (showToken t) of
      Just (c, "") -> guard (isAlphaNum c || c == '_') >> return (Text.singleton c)
      _ -> return (showToken t)


-- ** Links

-- | Finish a statement with a link.
finishWithOptLink :: FTL [Text]
finishWithOptLink = finish optLink

-- | Finish a statement without a link.
finishWithoutLink :: FTL [a]
finishWithoutLink = finish $ return []

-- | Parses an optionsl link expression, i.e. "(by ...)"
optLink :: FTL [Text]
optLink = optLL1 [] $ parenthesised $ token' "by" >> identifiers
  where
    identifiers = reference `sepByLL1` comma
    reference =
          texCommandWithArg "ref" identifier
      <|> texCommandWithArg "nameref" identifier
      <|> texCommandWithArg "cref" identifier
      <|> identifier


-- ** Labels

-- | Parse an environment label (TEX), i.e. one of the following expressions:
--
--  * A name together with a label, i.e. "[<name>]\label{<label>}"
--    In this case @<name>@ can be any string while @<label>@ must be an
--    identifier which is used as an idenfier of the top-level section it
--    belongs to.
--  * Just a name, i.e. "[<name>]".
--    In this case @<name>@ must be an identifier which is used as an
--    idenfier of the top-level section it belongs to.
--  * Just a label, i.e. "\label{<label>}".
--    In this case @<label>@ must be an identifier which is used as an idenfier
--    of the top-level section it belongs to.
--
envLabel :: FTL Text
envLabel = try nameAndLabel <|> name <|> label
  where
    -- "[<name>]\label{<label>}"
    nameAndLabel = do
      bracketed (chainLL1 notClosingBrk)
      label
    -- "[<name>]"
    name = bracketed identifier
    -- "\label{<label>}"
    label =
          texCommandWithArg "label" identifier
      <|> texCommandWithArg "printlabel" identifier

    notClosingBrk = tokenPrim notCl
    notCl t = let tk = showToken t in guard (tk /= "]") >> return tk

-- | Parse an optional environment label (TEX).
optionalEnvLabel :: FTL (Maybe Text)
optionalEnvLabel = optLLx Nothing (Just <$> envLabel)


-- * Declaration management, typings and pretypings

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


-- * Low-level header

-- | @[ "then" | "hence" | "thus" | "therefore" | "consequently" ]@
hence :: FTL ()
hence = optLL1 () $ tokenOf' ["then", "hence", "thus", "therefore", "consequently"]

-- | @[ ("let" "us") | ("we" "can") ]@
letUs :: FTL ()
letUs = optLL1 () $ (mu "let" >> mu "us") <|> (mu "we" >> mu "can")
  where
    mu = markupToken lowlevelHeader

-- | Header for choice expressions:
-- @[ <hence> ] [ <letUs> ] ("choose" | "take" | "consider")@
choiceHeader :: FTL ()
choiceHeader = hence >> letUs >> markupTokenOf lowlevelHeader ["choose", "take", "consider"]

-- | Header for case hypothesis:
-- @"case"@
caseHeader :: FTL ()
caseHeader = markupToken lowlevelHeader "case"

-- | Header for affirmation:
-- @<hence>@
affirmationHeader :: FTL ()
affirmationHeader = hence

-- | Header for assumption:
-- @"let" | (<letUs> ("assume" | "presume" | "suppose") ["that"])
assumptionHeader :: FTL ()
assumptionHeader = lus </> markupToken lowlevelHeader "let"
  where
    lus = letUs >> markupTokenOf lowlevelHeader ["assume", "presume", "suppose"] >> optLL1 () that

-- | Low-leve definition header:
-- @"define"@
lowLevelDefinitionHeader :: FTL ()
lowLevelDefinitionHeader = markupToken lowlevelHeader "define"


-- * Generic sentence parser

statementBlock :: Section
               -> FTL Formula
               -> FTL [Text]
               -> FTL Block
statementBlock kind p mbLink = do
  nm <- optLLx "__" (parenthesised identifier)
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
  dvs <- getDecl
  tvr <- fmap (Set.unions . map fst) getPretyped
  bl <- wellFormedCheck (wf dvs tvr) $ statementBlock kind p mbLink
  newDecl <- bindings dvs $ Block.formula bl
  let nbl = if Block.canDeclare kind then bl {Block.declaredVariables = newDecl} else bl
  addBlockReports nbl
  return nbl {Block.formula = Block.formula bl}
  where
    wf dvs tvr bl =
      let fr = Block.formula bl
          nvs = Set.intersection tvr $ fvToVarSet $ excludeSet (free fr) dvs
      in  wfVars (nvs <> dvs) fr

sentence :: Section
         -> FTL Formula
         -> (Set VariableName -> Formula -> Maybe Text)
         -> FTL [Text]
         -> FTL Block
sentence kind p wfVars mbLink = do
  dvs <- getDecl
  bl <- wellFormedCheck (wfVars dvs . Block.formula) $ statementBlock kind p mbLink
  newDecl <- bindings dvs $ Block.formula bl
  let nbl = bl {Block.declaredVariables = newDecl}
  addBlockReports nbl
  return nbl {Block.formula = Block.formula bl}


-- * Variable well-formedness checks

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


-- * Proofs

-- | Proof scheme
data Scheme =
    None            -- ^ No proof
  | Short           -- ^ Confirmation ("Indeed ... .")
  | Raw             -- ^ Proof without special method
  | Contradiction   -- ^ Proof by contradiction
  | InS             -- ^ Proof by induction
  | InT Formula     -- ^ Term to induce on (in a proof by induction)
  deriving (Eq, Ord, Show)

-- | Low-level theorem header:
-- @<letUs> ("prove" | "show" | "demonstrate") [<byProofMethod>] "that"@
letUsShowThat :: FTL Scheme
letUsShowThat = do
  letUs
  markupTokenOf lowlevelHeader ["prove", "show", "demonstrate"]
  method <- optLL1 Raw byProofMethod
  markupToken lowlevelHeader "that"
  return method

-- | Confirmation header (FTL):
-- @"indeed"@
ftlConfirmationHeader :: FTL Scheme
ftlConfirmationHeader = do
  markupToken proofStart "indeed"
  return Short

-- | Proof header (FTL)
-- @"proof" [<byProofMethod>] "."@
ftlProofHeader :: FTL Scheme
ftlProofHeader = do
  markupToken proofStart "proof"
  method <- optLL1 Raw byProofMethod
  dot
  return method

-- | Proof header (TEX):
-- @"\\begin" "{" "proof" "}" ["[" <byProofMethod> "]"]
texProofHeader :: FTL Scheme
texProofHeader = do
  texBegin (markupToken proofStart "proof")
  optLL1 Raw $ bracketed byProofMethod

-- | Proof method:
-- @"by" ("contradiction" | "case" "analysis" | "induction" ["on" <sTerm>])
byProofMethod :: FTL Scheme
byProofMethod = markupToken byAnnotation "by" >> (contradiction <|> caseAnalysis <|> induction)
  where
    contradiction = token' "contradiction" >> return Contradiction
    caseAnalysis = token' "case" >> token' "analysis" >> return Raw
    induction = token' "induction" >> optLL1 InS (token' "on" >> fmap InT sTerm)

-- | Proof end (FTL):
-- @"qed" | "end" | "trivial" | "obvious"@
ftlProofEnd :: FTL ()
ftlProofEnd = label "qed" $ markupTokenOf proofEnd ["qed", "end", "trivial", "obvious"]

-- | Proof end (TEX):
-- @"\\end" "{" "proof" "}"@
texProofEnd :: FTL ()
texProofEnd = label "qed" . texEnd $ markupToken proofEnd "proof"

-- | Creation of induction thesis.
indThesis :: Formula -> Scheme -> Scheme -> FTL Formula
indThesis fr pre post = do
  it <- indScheme pre post >>= indTerm fr
  dvs <- getDecl
  indFormula (fvToVarSet $ excludeSet (free it) dvs) it fr
  where
    indScheme (InT _) (InT _) = failWF "conflicting induction schemes"
    indScheme m@(InT _) _ = return m
    indScheme _ m@(InT _) = return m
    indScheme InS _ = return InS
    indScheme _ m = return m

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


-- ** Proof initiation

-- | Parse a statement with an optional proof.
proof :: FTL Block -> FTL Block
proof p = do
  pre <- optLLx None letUsShowThat
  block <- p
  post <- optLL1 None (ftlProofHeader <|> ftlConfirmationHeader)
  nf <- indThesis (Block.formula block) pre post
  addBody ftlProofEnd finishWithOptLink pre post $ block {Block.formula = nf}

ftlTopLevelProof :: FTL Block -> FTL [ProofText]
ftlTopLevelProof = topProof (optLLx None $ ftlProofHeader <|> ftlConfirmationHeader) ftlProofEnd finishWithOptLink

texTopLevelProof :: FTL Block -> FTL [ProofText]
texTopLevelProof = topProof (optLLx None texProofHeader) texProofEnd (return [])

-- | Parse a top-level proof:
-- @[<letUsShowThat>] <affirmation> [<ftlProofHeader>]
topProof :: FTL Scheme -> FTL () -> FTL [Text] -> FTL Block -> FTL [ProofText]
topProof postMethod qed link p = do
  pre <- optLLx None letUsShowThat
  bl <- p
  post <- postMethod
  typeBlock <- pretyping bl
  let pretyped = Block.declaredNames typeBlock
  nbl <- addDecl pretyped $ fmap ProofTextBlock $ do
    nf <- indThesis (Block.formula bl) pre post
    addBody qed link pre post $ bl {Block.formula = nf}
  return $ if null pretyped then [nbl] else [ProofTextBlock typeBlock, nbl]

-- Takes proof end parser @qed@ and the link @link@ to insert after the proof body as parameters.
addBody :: FTL ()     -- ^ Proof end parser
        -> FTL [Text] -- ^ Link parser
        -> Scheme     -- ^ Proof scheme from a "let us show" expression
        -> Scheme     -- ^ Proof scheme from a proof header
        -> Block
        -> FTL Block
-- No proof was given
addBody _ _ None None b = return b
-- A confirmation was given
addBody _ _ _ Short b = confirmationBody b
-- A full proof was given
addBody qed link pre post b = proofBody qed link $ b {Block.kind = kind}
  where kind = if pre == Contradiction || post == Contradiction then ProofByContradiction else Block.kind b



-- ** Proof texts

-- | Confirmation body:
-- @<assumption> | ((<affirmation> | <choose>) <proof>) | <lowLevelDefinition>@
confirmationBody :: Block -> FTL Block
confirmationBody block = do
  pbl <- narrow assumption </> proof (narrow $ affirmation </> choose) </> narrow lowLevelDefinition
  return block {Block.body = [ProofTextBlock pbl]}

-- | Proof body + proof end + link
-- @
proofBody :: FTL ()       -- ^ Proof end parser
          -> FTL [Text]   -- ^ Link parser
          -> Block
          -> FTL Block
proofBody qed link block = do
  bs <- proofText qed
  ls <- link
  return block {Block.body = bs, Block.link = ls ++ Block.link block}

-- | Proof body + proof end
-- @{ <assumption>
--    | (<affirmation> | <choose> | <lowLevelDefinition>) <proof>
--    | <caseDistinction>
--    | <instruction> }
--  <qed>@
proofText :: FTL () -> FTL [ProofText]
proofText qed =
  (qed >> return []) <|>
  (unfailing (fmap ProofTextBlock lowtext <|> instruction) `updateDeclbefore` proofText qed)
  where
    lowtext =
      narrow assumption </>
      proof (narrow $ affirmation </> choose </> lowLevelDefinition) </>
      caseDestinction
    instruction =
      fmap (uncurry ProofTextDrop) instrDrop </>
      fmap (uncurry ProofTextInstr) instr

-- | Case distinction:
-- @<caseHypothesis> <proofBody>@
caseDestinction :: FTL Block
caseDestinction = do
  bl@Block { Block.formula = fr } <- narrow caseHypothesis
  proofBody ftlProofEnd finishWithOptLink $ bl {
  Block.formula = Imp (Tag Tag.CaseHypothesis fr) mkThesis}


-- equality Chain

eqChain :: FTL Block
eqChain = do
  dvs <- getDecl; nm <- opt "__" (parenthesised identifier); inp <- getInput
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
  ln <- optLink
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
