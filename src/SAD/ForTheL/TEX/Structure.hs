-- |
-- Module      : SAD.ForTheL.TEX.Structure
-- Copyright   : (c) 2001 - 2008, Andrei Paskevich,
--               (c) 2017 - 2018, Steffen Frerix
--               (c) 2025 Marcel Schütz
-- License     : GPL-3
--
-- Document parsing (TeX).


{-# LANGUAGE OverloadedStrings #-}

module SAD.ForTheL.TEX.Structure where

import Data.List
import Control.Applicative
import Control.Monad
import Control.Monad.State.Class (modify)
import Data.Text.Lazy (Text)
import Data.Functor ((<&>))
import Data.Foldable (foldr')
import Data.Maybe (fromMaybe)
import Data.Either.Extra (fromEither)

import SAD.ForTheL.Structure
import SAD.ForTheL.FTL.Structure qualified as FTL -- for backward compatibility
import SAD.ForTheL.Base
import SAD.ForTheL.Statement
import SAD.ForTheL.Extension
import SAD.ForTheL.TEX.Extension qualified as TEX
import SAD.ForTheL.Reports (getMarkupToken, getMarkupTokenOf, markupToken)
import SAD.ForTheL.Instruction
import qualified SAD.ForTheL.Reports as Reports
import SAD.Parser.Base
import SAD.Parser.Combinators
import SAD.Parser.Token
import SAD.Parser.Primitives
import SAD.Data.Instr
import SAD.Data.Text.Block (Block(Block), ProofText(..), Section(..))
import SAD.Data.Text.Block qualified as Block
import SAD.Data.Formula
import SAD.Data.Tag qualified as Tag


-- * Parsing a ForTheL text

-- | Parse a @.ftl.tex@ document:
-- @{<topLevelBlock>} (<exitInstruction> | <EOF>)@
forthelText :: FTL [ProofText]
forthelText = repeatUntil topLevelBlock
  (try (instruction >>= exitInstruction) <|> (eof >> return []))

-- | Parse a top-level block (TEX):
-- @<topLevelSection> | <instruction> | <macro> | <pretyping>@
topLevelBlock :: FTL [ProofText]
topLevelBlock =
      try (section <&> singleton)
  <|> topLevelSection
  <|> ((instruction >>= addSynonym >>= resetPretyping) <&> singleton)
  <|> try (TEX.introduceMacro <&> singleton)
  <|> (pretypeVariable <&> singleton)


-- * Top-level sections

-- | Parse a top-level section:
-- @<signature> | <definition> | <axiom> | <theorem>@
topLevelSection :: FTL [ProofText]
topLevelSection =
      signatureSection
  <|> definitionSection
  <|> axiomSection
  <|> theoremSection
  <|> conventionSection

-- | @beginTopLevelSection keywords@ parses @"\\begin" "{" <keyword> ["*"] "}"@,
-- where @<keyword>@ is a member of @keywords@.
beginTopLevelSection :: [Text] -> FTL (Text,Bool)
beginTopLevelSection keywords = do
  texCommand "begin" <?> "\\begin"
  symbol "{" <?> "{"
  key <- getMarkupTokenOf Reports.sectionHeader keywords
  starred <- optLL1 False $ getMarkupToken Reports.sectionHeader "*" >> pure True
  symbol "}" <?> "}"
  return (key,starred)

-- | @endTopLevelSection <key> <starred>@ parses either
-- @"\\end" "{" <keyword> "}"@ or @"\\end" "{" <keyword> "*" "}"@ depending on
-- whether @starred == False@ or @starred == True@.
endTopLevelSection :: Text -> Bool -> FTL ()
endTopLevelSection keyword starred = do
  texCommand "end" <?> "\\end"
  symbol "{" <?> "{"
  getMarkupToken Reports.sectionHeader keyword <?> keyword
  when starred (markupToken Reports.sectionHeader "*" <?> "*")
  symbol "}" <?> "}"

-- | Parse a signature (TEX):
-- @"\\begin" "{" "signature" "}" ["[" <name> "]"] [<label>] <signatureBody>
-- "\\end" "{" "signature" "}"@
signatureSection :: FTL [ProofText]
signatureSection = do
  (keyword, starred) <- try $ beginTopLevelSection ["signature"]
  label <- optionalEnvLabel
  result <- sig label </> structSig label
  macrosAndPretypings <- many (try TEX.introduceMacro <|> pretypeVariable)
  endTopLevelSection keyword starred
  return $ result ++ macrosAndPretypings
  where
    sig label = do
      content <- signatureBody
      proofText <- addMetadata Signature content label
      return [proofText]
    structSig label = do
      (structVarAssumption, structContent) <- structSignatureBody
      structMetadata <- addMetadata Signature structContent label
      texCommand "begin" <?> "\\begin"
      symbol "{" <?> "{"
      env <- getTokenOf ["itemize", "enumerate"] <?> "\"itemize\" or \"enumerate\""
      symbol "}" <?> "}"
      compMetadata <- chainLL1 $ do
        texCommand "item" <?> "\\item"
        inlineSig structVarAssumption </> inlineDef structVarAssumption </> inlineAx structVarAssumption
      texCommand "end" <?> "\\end"
      symbol "{" <?> "{"
      token env <?> env
      symbol "}" <?> "}"
      return $ structMetadata : compMetadata
    inlineSig assumptions = do
      label <- optCompLabel
      content <- foldr' (pretypeBefore . pure) signatureBody assumptions
      addMetadata Signature content label
    inlineDef assumptions = do
      label <- optCompLabel
      content <- foldr' (pretypeBefore . pure) definitionBody assumptions
      addMetadata Definition content label
    inlineAx assumptions = do
      label <- optCompLabel
      content <- foldr' (pretypeBefore . pure) axiomBody assumptions
      addMetadata Axiom content label
    optCompLabel = optLL1 Nothing $ do
      label <- texCommandWithArg "label" identifier
      return (Just label)

-- | Parse a definition (TEX):
-- @"\\begin" "{" "definition" "}" ["[" <name> "]"] [<label>] <definitionBody>
-- "\\end" "{" "definition" "}"@
definitionSection :: FTL [ProofText]
definitionSection = do
  (keyword, starred) <- try $ beginTopLevelSection ["definition"]
  label <- optionalEnvLabel
  content <- definitionBody
  macrosAndPretypings <- many (try TEX.introduceMacro <|> pretypeVariable)
  endTopLevelSection keyword starred
  proofText <- addMetadata Definition content label
  return $ proofText : macrosAndPretypings

-- | Parse an axiom (TEX):
-- @"\\begin" "{" "axiom" "}" ["[" <name> "]"] [<label>] <axiomBody>
-- "\\end" "{" "axiom" "}"@
axiomSection :: FTL [ProofText]
axiomSection = do
  (keyword, starred) <- try $ beginTopLevelSection ["axiom"]
  label <- optionalEnvLabel
  content <- axiomBody
  macrosAndPretypings <- many (try TEX.introduceMacro <|> pretypeVariable)
  endTopLevelSection keyword starred
  proofText <- addMetadata Axiom content label
  return $ proofText : macrosAndPretypings

-- | Parse a theorem (TEX)
theoremSection :: FTL [ProofText]
theoremSection = do
  (keyword, starred) <- try $ beginTopLevelSection ["theorem", "proposition", "lemma", "corollary"]
  label <- optionalEnvLabel
  content <- addAssumptions . topLevelProof $
             pretypeSentence Affirmation (affirmationHeader >> statement) affirmVars finishWithOptLink <* endTopLevelSection keyword starred
  proofText <- addMetadata Theorem content label
  return [proofText]

-- | Parse a convention (TEX):
-- @"\\begin" "{" "convention" "}" (<introduceMacro> | <pretypeVariable>)+
-- "\\end" "{" "convention" "}"@
conventionSection :: FTL [ProofText]
conventionSection = do
  (keyword, starred) <- try $ beginTopLevelSection ["convention"]
  optionalEnvLabel
  macrosAndPretypings <- some (try TEX.introduceMacro <|> pretypeVariable)
  endTopLevelSection keyword starred
  return macrosAndPretypings


-- * Top-level section bodies

signatureBody :: FTL [ProofText]
signatureBody = addAssumptions $ pretype $ pretypeSentence Posit TEX.sigExtend defVars finishWithoutLink

structSignatureBody :: FTL ([Block], [ProofText])
structSignatureBody = do
  (varForm, pSent) <- pretypeSentence' Posit TEX.structSigExtend defVars structFinish
  structProofText <- addAssumptions $ pretype $ pure pSent
  varAssumption <- pretypeSentence Assumption (pure varForm) assumeVars (pure [])
  return ([varAssumption], structProofText)
  where
    structFinish = do
      tokenSeq' ["with", "the", "following", "properties"]
      symbol "." <|> symbol ":"
      return []

definitionBody :: FTL [ProofText]
definitionBody = addAssumptions $ pretype $ pretypeSentence Posit TEX.defExtend defVars finishWithoutLink

axiomBody :: FTL [ProofText]
axiomBody = addAssumptions $ pretype $ pretypeSentence Posit (affirmationHeader >> statement) affirmVars finishWithoutLink


-- | Adds parser for parsing any number of assumptions before the passed content
-- parser.
addAssumptions :: FTL [ProofText] -> FTL [ProofText]
addAssumptions content = body
  where
    body = assumption <|> content
    assumption = topAssume `pretypeBefore` body
    topAssume = pretypeSentence Assumption (assumptionHeader >> statement) assumeVars finishWithoutLink


-- * Resetting variable pretypings at new sections (TEX)

-- Reset all pretyped variables at a @\\section@ command.
section :: FTL ProofText
section = do
  pos <- tokenPos' "\\section"
  -- Reset all pretyped variables:
  modify (\st -> st {tvrExpr = []})
  return $ ProofTextInstr pos (Command ResetPretyping)


-- * Bracket expressions (aka instructions)

-- | Parses a bracket expression without evaluating it.
instruction :: FTL ProofText
instruction =
  fmap (uncurry ProofTextDrop) instrDrop
  </> fmap (uncurry ProofTextInstr) (instr </> instrExit </> instrRead)

-- | If ProofText has synonym instruction, it gets added.
addSynonym :: ProofText -> FTL ProofText
addSynonym text = case text of
  ProofTextInstr _ (Synonym syms) | length syms > 1 ->
    modify (\st -> st {strSyms = syms : strSyms st}) >> return text
  _ -> return text

-- | If ProofText has ResetPretyping instruction, we reset the pretyping.
resetPretyping :: ProofText -> FTL ProofText
resetPretyping text = case text of
  ProofTextInstr _ (Command ResetPretyping) ->
    modify (\st -> st {tvrExpr = []}) >> return text
  _ -> return text

-- | Succeeds if the ProofText consists of an exit instruction.
exitInstruction :: ProofText -> FTL [ProofText]
exitInstruction text = case text of
  ProofTextInstr _ (GetRelativeFilePath _) -> return [text]
  ProofTextInstr _ (GetModule _ _ _) -> return [text]
  ProofTextInstr _ (Command Exit) -> return []
  _ -> failing (return ()) >> return [] -- Not sure how to properly throw an error.


-- * Low-level blocks

-- | Parse a choice expression.
choose :: FTL Block
choose = sentence Choice (choiceHeader >> choice) assumeVars finishWithOptLink

-- | Parse a case hypothesis:
-- @"\begin" "{" "case "}" "{" <statement> "." "}"@
caseHypothesis :: FTL Block
caseHypothesis = do
  label "\"\\begin{case}\"" . texBegin $ markupToken Reports.proofStart "case"
  braced $ sentence Block.CaseHypothesis (finish statement) affirmVars (pure [])

-- | Parse an affirmation.
affirmation :: FTL Block
affirmation = sentence Affirmation (affirmationHeader >> statement) affirmVars finishWithOptLink </> eqChain

-- | Parse an assumption.
assumption :: FTL Block
assumption = sentence Assumption (assumptionHeader >> statement) assumeVars finishWithoutLink

-- | Parse a low-level definition.
lowLevelDefinition :: FTL Block
lowLevelDefinition = sentence LowDefinition (lowLevelDefinitionHeader >> classNotion </> mapNotion) llDefnVars finishWithoutLink


-- ** Links

-- | Finish a statement with a link.
finishWithOptLink :: FTL [Text]
finishWithOptLink = finish optLink

-- | Parses an optionsl link expression, i.e. "(by ...)"
optLink :: FTL [Text]
optLink = optLL1 [] $ parenthesised $ token' "by" >> identifiers
  where
    identifiers = reference `sepByLL1` tokenOf' [",", "and"]
    reference =
          texCommandWithArg "ref" identifier
      <|> texCommandWithArg "nameref" identifier
      <|> texCommandWithArg "cref" identifier
      <|> texCommandWithArg "printref" identifier
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
      symbolNotAfterSpace "["
      chainLL1 notClosingBrk
      symbol "]"
      label
    -- "[<name>]"
    name = do
      symbolNotAfterSpace "["
      id <- identifier
      symbol "]"
      return id
    -- "\label{<label>}"
    label = texCommandWithArg "label" identifier

    notClosingBrk = tokenPrim notCl
    notCl t = let tk = showToken t in guard (tk /= "]") >> return tk

-- | Parse an optional environment label (TEX).
optionalEnvLabel :: FTL (Maybe Text)
optionalEnvLabel = optLLx Nothing (Just <$> envLabel)


-- * Proofs

-- | Confirmation header (FTL):
-- @"indeed"@
confirmationHeader :: FTL Scheme
confirmationHeader = do
  label "\"indeed\"" $ markupToken Reports.proofStart "indeed"
  return Short

-- | Proof header (TEX):
-- @"\\begin" "{" "proof" "}" ["[" by <byProofMethod> "]"]
proofHeader :: FTL Scheme
proofHeader = do
  proofStart
  mbMbMethod <- optional $ do
    symbol "["
    token' "by"
    method <- proofMethod
    symbol "]"
    return method
  case mbMbMethod of
    Just method -> return method
    _ -> return Raw


-- | Proof start:
-- @"\\begin" "{" "proof" "}"@
proofStart :: FTL ()
proofStart = label "\"\\begin{proof}\"" . texBegin $ markupToken Reports.proofStart "proof"

-- | Proof end:
-- @"\\end" "{" "proof" "}"@
proofEnd :: FTL ()
proofEnd = label "\"\\end{proof}\"" . texEnd $ markupToken Reports.proofEnd "proof"


-- ** Proof initiation

-- | Parse a statement with an optional proof.
lowLevelProof :: FTL Block -> FTL Block
lowLevelProof p = do
  -- We use @Just@ and @Nothing@ to distinguish whether the proof belongs to a
  -- "Let us show" expression or not.
  mbPre <- optLLx Nothing (Just <$> letUsShowThat)
  let pre = fromMaybe None mbPre
  block <- p
  -- We use @Left@ and @Right@ to distinguish between the (legacy) FTL and the
  -- TEX dialect to select the right parser for the proof end. In the case of a
  -- confirmation header it does not matter if we wrap its result, namely the
  -- method @Short@, in @Left@ or @Right@ since the function @addBody@ does not
  -- run a proof end parser if the method is @Short@.
  lrPost <- optLLx (Left None) ((Left <$> FTL.proofHeader) </> (Right <$> proofHeader) </> (Right <$> confirmationHeader))
  let post = fromEither lrPost
  nf <- indThesis (Block.formula block) pre post
  let end = case lrPost of
        Left _ -> finish FTL.proofEnd
        Right _ -> proofEnd
  addBody end (pure []) pre post $ block {Block.formula = nf}

-- | Parse a top-level proof:
-- @[<letUsShowThat>] <affirmation> [<ftlProofHeader>]
topLevelProof :: FTL Block -> FTL [ProofText]
topLevelProof p = do
  bl <- p
  post <- optLLx None proofHeader
  typeBlock <- pretyping bl
  let pretyped = Block.declaredNames typeBlock
  nbl <- addDecl pretyped $ fmap ProofTextBlock $ do
    nf <- indThesis (Block.formula bl) None post
    addBody proofEnd (pure []) None post $ bl {Block.formula = nf}
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
  pbl <-
    narrow assumption </>
    lowLevelProof (narrow $ affirmation </> choose) </>
    narrow lowLevelDefinition
  return block {Block.body = [ProofTextBlock pbl]}

-- | Proof body + proof end + link
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
      lowLevelProof (narrow $ affirmation </> choose </> lowLevelDefinition) </>
      caseDestinction </> caseDestinction_old
    instruction =
      fmap (uncurry ProofTextDrop) instrDrop </>
      fmap (uncurry ProofTextInstr) instr

-- | Case distinction:
-- @<caseHypothesis> <proofBody>@
caseDestinction :: FTL Block
caseDestinction = do
  bl@Block { Block.formula = fr } <- narrow caseHypothesis
  proofBody caseDestinctionEnd (pure []) $ bl {
  Block.formula = Imp (Tag Tag.CaseHypothesis fr) mkThesis}

caseDestinctionEnd :: FTL ()
caseDestinctionEnd = label "\"\\end{case}\"" . texEnd $ markupToken Reports.proofEnd "case"


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


-- Lecacy Parsers

-- | FTL-style case distinction (for backward compatibility only):
-- @<caseHypothesis> <proofBody>@
caseDestinction_old :: FTL Block
caseDestinction_old = do
  bl@Block { Block.formula = fr } <- narrow caseHypothesis_old
  proofBody FTL.proofEnd finishWithOptLink $ bl {
  Block.formula = Imp (Tag Tag.CaseHypothesis fr) mkThesis}

-- | FTL-style case hypothesis:
-- @<statement> [ "by" <references> ] "."@
caseHypothesis_old :: FTL Block
caseHypothesis_old = sentence Block.CaseHypothesis (FTL.caseHeader >> statement) affirmVars finishWithOptLink
