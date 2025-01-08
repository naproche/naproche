-- |
-- Module      : SAD.ForTheL.TEX.Structure
-- Copyright   : (c) 2001 - 2008, Andrei Paskevich,
--               (c) 2017 - 2018, Steffen Frerix
-- License     : GPL-3
--
-- Parsing ForTheL texts.


{-# LANGUAGE OverloadedStrings #-}

module SAD.ForTheL.TEX.Structure (
  forthelText
) where

import Data.List
import Control.Applicative
import Control.Monad
import Control.Monad.State.Class (modify)
import Data.Text.Lazy (Text)
import Data.Text.Lazy qualified as Text
import Data.Functor ((<&>))
import Data.Foldable (foldr')
import Data.Maybe (fromMaybe)
import System.FilePath hiding ((</>))

import SAD.ForTheL.Structure
import SAD.ForTheL.Base
import SAD.ForTheL.Statement
import SAD.ForTheL.Extension
import SAD.ForTheL.Reports (getMarkupToken, getMarkupTokenOf, markupToken, markupTokenOf)
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
import SAD.Helpers

import Isabelle.Position qualified as Position


-- * Parsing a ForTheL text

-- | Parse a @.ftl.tex@ document:
-- @{<topLevelBlock>} (<exitInstruction> | <EOF>)@
forthelText :: FTL [ProofText]
forthelText = repeatUntil topLevelBlock
  (try ((instruction <|> importModule <|> inputFile) >>= exitInstruction) <|> (eof >> return []))

-- | Parse a top-level block (TEX):
-- @<topLevelSection> | <instruction> | <macro> | <pretyping>@
topLevelBlock :: FTL [ProofText]
topLevelBlock =
      try (section <&> singleton)
  <|> try (importModule <&> singleton)
  <|> try (inputFile <&> singleton)
  <|> topLevelSection
  <|> ((instruction >>= addSynonym >>= resetPretyping) <&> singleton)
  <|> try (introduceMacro <&> singleton)
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
  label <- optTlsLabel
  result <- sig label </> structSig label
  macrosAndPretypings <- many (try introduceMacro <|> pretypeVariable)
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
  label <- optTlsLabel
  content <- definitionBody
  macrosAndPretypings <- many (try introduceMacro <|> pretypeVariable)
  endTopLevelSection keyword starred
  proofText <- addMetadata Definition content label
  return $ proofText : macrosAndPretypings

-- | Parse an axiom (TEX):
-- @"\\begin" "{" "axiom" "}" ["[" <name> "]"] [<label>] <axiomBody>
-- "\\end" "{" "axiom" "}"@
axiomSection :: FTL [ProofText]
axiomSection = do
  (keyword, starred) <- try $ beginTopLevelSection ["axiom"]
  label <- optTlsLabel
  content <- axiomBody
  macrosAndPretypings <- many (try introduceMacro <|> pretypeVariable)
  endTopLevelSection keyword starred
  proofText <- addMetadata Axiom content label
  return $ proofText : macrosAndPretypings

-- | Parse a theorem (TEX)
theoremSection :: FTL [ProofText]
theoremSection = do
  (keyword, starred) <- try $ beginTopLevelSection ["theorem", "proposition", "lemma", "corollary"]
  label <- optTlsLabel
  content <- addAssumptions . topLevelProof $
             pretypeSentence Affirmation (affirmationHeader >> statement) affirmVars finishWithOptLink <* endTopLevelSection keyword starred
  proofText <- addMetadata Theorem content label
  return [proofText]


-- * Top-level section bodies

signatureBody :: FTL [ProofText]
signatureBody = addAssumptions $ pretype $ pretypeSentence Posit sigExtend defVars finishWithoutLink

structSignatureBody :: FTL ([Block], [ProofText])
structSignatureBody = do
  (varForm, pSent) <- pretypeSentence' Posit structSigExtend defVars structFinish
  structProofText <- addAssumptions $ pretype $ pure pSent
  varAssumption <- pretypeSentence Assumption (pure varForm) assumeVars (pure [])
  return ([varAssumption], structProofText)
  where
    structFinish = do
      tokenSeq' ["with", "the", "following", "properties"]
      symbol "." <|> symbol ":"
      return []

definitionBody :: FTL [ProofText]
definitionBody = addAssumptions $ pretype $ pretypeSentence Posit defExtend defVars finishWithoutLink

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


-- * Importing Modules

importModule :: FTL ProofText
importModule = do
  beginPos <- texCommandPos "importmodule" <|> texCommandPos "usemodule"
  archivePath <- bracketed path
  (sndArgRange, (modulePath, moduleName)) <- enclosed "{" "}" $ do
    modulePath <- fromMaybe "" <$> optional (try $ path <* symbol "?")
    moduleName <- pathComponent
    return (modulePath, moduleName)
  let instr = GetModule archivePath modulePath moduleName
      endPos = Position.symbol_explode ("}" :: Text) $ snd sndArgRange
      pos = Position.range_position (beginPos, endPos)
  Reports.addInstrReport pos
  return $ ProofTextInstr pos instr

inputFile :: FTL ProofText
inputFile = do
  beginPos <- texCommandPos "inputref"
  archivePath <- bracketed path
  (filePathRange, filePath) <- enclosed "{" "}" path
  let instr = GetRelativeFilePath $ joinPath [archivePath, "source", filePath]
      endPos = Position.symbol_explode ("}" :: Text) $ snd filePathRange
      pos = Position.range_position (beginPos, endPos)
  Reports.addInstrReport pos
  return $ ProofTextInstr pos instr


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


-- ** Links

-- | Finish a statement with a link.
finishWithOptLink :: FTL [Text]
finishWithOptLink = finish optLink

-- | Parses an optionsl link expression, i.e. "(by ...)"
optLink :: FTL [Text]
optLink = optLL1 [] $ parenthesised $ markupToken Reports.reference "by" >> identifiers
  where
    identifiers = reference `sepByLL1` tokenOf' [",", "and"]
    reference =
          texCommandWithArg "ref" identifier
      <|> texCommandWithArg "nameref" identifier
      <|> texCommandWithArg "cref" identifier
      <|> texCommandWithArg "printref" identifier
      <|> identifier


-- ** Labels

-- | An optional parameter for a top-level section environment.
data TlsOption =
    TlsForthel      -- @forthel@
  | TlsTitle Text   -- @title=<title>@
  | TlsId Text      -- @id=<label>@

-- | Parse an environment label (TEX), i.e. a list of key-value pairs that
-- might contain a pair with an @id@ key and return its value.
tlsLabel :: FTL (Maybe Text)
tlsLabel = do
  symbolNotAfterSpace "["
  tlsOptions <- sepBy tlsOption (symbol ",")
  let mbLabelOption = find (\(key, val) -> key == "id") tlsOptions
  let mbLabel = case mbLabelOption of
        Just (_, TlsId label) -> Just label
        _ -> Nothing
  symbol "]"
  return mbLabel

-- | An option from the key-value list of the optional argument of a top-level
-- section environment.
tlsOption :: FTL (Text, TlsOption)
tlsOption = do
  key <- getTokenOf' ["forthel", "title", "id"]
  case key of
    "forthel" -> return (key, TlsForthel)
    "title" -> do
      symbol "="
      title <- Text.fromStrict . tokensText <$> optBraced (chainLL1 notReservedChar)
      return (key, TlsTitle title)
    "id" -> do
      symbol "="
      label <- identifier
      return (key, TlsId label)
    _ -> failWithMessage "SAD.ForTheL.Structure.tlsOption" "Unknown key."
  where
    notReservedChar = tokenPrim $ \t -> guard (showToken t `notElem` [",", "]"]) >> return t


-- | Parse an optional top-leve section environment label (TEX).
optTlsLabel :: FTL (Maybe Text)
optTlsLabel = optLLx Nothing tlsLabel


-- * Proofs

-- | An optional parameter for a @proof@ environment.
data ProofOption =
    ProofForthel        -- @forthel@
  | ProofMethod Scheme  -- @method=<proof method>@

-- | Confirmation header (FTL):
-- @"indeed"@
confirmationHeader :: FTL Scheme
confirmationHeader = do
  markupToken Reports.proofStart "indeed"
  return Short

-- | Proof header (TEX):
-- @"\\begin" "{" "proof" "}" ["[" <byProofMethod> "]"]
topLevelProofHeader :: FTL Scheme
topLevelProofHeader = do
  texBegin (markupToken Reports.proofStart "proof")
  mbMbMethod <- optional $ do
    symbol "["
    proofOptions <- sepBy0 proofOption (symbol ",")
    let mbMethodOption = find (\(key, val) -> key == "method") proofOptions
    let mbMethod = case mbMethodOption of
          Just (_, ProofMethod method) -> Just method
          _ -> Nothing
    symbol "]"
    return mbMethod
  case mbMbMethod of
    Just (Just method) -> return method
    _ -> return Raw

-- | Proof header (FTL)
-- @"proof" [<byProofMethod>] "."@
lowLevelProofHeader :: FTL Scheme
lowLevelProofHeader = do
  markupToken Reports.proofStart "proof"
  method <- optLL1 Raw byProofMethod
  dot
  return method

-- | Proof end (FTL):
-- @"qed" | "end" | "trivial" | "obvious"@
lowLevelProofEnd :: FTL ()
lowLevelProofEnd = label "qed" $ markupTokenOf Reports.proofEnd ["qed", "end", "trivial", "obvious"]

-- | An option from the key-value list of the optional argument of a proof
-- environment.
proofOption :: FTL (Text, ProofOption)
proofOption = do
  key <- getTokenOf' ["forthel", "method"]
  case key of
    "forthel" -> return (key, ProofForthel)
    "method" -> do
      symbol "="
      method <- optBraced proofMethod
      return (key, ProofMethod method)
    _ -> failWithMessage "SAD.ForTheL.Structure.proofOption" "Unknown key."

-- | Proof end (TEX):
-- @"\\end" "{" "proof" "}"@
topLevelProofEnd :: FTL ()
topLevelProofEnd = label "qed" . texEnd $ markupToken Reports.proofEnd "proof"


-- ** Proof initiation

-- | Parse a statement with an optional proof.
lowLevelProof :: FTL Block -> FTL Block
lowLevelProof p = do
  pre <- optLLx None letUsShowThat
  block <- p
  post <- optLL1 None (lowLevelProofHeader <|> confirmationHeader)
  nf <- indThesis (Block.formula block) pre post
  addBody lowLevelProofEnd finishWithOptLink pre post $ block {Block.formula = nf}

-- | Parse a top-level proof:
-- @[<letUsShowThat>] <affirmation> [<ftlProofHeader>]
topLevelProof :: FTL Block -> FTL [ProofText]
topLevelProof p = do
  pre <- optLLx None letUsShowThat
  bl <- p
  post <- optLLx None topLevelProofHeader
  typeBlock <- pretyping bl
  let pretyped = Block.declaredNames typeBlock
      link = pure []
      qed = topLevelProofEnd
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
  pbl <- narrow assumption </> lowLevelProof (narrow $ affirmation </> choose) </> narrow lowLevelDefinition
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
      lowLevelProof (narrow $ affirmation </> choose </> lowLevelDefinition) </>
      caseDestinction
    instruction =
      fmap (uncurry ProofTextDrop) instrDrop </>
      fmap (uncurry ProofTextInstr) instr

-- | Case distinction:
-- @<caseHypothesis> <proofBody>@
caseDestinction :: FTL Block
caseDestinction = do
  bl@Block { Block.formula = fr } <- narrow caseHypothesis
  proofBody lowLevelProofEnd finishWithOptLink $ bl {
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

