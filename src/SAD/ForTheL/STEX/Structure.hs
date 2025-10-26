-- |
-- Module      : SAD.ForTheL.STEX.Structure
-- Copyright   : (c) 2001 - 2008, Andrei Paskevich,
--               (c) 2017 - 2018, Steffen Frerix
--               (c) 2025 Marcel Schütz
-- License     : GPL-3
--
-- Document parsing (sTeX).


{-# LANGUAGE OverloadedStrings #-}

module SAD.ForTheL.STEX.Structure (
  forthelText
) where

import Data.List
import Control.Applicative
import Control.Monad
import Data.Text.Lazy (Text)
import Data.Text.Lazy qualified as Text
import Data.Functor ((<&>))
import Data.Foldable (foldr')
import Data.Maybe (fromMaybe)
import Data.Either.Extra (fromEither)
import System.FilePath hiding ((</>))

import SAD.ForTheL.TEX.Structure qualified as TEX
import SAD.ForTheL.Structure
import SAD.ForTheL.FTL.Structure qualified as FTL -- for backward compatibility
import SAD.ForTheL.Base
import SAD.ForTheL.Statement
import SAD.ForTheL.Extension
import SAD.ForTheL.STEX.Extension qualified as STEX
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
import SAD.Helpers

import Isabelle.Position qualified as Position


-- * Parsing a ForTheL text

-- | Parse a @.ftl.tex@ document:
-- @{<topLevelBlock>} (<exitInstruction> | <EOF>)@
forthelText :: FTL [ProofText]
forthelText = repeatUntil topLevelBlock
  (try ((instruction <|> importModule <|> inputFile) >>= TEX.exitInstruction) <|> (eof >> return []))

-- | Parse a top-level block (TEX):
-- @<topLevelSection> | <instruction> | <macro> | <pretyping>@
topLevelBlock :: FTL [ProofText]
topLevelBlock =
      try (TEX.section <&> singleton)
  <|> topLevelSection
  <|> ((instruction >>= TEX.addSynonym >>= TEX.resetPretyping) <&> singleton)
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
  label <- optTlsOptions
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
  label <- optTlsOptions
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
  label <- optTlsOptions
  content <- axiomBody
  macrosAndPretypings <- many (try introduceMacro <|> pretypeVariable)
  endTopLevelSection keyword starred
  proofText <- addMetadata Axiom content label
  return $ proofText : macrosAndPretypings

-- | Parse a theorem (TEX)
theoremSection :: FTL [ProofText]
theoremSection = do
  (keyword, starred) <- try $ beginTopLevelSection ["theorem", "proposition", "lemma", "corollary"]
  label <- optTlsOptions
  content <- TEX.addAssumptions . topLevelProof $
             pretypeSentence Affirmation (affirmationHeader >> statement) affirmVars finishWithOptLink <* endTopLevelSection keyword starred
  proofText <- addMetadata Theorem content label
  return [proofText]

-- | Parse a convention (TEX):
-- @"\\begin" "{" "convention" "}" (<introduceMacro> | <pretypeVariable>)+
-- "\\end" "{" "convention" "}"@
conventionSection :: FTL [ProofText]
conventionSection = do
  (keyword, starred) <- try $ beginTopLevelSection ["convention"]
  optTlsOptions
  macrosAndPretypings <- some (try introduceMacro <|> pretypeVariable)
  endTopLevelSection keyword starred
  return macrosAndPretypings


-- * Top-level section bodies

signatureBody :: FTL [ProofText]
signatureBody = TEX.addAssumptions $ pretype $ pretypeSentence Posit STEX.sigExtend defVars finishWithoutLink

structSignatureBody :: FTL ([Block], [ProofText])
structSignatureBody = do
  (varForm, pSent) <- pretypeSentence' Posit STEX.structSigExtend defVars structFinish
  structProofText <- TEX.addAssumptions $ pretype $ pure pSent
  varAssumption <- pretypeSentence Assumption (pure varForm) assumeVars (pure [])
  return ([varAssumption], structProofText)
  where
    structFinish = do
      tokenSeq' ["with", "the", "following", "properties"]
      symbol "." <|> symbol ":"
      return []

definitionBody :: FTL [ProofText]
definitionBody = TEX.addAssumptions $ pretype $ pretypeSentence Posit STEX.defExtend defVars finishWithoutLink

axiomBody :: FTL [ProofText]
axiomBody = TEX.addAssumptions $ pretype $ pretypeSentence Posit (affirmationHeader >> statement) affirmVars finishWithoutLink


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
  let instr = GetRelativeFilePath $ joinPath ["archive", archivePath, "source", filePath]
      endPos = Position.symbol_explode ("}" :: Text) $ snd filePathRange
      pos = Position.range_position (beginPos, endPos)
  Reports.addInstrReport pos
  return $ ProofTextInstr pos instr


-- * Bracket expressions (aka instructions)

-- | Parses a bracket expression without evaluating it.
instruction :: FTL ProofText
instruction =
  fmap (uncurry ProofTextDrop) instrDrop
  </> fmap (uncurry ProofTextInstr) (instr </> instrExit)


-- * Low-level blocks

-- | Parse a choice expression.
choose :: FTL Block
choose = sentence Choice (choiceHeader >> choice) assumeVars finishWithOptLink

-- | Parse an affirmation.
affirmation :: FTL Block
affirmation = sentence Affirmation (affirmationHeader >> statement) affirmVars finishWithOptLink </> eqChain


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
          symname
      <|> symref
      <|> identifier
    symname = do
      texCommand "sn" <|> texCommand "symname"
      optLL1 () $ do
        symbol "["
        (tokenOf ["pre", "post"] >> symbol "=" >> optBraced (chainLL1 notReservedChar)) `sepByLL1` symbol ","
        symbol "]"
      symbol "{"
      symName <- stexSymbolName
      symbol "}"
      return symName
    symref = do
      texCommand "sr" <|> texCommand "symref"
      symbol "{"
      symName <- stexSymbolName
      symbol "}"
      symbol "{"
      chainLL1 notClosingBrace
      symbol "}"
      return symName


-- ** Labels

-- | An optional parameter for a top-level section environment.
data TlsOption =
    TlsForthel      -- @forthel@
  | TlsTitle Text   -- @title=<title>@
  | TlsName Text    -- @name=<symbol>@
  | TlsFor [Text]   -- @for={<symbol_1>,...,<symbol_n>}@
  | TLsUnknown

-- | Parse an optional environment argument which is expected to be a list of
-- key-value pairs that might contain a pair with an @name@ key. If a @name@ key
-- is found, its value is returned.
tlsOptions :: FTL (Maybe Text)
tlsOptions = do
  symbolNotAfterSpace "["
  tlsOptions <- sepBy tlsOption (symbol ",")
  let mbLabelOption = find (\(key, val) -> key == "name") tlsOptions
  let mbLabel = case mbLabelOption of
        Just (_, TlsName symName) -> Just symName
        _ -> Nothing
  symbol "]"
  return mbLabel

-- | An option from the key-value list of the optional argument of a top-level
-- section environment.
tlsOption :: FTL (Text, TlsOption)
tlsOption = do
  key <- Text.fromStrict . tokensText <$> chainLL1 notReservedChar
  case key of
    "forthel" -> return (key, TlsForthel)
    "title" -> do
      symbol "="
      title <- Text.fromStrict . tokensText <$> optBraced (chainLL1 notReservedChar)
      return (key, TlsTitle title)
    "name" -> do
      symbol "="
      symName <- stexSymbolName
      return (key, TlsName symName)
    "for" -> do
      symbol "="
      symNames <- optBraced (stexSymbolName `sepByLL1` symbol ",")
      return (key, TlsFor symNames)
    _ -> return ("", TLsUnknown)

notReservedChar :: FTL Token
notReservedChar = tokenPrim $ \t -> guard (showToken t `notElem` [",", "]", "=", "}"]) >> return t

notClosingBrace :: FTL  Token
notClosingBrace = tokenPrim $ \t -> guard (showToken t /= "}") >> return t

-- | Parse an sTeX symbol name and replace all whitespaces and @-@ characters by
-- @_@ characters, so that, when passed to an ATP, these characters do not
-- cause the ATP to crash.
stexSymbolName :: FTL Text
stexSymbolName = Text.intercalate "_" . filter (/= "-") <$> chainLL1 (word <|> digit <|> getToken "-")


-- | Parse an optional top-leve section environment label.
optTlsOptions :: FTL (Maybe Text)
optTlsOptions = optLLx Nothing tlsOptions


-- * Proofs

-- | An optional parameter for a @proof@ environment.
data ProofOption =
    ProofForthel        -- @forthel@
  | ProofMethod Scheme  -- @method=<proof method>@

-- | Confirmation header (FTL):
-- @"indeed"@
confirmationHeader :: FTL Scheme
confirmationHeader = do
  label "\"indeed\"" $ markupToken Reports.proofStart "indeed"
  return Short

-- | Proof header (TEX):
-- @"\\begin" "{" "proof" "}" ["[" <byProofMethod> "]"]
proofHeader :: FTL Scheme
proofHeader = do
  TEX.proofStart
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

-- | An option from the key-value list of the optional argument of a proof
-- environment.
proofOption :: FTL (Text, ProofOption)
proofOption = proofMethodKey </> proofMethodBy
  where
    proofMethodKey = do
      key <- getTokenOf' ["forthel", "method"]
      case key of
        "forthel" -> return (key, ProofForthel)
        "method" -> do
          symbol "="
          method <- optBraced proofMethod
          return (key, ProofMethod method)
        _ -> failWithMessage "SAD.ForTheL.Structure.proofOption" "Unknown key."
    proofMethodBy = do
      token' "by"
      method <- proofMethod
      return ("method", ProofMethod method)


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
        Right _ -> TEX.proofEnd
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
    addBody TEX.proofEnd (pure []) None post $ bl {Block.formula = nf}
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
    narrow TEX.assumption </>
    lowLevelProof (narrow $ affirmation </> choose) </>
    narrow TEX.lowLevelDefinition
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
  (TEX.unfailing (fmap ProofTextBlock lowtext <|> instruction) `updateDeclbefore` proofText qed)
  where
    lowtext =
      narrow TEX.assumption </>
      lowLevelProof (narrow $ affirmation </> choose </> TEX.lowLevelDefinition) </>
      caseDestinction
    instruction =
      fmap (uncurry ProofTextDrop) instrDrop </>
      fmap (uncurry ProofTextInstr) instr

-- | Case distinction:
-- @<caseHypothesis> <proofBody>@
caseDestinction :: FTL Block
caseDestinction = do
  bl@Block { Block.formula = fr } <- narrow TEX.caseHypothesis
  proofBody TEX.caseDestinctionEnd (pure []) $ bl {
  Block.formula = Imp (Tag Tag.CaseHypothesis fr) mkThesis}


-- ** Wquality Chains

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
