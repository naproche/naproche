-- |
-- Module      : SAD.ForTheL.Structure
-- Copyright   : (c) 2001 - 2008, Andrei Paskevich,
--               (c) 2017 - 2018, Steffen Frerix
-- License     : GPL-3
--
-- Syntax of ForTheL sections.


{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}

module SAD.ForTheL.Structure (
  forthelFtl,
  forthelTex
) where

import Data.List
import Data.Maybe
import Control.Applicative
import Control.Monad
import Control.Monad.State.Class (modify)
import Data.Text.Lazy (Text)
import Data.Text.Lazy qualified as Text
import Data.Set qualified as Set
import Data.Set (Set)
import Data.Functor ((<&>))
import Data.Foldable (foldr')

import SAD.ForTheL.Base
import SAD.ForTheL.Statement
import SAD.ForTheL.Extension
import SAD.ForTheL.Instruction
import SAD.ForTheL.Reports (addBlockReports, getMarkupToken, getMarkupTokenOf, markupToken, markupTokenOf, markupTokenSeqOf)
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
import SAD.Data.Text.Decl
import SAD.Helpers


-- * Parsing a ForTheL text

-- ** FTL

-- | Parse a @.ftl@ document:
-- @{<topLevelBlock>} (<exitInstruction> | <EOF>)@
forthelFtl :: FTL [ProofText]
forthelFtl = repeatUntil (pure <$> topLevelBlockFtl)
  (try (bracketExpression >>= exitInstruction) <|> (eof >> return []))

-- | Parse a top-level block (FTL):
-- @<topLevelSection> | <instruction> | <macro> | <pretyping>@
topLevelBlockFtl :: FTL ProofText
topLevelBlockFtl =
      topLevelSectionFtl
  <|> (bracketExpression >>= addSynonym >>= resetPretyping)
  <|> try introduceMacro
  <|> pretypeVariable


-- ** TEX

-- | Parse a @.ftl.tex@ document:
-- @{<topLevelBlock>} (<exitInstruction> | <EOF>)@
forthelTex :: FTL [ProofText]
forthelTex = repeatUntil topLevelBlockTex
  (try (bracketExpression >>= exitInstruction) <|> (eof >> return []))

-- | Parse a top-level block (TEX):
-- @<topLevelSection> | <instruction> | <macro> | <pretyping>@
topLevelBlockTex :: FTL [ProofText]
topLevelBlockTex =
      try (section <&> singleton)
  <|> topLevelSectionTex
  <|> ((bracketExpression >>= addSynonym >>= resetPretyping) <&> singleton)
  <|> try (introduceMacro <&> singleton)
  <|> (pretypeVariable <&> singleton)


-- * Top-level sections

-- ** FTL

-- | Parse a top-level section (FTL):
-- @<signature> | <definition> | <axiom> | <theorem>@
topLevelSectionFtl :: FTL ProofText
topLevelSectionFtl =
      signatureFtl
  <|> definitionFtl
  <|> axiomFtl
  <|> theoremFtl

-- | Parse a signature (FTL):
-- @"signature" [<identifier>] "." <signatureBody>@
signatureFtl :: FTL ProofText
signatureFtl = do
  markupToken Reports.sectionHeader "signature"
  label <- optLL1 Nothing (Just <$> identifier)
  dot
  content <- signatureBody
  addMetadata Signature content label

-- | Parse a definition (FTL):
-- @"definition" [<identifier>] "." <definitionBody>@
definitionFtl :: FTL ProofText
definitionFtl = do
  markupToken Reports.sectionHeader "definition"
  label <- optLL1 Nothing (Just <$> identifier)
  dot
  content <- definitionBody
  addMetadata Definition content label

-- | Parse an axiom (FTL):
-- @"axiom" [<identifier>] "." <axiomBody>@
axiomFtl :: FTL ProofText
axiomFtl = do
  markupToken Reports.sectionHeader "axiom"
  label <- optLL1 Nothing (Just <$> identifier)
  dot
  content <- axiomBody
  addMetadata Axiom content label

-- | Parse a theorem (FTL):
-- @("theorem" | "proposition" | "lemma" | "corollary") [<identifier>] "."
-- <theoremBody>@
theoremFtl :: FTL ProofText
theoremFtl = do
  markupTokenOf Reports.sectionHeader ["theorem", "proposition", "lemma", "corollary"]
  label <- optLL1 Nothing (Just <$> identifier)
  dot
  content <- theoremBody
  addMetadata Theorem content label


-- ** TEX

-- | Parse a top-level section:
-- @<signature> | <definition> | <axiom> | <theorem>@
topLevelSectionTex :: FTL [ProofText]
topLevelSectionTex =
      signatureTex
  <|> definitionTex
  <|> axiomTex
  <|> theoremTex

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
signatureTex :: FTL [ProofText]
signatureTex = do
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
definitionTex :: FTL [ProofText]
definitionTex = do
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
axiomTex :: FTL [ProofText]
axiomTex = do
  (keyword, starred) <- try $ beginTopLevelSection ["axiom"]
  label <- optTlsLabel
  content <- axiomBody
  macrosAndPretypings <- many (try introduceMacro <|> pretypeVariable)
  endTopLevelSection keyword starred
  proofText <- addMetadata Axiom content label
  return $ proofText : macrosAndPretypings

-- | Parse a theorem (TEX)
theoremTex :: FTL [ProofText]
theoremTex = do
  (keyword, starred) <- try $ beginTopLevelSection ["theorem", "proposition", "lemma", "corollary"]
  label <- optTlsLabel
  content <- addAssumptions . texTopLevelProof $
             pretypeSentence Affirmation (affirmationHeader >> statement) affirmVars finishWithOptLink <* endTopLevelSection keyword starred
  proofText <- addMetadata Theorem content label
  return [proofText]


-- ** Adding meta data

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

-- | If ProofText has ResetPretyping instruction, we reset the pretyping.
resetPretyping :: ProofText -> FTL ProofText
resetPretyping text = case text of
  ProofTextInstr _ (Command ResetPretyping) ->
    modify (\st -> st {tvrExpr = []}) >> return text
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
      Just (c, "") -> guard (isAsciiAlphaNum c || c == '_') >> return (Text.singleton c)
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
  | TlsPrintId      -- @printid@

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
  key <- getTokenOf' ["forthel", "title", "id", "printid"]
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
    "printid" -> return (key, TlsPrintId)
    _ -> error "SAD.ForTheL.Structure.tlsOption: Unknown key. If you see this message, please file an issue."
  where
    notReservedChar = tokenPrim $ \t -> guard (showToken t `notElem` [",", "]"]) >> return t


-- | Parse an optional top-leve section environment label (TEX).
optTlsLabel :: FTL (Maybe Text)
optTlsLabel = optLLx Nothing tlsLabel


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
letUs = optLL1 () $ markupTokenSeqOf Reports.lowlevelHeader [["let",  "us"], ["we", "can"]]

-- | Header for choice expressions:
-- @[ <hence> ] [ <letUs> ] ("choose" | "take" | "consider")@
choiceHeader :: FTL ()
choiceHeader = hence >> letUs >> markupTokenOf Reports.lowlevelHeader ["choose", "take", "consider"]

-- | Header for case hypothesis:
-- @"case"@
caseHeader :: FTL ()
caseHeader = markupToken Reports.proofStart "case"

-- | Header for affirmation:
-- @<hence>@
affirmationHeader :: FTL ()
affirmationHeader = hence

-- | Header for assumption:
-- @"let" | (<letUs> ("assume" | "presume" | "suppose") ["that"])
assumptionHeader :: FTL ()
assumptionHeader = lus </> markupToken Reports.lowlevelHeader "let"
  where
    lus = letUs >> markupTokenOf Reports.lowlevelHeader ["assume", "presume", "suppose"] >> optLL1 () (token' "that")

-- | Low-leve definition header:
-- @"define"@
lowLevelDefinitionHeader :: FTL ()
lowLevelDefinitionHeader = markupToken Reports.lowlevelHeader "define"


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

statementBlock' :: Section
                -> FTL (a, Formula)
                -> FTL [Text]
                -> FTL (a, Block)
statementBlock' kind p mbLink = do
  nm <- optLLx "__" (parenthesised identifier)
  inp <- getInput
  (x, fr) <- p
  link <- mbLink
  toks <- getTokens inp
  return (x, Block.makeBlock fr [] kind nm link toks)


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

pretypeSentence' :: Section
                 -> FTL (a, Formula)
                 -> (Set VariableName -> Formula -> Maybe Text)
                 -> FTL [Text]
                 -> FTL (a, Block)
pretypeSentence' kind p wfVars mbLink = do
    (x, bl) <- prtp
    bl' <- narrow (pure bl)
    return (x, bl')
  where
    prtp = do
      dvs <- getDecl
      tvr <- fmap (Set.unions . map fst) getPretyped
      (x, bl') <- statementBlock' kind p mbLink
      bl <- wellFormedCheck (wf dvs tvr) $ pure bl'
      newDecl <- bindings dvs $ Block.formula bl
      let nbl = if Block.canDeclare kind then bl {Block.declaredVariables = newDecl} else bl
      addBlockReports nbl
      return (x, nbl {Block.formula = Block.formula bl})
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
    x = head . Set.elems $ declNames mempty f

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
  markupTokenOf Reports.lowlevelHeader ["prove", "show", "demonstrate"]
  method <- optLL1 Raw byProofMethod
  markupToken Reports.lowlevelHeader "that"
  return method

-- | Confirmation header (FTL):
-- @"indeed"@
ftlConfirmationHeader :: FTL Scheme
ftlConfirmationHeader = do
  markupToken Reports.proofStart "indeed"
  return Short

-- | Proof header (FTL)
-- @"proof" [<byProofMethod>] "."@
ftlProofHeader :: FTL Scheme
ftlProofHeader = do
  markupToken Reports.proofStart "proof"
  method <- optLL1 Raw byProofMethod
  dot
  return method

-- | An optional parameter for a @proof@ environment.
data ProofOption =
    ProofForthel        -- @forthel@
  | ProofMethod Scheme  -- @method=<proof method>@

-- | Proof header (TEX):
-- @"\\begin" "{" "proof" "}" ["[" <byProofMethod> "]"]
texProofHeader :: FTL Scheme
texProofHeader = do
  texBegin (markupToken Reports.proofStart "proof")
  mbMbMethod <- optional $ do
    symbol "["
    proofOptions <- sepBy proofOption (symbol ",")
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
proofOption = do
  key <- getTokenOf' ["forthel", "method"]
  case key of
    "forthel" -> return (key, ProofForthel)
    "method" -> do
      symbol "="
      method <- optBraced proofMethod
      return (key, ProofMethod method)
    _ -> error "SAD.ForTheL.Structure.proofOption: Unknown key. If you see this message, please file an issue."

-- | By proof method:
-- @"by" <proof method>@
byProofMethod :: FTL Scheme
byProofMethod = markupToken Reports.byAnnotation "by" >> proofMethod

-- | Proof method:
-- @"contradiction" | "case" "analysis" | "induction" ["on" <sTerm>]@
proofMethod :: FTL Scheme
proofMethod = contradiction <|> caseAnalysis <|> induction
  where
    contradiction = token' "contradiction" >> return Contradiction
    caseAnalysis = token' "case" >> token' "analysis" >> return Raw
    induction = token' "induction" >> optLL1 InS (token' "on" >> fmap InT sTerm)

-- | Proof end (FTL):
-- @"qed" | "end" | "trivial" | "obvious"@
ftlProofEnd :: FTL ()
ftlProofEnd = label "qed" $ markupTokenOf Reports.proofEnd ["qed", "end", "trivial", "obvious"]

-- | Proof end (TEX):
-- @"\\end" "{" "proof" "}"@
texProofEnd :: FTL ()
texProofEnd = label "qed" . texEnd $ markupToken Reports.proofEnd "proof"

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
