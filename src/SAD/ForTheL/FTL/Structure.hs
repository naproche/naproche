-- |
-- Module      : SAD.ForTheL.FTL.Structure
-- Copyright   : (c) 2001 - 2008, Andrei Paskevich,
--               (c) 2017 - 2018, Steffen Frerix
-- License     : GPL-3
--
-- Parsing ForTheL texts


{-# LANGUAGE OverloadedStrings #-}

module SAD.ForTheL.FTL.Structure (
  forthelText
) where

import Control.Applicative
import Control.Monad.State.Class (modify)
import Data.Text.Lazy (Text)

import SAD.ForTheL.Structure
import SAD.ForTheL.Base
import SAD.ForTheL.Statement
import SAD.ForTheL.Extension
import SAD.ForTheL.Reports (markupToken, markupTokenOf)
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

-- | Parse a @.ftl@ document:
-- @{<topLevelBlock>} (<exitInstruction> | <EOF>)@
forthelText :: FTL [ProofText]
forthelText = repeatUntil (pure <$> topLevelBlock)
  (try (instruction >>= exitInstruction) <|> (eof >> return []))

-- | Parse a top-level block (FTL):
-- @<topLevelSection> | <instruction> | <macro> | <pretyping>@
topLevelBlock :: FTL ProofText
topLevelBlock =
      topLevelSection
  <|> (instruction >>= addSynonym >>= resetPretyping)
  <|> try introduceMacro
  <|> pretypeVariable


-- * Top-level sections

-- | Parse a top-level section (FTL):
-- @<signature> | <definition> | <axiom> | <theorem>@
topLevelSection :: FTL ProofText
topLevelSection =
      signatureSection
  <|> definitionSection
  <|> axiomSection
  <|> theoremSection

-- | Parse a signature (FTL):
-- @"signature" [<identifier>] "." <signatureBody>@
signatureSection :: FTL ProofText
signatureSection = do
  markupToken Reports.sectionHeader "signature"
  label <- optLL1 Nothing (Just <$> identifier)
  dot
  content <- signatureBody
  addMetadata Signature content label

-- | Parse a definition (FTL):
-- @"definition" [<identifier>] "." <definitionBody>@
definitionSection :: FTL ProofText
definitionSection = do
  markupToken Reports.sectionHeader "definition"
  label <- optLL1 Nothing (Just <$> identifier)
  dot
  content <- definitionBody
  addMetadata Definition content label

-- | Parse an axiom (FTL):
-- @"axiom" [<identifier>] "." <axiomBody>@
axiomSection :: FTL ProofText
axiomSection = do
  markupToken Reports.sectionHeader "axiom"
  label <- optLL1 Nothing (Just <$> identifier)
  dot
  content <- axiomBody
  addMetadata Axiom content label

-- | Parse a theorem (FTL):
-- @("theorem" | "proposition" | "lemma" | "corollary") [<identifier>] "."
-- <theoremBody>@
theoremSection :: FTL ProofText
theoremSection = do
  markupTokenOf Reports.sectionHeader ["theorem", "proposition", "lemma", "corollary"]
  label <- optLL1 Nothing (Just <$> identifier)
  dot
  content <- theoremBody
  addMetadata Theorem content label


-- * Top-level section bodies

signatureBody :: FTL [ProofText]
signatureBody = addAssumptions $ pretype $ pretypeSentence Posit sigExtend defVars finishWithoutLink

definitionBody :: FTL [ProofText]
definitionBody = addAssumptions $ pretype $ pretypeSentence Posit defExtend defVars finishWithoutLink

axiomBody :: FTL [ProofText]
axiomBody = addAssumptions $ pretype $ pretypeSentence Posit (affirmationHeader >> statement) affirmVars finishWithoutLink

theoremBody :: FTL [ProofText]
theoremBody = addAssumptions $ topLevelProof $ pretypeSentence Affirmation (affirmationHeader >> statement) affirmVars finishWithOptLink


-- | Adds parser for parsing any number of assumptions before the passed content
-- parser.
addAssumptions :: FTL [ProofText] -> FTL [ProofText]
addAssumptions content = body
  where
    body = assumption <|> content
    assumption = topAssume `pretypeBefore` body
    topAssume = pretypeSentence Assumption (assumptionHeader >> statement) assumeVars finishWithoutLink


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

-- | Parses an optional link expression, i.e. "(by ...)"
optLink :: FTL [Text]
optLink = optLL1 [] $ parenthesised $ markupToken Reports.reference "by" >> identifiers
  where
    identifiers = identifier `sepByLL1` tokenOf' [",", "and"]


-- * Proofs

-- | Confirmation header (FTL):
-- @"indeed"@
confirmationHeader :: FTL Scheme
confirmationHeader = do
  markupToken Reports.proofStart "indeed"
  return Short

-- | Proof header (FTL)
-- @"proof" [<byProofMethod>] "."@
proofHeader :: FTL Scheme
proofHeader = do
  markupToken Reports.proofStart "proof"
  method <- optLL1 Raw byProofMethod
  dot
  return method

-- | Proof end (FTL):
-- @"qed" | "end" | "trivial" | "obvious"@
proofEnd :: FTL ()
proofEnd = label "qed" $ markupTokenOf Reports.proofEnd ["qed", "end", "trivial", "obvious"]


-- ** Proof initiation

topLevelProof :: FTL Block -> FTL [ProofText]
topLevelProof = topProof (optLLx None $ proofHeader <|> confirmationHeader) proofEnd finishWithOptLink


-- ** Proof initiation

-- | Parse a statement with an optional proof.
proof :: FTL Block -> FTL Block
proof p = do
  pre <- optLLx None letUsShowThat
  block <- p
  post <- optLL1 None (proofHeader <|> confirmationHeader)
  nf <- indThesis (Block.formula block) pre post
  addBody proofEnd finishWithOptLink pre post $ block {Block.formula = nf}

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
  proofBody proofEnd finishWithOptLink $ bl {
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

