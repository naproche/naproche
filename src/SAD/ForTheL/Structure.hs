-- |
-- Module      : SAD.ForTheL.Structure
-- Copyright   : (c) 2001 - 2008, Andrei Paskevich,
--               (c) 2017 - 2018, Steffen Frerix
-- License     : GPL-3
--
-- Document parsing.


{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}

module SAD.ForTheL.Structure where

import Data.List
import Data.Maybe
import Control.Applicative
import Control.Monad
import Data.Text.Lazy (Text)
import Data.Text.Lazy qualified as Text
import Data.Set qualified as Set
import Data.Set (Set)

import SAD.ForTheL.Base
import SAD.ForTheL.Statement
import SAD.ForTheL.Reports (addBlockReports, markupToken, markupTokenOf, markupTokenSeqOf)
import qualified SAD.ForTheL.Reports as Reports
import SAD.Parser.Base
import SAD.Parser.Combinators
import SAD.Parser.Token
import SAD.Parser.Primitives
import SAD.Data.Text.Block (Block, ProofText(..), Section(..))
import SAD.Data.Text.Block qualified as Block
import SAD.Data.Formula
import SAD.Data.Text.Decl
import SAD.Helpers


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

-- | Finish a statement without a link.
finishWithoutLink :: FTL [a]
finishWithoutLink = finish $ return []


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
