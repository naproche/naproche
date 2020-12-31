{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018)

Main verification loop.
-}

{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}
{-# LANGUAGE OverloadedStrings #-}

module SAD.Core.Verify (verify) where

import Data.IORef (IORef, readIORef)
import Data.Maybe (isJust)
import Control.Monad.Reader
import Data.Text.Lazy (Text)

import qualified Data.Text.Lazy as Text

import SAD.Core.Base
import SAD.Core.Check (fillDef)
import SAD.Core.Extract (addDefinition, addEvaluation, extractRewriteRule)
import SAD.Core.ProofTask (generateProofTask)
import SAD.Core.Reason (proveThesis)
import SAD.Core.Rewrite (equalityReasoning)
import SAD.Core.SourcePos (noSourcePos, fileOnlyPos)
import SAD.Core.Thesis (inferNewThesis)
import SAD.Data.Formula
import SAD.Data.Instr
import SAD.Data.Text.Block (Block(Block), ProofText(..), Section(..))
import SAD.Data.Text.Context (Context(Context))
import SAD.Export.Base (Prover)
import SAD.Helpers (notNull)

import qualified SAD.Core.Message as Message
import qualified SAD.Data.Tag as Tag
import qualified SAD.Data.Text.Block as Block
import qualified SAD.Data.Text.Context as Context
import qualified SAD.Prove.MESON as MESON

import qualified Isabelle.Markup as Markup

-- | Main verification loop
verify :: Text -> [Prover] -> IORef RState -> ProofText -> IO (Bool, Maybe ProofText)
verify fileName provers reasonerState (ProofTextRoot text) = do
  let text' = ProofTextInstr noPos (GetArgument (File NonTex) fileName) : text
  let verificationState = makeInitialVState provers text'
  Message.outputReasoner Message.TRACING (fileOnlyPos fileName) "verification started"

  result <- flip runRM reasonerState $
    runReaderT (verificationLoop verificationState) verificationState

  ignoredFails <- (\st -> sumCounter (trackers st) FailedGoals) <$>
    readIORef reasonerState

  let success = isJust result && ignoredFails == 0
  Message.outputReasoner Message.TRACING (fileOnlyPos fileName) $
    "verification " ++ (if success then "successful" else "failed")
  return (success, fmap (ProofTextRoot . tail . snd) result)

verificationLoop :: VState -> VM ([ProofText], [ProofText])
verificationLoop state@VS {
  thesisMotivated = motivated,
  rewriteRules    = rules,
  currentThesis   = thesis,
  currentBranch   = branch,
  currentContext  = context,
  mesonRules      = mRules,
  definitions     = defs,
  guards          = grds,
  restProofText = ProofTextBlock block@(Block f body kind declaredVariables _ _ _):blocks,
  evaluations     = evaluations }
    = local (const state) $ do
  justIO $ Message.report (Block.position block) Markup.running
  alreadyChecked <- askRS alreadyChecked

  -- statistics and user communication
  unless alreadyChecked $ incrementCounter Sections
  whenInstruction Printsection False $ justIO $
    Message.outputForTheL Message.WRITELN (Block.position block) $
    Message.trimString (Block.showForm 0 block "")
  let newBranch = block : branch
  let contextBlock = Context f newBranch []

  whenInstruction Translation False $
    unless (Block.isTopLevel block) $
      translateLog Message.WRITELN (Block.position block) $ Text.pack $ show f

  fortifiedFormula <-
    if Block.isTopLevel block
      then return f
      -- For low-level blocks we check definitions and fortify terms (by supplying evidence).
      else (fillDef alreadyChecked contextBlock) <|> (setFailed >> return f)

  unsetChecked

  ifAskFailed (return (restProofText state, restProofText state)) $ do
    let proofTask = generateProofTask kind (Block.declaredNames block) fortifiedFormula
    let freshThesis = Context proofTask newBranch []
    let toBeProved = (Block.needsProof block) && not (Block.isTopLevel block)
    proofBody <- do
      flat <- askInstructionBool Flat False
      if flat
        then return []
        else return body

    whenInstruction Printthesis False $ when (
      toBeProved && notNull proofBody &&
      not (hasDEC $ Context.formula freshThesis)) $
        thesisLog Message.WRITELN (Block.position block) (length branch - 1) $
        "thesis: " <> Text.pack (show (Context.formula freshThesis))


    (fortifiedProof, markedProof) <-
      if toBeProved
        then verifyProof state {
          thesisMotivated = True, currentThesis = freshThesis,
          currentBranch = newBranch, restProofText = proofBody }
        else verifyProof state {
          thesisMotivated = False, currentThesis = freshThesis,
          currentBranch = newBranch, restProofText = body }

    -- in what follows we prepare the current block to contribute to the context,
    -- extract rules, definitions and compute the new thesis
    thesisSetting <- askInstructionBool Thesis True
    let newBlock = block {
          Block.formula = deleteInductionOrCase fortifiedFormula,
          Block.body = fortifiedProof }
    let formulaImage = Block.formulate newBlock
    let markedBlock = block {Block.body = markedProof}

    ifAskFailed (return (ProofTextBlock newBlock : blocks, ProofTextBlock markedBlock : blocks)) $ do

      (mesonRules, intermediateSkolem) <- MESON.contras $ deTag formulaImage
      let (newDefinitions, newGuards) =
            if kind == Definition || kind == Signature
              then addDefinition (defs, grds) formulaImage
              else (defs, grds)
      let newContextBlock = Context formulaImage newBranch (uncurry (++) mesonRules)
      let newContext = newContextBlock : context
      let newRules =
            if Block.isTopLevel block
              then MESON.addRules mRules mesonRules
              else mRules
      let (newMotivation, hasChanged , newThesis) =
            if thesisSetting
              then inferNewThesis defs newContext thesis
              else (Block.needsProof block, False, thesis)

      whenInstruction Printthesis False $ when (
        hasChanged && motivated && newMotivation &&
        (not $ hasDEC $ Block.formula $ head branch) ) $
          thesisLog Message.WRITELN (Block.position block) (length branch - 2) $
          "new thesis: " <> Text.pack (show (Context.formula newThesis))

      when (not newMotivation && motivated) $
        thesisLog Message.WARNING (Block.position block) (length branch - 2) "unmotivated assumption"

      let newRewriteRules = extractRewriteRule (head newContext) ++ rules

      let newEvaluations =
            if   kind `elem` [LowDefinition, Definition]
            then addEvaluation evaluations formulaImage
            else evaluations-- extract evaluations
      justIO $ Message.report (Block.position block) Markup.finished
      -- Now we are done with the block. Move on and verify the rest.
      (newBlocks, markedBlocks) <- verifyProof state {
        thesisMotivated = motivated && newMotivation, guards = newGuards,
        rewriteRules = newRewriteRules, evaluations = newEvaluations,
        currentThesis = newThesis, currentContext = newContext,
        mesonRules = newRules, definitions = newDefinitions,
        skolemCounter = intermediateSkolem, restProofText = blocks }

      -- If this block made the thesis unmotivated, we must discharge a composite
      -- (and possibly quite difficult) prove task
      let finalThesis = Imp (Block.compose $ ProofTextBlock newBlock : newBlocks) (Context.formula thesis)

      -- notice that the following is only really executed if
      -- motivated && not newMotivated == True
      verifyProof state {
        thesisMotivated = motivated && not newMotivation,
        currentThesis = Context.setFormula thesis finalThesis, restProofText = [] }
      -- put everything together
      let checkMark = if Block.isTopLevel block then id else ProofTextChecked
      return (ProofTextBlock newBlock : newBlocks, checkMark (ProofTextBlock markedBlock) : markedBlocks)

-- if there is no text to be read in a branch it means we must call the prover
verificationLoop st@VS {
  thesisMotivated = True,
  rewriteRules    = rules,
  currentThesis   = thesis,
  currentContext  = context,
  restProofText        = [] }
  = local (const st) $ whenInstruction Prove True prove >> return ([], [])
  where
    prove =
      if hasDEC (Context.formula thesis) --computational reasoning
      then do
        let logAction = reasonLog Message.TRACING (Block.position block) $ "goal: " <> text
            block = Context.head thesis ; text = Block.text block
        incrementCounter Equations ; whenInstruction Printgoal True logAction
        timeWith SimplifyTimer (equalityReasoning thesis) <|> (
          reasonLog Message.WARNING (Block.position block) "equation failed" >> setFailed >>
          guardInstruction Skipfail False >> incrementCounter FailedEquations)
      else do
        let logAction = reasonLog Message.TRACING (Block.position block) $ "goal: " <> text
            block = Context.head thesis ; text = Block.text block
        unless (isTop . Context.formula $ thesis) $ incrementCounter Goals
        whenInstruction Printgoal True logAction
        proveThesis <|> (
          reasonLog Message.WARNING (Block.position block) "goal failed" >> setFailed >>
          --guardInstruction Skipfail False >>
          incrementCounter FailedGoals)

verificationLoop state@ VS {restProofText = ProofTextChecked txt : rest} =
  let newTxt = Block.setChildren txt (Block.children txt ++ newInstructions)
      newInstructions = [NonProofTextStoredInstr $
        SetFlag Prove False :
        SetFlag Printgoal False :
        SetFlag Printreason False :
        SetFlag Printsection False :
        SetFlag Printcheck False :
        SetFlag Printprover False :
        SetFlag Printunfold False :
        SetFlag Printfulltask False :
        instructions state]
  in  setChecked >> verificationLoop state {restProofText = newTxt : rest}

verificationLoop state@ VS {restProofText = NonProofTextStoredInstr ins : rest} =
  verificationLoop state {restProofText = rest, instructions = ins}

-- process instructions. we distinguish between those that influence the
-- verification state and those that influence (at most) the global state
verificationLoop state@VS {restProofText = i@(ProofTextInstr _ instr) : blocks} =
  fmap (\(as,bs) -> (as, i:bs)) $ local (const state {restProofText = blocks}) $ procProofTextInstr instr

{- process a command to drop an instruction, i.e. [/prove], etc.-}
verificationLoop state@VS {restProofText = (i@(ProofTextDrop _ instr) : blocks)} =
  fmap (\(as,bs) -> (as, i:bs)) $ local (const state {restProofText = blocks}) $ procProofTextDrop instr

verificationLoop st@VS {restProofText = (i@ProofTextSynonym{} : blocks)} =
  fmap (\(as,bs) -> (as, i:bs)) $ verificationLoop st {restProofText = blocks}
verificationLoop st@VS {restProofText = (i@ProofTextPretyping{} : blocks)} =
  fmap (\(as,bs) -> (as, i:bs)) $ verificationLoop st {restProofText = blocks}
verificationLoop st@VS {restProofText = (i@ProofTextMacro{} : blocks)} =
  fmap (\(as,bs) -> (as, i:bs)) $ verificationLoop st {restProofText = blocks}

verificationLoop VS {restProofText = []} = return ([], [])

{- some automated processing steps: add induction hypothesis and case hypothesis
at the right point in the context; extract rewriteRules from them and further
refine the currentThesis. Then move on with the verification loop.
If neither inductive nor case hypothesis is present this is the same as
verificationLoop state -}
verifyProof :: VState -> VM ([ProofText], [ProofText])
verifyProof state@VS {
  rewriteRules   = rules,
  currentThesis  = thesis,
  currentContext = context,
  currentBranch  = branch}
  = dive id context $ Context.formula thesis
  where
    dive construct context (Imp (Tag InductionHypothesis f) g)
      | isClosed f =
          process (Context.setFormula thesis f : context) (construct g)
    dive construct context (Imp (Tag Tag.CaseHypothesis f) g)
      | isClosed f =
          process (thesis {Context.formula = f} : context) (construct g)
    dive construct context (Imp f g)   = dive (construct . Imp f) context g
    dive construct context (All v f)   = dive (construct . All v) context f
    dive construct context (Tag tag f) = dive (construct . Tag tag) context f
    dive _ _ _ = verificationLoop state

    -- extract rules, compute new thesis and move on with the verification
    process newContext f = do
      let newRules = extractRewriteRule (head newContext) ++ rules
          (_, _, newThesis) =
            inferNewThesis (definitions state) newContext $ Context.setFormula thesis f
      whenInstruction Printthesis False $ when (
        noInductionOrCase (Context.formula newThesis) && not (null $ restProofText state)) $
          thesisLog Message.WRITELN
          (Block.position $ head $ Context.branch $ head context) (length branch - 2) $
          "new thesis " <> Text.pack (show (Context.formula newThesis))
      verifyProof state {
        rewriteRules = newRules, currentThesis = newThesis,
        currentContext = newContext}

{- checks that a formula containt neither induction nor case hyothesis -}
noInductionOrCase :: Formula -> Bool
noInductionOrCase (Tag InductionHypothesis _) = False
noInductionOrCase (Tag Tag.CaseHypothesis _) = False
noInductionOrCase f = allF noInductionOrCase f


{- delete induction or case hypothesis from a formula -}
deleteInductionOrCase :: Formula -> Formula
deleteInductionOrCase = dive id
  where
    dive c (Imp (Tag InductionHypothesis _) f) = c f
    dive c (Imp (Tag Tag.CaseHypothesis f) _) = c $ Not f
    dive c (Imp f g) = dive (c . Imp f) g
    dive c (All v f) = dive (c . All v) f
    dive c f = c f




-- Instruction handling

{- execute an instruction or add an instruction parameter to the state -}
procProofTextInstr :: Instr -> VM ([ProofText], [ProofText])
procProofTextInstr = flip proc $ ask >>= verificationLoop
  where
    proc (Command RULES) = (>>) $ do
      rules <- asks rewriteRules
      reasonLog Message.WRITELN noSourcePos $
        "current ruleset: " <> "\n" <> Text.unlines (map (Text.pack . show) (reverse rules))
    proc (Command THESIS) = (>>) $ do
      motivated <- asks thesisMotivated; thesis <- asks currentThesis
      let motivation = if motivated then "(motivated): " else "(not motivated): "
      reasonLog Message.WRITELN noSourcePos $
        "current thesis " <> motivation <> Text.pack (show (Context.formula thesis))
    proc (Command CONTEXT) = (>>) $ do
      context <- asks currentContext
      reasonLog Message.WRITELN noSourcePos $ "current context:\n" <>
        Text.concat (map (\form -> "  " <> Text.pack (show (Context.formula form)) <> "\n") (reverse context))
    proc (Command FILTER) = (>>) $ do
      context <- asks currentContext
      let topLevelContext = filter Context.isTopLevel context
      reasonLog Message.WRITELN noSourcePos $ "current filtered top-level context:\n" <>
        Text.concat (map (\form -> "  " <> Text.pack (show (Context.formula form)) <> "\n") (reverse topLevelContext))

    proc (Command _) = (>>) $ reasonLog Message.WRITELN noSourcePos "unsupported instruction"

    proc (SetFlag Verbose False) =
      addInstruction (SetFlag Printgoal False) .
      addInstruction (SetFlag Printreason False) .
      addInstruction (SetFlag Printsection False) .
      addInstruction (SetFlag Printcheck False) .
      addInstruction (SetFlag Printprover False) .
      addInstruction (SetFlag Printunfold False) .
      addInstruction (SetFlag Printfulltask False)

    proc (SetFlag Verbose True) =
      addInstruction (SetFlag Printgoal True) .
      addInstruction (SetFlag Printreason True) .
      addInstruction (SetFlag Printcheck True) .
      addInstruction (SetFlag Printprover True) .
      addInstruction (SetFlag Printunfold True) .
      addInstruction (SetFlag Printfulltask True)

    proc i
      | isParserInstruction i = id
      | otherwise = addInstruction i

{- drop an instruction from the state -}
procProofTextDrop :: Drop -> VM ([ProofText], [ProofText])
procProofTextDrop = flip dropInstruction $ ask >>= verificationLoop
