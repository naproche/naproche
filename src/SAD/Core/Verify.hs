{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018)

Main verification loop.
-}

module SAD.Core.Verify (verify) where

import Control.Monad
import Control.Monad.Trans.Class
import Control.Applicative hiding ((<|>))
import Data.IORef
import Data.Maybe
import qualified Data.IntMap.Strict as IM
import Data.List
import qualified Data.Set as Set
import Control.Monad.State
import qualified Control.Monad.Writer as W
import Control.Monad.Reader
import Data.Function

import SAD.Core.SourcePos
import SAD.Core.Base
import SAD.Core.Check
import qualified SAD.Core.Message as Message
import SAD.Core.Reason
import SAD.Core.Thesis
import SAD.Data.Formula
import qualified SAD.Data.Tag as Tag
import SAD.Data.Instr (Instr, isParserInstruction)
import qualified SAD.Data.Instr as Instr
import SAD.Data.Text.Block (Block(Block), Text(..), Section(..))
import qualified SAD.Data.Text.Block as Block
import SAD.Data.Text.Context (Context(Context))
import qualified SAD.Data.Text.Context as Context
import SAD.Data.Rules (Rule)
import qualified SAD.Data.Rules as Rule
import SAD.Prove.Normalize
import SAD.Prove.MESON
import SAD.Core.Reduction
import SAD.Core.ProofTask
import SAD.Core.Extract
import qualified SAD.Data.Structures.DisTree as DT
import SAD.Core.Rewrite
import SAD.Export.Base (Prover)

import qualified Isabelle.Markup as Markup

-- Main verification loop

verify :: String -> [Prover] -> IORef RState -> Text -> IO (Maybe Text)
verify fileName provers reasonerState (TextRoot text) = do
  let text' = TextInstr Instr.noPos (Instr.String Instr.File fileName) : text
  Message.outputReasoner Message.TRACING (fileOnlyPos fileName) "verification started"

  let verificationState =
        VS False [] DT.empty (Context Bot [] [] Bot) [] [] (DT.empty, DT.empty) 
          initialDefinitions initialGuards 0 [] provers text'
  result <- flip runRM reasonerState $
    runReaderT (verificationLoop verificationState) verificationState
  ignoredFails <- (\st -> accumulateIntCounter (counters st) 0 FailedGoals) <$>
    readIORef reasonerState

  let success = isJust result && ignoredFails == 0
  Message.outputReasoner Message.TRACING (fileOnlyPos fileName) $
    "verification " ++ (if success then "successful" else "failed")
  return $ fmap (TextRoot . tail . snd) result

verificationLoop :: VState -> VM ([Text], [Text])
verificationLoop state@VS {
  thesisMotivated = motivated,
  rewriteRules    = rules,
  currentThesis   = thesis,
  currentBranch   = branch,
  currentContext  = context,
  mesonRules      = mRules,
  definitions     = defs,
  guards          = grds,
  restText = TextBlock block@(Block f body kind declaredVariables _ _ _ _):blocks,
  evaluations     = evaluations }
    = local (const state) $ do
  justIO $ Message.report (Block.position block) Markup.running
  alreadyChecked <- askRS alreadyChecked

  -- statistics and user communication
  unless alreadyChecked $ incrementIntCounter Sections
  whenInstruction Instr.Printsection False $ justIO $
    Message.outputForTheL Message.WRITELN (Block.position block) $
    Message.trimText (Block.showForm 0 block "")
  let newBranch = block : branch; contextBlock = Context f newBranch [] f
  
  whenInstruction Instr.Translation False $
    unless (Block.isTopLevel block) $ translateLog Message.WRITELN (Block.position block) $ show f

  fortifiedFormula <-
    if   Block.isTopLevel block
    then return f
    else fillDef alreadyChecked contextBlock <|> (setFailed >> return f) -- check definitions and fortify terms
  
  unsetChecked

  checkFailed (return (restText state, restText state)) $ do

    let proofTask = generateProofTask kind (Block.declaredNames block) fortifiedFormula
        freshThesis = Context proofTask newBranch [] proofTask
        toBeProved = (Block.needsProof block) && not (Block.isTopLevel block)
    proofBody <- askInstructionBool Instr.Flat False >>= \p ->
      if p then return [] else return body

    whenInstruction Instr.Printthesis False $ when (
      toBeProved && (not . null) proofBody &&
      not (hasDEC $ Context.formula freshThesis)) $
        thesisLog Message.WRITELN (Block.position block) (length branch - 1) $
        "thesis: " ++ show (Context.formula freshThesis)


    (fortifiedProof, markedProof) <-
      if   toBeProved
      then verifyProof state {
        thesisMotivated = True, currentThesis = freshThesis,
        currentBranch = newBranch, restText = proofBody }
      else verifyProof state {
        thesisMotivated = False, currentThesis = freshThesis,
        currentBranch = newBranch, restText = body }

    -- in what follows we prepare the current block to contribute to the context,
    -- extract rules, definitions and compute the new thesis
    thesisSetting <- askInstructionBool Instr.Thesis True
    let newBlock = block {
          Block.formula = deleteInductionOrCase fortifiedFormula,
          Block.body = fortifiedProof }
        formulaImage = Block.formulate newBlock
        markedBlock = block {Block.body = markedProof}
    
    checkFailed (return (TextBlock newBlock : blocks, TextBlock markedBlock : blocks)) $ do

      (mesonRules, intermediateSkolem) <- contras $ deTag formulaImage
      let (newDefinitions, newGuards) =
            if   kind == Definition || kind == Signature
            then addDefinition (defs, grds) formulaImage
            else (defs, grds)
          (ontoReduction, newSkolem) =
            if Block.isTopLevel block
            then ontoReduce newDefinitions newGuards intermediateSkolem formulaImage
            else (formulaImage, intermediateSkolem)
          newContextBlock =
            Context formulaImage newBranch (uncurry (++) mesonRules) ontoReduction
          newContext = newContextBlock : context
          newRules =
            if   Block.isTopLevel block
            then addRules mRules mesonRules
            else mRules

      let (newMotivation, hasChanged , newThesis) =
            if   thesisSetting
            then inferNewThesis defs newContext thesis
            else (Block.needsProof block, False, thesis)

      whenInstruction Instr.Printthesis False $ when (
        hasChanged && motivated && newMotivation &&
        (not $ hasDEC $ Block.formula $ head branch) ) $
          thesisLog Message.WRITELN (Block.position block) (length branch - 2) $
          "new thesis: " ++ show (Context.formula newThesis)

      when (not newMotivation && motivated) $
        thesisLog Message.WARNING (Block.position block) (length branch - 2) "unmotivated assumption"

      let newRewriteRules = extractRewriteRule (head newContext) ++ rules

      let newEvaluations =
            if   kind `elem` [LowDefinition, Definition]
            then addEvaluation evaluations formulaImage
            else evaluations-- extract evaluations
      justIO $ Message.report (Block.position block) Markup.finished
      -- Now we are done with the block. Move on and verifiy the rest.
      (newBlocks, markedBlocks) <- verifyProof state {
        thesisMotivated = motivated && newMotivation, guards = newGuards,
        rewriteRules = newRewriteRules, evaluations = newEvaluations,
        currentThesis = newThesis, currentContext = newContext,
        mesonRules = newRules, definitions = newDefinitions,
        skolemCounter = newSkolem, restText = blocks }
        
      -- if this block made the thesis unmotivated, we must discharge a composite
      -- (and possibly quite difficult) prove task
      let finalThesis = Imp (Block.compose $ TextBlock newBlock : newBlocks) (Context.formula thesis)

      -- notice that the following is only really executed if 
      -- motivated && not newMotivated == True
      verifyProof state {
        thesisMotivated = motivated && not newMotivation,
        currentThesis = Context.setForm thesis finalThesis, restText = [] }
      -- put everything together
      let checkMark = if Block.isTopLevel block then id else TextChecked
      return (TextBlock newBlock : newBlocks, checkMark (TextBlock markedBlock) : markedBlocks)

-- if there is no text to be read in a branch it means we must call the prover
verificationLoop st@VS {
  thesisMotivated = True,
  rewriteRules    = rules,
  currentThesis   = thesis,
  currentContext  = context,
  restText        = [] }
  = local (const st) $ whenInstruction Instr.Prove True prove >> return ([], [])
  where
    prove =
      if hasDEC (Context.formula thesis) --computational reasoning
      then do
        let logAction = reasonLog Message.TRACING (Block.position block) $ "goal: " ++ text
            block = Context.head thesis ; text = Block.text block
        incrementIntCounter Equations ; whenInstruction Instr.Printgoal True logAction
        timer SimplifyTime (equalityReasoning thesis) <|> (
          reasonLog Message.WARNING (Block.position block) "equation failed" >> setFailed >>
          guardInstruction Instr.Skipfail False >> incrementIntCounter FailedEquations)
      else do
        let logAction = reasonLog Message.TRACING (Block.position block) $ "goal: " ++ text
            block = Context.head thesis ; text = Block.text block
        unless (isTop . Context.formula $ thesis) $ incrementIntCounter Goals
        whenInstruction Instr.Printgoal True logAction
        proveThesis <|> (
          reasonLog Message.WARNING (Block.position block) "goal failed" >> setFailed >>
          --guardInstruction Instr.Skipfail False >>
          incrementIntCounter FailedGoals)

verificationLoop state@ VS {restText = TextChecked txt : rest} =
  let newTxt = Block.setChildren txt (Block.children txt ++ newInstructions)
      newInstructions = [NonTextStoredInstr $
        Instr.Bool Instr.Prove False :
        Instr.Bool Instr.Printgoal False :
        Instr.Bool Instr.Printreason False :
        Instr.Bool Instr.Printsection False :
        Instr.Bool Instr.Printcheck False :
        Instr.Bool Instr.Printprover False :
        Instr.Bool Instr.Printunfold False :
        Instr.Bool Instr.Printfulltask False :
        instructions state]
  in  setChecked >> verificationLoop state {restText = newTxt : rest}

verificationLoop state@ VS {restText = NonTextStoredInstr ins : rest} =
  verificationLoop state {restText = rest, instructions = ins}

-- process instructions. we distinguish between those that influence the
-- verification state and those that influence (at most) the global state
verificationLoop state@VS {restText = i@(TextInstr _ instr) : blocks} =
  fmap (\(as,bs) -> (as, i:bs)) $ local (const state {restText = blocks}) $ procTextInstr instr

{- process a command to drop an instruction, i.e. [/prove], [/ontored], etc.-}
verificationLoop state@VS {restText = (i@(TextDrop _ instr) : blocks)} =
  fmap (\(as,bs) -> (as, i:bs)) $ local (const state {restText = blocks}) $ procTextDrop instr

verificationLoop st@VS {restText = (i@TextSynonym{} : blocks)} =
  fmap (\(as,bs) -> (as, i:bs)) $ verificationLoop st {restText = blocks}
verificationLoop st@VS {restText = (i@TextPretyping{} : blocks)} =
  fmap (\(as,bs) -> (as, i:bs)) $ verificationLoop st {restText = blocks}
verificationLoop st@VS {restText = (i@TextMacro{} : blocks)} =
  fmap (\(as,bs) -> (as, i:bs)) $ verificationLoop st {restText = blocks}

verificationLoop VS {restText = []} = return ([], [])

{- some automated processing steps: add induction hypothesis and case hypothesis
at the right point in the context; extract rewriteRules from them and further
refine the currentThesis. Then move on with the verification loop.
If neither inductive nor case hypothesis is present this is the same as
verificationLoop state -}
verifyProof :: VState -> VM ([Text], [Text])
verifyProof state@VS {
  rewriteRules   = rules,
  currentThesis  = thesis,
  currentContext = context,
  currentBranch  = branch}
  = dive id context $ Context.formula thesis
  where
    dive construct context (Imp (Tag InductionHypothesis f) g)
      | closed f =
          process (Context.setForm thesis f : context) (construct g)
    dive construct context (Imp (Tag Tag.CaseHypothesis f) g)
      | closed f =
          process (thesis {Context.formula = f, Context.reducedFormula = f} : context) (construct g)
    dive construct context (Imp f g)   = dive (construct . Imp f) context g
    dive construct context (All v f)   = dive (construct . All v) context f
    dive construct context (Tag tag f) = dive (construct . Tag tag) context f
    dive _ _ _ = verificationLoop state

    -- extract rules, compute new thesis and move on with the verification
    process newContext f = do
      let newRules = extractRewriteRule (head newContext) ++ rules
          (_, _, newThesis) =
            inferNewThesis (definitions state) newContext $ Context.setForm thesis f
      whenInstruction Instr.Printthesis False $ when (
        noInductionOrCase (Context.formula newThesis) && not (null $ restText state)) $
          thesisLog Message.WRITELN
          (Block.position $ head $ Context.branch $ head context) (length branch - 2) $
          "new thesis " ++ show (Context.formula newThesis)
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
procTextInstr :: Instr -> VM ([Text], [Text])
procTextInstr = flip proc $ ask >>= verificationLoop
  where
    proc (Instr.Command Instr.RULES) = (>>) $ do
      rules <- asks rewriteRules
      reasonLog Message.WRITELN noPos $
        "current ruleset: " ++ "\n" ++ Rule.printrules (reverse rules)
    proc (Instr.Command Instr.THESIS) = (>>) $ do
      motivated <- asks thesisMotivated; thesis <- asks currentThesis
      let motivation = if motivated then "(motivated): " else "(not motivated): "
      reasonLog Message.WRITELN noPos $
        "current thesis " ++ motivation ++ show (Context.formula thesis)
    proc (Instr.Command Instr.CONTEXT) = (>>) $ do
      context <- asks currentContext
      reasonLog Message.WRITELN noPos $ "current context:\n" ++
        concatMap (\form -> "  " ++ show form ++ "\n") (reverse context)
    proc (Instr.Command Instr.FILTER) = (>>) $ do
      context <- asks currentContext
      let topLevelContext = filter Context.isTopLevel context
      reasonLog Message.WRITELN noPos $ "current filtered top-level context:\n" ++
        concatMap (\form -> "  " ++ show form ++ "\n") (reverse topLevelContext)

    proc (Instr.Command _) = (>>) $ reasonLog Message.WRITELN noPos "unsupported instruction"

    proc (Instr.Bool Instr.Verbose False) =
      addInstruction (Instr.Bool Instr.Printgoal False) .
      addInstruction (Instr.Bool Instr.Printreason False) .
      addInstruction (Instr.Bool Instr.Printsection False) .
      addInstruction (Instr.Bool Instr.Printcheck False) .
      addInstruction (Instr.Bool Instr.Printprover False) .
      addInstruction (Instr.Bool Instr.Printunfold False) .
      addInstruction (Instr.Bool Instr.Printfulltask False)

    proc (Instr.Bool Instr.Verbose True) =
      addInstruction (Instr.Bool Instr.Printgoal True) .
      addInstruction (Instr.Bool Instr.Printreason True) .
      addInstruction (Instr.Bool Instr.Printcheck True) .
      addInstruction (Instr.Bool Instr.Printprover True) .
      addInstruction (Instr.Bool Instr.Printunfold True) .
      addInstruction (Instr.Bool Instr.Printfulltask True)

    proc i 
      | isParserInstruction i = id
      | otherwise = addInstruction i

{- drop an instruction from the state -}
procTextDrop :: Instr.Drop -> VM ([Text], [Text])
procTextDrop = flip dropInstruction $ ask >>= verificationLoop