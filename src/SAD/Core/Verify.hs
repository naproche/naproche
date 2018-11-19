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
import SAD.Data.Instr (Instr)
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

-- Main verification loop

verify :: String -> IORef RState -> [Text] -> IO (Maybe ([Text], GState))
verify fileName reasonerState text = do
  let text' = TextInstr Instr.noPos (Instr.String Instr.File fileName) : text
  Message.outputReason Message.TRACING (fileOnlyPos fileName) "verification started"

  let verificationState = VS False [] DT.empty (Context Bot [] [] Bot) [] [] text'
  result <- flip runRM reasonerState $
    flip runStateT initialGlobalState $
    runReaderT (verificationLoop verificationState) undefined
  ignoredFails <- (\st -> accumulateIntCounter (counters st) 0 FailedGoals) <$>
    readIORef reasonerState

  let success = isJust result && ignoredFails == 0
  Message.outputReason Message.TRACING (fileOnlyPos fileName) $
    "verification " ++ (if success then "successful" else "failed")
  return result




verificationLoop :: VState -> VM [Text]
verificationLoop state@VS {
  thesisMotivated = motivated,
  rewriteRules    = rules,
  currentThesis   = thesis,
  currentBranch   = branch,
  currentContext  = context,
  restText = TextBlock block@(Block f body kind declaredVariables _ _ _ _):blocks,
  evaluations     = evaluations }
    = local (const state) $ do

  -- statistics and user communication
  incrementIntCounter Sections
  whenInstruction Instr.Printsection False $ justIO $
    Message.outputForTheL Message.WRITELN (Block.position block) $
    Message.trim (Block.showForm 0 block "")
  let newBranch = block : branch; contextBlock = Context f newBranch [] f


  fortifiedFormula <-
    if   Block.isTopLevel block
    then return f
    else fillDef contextBlock -- check definitions and fortify terms

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


  fortifiedProof <-
    if   toBeProved
    then verifyProof state {
      thesisMotivated = True, currentThesis = freshThesis,
      currentBranch = newBranch, restText = proofBody }
    else verifyProof state {
      thesisMotivated = False, currentThesis = freshThesis,
      currentBranch = newBranch, restText = body }

  whenInstruction Instr.Printthesis False $ when (
    toBeProved && (not . null) proofBody &&
    not (hasDEC $ Context.formula freshThesis)) $
      thesisLog Message.WRITELN (Block.position block) (length branch - 1) "thesis resolved"

  -- in what follows we prepare the current block to contribute to the context,
  -- extract rules, definitions and compute the new thesis
  thesisSetting <- askInstructionBool Instr.Thesis True
  let newBlock = block {
        Block.formula = deleteInductionOrCase fortifiedFormula,
        Block.body = fortifiedProof }
      formulaImage = Block.formulate newBlock

  -- extract definitions
  when (kind == Definition || kind == Signature) $ addDefinition formulaImage
  -- compute MESON rules
  mesonRules  <- contras $ deTag formulaImage
  definitions <- askGlobalState definitions
  let ontoReduction =
        foldr1 And $ map (onto_reduce definitions) (assm_nf formulaImage)
      newContextBlock =
        let reduction = if Block.isTopLevel block then ontoReduction else formulaImage
        in  Context formulaImage newBranch mesonRules reduction
      newContext = newContextBlock : context
  when (Block.isTopLevel block) $ addGlobalContext newContextBlock
  when (Block.isTopLevel block) $ insertMRule mesonRules

  let (newMotivation, hasChanged , newThesis) =
        if   thesisSetting
        then inferNewThesis definitions newContext thesis
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


  -- Now we are done with the block. Move on and verifiy the rest.
  newBlocks <- verifyProof state {
    thesisMotivated = motivated && newMotivation,
    rewriteRules = newRewriteRules, evaluations = newEvaluations,
    currentThesis = newThesis, currentContext = newContext, restText = blocks }

  -- if this block made the thesis unmotivated, we must discharge a composite
  -- (and possibly quite difficult) prove task
  let finalThesis = Imp (Block.compose $ TextBlock newBlock : newBlocks) (Context.formula thesis)

  -- notice that the following is only really executed if 
  -- motivated && not newMotivated == True
  verifyProof state {
    thesisMotivated = motivated && not newMotivation,
    currentThesis = Context.setForm thesis finalThesis, restText = [] }

  -- put everything together
  return $ TextBlock newBlock : newBlocks

-- if there is no text to be read in a branch it means we must call the prover
verificationLoop st@VS {
  thesisMotivated = True,
  rewriteRules    = rules,
  currentThesis   = thesis,
  currentContext  = context,
  restText        = [] }
  = local (const st) $ whenInstruction Instr.Prove True prove >> return []
  where
    prove =
      if hasDEC (Context.formula thesis) --computational reasoning
      then do
        let logAction = reasonLog Message.WRITELN (Block.position block) $ "goal: " ++ text
            block = Context.head thesis ; text = Block.text block
        incrementIntCounter Equations ; whenInstruction Instr.Printgoal True logAction
        timer SimplifyTime (equalityReasoning thesis) <|> (
          reasonLog Message.WARNING (Block.position block) "equation failed" >>
          guardInstruction Instr.Skipfail False >> incrementIntCounter FailedEquations)
      else do
        let logAction = reasonLog Message.WRITELN (Block.position block) $ "goal: " ++ text
            block = Context.head thesis ; text = Block.text block
        unless (isTop . Context.formula $ thesis) $ incrementIntCounter Goals
        whenInstruction Instr.Printgoal True logAction
        proveThesis <|> (
          reasonLog Message.WARNING (Block.position block) "goal failed" >>
          guardInstruction Instr.Skipfail False >>
          incrementIntCounter FailedGoals)

-- process instructions. we distinguish between those that influence the
-- verification state and those that influence (at most) the global state
verificationLoop state@VS {restText = TextInstr _ instr : blocks}
  | Instr.relevant instr = contextTextInstr state {restText = blocks} instr
  | otherwise = procTextInstr state instr >>
      verificationLoop state {restText = blocks}

{- process a command to drop an instruction, i.e. [/prove], [/ontored], etc.-}
verificationLoop st@VS {restText = (TextDrop _ instr : blocks)} =
  procTextDrop st instr >> verificationLoop st {restText = blocks}

verificationLoop st@VS {restText = (TextExtension _ : blocks)} =
  verificationLoop st {restText = blocks}

verificationLoop _ = return []

{- some automated processing steps: add induction hypothesis and case hypothesis
at the right point in the context; extract rewriteRules from them and further
refine the currentThesis. Then move on with the verification loop.
If neither inductive nor case hypothesis is present this is the same as
verificationLoop state -}
verifyProof :: VState -> VM [Text]
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
      definitions <- askGlobalState definitions
      let newRules = extractRewriteRule (head newContext) ++ rules
          (_, _, newThesis) =
            inferNewThesis definitions newContext $ Context.setForm thesis f
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
procTextInstr :: VState -> Instr -> VM ()
procTextInstr VS {
  thesisMotivated = motivated,
  rewriteRules    = rules,
  currentThesis   = thesis,
  currentContext  = context}
  = proc
  where
    proc (Instr.Command Instr.RULES) =
      reasonLog Message.WRITELN noPos $ "current ruleset: " ++ "\n" ++ Rule.printrules (reverse rules)
    proc (Instr.Command Instr.THESIS) = do
      let motivation = if motivated then "(motivated): " else "(not motivated): "
      reasonLog Message.WRITELN noPos $ "current thesis " ++ motivation ++ show (Context.formula thesis)
    proc (Instr.Command Instr.CONTEXT) =
      reasonLog Message.WRITELN noPos $ "current context:\n" ++
        concatMap (\form -> "  " ++ show form ++ "\n") (reverse context)
    proc (Instr.Command Instr.FILTER) = do
      let topLevelContext = filter Context.isTopLevel context
      reasonLog Message.WRITELN noPos $ "current filtered top-level context:\n" ++
        concatMap (\form -> "  " ++ show form ++ "\n") (reverse topLevelContext)

    proc (Instr.Command _) = reasonLog Message.WRITELN noPos "unsupported instruction"

    proc (Instr.Bool Instr.Verbose False) = do
      addInstruction $ Instr.Bool Instr.Printgoal False
      addInstruction $ Instr.Bool Instr.Printreason False
      addInstruction $ Instr.Bool Instr.Printsection False
      addInstruction $ Instr.Bool Instr.Printcheck False
      addInstruction $ Instr.Bool Instr.Printprover False
      addInstruction $ Instr.Bool Instr.Printunfold False
      addInstruction $ Instr.Bool Instr.Printfulltask False

    proc (Instr.Bool Instr.Verbose True) = msum [
      guardNotInstruction Instr.Printgoal True
        >> addInstruction (Instr.Bool Instr.Printgoal True),
      guardNotInstruction Instr.Printreason False
        >> addInstruction (Instr.Bool Instr.Printreason True),
      guardNotInstruction Instr.Printsection False
        >> addInstruction (Instr.Bool Instr.Printsection True),
      guardNotInstruction Instr.Printcheck False
        >> addInstruction (Instr.Bool Instr.Printcheck True),
      guardNotInstruction Instr.Printprover False
        >> addInstruction (Instr.Bool Instr.Printprover True),
      guardNotInstruction Instr.Printunfold False
        >> addInstruction (Instr.Bool Instr.Printunfold True),
      guardNotInstruction Instr.Printfulltask False
        >> addInstruction (Instr.Bool Instr.Printfulltask True),
      return ()]

    proc (Instr.Strings Instr.Group ps) = addGroup ps

    proc i = addInstruction i

{- drop an instruction from the state -}
procTextDrop :: VState -> Instr.Drop -> VM ()
procTextDrop _ = dropInstruction

-- Context settings

{- manipulate context by hand -}
contextTextInstr :: VState -> Instr -> VM [Text]
contextTextInstr state@VS {
  thesisMotivated = motivated,
  rewriteRules    = rules,
  currentThesis   = thesis,
  currentContext  = context}
  = proc
  where
    proc (Instr.Strings Instr.SetCtxt groupLink) = do
      newContext <- setContext groupLink
      verificationLoop state {
        currentContext = takeWhile Context.isLowLevel context ++ newContext}
    proc (Instr.Strings Instr.DrpCtxt groupLink) = do
      link <- getLink groupLink
      verificationLoop state {
        currentContext = filter (not . flip elem link . Context.name) context }
    proc (Instr.Strings Instr.AddCtxt groupLink) = do
      newContext <- setContext groupLink
      verificationLoop state {
        currentContext = unionBy ((==) `on` Context.name) newContext context}
{- the function definition must include the continuation with verificationLoop
since it influences the verification state (procTextInstr only influences the
global state) -}

setContext [] = askGlobalState globalContext
setContext groupLink = getLink groupLink >>= retrieveContext
