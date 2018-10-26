{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018)

Main verification loop.
-}

module Alice.Core.Verify (verify) where

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

import Alice.Parser.Position
import Alice.Core.Base
import Alice.Core.Check
import Alice.Core.Reason
import Alice.Core.Thesis
import Alice.Data.Formula
import Alice.Data.Instr
import Alice.Data.Text.Block as Block
import Alice.Data.Text.Context
import Alice.Data.Rules
import Alice.Prove.Normalize
import Alice.Prove.MESON
import Alice.Core.Reduction
import Alice.Core.ProofTask
import Alice.Core.Extract
import qualified Alice.Data.Structures.DisTree as DT
import Alice.Core.Rewrite

-- Main verification loop

verify :: String -> IORef RState -> [Text] -> IO (Maybe ([Text], GState))
verify file reasonerState blocks = do
  let text = TI (InStr ISfile file) : blocks
      fileName = if null file then "stdin" else file
  putStrLn $ "[Reasoner] " ++ fileName ++ ": verification started"

  let initialVerificationState =
        VS False [] DT.empty (Context Bot [] [] Bot) [] [] text
  result <- flip runRM reasonerState $
    flip runStateT initialGlobalState $
    runReaderT (verificationLoop initialVerificationState) undefined
  ignoredFails <- (\st -> accumulateIntCounter (counters st) 0 FailedGoals) <$>
    readIORef reasonerState

  let success = isJust result && ignoredFails == 0
      out = if success then " successful" else " failed"
  putStrLn $ "[Reasoner] " ++ fileName ++ ": verification" ++ out
  return result




verificationLoop :: VState -> VM [Text]
verificationLoop state@VS {
  thesisMotivated = motivated,
  rewriteRules    = rules,
  currentThesis   = thesis,
  currentBranch   = branch,
  currentContext  = context,
  restText = TB block@(Block f body kind declaredVariables _ _ _ _):blocks,
  evaluations     = evaluations }
    = local (const state) $ do

  -- statistics and user communication
  incrementIntCounter Sections
  whenInstruction IBPsct False $
    putMessage "ForTheL" Normal (position block) $ trimLine (showForm 0 block "")
  let newBranch = block : branch; contextBlock = Context f newBranch [] f


  fortifiedFormula <-
    if   isTopLevel block
    then return f
    else fillDef contextBlock -- check definitions and fortify terms

  let proofTask = generateProofTask kind declaredVariables fortifiedFormula
      freshThesis = Context proofTask newBranch [] proofTask
      toBeProved = (needsProof block) && not (isTopLevel block)
  proofBody <- askInstructionBin IBflat False >>= \p ->
    if p then return [] else return body

  whenInstruction IBPths False $ when (
    toBeProved && (not . null) proofBody &&
    not (hasDEC $ cnForm freshThesis)) $
      thesisLog Normal (position block) (length branch - 1) $
      "thesis: " ++ show (cnForm freshThesis)


  fortifiedProof <-
    if   toBeProved
    then verifyProof state {
      thesisMotivated = True, currentThesis = freshThesis,
      currentBranch = newBranch, restText = proofBody }
    else verifyProof state {
      thesisMotivated = False, currentThesis = freshThesis,
      currentBranch = newBranch, restText = body }

  whenInstruction IBPths False $ when (
    toBeProved && (not . null) proofBody &&
    not (hasDEC $ cnForm freshThesis)) $
      thesisLog Normal (position block) (length branch - 1) "thesis resolved"

  -- in what follows we prepare the current block to contribute to the context,
  -- extract rules, definitions and compute the new thesis
  thesisSetting <- askInstructionBin IBthes True
  let newBlock = block {
        formula = deleteInductionOrCase fortifiedFormula, 
        body = fortifiedProof }
      formulaImage = formulate newBlock

  -- extract definitions
  when (kind == Definition || kind == Signature) $ addDefinition formulaImage
  -- compute MESON rules
  mesonRules  <- contras (isTopLevel block) (deTag formulaImage)
  definitions <- askGlobalState definitions
  let ontoReduction =
        foldr1 And $ map (onto_reduce definitions) (assm_nf formulaImage)
      newContextBlock =
        let reduction = if isTopLevel block then ontoReduction else formulaImage
        in  Context formulaImage newBranch mesonRules reduction
      newContext = newContextBlock : context
  when (isTopLevel block) $ addGlobalContext newContextBlock
  when (isTopLevel block) $ insertMRule mesonRules

  let (newMotivation, hasChanged , newThesis) =
        if   thesisSetting
        then inferNewThesis definitions newContext thesis
        else (needsProof block, False, thesis)

  whenInstruction IBPths False $ when (
    hasChanged && motivated && newMotivation &&
    (not $ hasDEC $ formula $ head branch) ) $
      thesisLog Normal (position block) (length branch - 2) $
      "new thesis: " ++ show (cnForm newThesis)

  when (not newMotivation && motivated) $
    thesisLog Warning (position block) (length branch - 2) "unmotivated assumption"

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
  let finalThesis = Imp (compose $ TB newBlock : newBlocks) (cnForm thesis)

  -- notice that the following is only really executed if 
  -- motivated && not newMotivated == True
  verifyProof state {
    thesisMotivated = motivated && not newMotivation,
    currentThesis = setForm thesis finalThesis, restText = [] }

  -- put everything together
  return $ TB newBlock : newBlocks

-- if there is no text to be read in a branch it means we must call the prover
verificationLoop st@VS {
  thesisMotivated = True,
  rewriteRules    = rules,
  currentThesis   = thesis,
  currentContext  = context,
  restText        = [] }
  = local (const st) $ whenInstruction IBprov True prove >> return []
  where
    prove =
      if hasDEC (cnForm thesis) --computational reasoning
      then do
        let logAction = reasonLog Normal (position block) $ "goal: " ++ text
            block = cnHead thesis ; text = Block.text block
        incrementIntCounter Equations ; whenInstruction IBPgls True logAction
        timer SimplifyTime (equalityReasoning thesis) <|> (
          reasonLog Normal (position block) "equation failed" >>
          guardInstruction IBskip False >> incrementIntCounter FailedEquations)
      else do
        let logAction = reasonLog Normal (position block) $ "goal: " ++ text
            block = cnHead thesis ; text = Block.text block
        unless (isTop . cnForm $ thesis) $ incrementIntCounter Goals
        whenInstruction IBPgls True logAction
        proveThesis <|> (
          reasonLog Normal (position block) "goal failed" >>
          guardInstruction IBskip False >>
          incrementIntCounter FailedGoals)

-- process instructions. we distinguish between those that influence the
-- verification state and those that influence (at most) the global state
verificationLoop state@VS {restText = TI instruction : blocks}
  | relevant instruction = contextTI state {restText = blocks} instruction
  | otherwise = procTI state instruction >>
      verificationLoop state {restText = blocks}

{- process a command to drop an instruction, i.e. [/prove], [/ontored], etc.-}
verificationLoop st@VS {restText = (TD instruction : blocks)} =
  procTD st instruction >> verificationLoop st {restText = blocks}

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
  = dive id context $ cnForm thesis
  where
    dive construct context (Imp (Tag DIH f) g)
      | closed f =
          process (setForm thesis f : context) (construct g)
    dive construct context (Imp (Tag DCH f) g)
      | closed f =
          process (thesis {cnForm = f, cnRedu = f} : context) (construct g)
    dive construct context (Imp f g)   = dive (construct . Imp f) context g
    dive construct context (All v f)   = dive (construct . All v) context f
    dive construct context (Tag tag f) = dive (construct . Tag tag) context f
    dive _ _ _ = verificationLoop state

    -- extract rules, compute new thesis and move on with the verification
    process newContext f = do
      definitions <- askGlobalState definitions
      let newRules = extractRewriteRule (head newContext) ++ rules
          (_, _, newThesis) =
            inferNewThesis definitions newContext $ setForm thesis f
      whenInstruction IBPths False $ when (
        noInductionOrCase (cnForm newThesis) && not (null $ restText state)) $
          thesisLog Normal (position $ head $ cnBran $ head context) (length branch - 2) $
          "new thesis " ++ show (cnForm newThesis)
      verifyProof state {
        rewriteRules = newRules, currentThesis = newThesis,
        currentContext = newContext}

{- checks that a formula containt neither induction nor case hyothesis -}
noInductionOrCase :: Formula -> Bool
noInductionOrCase (Tag DIH _) = False
noInductionOrCase (Tag DCH _) = False
noInductionOrCase f = allF noInductionOrCase f


{- delete induction or case hypothesis from a formula -}
deleteInductionOrCase :: Formula -> Formula
deleteInductionOrCase = dive id
  where
    dive c (Imp (Tag DIH _) f) = c f
    dive c (Imp (Tag DCH f) _) = c $ Not f
    dive c (Imp f g) = dive (c . Imp f) g
    dive c (All v f) = dive (c . All v) f
    dive c f = c f




-- Instruction handling

{- execute an instruction or add an instruction parameter to the state -}
procTI :: VState -> Instr -> VM ()
procTI VS {
  thesisMotivated = motivated,
  rewriteRules    = rules,
  currentThesis   = thesis,
  currentContext  = context}
  = proc
  where
    proc (InCom ICRuls) =
      reasonLog Normal noPos $ "current ruleset: " ++ "\n" ++ printrules (reverse rules)
    proc (InCom ICPths) = do
      let motivation = if motivated then "(mot): " else "(nmt): "
      reasonLog Normal noPos $ "current thesis " ++ motivation ++ show (cnForm thesis)
    proc (InCom ICPcnt) =
      reasonLog Normal noPos $ "current context:\n" ++
        concatMap (\form -> "  " ++ show form ++ "\n") (reverse context)
    proc (InCom ICPflt) = do
      let topLevelContext = filter cnTopL context
      reasonLog Normal noPos $ "current filtered top-level context:\n" ++
        concatMap (\form -> "  " ++ show form ++ "\n") (reverse topLevelContext)

    proc (InCom _) = reasonLog Normal noPos "unsupported instruction"

    proc (InBin IBverb False) = do
      addInstruction $ InBin IBPgls False
      addInstruction $ InBin IBPrsn False
      addInstruction $ InBin IBPsct False
      addInstruction $ InBin IBPchk False
      addInstruction $ InBin IBPprv False
      addInstruction $ InBin IBPunf False
      addInstruction $ InBin IBPtsk False

    proc (InBin IBverb True) = msum [
      (guardNotInstruction IBPgls True  >> addInstruction (InBin IBPgls True)),
      (guardNotInstruction IBPrsn False >> addInstruction (InBin IBPrsn True)),
      (guardNotInstruction IBPsct False >> addInstruction (InBin IBPsct True)),
      (guardNotInstruction IBPchk False >> addInstruction (InBin IBPchk True)),
      (guardNotInstruction IBPprv False >> addInstruction (InBin IBPprv True)),
      (guardNotInstruction IBPunf False >> addInstruction (InBin IBPunf True)),
      (guardNotInstruction IBPtsk False >> addInstruction (InBin IBPtsk True)),
       return () ]

    proc (InPar IPgrup ps) = addGroup ps

    proc i = addInstruction i

{- drop an instruction from the state -}
procTD :: VState -> Idrop -> VM ()
procTD _ = dropInstruction

-- Context settings

{- manipulate context by hand -}
contextTI :: VState -> Instr -> VM [Text]
contextTI state@VS {
  thesisMotivated = motivated,
  rewriteRules    = rules,
  currentThesis   = thesis,
  currentContext  = context}
  = proc
  where
    proc (InPar IPscnt groupLink) = do
      newContext <- setContext groupLink
      verificationLoop state {
        currentContext = takeWhile cnLowL context ++ newContext}
    proc (InPar IPdcnt groupLink) = do
      link <- getLink groupLink
      verificationLoop state {
        currentContext = filter (not . flip elem link . cnName) context }
    proc (InPar IPacnt groupLink) = do
      newContext <- setContext groupLink
      verificationLoop state {
        currentContext = unionBy ((==) `on` cnName) newContext context}
{- the function definition must include the continuation with verificationLoop
since it influences the verification state (procTI only influences the global
state) -}

setContext [] = askGlobalState globalContext
setContext groupLink = getLink groupLink >>= retrieveContext
