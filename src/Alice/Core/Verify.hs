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

import Alice.Data.Base
import Alice.Core.Base
import Alice.Core.Check
import Alice.Core.Reason
import Alice.Core.Thesis
import Alice.Data.Formula
import Alice.Data.Kit
import Alice.Data.Instr
import Alice.Data.Text
import Alice.Prove.Normalize
import Alice.Prove.MESON
import Alice.Core.Reduction
import Alice.Core.ProofTask
import Alice.Core.Extract
import qualified Alice.Data.DisTree as DT

import Alice.Core.Rewrite hiding (simplify)

import Debug.Trace

-- Main verification loop




-- rst -> reasoner state, bs -> blocks
verify file rst bs =
  do  let text = TI (InStr ISfile file) : bs
          fnam = if null file then "stdin" else file
      putStrLn $ "[Reason] " ++ fnam ++ ": verification started"

      let initVS = VS False [] DT.empty (Context Bot [] [] Bot) [] [] text
      res <- flip runRM rst $  flip runStateT initialGlobalState $ runReaderT (vLoop initVS) undefined -- here we start the verification
      ign <- liftM (\st -> accumulateIntCounter (counters st) 0 FailedGoals) $ readIORef rst

      let scs = isJust res && ign == 0
          out = if scs then " successful" else " failed" -- successful if everything went through without failures
      putStrLn $ "[Reason] " ++ fnam ++ ": verification" ++ out
      return res




vLoop :: VState -> VM [Text]
vLoop st@VS {thesisMotivated = mot, rewriteRules = rls, currentThesis = ths, branch = brn, currentContext = cnt, remainingText = TB bl@(Block fr pr sg dv _ _ _ _) : bs, evaluations = evs } = local (const st) $
  do  incrementIntCounter Sections ; tfn <- askInstructionString ISfile "" ; whenInstruction IBPsct False $
        putStrRM $ "[ForTheL] " ++ blockLabel tfn bl ++ showForm 0 bl ""
      let nbr = bl : brn; cbl = Context fr nbr [] fr

      -- so far only maintanance, user communication and namings
      nfr <- if noForm bl then return fr               -- noForm signifies that the current block is a top level block
             else fillDef cbl   -- check definitions and fortify the formula of the block

      flt <- askInstructionBin IBflat False
      let prt = proofTask sg dv nfr             -- in case of a "Choice" block, the proof task is set here to an existential statement
          sth = Context prt nbr [] prt
          bsg = null brn || blSign (head brn)          -- bsg is false iff the block is an immediate subblock of sigext, definiton or axiom
          smt = bsg && (blSign bl) && not (noForm bl)  -- smt is true iff the block represents a statement that must be proved
          spr = if flt then [] else pr                 -- this sets the proof for the following proof task. It is empty if "flat" has been activated by the user

      whenInstruction IBPths False $ do when (smt && (not . null) spr && not (hasDEC $ cnForm sth)) $ thesisLog (length brn - 1) bl $ "thesis: " ++ show (cnForm sth) --communicate thesis to the user


      npr <- if smt then splitTh st {thesisMotivated = smt, currentThesis = sth, branch = nbr, remainingText = spr } -- recursively move into the proof to verify the block at hand
                    else splitTh st {thesisMotivated = smt, currentThesis = sth, branch = nbr, remainingText =  pr } -- after success npr is returned, i.e the proof blocks with fortified formulas

      whenInstruction IBPths False $ when (smt && (not . null) spr && not (hasDEC $ cnForm sth)) $ thesisLog (length brn -1 ) bl $ "thesis resolved"

      -- in what follows we prepare the current block to contribute to the context, extract rules, definitions and compute the new thesis
      mtv <- askInstructionBin IBthes True
      let nbl = bl { blForm = deICH nfr, blBody = npr }
          blf = formulate nbl

      when (sg == Defn || sg == Sign) $ addDefinition blf -- extract Definitions
      mrl <- contras (noForm bl) (deTag blf) -- compute MESON rules for the internal proof method
      dfs <- askGlobalState definitions
      let red = foldr1 And $ map (onto_reduce dfs) (assm_nf blf) -- compute ontological reduction of the formula
          ncn = Context blf nbr mrl (if noForm bl then red else blf) --put everything together
          nct = ncn : cnt -- add to context
      when (noForm bl) $ addGlobalContext ncn -- if the current block is a top level block, add its context to the global context
      when (noForm bl) $ insertMRule mrl

      let (nmt, chng , nth) = if mtv then new_thesis dfs nct ths  -- compute the new thesis if thesis management is not disabled by the user
                                     else (blSign bl,False, ths)

      whenInstruction IBPths False $ do when (chng && mot && nmt && (not $ hasDEC $ blForm $ head brn) ) $ thesisLog (length brn - 2) bl $ "new thesis: " ++ show (cnForm nth)
      
      when (not nmt && mot) $ thesisLog (length brn - 2) bl $ "Warning: unmotivated assumption"

      let nrls = extractRule (head nct) ++ rls -- extract rewrite rules

      let nevs = if sg `elem` [Declare, Defn] then addEvaluation evs blf else evs-- extract evaluations


      -- now we are done with the block and move on to verify the rest of the text (with an updated VS)
      nbs <- splitTh st {thesisMotivated = mot && nmt, rewriteRules = nrls, evaluations = nevs, currentThesis = nth, currentContext = nct, remainingText = bs }

      -- if the thesis was turned unmotivated by this block, we must provide a composite (and possibly quite difficult) prove task
      let fth = Imp (compose $ TB nbl : nbs) (cnForm ths)
      splitTh st {thesisMotivated = mot && not nmt, currentThesis = setForm ths fth, remainingText = [] } -- notice that this is only really executed if mot && not nmt == True

      -- put everything together
      return $ TB nbl : nbs

-- if there is no text to be read in a branch it means we must call the prover
vLoop st@VS {thesisMotivated = True, rewriteRules = rls, currentThesis = ths, currentContext = cnt, remainingText = [] }
  = local (const st) $  whenInstruction IBprov True prove >> return []
  where
    prove = if hasDEC (cnForm ths) then -- this signifies computational reasoning -> passed to the simplifier (after some bookkeeping operations)
            do  let rl = reasonerLog bl $ "goal: " ++ tx
                    bl = cnHead ths ; tx = blText bl
                incrementIntCounter Equations ; whenInstruction IBPgls True rl
                timer SimplifyTime (eqReason ths) <|> (reasonerLog bl "equation failed" >>
                    guardInstruction IBskip False >> incrementIntCounter FailedEquations)
            else -- this signifies conventional reasoning -> passed to the prover
            do  let rl = reasonerLog bl $ "goal: " ++ tx
                    bl = cnHead ths ; tx = blText bl
                when (not . isTop . cnForm $ ths) $ incrementIntCounter Goals
                whenInstruction IBPgls True rl
                proveThesis <|> (reasonerLog bl "goal failed" >> guardInstruction IBskip False >> incrementIntCounter FailedGoals)

{- process instructions in the text. We distinguis those that do not concern the
   proof process (simply print something to the screen or change an instruction value)
   and those that do (at the moment only : changing the context with [setCtxt ..]) -}
vLoop st@VS {remainingText = TI ins : bs}
  | relevant ins = chngTI st {remainingText = bs} ins
  | otherwise = procTI st ins >> vLoop st {remainingText = bs}

{- process a command to drop an instruction, i.e. [/prove], [/ontored], etc.-}
vLoop st@VS {remainingText = (TD ind : bs)} =
      procTD st ind >> vLoop st {remainingText = bs}

vLoop _ = return []

{- Take care of induction hypothesis and case hypothesis befor calling the usual vLoop.
   If no induction or case hypothesis is present in the current block this is equal
   to simply "vLoop st". -}
splitTh st@VS {rewriteRules = rls, currentThesis = ths, currentContext = cnt, branch = brn}
      = dive id cnt $ cnForm ths
  where
    dive c cn (Imp (Tag DIH f) g)  | closed f
                                   = fine (setForm ths f : cn) (c g)
    dive c cn (Imp (Tag DCH f) g)  | closed f
                                   = fine (ths {cnForm = f, cnRedu = f} : cn) (c g)
    dive c cn (Imp f g)            = dive (c . Imp f) cn g
    dive c cn (All v f)            = dive (c . All v) cn f
    dive c cn (Tag tg f)           = dive (c . Tag tg) cn f
    dive _ _ _                     = vLoop st

    fine nct f  = do dfs <- askGlobalState definitions
                     let nrls     = extractRule (head nct) ++ rls
                         (_,_,nth) = new_thesis dfs nct $ setForm ths f
                     ib <- askInstructionBin IBPths False
                     when (ib && noICH (cnForm nth) && not (null $ remainingText st)) $ thesisLog (length brn - 2) (head $ cnBran $ head cnt) $ "new thesis " ++ show (cnForm nth)
                     splitTh st {rewriteRules = nrls, currentThesis = nth, currentContext = nct}


noICH (Tag DIH _) = False
noICH (Tag DCH _) = False
noICH f = allF noICH f


{- reconstruct statement from induction and case hypothesis -}
deICH = dive id
  where
    dive c (Imp (Tag DIH _) f)  = c f
    dive c (Imp (Tag DCH f) _)  = c $ Not f
    dive c (Imp f g)            = dive (c . Imp f) g
    dive c (All v f)            = dive (c . All v) f
    dive c f                    = c f




-- Instruction handling

procTI VS {thesisMotivated = mot, rewriteRules = rls, currentThesis = ths, currentContext = cnt} = proc
  where
    proc (InCom ICRuls)
      = do  reasonerLog0 $ "current ruleset: " ++ "\n" ++ printrules (reverse rls)
    proc (InCom ICPths)
      = do  let smt = if mot then "(mot): " else "(nmt): "
            reasonerLog0 $ "current thesis " ++ smt ++ show (cnForm ths)

    proc (InCom ICPcnt)
      = do  let srl = reverse $ cnt
            reasonerLog0 $ "current context:"
            mapM_ ((putStrRM "  " >>) . printRM) srl

    proc (InCom ICPflt)
      = do  let srl = reverse $ filter cnTopL cnt
            reasonerLog0 $ "current filtered top-level context:"
            mapM_ ((putStrRM "  " >>) . printRM) srl

    proc (InCom _)  = reasonerLog0 $ "unsupported instruction"

    proc (InBin IBverb False)
      = do  addInstruction $ InBin IBPgls False
            addInstruction $ InBin IBPrsn False
            addInstruction $ InBin IBPsct False
            addInstruction $ InBin IBPchk False
            addInstruction $ InBin IBPprv False
            addInstruction $ InBin IBPunf False
            addInstruction $ InBin IBPtsk False

    proc (InBin IBverb True)
      = do (guardNotInstruction IBPgls True  >> addInstruction (InBin IBPgls True))
        <|> (guardNotInstruction IBPrsn False >> addInstruction (InBin IBPrsn True))
        <|> (guardNotInstruction IBPsct False >> addInstruction (InBin IBPsct True))
        <|> (guardNotInstruction IBPchk False >> addInstruction (InBin IBPchk True))
        <|> (guardNotInstruction IBPprv False >> addInstruction (InBin IBPprv True))
        <|> (guardNotInstruction IBPunf False >> addInstruction (InBin IBPunf True))
        <|> (guardNotInstruction IBPtsk False >> addInstruction (InBin IBPtsk True))
        <|> return ()

    proc (InPar IPgrup ps) = addGroup ps

    proc i  = addInstruction i

procTD _ = proc
  where
    proc i  = dropInstruction i

-- Context settings

chngTI st@VS {thesisMotivated = mot, rewriteRules = rls, currentThesis = ths, currentContext = cnt} = proc
  where
    proc (InPar IPscnt ps) = setCtxt ps >>= \nct -> vLoop st {currentContext = takeWhile cnLowL cnt  ++ nct}
    proc (InPar IPdcnt ps) = getLink ps >>= \nms -> vLoop st {currentContext = filter (not. flip elem nms . cnName) cnt }
    proc (InPar IPacnt ps) = setCtxt ps >>= \nct -> vLoop st {currentContext = unionBy ((==) `on` cnName) nct cnt}

setCtxt [] = askGlobalState globalContext
setCtxt ps = do nms <- getLink ps; retrieveContext nms
