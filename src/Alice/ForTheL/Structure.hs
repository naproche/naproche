{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018)

Syntax of ForTheL sections.
-}


module Alice.ForTheL.Structure (forthel, textReports) where


import qualified Data.Char as Char
import Data.Set (Set)
import qualified Data.Set as Set

import qualified Isabelle.Markup as Markup
import qualified Alice.Core.Message as Message

import Alice.ForTheL.Base
import Alice.ForTheL.Statement
import Alice.ForTheL.Extension
import Alice.ForTheL.Instruction

import Alice.Parser.Base
import Alice.Parser.Combinators
import Alice.Parser.Token
import Alice.Parser.Primitives

import Alice.Data.Text.Block (Block(Block), Text(..), Section(..))
import qualified Alice.Data.Text.Block as Block
import Alice.Data.Formula
import qualified Alice.Data.Tag as Tag



import Data.List
import Data.Maybe
import Data.Char (isAlphaNum)
import Control.Monad

import Debug.Trace

forthel :: FTL [Text]
forthel = section <|> macroOrPretype <|> bracketExpression
  where
    section = liftM2 ((:) . TB) topsection forthel
    macroOrPretype = (introduceMacro </> pretypeVariable) >> forthel

{- this part may seem a bit finicky, but must be coded this way to avoid
   memory leaks. The problem is that we cannnot distinguish in an LL1 fashion
   between instructions and synonym introductions.-}

bracketExpression = exit </> readfile </> do
  mbInstr <- liftM Left instruction </> liftM Right introduceSynonym
  either (\instr -> liftM ((:) instr) forthel) (\_ -> forthel) mbInstr
  where
    exit = (iExit <|> eof) >> return []
    readfile = liftM2 ((:) . TI) iRead (return [])
    instruction = liftM TD iDrop </> liftM TI instr

topsection = signature <|> definition <|> axiom <|> theorem

--- generic topsection parsing

genericTopsection kind header endparser = do
  pos <- getPos; inp <- getInput; nm <- header;
  toks <- getTokens inp; bs <- body
  return $ Block.makeBlock zHole bs kind nm [] pos toks
  where
    body = assumption <|> endparser
    assumption = topAssume `pretypeBefore` body
    topAssume = pretypeSentence Assumption (asmH >> statement) assumeVars noLink

--- generic header parser

header titles = dot $ wd_tokenOf titles >> optLL1 "" topIdentifier


-- topsections

signature =
  let sigext = pretype $ pretypeSentence Posit sigExtend defVars noLink
  in  genericTopsection Signature sigH sigext
definition =
  let define = pretype $ pretypeSentence Posit defExtend defVars noLink
  in  genericTopsection Definition defH define
axiom =
  let posit = pretype $ 
        pretypeSentence Posit (affH >> statement) affirmVars noLink
  in  genericTopsection Axiom axmH posit
theorem = 
  let topAffirm = pretypeSentence Affirmation (affH >> statement) affirmVars link
  in  genericTopsection Theorem thmH (topProof topAffirm)
    

sigH = header ["signature"]
defH = header ["definition"]
axmH = header ["axiom"]
thmH = header ["theorem", "lemma", "corollary", "proposition"]

headers :: Set String
headers =
  Set.fromList ["signature", "definition", "axiom", "theorem", "lemma", "corollary", "proposition"]

-- low-level
choose   = sentence Selection (chsH >> selection) assumeVars link
caseHypo = sentence Block.CaseHypothesis   (casH >> statement) affirmVars link
affirm   = sentence Affirmation (affH >> statement) affirmVars link </> eqChain
assume   = sentence Assumption (asmH >> statement) assumeVars noLink
llDefn   = sentence LowDefinition(ldfH >> setNotion </> functionNotion)     llDefnVars noLink

-- Links and Identifiers
link = dot eqLink
  where
    identifiers = topIdentifier `sepByLL1` comma

topIdentifier = tokenPrim notSymb
  where
    notSymb t = case showToken t of
      [c] -> guard (isAlphaNum c) >> return [c]
      tk  -> return tk

lowIdentifier = expar topIdentifier

noLink = dot $ return []

eqLink = optLL1 [] $ expar $ wd_token "by" >> identifiers
  where
    identifiers = topIdentifier `sepByLL1` comma

-- declaration management, typings and pretypings

updateDeclbefore :: FTL Block -> FTL [Text] -> FTL [Text]
updateDeclbefore blp p = do bl <- blp; addDecl (Block.declaredVariables bl) $ liftM (TB bl : ) p


pretyping :: Block -> FTL Block
pretyping = (<*>) (liftM2 pret getDecl getPretyped) . return

pret dvs tvs bl =
  assumeBlock {Block.formula = typing, Block.declaredVariables = untyped}
  where
    blockVars   = Block.declaredVariables bl
    untyped     = free (blockVars ++ dvs) (Block.formula bl)
    typing      = if   null untyped
                  then Top
                  else foldl1 And $ map (`typeWith` tvs) untyped
    assumeBlock = bl {Block.body = [], Block.kind = Assumption, Block.link = []}
    typeWith v  = substHole (zVar v) . snd . fromJust . find (elem v . fst)

pretypeBefore :: FTL Block -> FTL [Text] -> FTL [Text]
pretypeBefore blp p = do
  bl <- blp; typeBlock <- pretyping bl; let pretyped = Block.declaredVariables typeBlock
  pResult   <- addDecl (pretyped ++ Block.declaredVariables bl) $ liftM (TB bl : ) p
  return $ if null pretyped then pResult else TB typeBlock : pResult

pretype :: FTL Block -> FTL [Text]
pretype p = p `pretypeBefore` return []


-- low-level header
hence = optLL1 () $ wd_tokenOf ["then", "hence", "thus", "therefore"]
letUs = optLL1 () $ (wd_token "let" >> wd_token "us") <|> (wd_token "we" >> wd_token "can")

chsH = hence >> letUs >> wd_tokenOf ["choose", "take", "consider"]
casH = wd_token "case"
affH = hence
asmH =  lus </> wd_token "let"
  where
    lus = letUs >> wd_tokenOf ["assume", "presume", "suppose"] >> optLL1 () that
ldfH = wd_token "define"


-- generic sentence parser

statementBlock kind p mbLink = do
  nm <- opt "__" lowIdentifier;
  pos <- getPos; inp <- getInput;
  fr <- p; link <- mbLink;
  toks <- getTokens inp;
  return $ Block.makeBlock fr [] kind nm link pos toks


pretypeSentence kind p wfVars mbLink = narrow $ do
  dvs <- getDecl; tvr <- liftM (concatMap fst) getPretyped
  bl <- wellFormedCheck (wf dvs tvr) $ statementBlock kind p mbLink
  return bl {Block.declaredVariables = decl (dvs ++ tvr) $ Block.formula bl }
  where
    wf dvs tvr bl =
      let fr = Block.formula bl; nvs = intersect tvr $ free dvs fr
      in  wfVars (nvs ++ dvs) fr

sentence kind p wfVars mbLink = do
  dvs <- getDecl;
  bl  <- wellFormedCheck (wfVars dvs . Block.formula) $ statementBlock kind p mbLink
  return bl {Block.declaredVariables = decl dvs $ Block.formula bl}

-- variable well-formedness checks

defVars, assumeVars, affirmVars :: [String] -> Formula -> Maybe String

defVars dvs f | null unusedVars = affirmVars dvs f
              | otherwise       = return errorMsg
  where
    unusedVars = let fvs = free [] f in filter (`notElem` fvs) dvs
    errorMsg   = "extra variables in the guard: " ++ varString
    varString  = concatMap ((' ' :) . showVar) unusedVars

llDefnVars dvs f
  | x `elem` dvs = Just $ "Defined variable is already in use: " ++ showVar x
  | otherwise    = affirmVars (x : dvs) f
  where
    [x] = decl [] f

assumeVars dvs f = affirmVars (decl dvs f ++ dvs) f

affirmVars dvs f = overfree dvs f


-- proofs

-- proof methods

data Scheme = None | Short | Raw | InS | InT Formula deriving Show

preMethod  = optLLx None $ letUs >> dem >> after method that
  where
    dem = wd_tokenOf ["prove", "show", "demonstrate"]

postMethod = optLL1 None $ short <|> explicit
  where
    short    = wd_token "indeed" >> return Short
    explicit = dot $ wd_token "proof"  >> method

method = optLL1 Raw $ wd_token "by" >> (contradict <|> cases <|> induction)
  where
    contradict = wd_token "contradiction" >> return Raw
    cases      = wd_token "case" >> wd_token "analysis" >> return Raw
    induction  = wd_token "induction" >> optLL1 InS (wd_token "on" >> liftM InT s_term)


--- creation of induction thesis

indThesis fr pre post = do
  it <- indScheme pre post >>= indTerm fr; dvs <- getDecl
  indFormula (free dvs it) it fr
  where
    indScheme (InT _) (InT _) = failWF "conflicting induction schemes"
    indScheme m@(InT _) _ = return m;   indScheme _ m@(InT _) = return m
    indScheme InS _        = return InS; indScheme _ m          = return m

    indTerm _ (InT t)     = return t
    indTerm (All v _) InS = return $ zVar v
    indTerm _ InS         = failWF "invalid induction thesis"
    indTerm _ _           = return Top

    indFormula _ Top fr = return fr
    indFormula vs it fr = liftM (insertIndTerm it) $ indStatem vs fr

    indStatem vs (Imp g f) = liftM (Imp  g .) $ indStatem vs f
    indStatem vs (All v f) = liftM (zAll v .) $ indStatem (delete v vs) f
    indStatem [] f         = return (`Imp` f)
    indStatem _ _          = failWF $  "invalid induction thesis " ++ show fr

    insertIndTerm it cn = cn $ Tag InductionHypothesis $ substHole it $ cn $ zLess it zHole



-- proof initiation

proof p = do
  pre <- preMethod; bl <- p; post <- postMethod;
  nf <- indThesis (Block.formula bl) pre post
  addBody pre post $ bl {Block.formula = nf}



topProof p = do
  pre <- preMethod; bl <- p; post <- postMethod; typeBlock <- pretyping bl;
  let pretyped = Block.declaredVariables typeBlock
  nbl <- addDecl pretyped $ liftM TB $ do
          nf <- indThesis (Block.formula bl) pre post
          addBody pre post $ bl {Block.formula = nf}
  return $ if null pretyped then [nbl] else [TB typeBlock, nbl]

addBody None None = return -- no proof was given
addBody _ Short   = proofSentence    -- a short proof was given
addBody _ _       = proofBody    -- a full proof was given



-- proof texts

proofSentence bl = do
  pbl <- narrow assume </> proof (narrow $ affirm </> choose) </> narrow llDefn
  return bl {Block.body = [TB pbl]}

proofBody bl = do
  bs <- proofText; ls <- link
  return bl {Block.body = bs, Block.link = ls ++ Block.link bl}

proofText = assume_affirm_choose_lldefine <|> caseText <|> qed <|> llInstr
  where
    assume_affirm_choose_lldefine =
      (narrow assume </> proof (narrow $ affirm </> choose) </> narrow llDefn) `updateDeclbefore` proofText
    qed = wd_tokenOf ["qed", "end", "trivial", "obvious"] >> return []
    llInstr = liftM2 (:) (liftM TI instr </> liftM TD iDrop) proofText

caseText = caseD
  where
    caseChain = caseD <|> qed
    caseD     = liftM2 (:) caseDestinction caseChain
    qed       = wd_tokenOf ["qed", "end", "trivial", "obvious"] >> return []

    caseDestinction = do
      bl@(Block { Block.formula = fr }) <- narrow caseHypo
      liftM TB $ proofBody $ bl { Block.formula = Imp (Tag Tag.CaseHypothesis fr) zThesis}


-- equality Chain

eqChain = do
  dvs <- getDecl; nm <- opt "__" lowIdentifier; pos <- getPos; inp <- getInput
  body <- wellFormedCheck (chainVars dvs) $ s_term >>= nextTerm
  toks <- getTokens inp
  let Tag EqualityChain Trm{trArgs = [t,_]} = Block.formula $ head body
      Tag EqualityChain Trm{trArgs = [_,s]} = Block.formula $ last body
      fr = Tag EqualityChain $ zEqu t s; tBody = map TB body
  return $ Block.makeBlock fr tBody Affirmation nm [] pos toks
  where
    chainVars dvs = affirmVars dvs . foldl1 And . map Block.formula


eq_tail t = nextTerm t </> (sm_token "." >> return [])

nextTerm :: Formula -> FTL [Block]
nextTerm t = do
  pos <- getPos; inp <- getInput
  symbol ".="; s <- s_term; ln <- eqLink; toks <- getTokens inp
  liftM ((:) $ Block.makeBlock (Tag EqualityChain $ zEqu t s)
    [] Affirmation "__" ln pos toks) $ eq_tail s


-- markup reports

textReports :: Text -> [Message.Report]
textReports (TB block) =
  let
    reports =
      case Block.tokens block of
        tok : _ | Set.member (map Char.toLower $ tokenText tok) headers ->
          [(tokenPos tok, Markup.keyword1)]
        _ -> []
  in reports ++ concatMap textReports (Block.body block)
textReports (TI _) = []
textReports (TD _) = []
