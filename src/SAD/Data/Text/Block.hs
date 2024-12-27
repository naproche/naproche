-- |
-- Module      : SAD.Data.Text.Block
-- Copyright   : (c) 2001 - 2008, Andrei Paskevich,
--               (c) 2017 - 2018, Steffen Frerix
-- License     : GPL-3
--
-- TODO: Add description.


{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}

module SAD.Data.Text.Block (
  ProofText(..),
  Block(..),
  makeBlock,
  position,
  declaredNames,
  text,
  Section(..),
  showForm,
  formulate,
  compose,
  needsProof,
  isTopLevel,
  file,
  parseErrors,
  canDeclare
) where

import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text.Lazy (Text)
import Data.Text.Lazy qualified as Text
import Data.Maybe (fromMaybe)

import SAD.Data.Formula hiding (CaseHypothesis)
import SAD.Data.Instr
import SAD.Parser.Token
import SAD.Data.Text.Decl
import SAD.Parser.Error (ParseError)
import SAD.Export.TPTP qualified as TPTP

import Isabelle.Bytes qualified as Bytes
import Isabelle.Position qualified as Position
import Isabelle.Library (make_text)


data ProofText =
    ProofTextBlock Block
  | ProofTextInstr Position.T Instr
  | ProofTextDrop Position.T Drop
  | ProofTextSynonym Position.T
  | ProofTextPretyping Position.T (Set PosVar)
  | ProofTextMacro Position.T
  | ProofTextError ParseError
  deriving (Eq, Ord)

data Block = Block {
  formula           :: Formula,
  body              :: [ProofText],
  kind              :: Section,
  declaredVariables :: Set Decl,
  name              :: Text,
  link              :: [Text],
  tokens            :: [Token] }
  deriving (Eq, Ord)

makeBlock :: Formula -> [ProofText] -> Section -> Text -> [Text] -> [Token] -> Block
makeBlock form body kind = Block form body kind mempty

position :: Block -> Position.T
position = Position.range_position . tokensRange . tokens

isTopLevel :: Block -> Bool
isTopLevel = isHole . formula

text :: Block -> Text
text Block {tokens} = composeTokens tokens

{- All possible types that a ForTheL block can have. -}
data Section =
  Definition | Signature | Axiom | Theorem | CaseHypothesis |
  Assumption | Choice | Affirmation | Posit | LowDefinition |
  ProofByContradiction
  deriving (Eq, Ord, Show)

renderSection :: Section -> String
renderSection Definition = "Definition"
renderSection Signature = "Signature"
renderSection Axiom = "Axiom"
renderSection Theorem = "Theorem"
renderSection CaseHypothesis = "Case hypothesis"
renderSection Assumption = "Assumption"
renderSection Choice = "Choice"
renderSection Affirmation = "Affirmation"
renderSection Posit = "Posit"
renderSection LowDefinition = "Low-level definition"
renderSection ProofByContradiction = "Proof by contradiction"


-- Composition

{- form the formula image of a whole block -}
formulate :: Block -> Formula
formulate block =
  if isTopLevel block then compose $ body block else formula block

compose :: [ProofText] -> Formula
compose = foldr comp Top
  where
    comp (ProofTextBlock block@Block{ declaredVariables = dvs }) f
      -- In this case, we give the formula 'exists x_1,...,x_n . (formulate block) ^ f'.
      | needsProof block || kind block == Posit =
          Set.foldr mkExi (blAnd (formulate block) f) $ Set.map declName dvs
      -- Otherwise, we give the formula 'forall x_1,...,x_n . (formulate block) => f'.
      | otherwise = Set.foldr mkAll (blImp (formulate block) f) $ Set.map declName dvs
    comp _ fb = fb



{- necessity of proof as derived from the block type -}
needsProof :: Block -> Bool
needsProof block = sign $ kind block
  where
    sign Definition = False
    sign Signature  = False
    sign Axiom      = False
    sign Assumption = False
    sign Posit      = False
    sign _          = True


{- which statements can declare variables -}
canDeclare :: Section -> Bool
canDeclare Assumption = True
canDeclare Choice = True
canDeclare LowDefinition = True
canDeclare _ = False


file :: Block -> Text
file = Text.fromStrict . make_text . fromMaybe Bytes.empty . Position.file_of . position

declaredNames :: Block -> Set VariableName
declaredNames = Set.map declName . declaredVariables

-- Show instances

instance Show ProofText where
  showsPrec p (ProofTextBlock block) = showsPrec p block
  showsPrec 0 (ProofTextInstr _ instr) = shows instr . showChar '\n'
  showsPrec 0 (ProofTextDrop _ instr) = shows instr . showChar '\n'
  showsPrec _ (ProofTextError err) = shows err . showChar '\n'
  showsPrec _ _ = id

instance Show Block where
  showsPrec p block@Block {body = b, name = name, kind = kind}
    | null b = showForm p block
    | isTopLevel block = showString (renderSection kind ++ addName ++ ":\n") . showBlockForm (p + 1) block .
        (if needsProof block
          then if null b
            then showIndent p . showString "Trivial:\n"
            else let proof = last b in
              case proof of
                ProofTextBlock proofBlock -> showIndent p . showString "Proof:\n" . showProof (body proofBlock) . showIndent p . showString "Qed.\n"
                _ -> id
          else id)
    -- | otherwise = showForm p block .
    --     showIndent p . showString "Proof:\n" . showProof .
    --     showIndent p . showString "Qed.\n"
    | otherwise = error "foo!!!"
    where
      showProof proofTexts = foldr ((.) . showsPrec (p + 1)) id proofTexts
      name' = Text.unpack name
      addName = if null name' then "" else " (" ++ name' ++ ")"

showForm :: Int -> Block -> String -> String
showForm p block@Block {formula = formula, name = name, kind = kind} =
  showIndent p . sform (needsProof block) . showString "\n"
  where
    sform False = showString . Text.unpack $ TPTP.renderLogicFormula name TPTP.Hypothesis formula
    sform True  = showString . Text.unpack $ TPTP.renderLogicFormula name TPTP.Conjecture formula

showBlockForm :: Int -> Block -> String -> String
showBlockForm p block =
  showIndent p . sform (needsProof block) . showString "\n"
  where
    sform False = showString . Text.unpack $ TPTP.renderLogicFormula "" TPTP.Hypothesis (formulate block)
    sform True  = showString . Text.unpack $ TPTP.renderLogicFormula "" TPTP.Conjecture (formulate block)

showIndent :: Int -> ShowS
showIndent n = showString $ replicate (n * 2) ' '

parseErrors :: ProofText -> [ParseError]
parseErrors (ProofTextError err) = [err]
parseErrors (ProofTextBlock bl) = concatMap parseErrors (body bl)
parseErrors _ = []
