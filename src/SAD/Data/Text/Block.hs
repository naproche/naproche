{-# LANGUAGE GADTs #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}

-- |
-- Module      : SAD.Data.Text.Block
-- Description : TODO
-- Copyright   : (c) 2001 - 2008, Andrei Paskevich
--               (c) 2017 - 2018, Steffen Frerix
-- License     : GPL-3
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
  parseErrors,
  canDeclare
) where

import Data.Set (Set)
import Data.Set qualified as Set

import Isabelle.Bytes (Bytes)
import Isabelle.Bytes qualified as Bytes
import Isabelle.Library (make_bytes, show_bytes)
import Isabelle.Position qualified as Position

import SAD.Data.Formula hiding (CaseHypothesis)
import SAD.Data.Instr
import SAD.Data.Text.Decl
import SAD.Export.Presentation
import SAD.Parser.Error (ParseError)
import SAD.Parser.Token


data ProofText =
    ProofTextBlock Block
  | ProofTextInstr Position.T Instr
  | ProofTextDrop Position.T Drop
  | ProofTextSynonym Position.T
  | ProofTextPretyping Position.T (Set PosVar)
  | ProofTextMacro Position.T
  | ProofTextError ParseError

instance Presentation ProofText where
  present (ProofTextBlock block) = present block
  present (ProofTextInstr _ instr) = show_bytes instr
  present (ProofTextDrop _ instr) = show_bytes instr
  present (ProofTextError err) = present err
  present _ = ""

data Block = Block {
  formula :: Formula,
  body :: [ProofText],
  kind :: Section,
  declaredVariables :: Set Decl,
  name :: Bytes,
  link :: [Bytes],
  tokens :: [Token] }

makeBlock :: Formula -> [ProofText] -> Section -> Bytes -> [Bytes] -> [Token] -> Block
makeBlock form body kind = Block form body kind mempty

position :: Block -> Position.T
position = Position.range_position . tokensRange . tokens

isTopLevel :: Block -> Bool
isTopLevel = isHole . formula

text :: Block -> Bytes
text Block {tokens} = composeTokens tokens

{- All possible types that a ForTheL block can have. -}
data Section =
  Definition | Signature | Axiom | Theorem | CaseHypothesis |
  Assumption | Choice | Affirmation | Posit | LowDefinition |
  ProofByContradiction
  deriving (Eq)

instance Presentation Section where
  present Definition = "Definition"
  present Signature = "Signature"
  present Axiom = "Axiom"
  present Theorem = "Theorem"
  present CaseHypothesis = "Case hypothesis"
  present Assumption = "Assumption"
  present Choice = "Choice"
  present Affirmation = "Affirmation"
  present Posit = "Posit"
  present LowDefinition = "Low-level definition"
  present ProofByContradiction = "Proof by contradiction"

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
    sign Signature = False
    sign Axiom = False
    sign Assumption = False
    sign Posit = False
    sign _ = True


{- which statements can declare variables -}
canDeclare :: Section -> Bool
canDeclare Assumption = True
canDeclare Choice = True
canDeclare LowDefinition = True
canDeclare _ = False

declaredNames :: Block -> Set VariableName
declaredNames = Set.map declName . declaredVariables

-- Show instances

instance Presentation Block where
  present = showBlock 0

showBlock :: Int -> Block -> Bytes
showBlock p block@Block{body = b, name = name, kind = kind}
  | null b = showForm p block
  | isTopLevel block = present kind <> addName <> ":\n" <> showBlockForm (p + 1) block <>
      (if needsProof block
        then if null b
          then indent p "Trivial:\n"
          else let proof = last b in
            case proof of
              ProofTextBlock proofBlock -> indent p "Proof:\n" <> showProof (p + 1) (body proofBlock) <> indent p "Qed.\n"
              _ -> ""
        else "")
  | otherwise = showForm p block <>
      indent p "Proof:\n" <> showProof (p + 1) (body block) <> indent p "Qed.\n"
  where
    name' = make_bytes name
    addName = if Bytes.null name' then "" else " (" <> name' <> ")"

showForm :: Int -> Block -> Bytes
showForm p block@Block{formula = formula, name = name} =
  indent p $ present formula <> "\n"

showBlockForm :: Int -> Block -> Bytes
showBlockForm p block =
  indent p $ present (formulate block) <> "\n"

showProof :: Int -> [ProofText] -> Bytes
showProof p = foldr (\pt bs -> indent p (present pt) <> bs) ""

indent :: Int -> Bytes -> Bytes
indent n bs = Bytes.pack (replicate (2 * n) 0x20) <> bs

parseErrors :: ProofText -> [ParseError]
parseErrors (ProofTextError err) = [err]
parseErrors (ProofTextBlock bl) = concatMap parseErrors (body bl)
parseErrors _ = []
