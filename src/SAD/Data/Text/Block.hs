-- |
-- Module      : SAD.Data.Text.Block
-- Copyright   : (c) 2001 - 2008, Andrei Paskevich,
--               (c) 2017 - 2018, Steffen Frerix
-- License     : GPL-3
--
-- TODO: Add description.


{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE GADTs #-}

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

import SAD.Data.Formula
import SAD.Data.Instr
import SAD.Parser.Token
import SAD.Data.Text.Decl
import SAD.Parser.Error (ParseError)

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
  showsPrec p block@Block {body = body}
    | null body = showForm p block
    | isTopLevel block = showForm p block . showBody
    | otherwise = showForm p block .
        showIndent p . showString "proof.\n" . showBody .
        showIndent p . showString "qed.\n"
    where
      showBody = foldr ((.) . showsPrec (p + 1)) id body

showForm :: Int -> Block -> String -> String
showForm p block@Block {formula = formula, name = name} =
  showIndent p . sform (isTopLevel block) (needsProof block) . dot
  where
    sform True  True  = showString $ "conjecture" ++ addName
    sform True  False = showString $ "hypothesis" ++ addName
    sform False False = showString "assume " . shows formula
    sform False True  = shows formula

    name' = Text.unpack name
    addName = if null name' then "" else ' ':name'
    dot = showString ".\n"

showIndent :: Int -> ShowS
showIndent n = showString $ replicate (n * 2) ' '

parseErrors :: ProofText -> [ParseError]
parseErrors (ProofTextError err) = [err]
parseErrors (ProofTextBlock bl) = concatMap parseErrors (body bl)
parseErrors _ = []
