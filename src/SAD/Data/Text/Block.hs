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
  needsProof,
  isTopLevel,
  findParseError,
  canDeclare,
  )where

import SAD.Data.Formula
import SAD.Core.SourcePos
import SAD.Data.Instr hiding (position)
import SAD.Parser.Token
import SAD.Parser.Error (ParseError)

import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text

import Control.Monad


data ProofText =
    ProofTextBlock Block
  | ProofTextInstr Pos Instr
  | ProofTextDrop Pos Drop
  | ProofTextSynonym SourcePos
  | ProofTextPretyping SourcePos (Set PosVar)
  | ProofTextMacro SourcePos
  | ProofTextError ParseError
  | ProofTextRoot [ProofText]
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

position :: Block -> SourcePos
position = rangePos . tokensRange . tokens

text :: Block -> Text
text Block {tokens} = composeTokens tokens

{- All possible types that a ForTheL block can have. -}
data Section =
  Definition | Signature | Axiom       | Theorem | CaseHypothesis  |
  Assumption | Selection | Affirmation | Posit   | LowDefinition   |
  ProofByContradiction | Coercion
  deriving (Eq, Ord, Show)

-- Composition

{- form the formula image of a whole block -}
formulate :: Block -> Formula
formulate block
  | isTopLevel block = compose $ body block
  | otherwise = formula block

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
    sign Coercion   = False
    sign _          = True


{- which statements can declare variables -}
canDeclare :: Section -> Bool
canDeclare Assumption = True; canDeclare Selection = True
canDeclare LowDefinition = True; canDeclare _ = False


isTopLevel :: Block -> Bool
isTopLevel  = isHole' . formula
  where
    isHole' Var {varName = VarHole _} = True
    isHole' _ = False

declaredNames :: Block -> Set VarName
declaredNames = Set.map declName . declaredVariables

-- Show instances

instance Show ProofText where
  showsPrec p (ProofTextBlock block) = showsPrec p block
  showsPrec 0 (ProofTextInstr _ instr) = shows instr . showChar '\n'
  showsPrec 0 (ProofTextDrop _ instr) = shows instr . showChar '\n'
  showsPrec _ (ProofTextError err) = shows err . showChar '\n'
  showsPrec 0 (ProofTextRoot txt ) = shows txt
  showsPrec _ _ = id

instance Show Block where
  showsPrec p block@Block {body = body}
    | null body = showForm p block
    | isTopLevel block = showForm p block . showBody
    | otherwise = showForm p block .
        showIndent p . showString "proof.\n" . showBody .
        showIndent p . showString "qed.\n"
    where
      showBody = foldr ((.) . showsPrec (succ p)) id body

showForm :: Int -> Block -> String -> String
showForm p block@Block {formula = formula, name = name} =
  showIndent p . sform (isTopLevel block) (needsProof block) . dot
  where
    sform True  True  = showString $ "conjecture" ++ addName
    sform True  False = showString $ "hypothesis" ++ addName
    sform False False = showString "assume " . showsPrecFormula 0 formula
    sform False True  = showsPrecFormula 0 formula

    name' = Text.unpack name
    addName = if null name' then "" else ' ':name'
    dot = showString ".\n"

showIndent :: Int -> ShowS
showIndent n = showString $ replicate (n * 2) ' '

children :: ProofText -> [ProofText]
children (ProofTextRoot texts) = texts
children (ProofTextBlock bl) = body bl
children _ = []

-- parse correctness of a structure tree


findParseError :: MonadPlus m => ProofText -> m ParseError
findParseError (ProofTextError err) = pure err
findParseError txt = dive $ children txt
  where
    dive [] = mzero
    dive (ProofTextBlock bl : rest) =
      dive (body bl) `mplus` dive rest
    dive (ProofTextError err : _) = return err
    dive (_ : rest) = dive rest
