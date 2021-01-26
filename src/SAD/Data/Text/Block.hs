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
  textToCheck,
  findParseError,
  isChecked,
  children, setChildren,
  canDeclare
  )where

import SAD.Data.Formula
import SAD.Core.SourcePos
import SAD.Data.Instr hiding (position)
import SAD.Parser.Token
import SAD.Data.Text.Decl
import SAD.Parser.Error (ParseError)

import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text.Lazy (Text)
import qualified Data.Text.Lazy as Text

import Control.Monad


data ProofText =
    ProofTextBlock Block
  | ProofTextInstr Pos Instr
  | NonProofTextStoredInstr [Instr] -- a way to restore instructions during verification
  | ProofTextDrop Pos Drop
  | ProofTextSynonym SourcePos
  | ProofTextPretyping SourcePos (Set PosVar)
  | ProofTextMacro SourcePos
  | ProofTextError ParseError
  | ProofTextChecked (ProofText)
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
  ProofByContradiction
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
    comp (ProofTextChecked txt) f = comp txt f
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
canDeclare Assumption = True; canDeclare Selection = True
canDeclare LowDefinition = True; canDeclare _ = False


isTopLevel :: Block -> Bool
isTopLevel  = isHole' . formula
  where
    isHole' Var {varName = VarHole _} = True
    isHole' _ = False

file :: Block-> Text
file = sourceFile . position


declaredNames :: Block -> Set VariableName
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
    sform False False = showString "assume " . shows formula
    sform False True  = shows formula

    name' = Text.unpack name
    addName = if null name' then "" else ' ':name'
    dot = showString ".\n"

showIndent :: Int -> ShowS
showIndent n = showString $ replicate (n * 2) ' '

--- comparison of text trees, computation of parts that need checking

textToCheck :: ProofText -> ProofText -> ProofText
textToCheck old new
  | isRoot old && isRoot new = dive [] (isChecked old) new (children old) (children new)
  | otherwise = new
  where
    dive acc checked root [] [] = setChecked checked $ setChildren root (reverse acc)
    dive acc _ root old [] = setChildren root (reverse acc)
    dive acc _ root [] new = setChildren root (reverse acc ++ new)
    dive acc checked root (o:old) (n:new) =
      if   textCompare o n
      then let newAcc = dive [] (isChecked o) n (children o) (children n) : acc
           in  dive newAcc checked root old new
      else setChildren root (reverse acc ++ (n:new))

isRoot :: ProofText -> Bool
isRoot (ProofTextRoot _) = True; isRoot _ = False

isChecked :: ProofText -> Bool
isChecked (ProofTextChecked _) = True; isChecked _ = False

children :: ProofText -> [ProofText]
children (ProofTextRoot texts) = texts
children (ProofTextChecked text) = children text
children (ProofTextBlock bl) = body bl
children _ = []

setChecked :: Bool -> ProofText -> ProofText
setChecked p = if p then ProofTextChecked else id

setChildren :: ProofText -> [ProofText] -> ProofText
setChildren (ProofTextRoot _) children = ProofTextRoot children
setChildren (ProofTextBlock bl) children = ProofTextBlock bl {body = children}
setChildren txt _ = txt

textCompare :: ProofText -> ProofText -> Bool
textCompare (ProofTextInstr _ i1) (ProofTextInstr _ i2) = i1 == i2
textCompare (ProofTextDrop _ d1) (ProofTextDrop _ d2) = d1 == d2
textCompare (ProofTextSynonym _) (ProofTextSynonym _) = True
textCompare (ProofTextPretyping _ _) (ProofTextPretyping _ _) = True
textCompare (ProofTextMacro _) (ProofTextMacro _) = True
textCompare (ProofTextError _) (ProofTextError _) = True
textCompare (ProofTextChecked txt) text = textCompare txt text
textCompare text (ProofTextChecked txt) = textCompare text txt
textCompare (ProofTextRoot _) (ProofTextRoot _) = True
textCompare (ProofTextBlock bl1) (ProofTextBlock bl2) =
  syntacticEquality (formulate bl1) (formulate bl2)
textCompare _ _ = False

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
