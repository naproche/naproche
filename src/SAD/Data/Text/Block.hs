{-# LANGUAGE NamedFieldPuns #-}

module SAD.Data.Text.Block (
  Text(..),
  Block(..),
  makeBlock,
  declaredNames,
  text,
  Section(..),
  showForm,
  formulate,
  compose,
  needsProof,
  isTopLevel,
  file
  )where

import SAD.Data.Formula
import SAD.Core.Position
import SAD.Data.Instr (Instr)
import qualified SAD.Data.Instr as Instr
import SAD.Parser.Token
import SAD.Data.Text.Declaration (Declaration)
import qualified SAD.Data.Text.Declaration as Declaration


data Text = TextBlock Block | TextInstr Instr | TextDrop Instr.Drop

data Block  = Block {
  formula           :: Formula,
  body              :: [Text],
  kind              :: Section,
  declaredVariables :: [Declaration],
  name              :: String,
  link              :: [String],
  position          :: SourcePos,
  tokens            :: [Token] }

makeBlock :: Formula -> [Text] -> Section -> String -> [String] -> SourcePos -> [Token] -> Block
makeBlock form body kind name link pos toks =
  Block form body kind [] name link (rangePos (tokensRange toks)) toks

text :: Block -> String
text Block {tokens} = composeTokens tokens

{- All possible types that a ForThel block can have. -}
data Section =
  Definition | Signature | Axiom       | Theorem | CaseHypothesis  |
  Assumption | Selection | Affirmation | Posit   | LowDefinition
  deriving Eq

-- Composition

{- form the formula image of a whole block -}
formulate :: Block -> Formula
formulate block
  | isTopLevel block = compose $ body block
  | otherwise = formula block

compose :: [Text] -> Formula
compose = foldr comp Top
  where
    comp (TextBlock block@Block{ declaredVariables = dvs }) f
      | needsProof block || kind block == Posit =
          foldr zExi (blAnd (formulate block) f) $ map Declaration.name dvs
      | otherwise = foldr zAll (blImp (formulate block) f) $ map Declaration.name dvs
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


isTopLevel :: Block -> Bool
isTopLevel  = isHole . formula

noBody :: Block -> Bool
noBody  = null . body

file :: Block -> String
file = sourceFile . position


declaredNames :: Block -> [String]
declaredNames = map Declaration.name . declaredVariables

-- Show instances

instance Show Text where
  showsPrec p (TextBlock block) = showsPrec p block
  showsPrec 0 (TextInstr instr) = shows instr . showChar '\n'
  showsPrec 0 (TextDrop instr) = shows instr . showChar '\n'
  showsPrec _ _ = id

instance Show Block where
  showsPrec p block@Block {body = body}
    | noBody block = showForm p block
    | isTopLevel block = showForm p block . showBody
    | otherwise = showForm p block .
        showIndent p . showString "proof.\n" . showBody .
        showIndent p . showString "qed.\n"
    where
      showBody = foldr ((.) . showsPrec (succ p)) id body

showForm p block@Block {formula = formula, name = name} =
  showIndent p . sform (isTopLevel block) (needsProof block) . dot
  where
    sform True  True  = showString $ "conjecture" ++ addName
    sform True  False = showString $ "hypothesis" ++ addName
    sform False False = showString "assume " . shows formula
    sform False True  = shows formula

    addName = if null name then "" else (' ':name)
    dot = showString ".\n"

showIndent :: Int -> ShowS
showIndent n = showString $ replicate (n * 2) ' '