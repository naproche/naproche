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
  file,
  textToCheck,
  findParseError,
  isChecked,
  children, setChildren,
  canDeclare
  )where

import SAD.Data.Formula
import SAD.Core.SourcePos
import SAD.Data.Instr (Instr)
import qualified SAD.Data.Instr as Instr
import SAD.Parser.Token
import SAD.Data.Text.Decl (Decl)
import qualified SAD.Data.Text.Decl as Decl
import SAD.ForTheL.Base (VarName)
import SAD.Parser.Error (ParseError)

import Control.Monad


data Text =
    TextBlock Block
  | TextInstr Instr.Pos Instr
  | NonTextStoredInstr [Instr] -- a way to restore instructions during verification
  | TextDrop Instr.Pos Instr.Drop
  | TextSynonym SourcePos
  | TextPretyping SourcePos [VarName]
  | TextMacro SourcePos
  | TextError ParseError
  | TextChecked Text
  | TextRoot [Text]

data Block  = Block {
  formula           :: Formula,
  body              :: [Text],
  kind              :: Section,
  declaredVariables :: [Decl],
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
          foldr zExi (blAnd (formulate block) f) $ map Decl.name dvs
      | otherwise = foldr zAll (blImp (formulate block) f) $ map Decl.name dvs
    comp (TextChecked txt) f = comp txt f
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
isTopLevel  = isHole . formula

noBody :: Block -> Bool
noBody  = null . body

file :: Block -> String
file = sourceFile . position


declaredNames :: Block -> [String]
declaredNames = map Decl.name . declaredVariables

-- Show instances

instance Show Text where
  showsPrec p (TextBlock block) = showsPrec p block
  showsPrec 0 (TextInstr _ instr) = shows instr . showChar '\n'
  showsPrec 0 (TextDrop _ instr) = shows instr . showChar '\n'
  showsPrec _ (TextError err) = shows err . showChar '\n'
  showsPrec 0 (TextRoot txt ) = shows txt
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

    addName = if null name then "" else ' ':name
    dot = showString ".\n"

showIndent :: Int -> ShowS
showIndent n = showString $ replicate (n * 2) ' '

--- comparison of text trees, computation of parts that need checking

textToCheck :: Text -> Text -> Text
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

isRoot (TextRoot _) = True; isRoot _ = False

isChecked :: Text -> Bool
isChecked (TextChecked _) = True; isChecked _ = False

children :: Text -> [Text]
children (TextRoot texts) = texts
children (TextChecked text) = children text
children (TextBlock bl) = body bl
children _ = []

setChecked :: Bool -> Text -> Text
setChecked p = if p then TextChecked else id

setChildren :: Text -> [Text] -> Text
setChildren (TextRoot _) children = TextRoot children
setChildren (TextBlock bl) children = TextBlock bl {body = children}
setChildren txt _ = txt

textCompare :: Text -> Text -> Bool
textCompare (TextInstr _ i1) (TextInstr _ i2) = i1 == i2
textCompare (TextDrop _ d1) (TextDrop _ d2) = d1 == d2
textCompare (TextSynonym _) (TextSynonym _) = True
textCompare (TextPretyping _ _) (TextPretyping _ _) = True
textCompare (TextMacro _) (TextMacro _) = True
textCompare (TextError _) (TextError _) = True
textCompare (TextChecked txt) text = textCompare txt text
textCompare (TextRoot _) (TextRoot _) = True
textCompare (TextBlock bl1) (TextBlock bl2) =
  syntacticEquality (formulate bl1) (formulate bl2)
textCompare _ _ = False

-- parse correctness of a structure tree


findParseError :: MonadPlus m => Text -> m ParseError
findParseError txt = dive $ children txt
  where
    dive [] = mzero
    dive (TextBlock bl : rest) =
      dive (body bl) `mplus` dive rest
    dive (TextError err : _) = return err
    dive (_ : rest) = dive rest