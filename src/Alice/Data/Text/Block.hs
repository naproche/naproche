module Alice.Data.Text.Block where

import Alice.Data.Formula
import Alice.Parser.Position
import Alice.Data.Instr (Instr, Idrop)

data Text = TB Block | TI Instr | TD Idrop



-- Block utilities



getBlock :: Text -> Block
getBlock (TB bl) = bl


-- Composition

{- form the formula image of a whole block -}
formulate :: Block -> Formula
formulate bl  | noForm bl = compose $ blBody bl
              | otherwise = blForm bl

compose :: [Text] -> Formula
compose tx = foldr comp Top tx
  where
    comp (TB bl@(Block{ blDecl = dvs })) fb
      | blSign bl || blType bl == Posit = foldr zExi (blAnd (formulate bl) fb) dvs
      | otherwise = foldr zAll (blImp (formulate bl) fb) dvs
    comp _ fb = fb



-- Show instances

instance Show Text where
  showsPrec p (TB bl) = showsPrec p bl
  showsPrec 0 (TI is) = showsPrec 0 is . showChar '\n'
  showsPrec 0 (TD is) = showsPrec 0 is . showChar '\n'
  showsPrec _ _ = id

instance Show Block where
  showsPrec p bl  | noBody bl = showForm p bl
                  | noForm bl = showForm p bl . sbody
                  | otherwise = showForm p bl
                              . showIndent p . showString "proof.\n"
                              . sbody
                              . showIndent p . showString "qed.\n"
    where
      sbody = foldr ((.) . showsPrec (succ p)) id $ blBody bl

showForm p bl = showIndent p . sform (noForm bl) (blSign bl) . dt
  where
      sform True  True  = showString $ "conjecture" ++ mr
      sform True  False = showString $ "hypothesis" ++ mr
      sform False False = showString "assume " . shows fr
      sform False True  = shows fr

      mr = if null nm then "" else (' ':nm)
      fr = blForm bl ; nm = blName bl
      dt = showString ".\n"

showIndent :: Int -> ShowS
showIndent n  = showString $ replicate (n * 2) ' '


data Block  = Block { blForm :: Formula,  blBody :: [Text],   -- Formula image / body of the block
                      blType :: Section,  blDecl :: [String], -- block type / variables declared in the block
                      blName :: String,   blLink :: [String], -- identifier of the block / proof link provided in the block ("by" statement)
                      blPos :: SourcePos, blText :: String }


{- All possible types that a ForThel block can have. -}
data Section = Defn | Sign | Axiom | Theorem | Case | Assume | Select | Affirm | Posit | Frame | Declare deriving Eq

{- necessity of proof as derived from the block type -}
blSign bl = sign $ blType bl
  where
    sign Defn    = False
    sign Sign    = False
    sign Axiom   = False
    sign Assume  = False
    sign Posit   = False
    sign Declare = True
    sign _       = True

isDecl = (==) Declare . blType


noForm :: Block -> Bool
noForm  = isHole . blForm

noBody :: Block -> Bool
noBody  = null . blBody



blFile :: Block -> String
blFile = sourceFile . blPos

blLnCl :: Block -> (Int, Int)
blLnCl bl = let pos = blPos bl in (sourceLine pos, sourceColumn pos)