{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018), Makarius Wenzel (2018)

Instruction datatype and core functions.
-}

{-# LANGUAGE OverloadedStrings #-}

module SAD.Data.Instr where

import SAD.Core.SourcePos (SourcePos, SourceRange(..), noSourcePos, noRange)
import Data.Text (Text)


-- Position information

data Pos = Pos {start :: SourcePos, stop :: SourcePos, range :: SourceRange}
  deriving (Eq, Ord, Show)

position :: Pos -> SourcePos
position p = let SourceRange a _ = range p in a

noPos :: Pos
noPos = Pos noSourcePos noSourcePos noRange


-- | Indicate which of the parsers is currently used. This is must be recorded in the State
-- for read instruction to work properly.
data ParserKind = NonTex | Tex deriving (Eq, Ord, Show)

data Instr =
    Command Command
  | GetArgument Argument Text
  | GetArguments Arguments [Text]
  deriving (Eq, Ord, Show)

data Drop =
    DropCommand Command
  | DropArgument Argument
  deriving (Eq, Ord, Show)


-- Instructions

data Command =
    EXIT     -- exit
  | QUIT     -- exit
  deriving (Eq, Ord, Show)

data Argument =
    Text ParserKind    --  literal text
  | Read ParserKind    --  read file
  deriving (Eq, Ord, Show)

data Arguments =
  Synonym
  deriving (Eq, Ord, Show)

-- Ask

askArgument :: Argument -> Text -> [Instr] -> Text
askArgument i d is  = head $ [ v | GetArgument j v <- is, i == j ] ++ [d]

-- Drop

-- | Drop an @Instr@ from the @[Instr]@ (assuming the latter doesn't contain duplicates)
dropInstr :: Drop -> [Instr] -> [Instr]
dropInstr (DropCommand m) (Command n : rs) | n == m = rs
dropInstr (DropArgument m) (GetArgument n _ : rs) | n == m = rs
dropInstr i (r : rs)  = r : dropInstr i rs
dropInstr _ _ = []


-- Keywords

keywordsCommand :: [(Command, Text)]
keywordsCommand =
 [(EXIT, "exit"),
  (QUIT, "quit")]


keywordsArgument :: [(Argument, Text)]
keywordsArgument =
 [(Read NonTex, "read"),
  (Read Tex, "readtex")]

keywordsArguments :: [(Arguments, Text)]
keywordsArguments =
  [(Synonym, "synonym")]

-- distinguish between parser and verifier instructions

isParserInstruction :: Instr -> Bool
isParserInstruction i = case i of
  Command EXIT -> True
  Command QUIT -> True
  GetArgument (Read _) _ -> True
  GetArguments Synonym _ -> True
  _ -> False
