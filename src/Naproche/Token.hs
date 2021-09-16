{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ImportQualifiedPost #-}

-- |
-- This module defines the Naproche lexer and its associated data types.
-- The lexer takes a UTF-8 encoded 'ByteString' as input and
-- produces a stream of tokens annotated with positional information.
-- This information is bundled together with the original raw input
-- for producing error messages.
--
-- The lexer perfoms some normalizations to make describing the grammar easier.
-- We use 'ByteString'/'ShortByteString' for efficiency and a smoother handover
-- to Isabelle. Non-ASCII bytes are treated as “abstract symbols”, which causes
-- some minor inconsistencies. For example, non-ASCII letters are case-sensitive
-- in words, whereas ASCII letters are normalized to lowercase to accommodate
-- the need for capitalization at the start of sentences.
--
-- Throughout we make the assumption that the input is wellformed LaTeX markup:
-- for instance, braces are assumed to be balanced.
--
module Naproche.Token where


import Control.Monad.State.Strict
import Naproche.Helpers (guardM)
import Data.Ascii.Word8 (ascii)
import Data.Void (Void)
import Data.Foldable
import Data.Function (on)
import Data.Ascii.Word8 qualified as Ascii
import Data.ByteString qualified as BS
import Data.ByteString (ByteString)
import Data.Word (Word8)
import Data.ByteString.Short (ShortByteString, toShort)
import Text.Megaparsec hiding (State)
import Text.Megaparsec.Byte qualified as Byte
import Text.Megaparsec.Byte.Lexer qualified as ByteLexer
import Data.String (IsString(..))


runLexer :: String -> ByteString -> Either (ParseErrorBundle ByteString Void) [[Located Tok]]
runLexer file raw = evalState (runParserT topLevelChunks file raw) initLexerState


type Lexer = ParsecT Void ByteString (State LexerState)

data LexerState = LexerState
    { textNesting :: Int
    -- ^ Represents nesting of braces inside of the @\text{...}@
    -- command. When we encounter @\text@ the token mode switches
    -- to text tokens. In order to switch back to math mode correctly
    -- we need to count the braces.
    , mode :: Mode
    } deriving (Show, Eq)


initLexerState :: LexerState
initLexerState = LexerState 0 TextMode


incrNesting, decrNesting :: LexerState -> LexerState
incrNesting (LexerState n m) = LexerState (succ n) m
decrNesting (LexerState n m) = LexerState (pred n) m


data Mode = TextMode | MathMode deriving (Show, Eq)


isTextMode, isMathMode :: Lexer Bool
isTextMode = do
    m <- gets mode
    pure (m == TextMode)
isMathMode = do
    m <- gets mode
    pure (m == MathMode)


setTextMode, setMathMode :: Lexer ()
setTextMode = do
    st <- get
    put st{mode = TextMode}
setMathMode = do
    st <- get
    put st{mode = MathMode}


-- |
-- A token stream as input stream for a parser. Contains the raw input
-- before lexing as 'ByteString' for showing error messages.
--
data TokenChunks = TokenChunks
    { rawInput :: ByteString
    , unTokenChunks :: [[Located Tok]]
    } deriving (Show, Eq)


data Tok
    = Word ShortByteString
    | Variable ShortByteString
    | Symbol ShortByteString
    | Integer Integer
    | Command ShortByteString
    | BeginEnv ShortByteString
    | EndEnv ShortByteString
    | ParenL | ParenR
    | GroupL | GroupR
    | BraceL | BraceR
    | BracketL | BracketR
    deriving (Show, Eq, Ord)


instance IsString Tok where
    -- Does not handle non-ASCII chars! But it’s good enough
    -- for specifying keywords in the grammar.
    fromString w = Word (fromString w)



data Located a = Located
    { startPos :: SourcePos
    , endPos :: SourcePos
    , tokenLength :: Int
    , unLocated :: a
    } deriving (Show)

instance Eq a  => Eq  (Located a) where (==) = (==) `on` unLocated
instance Ord a => Ord (Located a) where compare = compare `on` unLocated


topLevelChunks :: Lexer [[Located Tok]]
topLevelChunks = space *> many topLevelChunk


-- | To limit the scope of ambiguities to a single top-level environment,
-- we split tokens into chunks, each containing the tokens of a single
-- top-level environment.
topLevelChunk :: Lexer [Located Tok]
topLevelChunk = do
    --env <- anySingle `skipManyTill` beginTopLevel
    env <- beginTopLevel
    rest <- some tok
    -- The ending token is left implicit.
    _ <- endTopLevel -- TODO throw error if this is not equal to @env@?
    pure (env : rest)



-- | Parses a single normal mode token.
tok :: Lexer (Located Tok)
tok = word <|> var <|> asciiSymbol
    <|> beginInlineText <|> endInlineText
    <|> beginLowLevel <|> endLowLevel
    <|> mathBegin <|> mathEnd
    <|> opening <|> closing <|> mathBegin <|> command
    <|> number


beginInlineText :: Lexer (Located Tok)
beginInlineText = lexeme do
    guardM isMathMode
    Byte.string "\\text{"
    setTextMode
    pure (BeginEnv "text")


endInlineText :: Lexer (Located Tok)
endInlineText = lexeme do
    guardM isTextMode
    0 <- gets textNesting -- Otherwise fail.
    Byte.char (ascii '}')
    setMathMode
    pure (EndEnv "text")


opening :: Lexer (Located Tok)
opening = lexeme (brace <|> group <|> paren <|> bracket)
    where
        brace = BraceL <$ lexeme (Byte.string "\\{")
        group = GroupL <$ lexeme (Byte.char (ascii '{')) <* modify' incrNesting
        paren = ParenL <$ lexeme (Byte.char (ascii '('))
        bracket = BracketL <$ lexeme (Byte.char (ascii '['))


closing :: Lexer (Located Tok)
closing = lexeme (brace <|> group <|> paren <|> bracket)
    where
        brace = BraceR <$ lexeme (Byte.string "\\}")
        group = GroupR <$ lexeme (Byte.char (ascii '}')) <* modify' decrNesting
        paren = ParenR <$ lexeme (Byte.char (ascii ')'))
        bracket = BracketR <$ lexeme (Byte.char (ascii ']'))


-- | Parses a single begin math token.
mathBegin :: Lexer (Located Tok)
mathBegin = guardM isTextMode *> lexeme do
    Byte.string "\\(" <|> Byte.string "\\[" <|> Byte.string "$"
    setMathMode
    pure (BeginEnv "math")


-- | Parses a single end math token.
mathEnd :: Lexer (Located Tok)
mathEnd = guardM isMathMode *> lexeme do
    Byte.string "\\)" <|> Byte.string "\\]" <|> Byte.string "$"
    setTextMode
    pure (EndEnv "math")


-- | Parses a word. Words are returned casefolded, since we want to ignore their case later on.
word :: Lexer (Located Tok)
word = guardM isTextMode *> lexeme do
    w <- takeWhile1P (Just "word") (\c -> not (Ascii.isAscii c) || Ascii.isAlpha c || c == ascii '\'' || c == ascii '-')
    let t = Word (toShort (BS.map Ascii.toLower w))
    pure t


number :: Lexer (Located Tok)
number = lexeme $ Integer <$> ByteLexer.decimal


var :: Lexer (Located Tok)
var = guardM isMathMode *> lexeme (Variable . toShort <$> var')
    where
    var' = do
        alphabeticPart <- letter <|> greek <|> bb
        variationPart <- subscriptNumber <|> ticked
        pure (alphabeticPart <> variationPart)

    subscriptNumber :: Lexer ByteString
    subscriptNumber = do
        Byte.char (ascii '_')
        n <- takeWhile1P (Just "subscript number") Ascii.isDigit
        pure n

    -- 0 or more ASCII apostrophes (0x27): always succeeds.
    -- Apostrophes have a special use in TPTP, so we replace
    -- them with the string "prime" for an easier translation.
    ticked :: Lexer ByteString
    ticked = do
        ticks <- many $ Byte.char (ascii '\'')
        let ticks' = "prime" <$ ticks
        pure (BS.concat ticks')

    letter :: Lexer ByteString
    letter = fmap BS.singleton Byte.letterChar

    bb :: Lexer ByteString
    bb = do
        Byte.string "\\mathbb{"
        l <- symbolParser bbs
        Byte.char (ascii '}')
        pure ("bb" <> l)

    bbs :: [ByteString]
    bbs = BS.singleton . ascii <$> ['A'..'Z']

    greek :: Lexer ByteString
    greek = try do
        l <- symbolParser greeks
        notFollowedBy Byte.letterChar
        pure l

    greeks :: [ByteString]
    greeks =
        [ "\\alpha", "\\beta", "\\gamma", "\\delta", "\\epsilon", "\\zeta"
        , "\\eta", "\\theta", "\\iota", "\\kappa", "\\lambda", "\\mu", "\\nu"
        , "\\xi", "\\pi", "\\rho", "\\sigma", "\\tau", "\\upsilon", "\\phi"
        , "\\chi", "\\psi", "\\omega"
        , "\\Gamma", "\\Delta", "\\Theta", "\\Lambda", "\\Xi", "\\Pi", "\\Sigma"
        , "\\Upsilon", "\\Phi", "\\Psi", "\\Omega"
        ]

    symbolParser :: [ByteString] -> Lexer ByteString
    symbolParser symbols = asum [Byte.string s | s <- symbols]


asciiSymbol :: Lexer (Located Tok)
asciiSymbol = lexeme do
    symb <- satisfy (`elem` symbols)
    pure (Symbol (toShort (BS.singleton symb)))
    where
        symbols :: [Word8]
        symbols = fmap ascii ".,:;!?@=+-/^><*&"


-- | Parses a TEX-style command, except @\\begin@ and @\\end@.
-- Should occur after the variable lexer so that special variables
-- (Greek, blackboard bold, etc.) can be lexed correctly.
command :: Lexer (Located Tok)
command = lexeme $ try do
    Byte.char (ascii '\\')
    cmd <- takeWhile1P (Just "TeX command") Ascii.isAlpha
    if
        | cmd == "begin" || cmd == "end" -> empty
        | otherwise -> pure (Command (toShort cmd))


topLevelEnvs :: [ByteString]
topLevelEnvs =
    [ "axiom"
    , "definition"
    , "inductive"
    , "lemma"
    , "proof"
    , "proposition"
    , "signature"
    , "theorem"
    ]


lowLevelEnvs :: [ByteString]
lowLevelEnvs =
    [ "byCase"
    , "enumerate"
    , "subproof"
    , "itemize"
    ]


begin :: ByteString -> Lexer (Located Tok)
begin env = lexeme do
    Byte.string ("\\begin{" <> env <> "}")
    pure (BeginEnv (toShort env))


end :: ByteString -> Lexer (Located Tok)
end env = lexeme do
    Byte.string ("\\end{" <> env <> "}")
    pure (BeginEnv (toShort env))


beginTopLevel, endTopLevel :: Lexer (Located Tok)
beginTopLevel = asum $ begin <$> topLevelEnvs
endTopLevel   = asum $ end   <$> topLevelEnvs


beginLowLevel, endLowLevel :: Lexer (Located Tok)
beginLowLevel = asum $ begin <$> lowLevelEnvs
endLowLevel   = asum $ end   <$> lowLevelEnvs


-- | Turns a Lexer into one that tracks the source position of the token
-- and consumes trailing whitespace.
lexeme :: Lexer a -> Lexer (Located a)
lexeme p = do
    start <- getSourcePos
    startOffset <- getOffset
    t <- p
    space
    stop <- getSourcePos
    stopOffset <- getOffset
    let l = stopOffset - startOffset
    pure (Located start stop l t)


space :: Lexer ()
space = ByteLexer.space Byte.space1 (ByteLexer.skipLineComment "%") empty
