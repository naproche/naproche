{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ImportQualifiedPost #-}

-- |
-- This module defines the Naproche lexer and its associated data types.
-- The lexer takes 'Text' as input and produces chunks (list of lists)
-- of tokens annotated with positional information. This information is
-- bundled together with the original raw input for producing error messages.
--
-- The lexer perfoms some normalizations to make describing the grammar easier.
-- For instance, words are casefolded to allow for capitalization at the start
-- of sentences.
--
-- Throughout we make the assumption that the input is wellformed LaTeX markup:
-- for instance, braces are assumed to be balanced.
--
module Naproche.Token where


import Control.Monad.State.Strict
import Naproche.Helpers (guardM)
import Data.Void (Void)
import Data.Foldable
import Data.Function (on)
import Data.Text qualified as Text
import Data.Text (Text)
import Text.Megaparsec hiding (State)
import Text.Megaparsec.Char qualified as Char
import Text.Megaparsec.Char.Lexer qualified as Lexer
import Data.String (IsString(..))
import Isabelle.Bytes (Bytes)
import Isabelle.Library (make_bytes)
import Data.Char



runLexer :: String -> Text -> Either (ParseErrorBundle Text Void) [[Located Tok]]
runLexer file raw = evalState (runParserT topLevelChunks file raw) initLexerState


type Lexer = ParsecT Void Text (State LexerState)

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
-- before lexing as 'Text' for showing error messages.
--
data TokenChunks = TokenChunks
    { rawInput :: Text
    , unTokenChunks :: [[Located Tok]]
    } deriving (Show, Eq)


data Tok
    = Word Bytes
    | Variable Bytes
    | Symbol Bytes
    | Integer Integer
    | Command Bytes
    | BeginEnv Bytes
    | EndEnv Bytes
    | ParenL | ParenR
    | GroupL | GroupR
    | BraceL | BraceR
    | BracketL | BracketR
    deriving (Show, Eq, Ord)


instance IsString Tok where
    -- Does not handle non-ASCII chars! But it’s good enough
    -- for specifying keywords in the grammar.
    fromString w = Word (fromString w)


maybeVarTok :: Located Tok -> Maybe (Bytes, SourcePos)
maybeVarTok t = case unLocated t of
    Variable x -> Just (x, startPos t)
    _tok -> Nothing


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
tok = word <|> var <|> symbol
    <|> beginInlineText <|> endInlineText
    <|> beginLowLevel <|> endLowLevel
    <|> mathBegin <|> mathEnd
    <|> opening <|> closing <|> mathBegin <|> command
    <|> number


beginInlineText :: Lexer (Located Tok)
beginInlineText = lexeme do
    guardM isMathMode
    Char.string "\\text{"
    setTextMode
    pure (BeginEnv "text")

endInlineText :: Lexer (Located Tok)
endInlineText = lexeme do
    guardM isTextMode
    0 <- gets textNesting -- Otherwise fail.
    Char.char '}'
    setMathMode
    pure (EndEnv "text")


opening :: Lexer (Located Tok)
opening = lexeme (brace <|> group <|> paren <|> bracket)
    where
        brace = BraceL <$ lexeme (Char.string "\\{")
        group = GroupL <$ lexeme (Char.char '{') <* modify' incrNesting
        paren = ParenL <$ lexeme (Char.char '(')
        bracket = BracketL <$ lexeme (Char.char '[')


closing :: Lexer (Located Tok)
closing = lexeme (brace <|> group <|> paren <|> bracket)
    where
        brace = BraceR <$ lexeme (Char.string "\\}")
        group = GroupR <$ lexeme (Char.char '}') <* modify' decrNesting
        paren = ParenR <$ lexeme (Char.char ')')
        bracket = BracketR <$ lexeme (Char.char ']')


-- | Parses a single begin math token.
mathBegin :: Lexer (Located Tok)
mathBegin = guardM isTextMode *> lexeme do
    Char.string "\\(" <|> Char.string "\\[" <|> Char.string "$"
    setMathMode
    pure (BeginEnv "math")


-- | Parses a single end math token.
mathEnd :: Lexer (Located Tok)
mathEnd = guardM isMathMode *> lexeme do
    Char.string "\\)" <|> Char.string "\\]" <|> Char.string "$"
    setTextMode
    pure (EndEnv "math")


-- | Parses a word. Words are returned casefolded, since we want to ignore their case later on.
word :: Lexer (Located Tok)
word = guardM isTextMode *> lexeme do
    w <- takeWhile1P (Just "word") (\c -> isAlpha c || c == '\'' || c == '-')
    let t = Word (make_bytes (Text.toCaseFold w))
    pure t


number :: Lexer (Located Tok)
number = lexeme $ Integer <$> Lexer.decimal


var :: Lexer (Located Tok)
var = guardM isMathMode *> lexeme (Variable . make_bytes <$> var')
    where
    var' = do
        alphabeticPart <- letter <|> greek <|> bb
        variationPart <- subscriptNumber <|> ticked
        pure (alphabeticPart <> variationPart)

    subscriptNumber :: Lexer Text
    subscriptNumber = do
        Char.char '_'
        n <- takeWhile1P (Just "subscript number") isDigit
        pure n

    -- 0 or more ASCII apostrophes (0x27): always succeeds.
    -- Apostrophes have a special use in TPTP, so we replace
    -- them with the string "prime" for an easier translation.
    ticked :: Lexer Text
    ticked = do
        ticks <- many $ Char.char '\''
        let ticks' = "prime" <$ ticks
        pure (Text.concat ticks')

    letter :: Lexer Text
    letter = fmap Text.singleton Char.letterChar

    bb :: Lexer Text
    bb = do
        Char.string "\\mathbb{"
        l <- symbolParser bbs
        Char.char '}'
        pure ("bb" <> l)

    bbs :: [Text]
    bbs = Text.singleton <$> ['A'..'Z']

    greek :: Lexer Text
    greek = try do
        l <- symbolParser greeks
        notFollowedBy Char.letterChar
        pure l

    greeks :: [Text]
    greeks =
        [ "\\alpha", "\\beta", "\\gamma", "\\delta", "\\epsilon", "\\zeta"
        , "\\eta", "\\theta", "\\iota", "\\kappa", "\\lambda", "\\mu", "\\nu"
        , "\\xi", "\\pi", "\\rho", "\\sigma", "\\tau", "\\upsilon", "\\phi"
        , "\\chi", "\\psi", "\\omega"
        , "\\Gamma", "\\Delta", "\\Theta", "\\Lambda", "\\Xi", "\\Pi", "\\Sigma"
        , "\\Upsilon", "\\Phi", "\\Psi", "\\Omega"
        ]

    symbolParser :: [Text] -> Lexer Text
    symbolParser symbols = asum [Char.string s | s <- symbols]


symbol :: Lexer (Located Tok)
symbol = lexeme do
    symb <- satisfy (`elem` symbols)
    pure (Symbol (make_bytes (Text.singleton symb)))
    where
        symbols :: [Char]
        symbols = ".,:;!?@=+-/^><*&"


-- | Parses a TEX-style command, except @\\begin@ and @\\end@.
-- Should occur after the variable lexer so that special variables
-- (Greek, blackboard bold, etc.) can be lexed correctly.
command :: Lexer (Located Tok)
command = lexeme $ try do
    Char.char '\\'
    cmd <- takeWhile1P (Just "TeX command") isAlpha
    if
        | cmd == "begin" || cmd == "end" -> empty
        | otherwise -> pure (Command (make_bytes cmd))


topLevelEnvs :: [Text]
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


lowLevelEnvs :: [Text]
lowLevelEnvs =
    [ "byCase"
    , "enumerate"
    , "subproof"
    , "itemize"
    ]



begin :: Text -> Lexer (Located Tok)
begin env = lexeme do
    Char.string ("\\begin{" <> env <> "}")
    pure (BeginEnv (make_bytes env))


end :: Text -> Lexer (Located Tok)
end env = lexeme do
    Char.string ("\\end{" <> env <> "}")
    pure (BeginEnv (make_bytes env))


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
space = Lexer.space Char.space1 (Lexer.skipLineComment "%") empty
