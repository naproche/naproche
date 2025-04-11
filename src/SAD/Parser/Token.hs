-- |
-- Module      : SAD.Parser.Token
-- Copyright   : (c) 2001 - 2008, Andrei Paskevich,
--               (c) 2017 - 2018, Steffen Frerix,
--               (c) 2024, Marcel Schütz
-- License     : GPL-3
--
-- Generic tokenization setup


{-# LANGUAGE OverloadedStrings #-}

module SAD.Parser.Token (
  Token(..),
  renderTokens,

  Warning(..),
  reportWarnings,
  concatTokWarn,

  handleError,
  unknownError,

  isabelleSymbols,

  tokensRange,
  tokensPos,
  tokensText,
  showToken,
  mergeTokens,
  composeTokens,
  isEOF,
  noTokens
) where

import Data.Text (Text)
import Data.Text qualified as Text
import Data.Text.Lazy qualified as Lazy
import Data.List.NonEmpty qualified as NonEmpty
import Data.Set (Set)
import Data.Set qualified as Set
import Data.List
import Data.Bifunctor (bimap)
import Text.Megaparsec hiding (State, Pos, Token)

import SAD.Core.Message qualified as Message
import SAD.Helpers (failureMessage)

import Isabelle.Position qualified as Position


-- * Tokens

-- | A token of a ForTheL text
data Token =
    Token {
      tokenText :: Text
    , tokenPos :: Position.T
    }
  | EOF { tokenPos :: Position.T }
  deriving (Eq, Ord)

-- | Render a list of tokens.
renderTokens :: [Token] -> String
renderTokens tokens = intercalate "\n" $ map renderToken tokens

-- | Render a token.
renderToken :: Token -> String
renderToken (Token text pos) =
  "Token:\n" ++
  "  Text: " ++ show text ++ "\n" ++
  "  Position:\n" ++
  "    Line: " ++ maybe (failureMessage "SAD.Parser.Token.renderToken" "Unknown line") show (Position.line_of pos) ++ "\n" ++
  "    Column: " ++ maybe (failureMessage "SAD.Parser.Token.renderToken" "Unknown column") show (Position.column_of pos) ++ "\n" ++
  "    Offset: " ++ maybe (failureMessage "SAD.Parser.Token.renderToken" "Unknown offset") show (Position.offset_of pos) ++ "\n" ++
  "    End-Offset: " ++ maybe (failureMessage "SAD.Parser.Token.renderToken" "Unknown end-offset") show (Position.end_offset_of pos)
renderToken EOF{} = ""


-- * Warnings

-- | A warning: A message equipped with a position that message refers to.
data Warning = Warning Text Position.T

-- | Report several warnings at once.
reportWarnings :: [Warning] -> IO ()
reportWarnings = foldr ((>>) . reportWarning) (return ())

-- | Report a single warning.
reportWarning :: Warning -> IO ()
reportWarning (Warning text pos) = Message.outputTokenizer Message.WARNING pos text

-- | Concatenate a list of tokens/warnings-pairs.
concatTokWarn :: [([Token], [Warning])] -> ([Token], [Warning])
concatTokWarn [] = ([],[])
concatTokWarn ((xs,ys) : rest) = bimap (xs ++) (ys ++) (concatTokWarn rest)


-- * Error Handling

-- | Report a tokenizing error.
handleError :: (error -> (Text, Position.T)) -> ParseErrorBundle [a] error -> IO b
handleError errorHandler errors = do
  let (errorMsg, errorPos) = showError errors errorHandler
  Message.errorTokenizer errorPos errorMsg

-- | Return an error message and the position of the first error that occured
-- during tokenizing.
showError :: ParseErrorBundle [a] error -> (error -> (Text, Position.T)) -> (Text, Position.T)
showError (ParseErrorBundle parseErrors _) errorHandler = case NonEmpty.head parseErrors of
  TrivialError{} -> unknownError
  FancyError _ errs -> properError errorHandler errs

-- | Located error message for an error that is not handled as a custom error
-- of type "Error" during tokenizing.
unknownError :: (Text, Position.T)
unknownError =
  let msg = Text.pack $ failureMessage "SAD.Parser.Token.unknownError" "Unknown tokenizing error."
      pos = Position.none
  in (msg, pos)

-- | Turn a set of tokenizing errors into an error message.
properError :: (error -> (Text, Position.T)) -> Set (ErrorFancy error) -> (Text, Position.T)
properError errorHandler errs =
  case Set.elems errs of
    [] -> unknownError
    err : _ -> fancyError errorHandler err

-- | Turn a tokenizing error into an error message.
fancyError :: (error -> (Text, Position.T)) -> ErrorFancy error -> (Text, Position.T)
fancyError errorHandler err = case err of
  ErrorFail{} -> unknownError
  ErrorIndentation{} -> unknownError
  ErrorCustom err -> errorHandler err


-- * Isabelle Symbols

-- | Identifiers of "Isabelle symbols" (e.g. @\<in>@).
isabelleSymbols :: [Text]
isabelleSymbols = [
    -- digit:
    "zero", "one", "two", "three", "four", "five", "six", "seven", "eight",
    "nine", "onequarter", "onehalf", "threequarters",
    -- letter:
    "A", "B", "C", "D", "E", "F", "G", "H", "I", "J", "K", "L", "M", "N", "O",
    "P", "Q", "R", "S",  "T", "U", "V", "W", "X", "Y", "Z",
    "a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m", "n", "o",
    "p", "q", "r", "s", "t", "u", "v", "w", "x", "y", "z",
    "AA", "BB", "CC", "DD", "EE", "FF", "GG", "HH", "II", "JJ", "KK", "LL",
    "MM", "NN", "OO", "PP", "QQ", "RR", "SS", "TT", "UU", "VV", "WW", "XX",
    "YY", "ZZ",
    "aa", "bb", "cc", "dd", "ee", "ff", "gg", "hh", "ii", "jj", "kk", "ll",
    "mm", "nn", "oo", "pp", "qq", "rr", "ss", "tt", "uu", "vv", "ww", "xx",
    "yy", "zz",
    "alpha", "beta", "gamma", "delta", "epsilon", "zeta", "eta", "theta",
    "iota", "kappa", "lambda", "mu", "nu", "xi", "pi", "rho", "sigma", "tau",
    "upsilon", "phi", "chi", "psi", "omega",
    "Gamma", "Delta", "Theta", "Lambda", "Xi", "Pi", "Sigma", "Upsilon", "Phi",
    "Psi", "Omega",
    "bbbA", "bool", "complex", "bbbD", "bbbE", "bbbF", "bbbG", "bbbH", "bbbI",
    "bbbJ", "bbbK", "bbbL", "bbbM", "nat", "bbbO", "bbbP", "rat", "real",
    "bbbS", "bbbT", "bbbU", "bbbV", "bbbW", "bbbX", "bbbY","int",
    -- arrow:
    "leftarrow", "longleftarrow", "longlongleftarrow", "longlonglongleftarrow",
    "rightarrow", "longrightarrow", "longlongrightarrow",
    "longlonglongrightarrow", "Leftarrow", "Longleftarrow", "Lleftarrow",
    "Rightarrow", "Longrightarrow", "Rrightarrow", "leftrightarrow",
    "longleftrightarrow", "Leftrightarrow", "Longleftrightarrow", "mapsto",
    "longmapsto", "midarrow", "Midarrow", "hookleftarrow", "hookrightarrow",
    "leftharpoondown", "rightharpoondown", "leftharpoonup", "rightharpoonup",
    "rightleftharpoons", "leadsto", "downharpoonleft", "downharpoonright",
    "upharpoonleft", "upharpoonright", "restriction", "up", "Up", "down",
    "Down", "updown", "Updown",
    -- punctuation:
    "Colon", "bar", "bbar", "langle", "rangle", "llangle", "rrangle", "lceil",
    "rceil", "lfloor", "rfloor", "lparr", "rparr", "lbrakk", "rbrakk", "lbrace",
    "rbrace", "lblot", "rblot", "guillemotleft", "guillemotright", "dots",
    "cdots", "hyphen", "sqdot", "open", "close",
    -- logic:
    "bottom", "top", "and", "And", "or", "Or", "forall", "exists", "nexists",
    "not", "circle", "box", "diamond",
    -- relation:
    "turnstile", "Turnstile", "tturnstile", "TTurnstile", "stileturn", "surd",
    "le", "ge", "lless", "ggreater", "lesssim", "greatersim", "lessapprox",
    "greaterapprox", "in", "notin", "subset", "supset", "subseteq", "supseteq",
    "sqsubset", "sqsupset", "sqsubseteq", "sqsupseteq", "noteq", "sim", "doteq",
    "simeq", "approx", "asymp", "cong", "smile", "equiv", "frown", "prec",
    "succ", "preceq", "succeq", "parallel", "Parallel", "interleave", "sslash",
    "lhd", "rhd", "unlhd", "unrhd", "triangleleft", "triangleright", "triangle",
    "triangleq", "wrong",
    -- operator:
    "diamondop", "inter", "Inter", "union", "Union", "squnion", "Squnion",
    "sqinter", "Sqinter", "setminus", "propto", "uplus", "Uplus", "plusminus",
    "minusplus", "times", "div", "cdot", "star", "bullet", "circ", "oplus",
    "Oplus", "otimes", "Otimes", "odot", "Odot", "ominus", "oslash", "Sum",
    "Prod", "Coprod", "integral", "ointegral", "inverse", "amalg", "mho",
    "bind", "then",
    -- unsorted:
    "Join", "bowtie", "dagger", "ddagger", "infinity", "clubsuit",
    "diamondsuit", "heartsuit", "spadesuit", "aleph", "emptyset", "nabla",
    "partial", "flat", "natural", "angle", "copyright", "registered",
    "ordfeminine", "ordmasculine", "section", "paragraph", "exclamdown",
    "questiondown", "euro", "pounds", "yen", "cent", "currency", "degree",
    "lozenge", "wp", "acute", "index", "dieresis", "cedilla", "hungarumlaut",
    "some", "hole", "newline", "checkmark", "crossmark", "^here", "^undefined",
    -- z-notation:
    "sharp", "Zcomp", "Zinj", "Zpinj", "Zfinj", "Zsurj", "Zpsurj", "Zbij",
    "Zpfun", "Zffun", "Zdres", "Zndres", "Zrres", "Znrres", "Zspot", "Zsemi",
    "Zproject", "Ztypecolon", "Zhide", "Zcat", "Zinbag", "Zprime",
    -- document:
    "comment", "^cancel", "^marker", "^noindent", "^smallskip", "^medskip",
    "^bigskip", "^item", "^enum", "^descr", "^footnote", "^verbatim",
    "^theory_text", "^emph", "^bold",
    -- control:
    "^sub", "^sup",
    -- control block:
    "^bsub", "^esub", "^bsup", "^esup",
    -- icon:
    "^file", "^dir", "^url", "^doc", "^action"
  ]


-- * Legacy Dependencies

-- | Get the end position of a token
tokenEndPos :: Token -> Position.T
tokenEndPos tok@Token{} = Position.symbol_explode (tokenText tok) (tokenPos tok)
tokenEndPos tok@EOF{} = tokenPos tok

-- | The range in which the tokens lie
tokensRange :: [Token] -> Position.Range
tokensRange [] = Position.no_range
tokensRange toks = Position.range (tokenPos $ head toks, tokenEndPos $ last toks)

-- | Get the positon of a token, ranging from the beginnig of the first token to
-- the end of the last one.
tokensPos :: [Token] -> Position.T
tokensPos = Position.range_position . tokensRange

-- | Concatenate the text components of a list of tokens.
tokensText :: [Token] -> Text
tokensText = Text.concat . map tokenText

-- | Merge a list of tokens into a single token.
mergeTokens :: [Token] -> Token
mergeTokens tokens = Token (tokensText tokens) (tokensPos tokens)

-- | Print a token
showToken :: Token -> Lazy.Text
showToken t@Token{} = Lazy.fromStrict $ tokenText t
showToken EOF{} = Lazy.pack "end of input"

-- | Append tokens separated by a single space if they were separated
-- by whitespace before
composeTokens :: [Token] -> Lazy.Text
composeTokens = Lazy.concat . dive
  where
    dive [] = []
    dive [t] = [showToken t]
    dive (t : t' : ts) = if noSpaceBetween t t'
      then showToken t : dive (t' : ts)
      else showToken t : " " : dive (t' : ts)
    noSpaceBetween t t' = case Position.offset_of (tokenPos t) of
        Just n -> case Position.offset_of (tokenPos t') of
          Just m -> n == m + 1
          Nothing -> False
        Nothing -> False

-- | A singleton /end of file/ token, i.e. the result of tokenizing an empty
-- document
noTokens :: [Token]
noTokens = [EOF Position.none]

-- | Determines whether a token is an /end of file/ token
isEOF :: Token -> Bool
isEOF EOF{} = True
isEOF _ = False
