-- This module contains primitives for tex parsing.

{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}

module SAD.Parser.Tex where

import Control.Applicative
import Data.Text.Lazy (Text)

import SAD.ForTheL.Base

import SAD.Parser.Primitives
import SAD.Parser.Combinators


-- | @texEnv envType labelParser parseContent@ is a general purpose tex environment parser.
-- @envType@ parses the environment type specified in the environment declaration.
-- @labelParser@ parses a label declaration such as '[label]'.
-- @content@ parses the insides of the environment.
texEnv :: FTL Text -> LabelOptions b -> FTL a -> FTL (a, b)
texEnv envType labelParser content = do
  -- We use 'try' to backtrack if parsing the environment declaration fails.
  envType' <- try $ texBegin envType
  envLabel <- labelParser
  (, envLabel) <$> (content <* texEnd (token envType'))

-- | Parses tex environment while iterating a parser inside it until '\end{...}' is parsed or the end parser succeeds.
-- is passed.
repeatInTexEnv :: Monoid a => FTL Text -> LabelOptions b -> FTL a -> FTL a -> FTL (a, b)
repeatInTexEnv envType labelParser content end = do
  envType' <- try $ texBegin envType
  envLabel <- labelParser
  (, envLabel) <$> repeatUntil content (texEnd (token envType') >> return mempty <|> end)


-- | Parses '\begin{env}'. Takes a parser for parsing 'env'.
texBegin :: FTL a -> FTL a
texBegin envType = do
  token "\\begin"
  symbol "{"
  envType' <- envType
  symbol "}"
  return envType'

-- | Parses '\end{env}'. Takes a parser for parsing 'env'.
texEnd :: FTL () -> FTL ()
texEnd envType = do
  token "\\end"
  symbol "{"
  envType
  symbol "}"

-- | This is used for controlling the different options for parsing labels. For instance,
-- in '\begin{env}[lbl]', 'lbl' would be the label.
type LabelOptions a = FTL a

envLabel :: LabelOptions Text
envLabel = do
  symbol "["
  label <- anyToken
  symbol "]"
  return label

noEnvLabel :: LabelOptions ()
noEnvLabel = return ()

optionalEnvLabel :: LabelOptions (Maybe Text)
optionalEnvLabel = optLLx Nothing (Just <$> envLabel)