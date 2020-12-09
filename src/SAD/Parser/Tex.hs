{-# LANGUAGE TupleSections #-}
-- This module contains primitives for tex parsing.

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
texEnv :: FTL Text -> LabelOptions label -> FTL content -> FTL (content, label)
texEnv envType labelParser content = do
  -- We use 'try' to backtrack if parsing the environment declaration fails.
  envType' <- try $ texBegin envType
  envLabel <- labelParser
  (, envLabel) <$> after content (texEnd $ token envType')

-- | Parses tex environment while iterating a parser inside it until '\end{...}' is parsed or abort instruction
-- is passed.
repeatInTexEnv :: Monoid content => FTL () -> LabelOptions label -> FTL (StepStatus content) -> FTL (content, label)
repeatInTexEnv envType labelParser content = do
  try $ texBegin envType
  envLabel <- labelParser
  (, envLabel) <$> untilEnd content (texEnd envType)
  where
    -- Repeats a parser until the end parser succeeds or the content parser aborts.
    untilEnd :: Monoid a => FTL (StepStatus a) -> FTL () -> FTL a
    untilEnd content end = repeatM $ (end >> return (Abort mempty)) <|> content


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