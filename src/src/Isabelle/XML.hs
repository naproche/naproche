{- generated by Isabelle -}

{-  Title:      Isabelle/XML.hs
    Author:     Makarius
    LICENSE:    BSD 3-clause (Isabelle)

Untyped XML trees and representation of ML values.

See "$ISABELLE_HOME/src/Pure/PIDE/xml.ML".
-}

{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}

module Isabelle.XML (Attributes, Body, Tree(..), wrap_elem, unwrap_elem, content_of)
where

import Isabelle.Library
import qualified Isabelle.Properties as Properties
import qualified Isabelle.Markup as Markup
import qualified Isabelle.Buffer as Buffer
import qualified Isabelle.Bytes as Bytes
import Isabelle.Bytes (Bytes)


{- types -}

type Attributes = Properties.T
type Body = [Tree]
data Tree = Elem (Markup.T, Body) | Text Bytes


{- wrapped elements -}

wrap_elem :: ((Markup.T, Body), [Tree]) -> Tree
wrap_elem (((a, atts), body1), body2) =
  Elem (("xml_elem", ("xml_name", a) : atts), Elem (("xml_body", []), body1) : body2)

unwrap_elem :: Tree -> Maybe ((Markup.T, Body), [Tree])
unwrap_elem
  (Elem (("xml_elem", ("xml_name", a) : atts), Elem (("xml_body", []), body1) : body2)) =
  Just (((a, atts), body1), body2)
unwrap_elem _ = Nothing


{- text content -}

add_content :: Tree -> Buffer.T -> Buffer.T
add_content tree =
  case unwrap_elem tree of
    Just (_, ts) -> fold add_content ts
    Nothing ->
      case tree of
        Elem (_, ts) -> fold add_content ts
        Text s -> Buffer.add s

content_of :: Body -> Bytes
content_of = Buffer.build_content . fold add_content


{- string representation -}

encode_char :: Char -> String
encode_char '<' = "&lt;"
encode_char '>' = "&gt;"
encode_char '&' = "&amp;"
encode_char '\'' = "&apos;"
encode_char '\"' = "&quot;"
encode_char c = [c]

encode_text :: Bytes -> Bytes
encode_text = make_bytes . concatMap (encode_char . Bytes.char) . Bytes.unpack

instance Show Tree where
  show tree =
    make_string $ Buffer.build_content (show_tree tree)
    where
      show_tree (Elem ((name, atts), [])) =
        Buffer.add "<" #> Buffer.add (show_elem name atts) #> Buffer.add "/>"
      show_tree (Elem ((name, atts), ts)) =
        Buffer.add "<" #> Buffer.add (show_elem name atts) #> Buffer.add ">" #>
        fold show_tree ts #>
        Buffer.add "</" #> Buffer.add name #> Buffer.add ">"
      show_tree (Text s) = Buffer.add (encode_text s)

      show_elem name atts =
        space_implode " " (name : map (\(a, x) -> a <> "=\"" <> encode_text x <> "\"") atts)