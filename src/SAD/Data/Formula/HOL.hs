{-
Authors: Makarius Wenzel (2021)

The Naproche logic within Isabelle/HOL.
-}

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NamedFieldPuns #-}

module SAD.Data.Formula.HOL (
  base_type, prop_type, export_formula,
  cert_terms, cert_term, print_terms, print_term, print_sequents, print_sequent
)
where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)

import SAD.Data.VarName (VariableName (..))
import SAD.Data.Text.Decl (Decl (..))
import SAD.Data.Terms
import SAD.Data.Formula.Base

import Isabelle.Bytes (Bytes)
import qualified Isabelle.Value as Value
import qualified Isabelle.Name as Isabelle
import qualified Isabelle.Term as Isabelle
import Isabelle.Term ((--->))
import qualified Isabelle.HOL as Isabelle
import qualified Isabelle.Naproche as Isabelle
import Isabelle.Library
import qualified Naproche.Program as Program
import qualified Isabelle.YXML as YXML
import qualified Isabelle.XML.Encode as Encode
import qualified Isabelle.Term_XML.Encode as Encode
import qualified Isabelle.Term_XML.Decode as Decode


{- export formula -}

base_type, prop_type :: Isabelle.Typ
base_type = Isabelle.iT
prop_type = Isabelle.boolT

free_name :: VariableName -> Isabelle.Name
free_name (VarConstant s) = "x" <> make_bytes s
free_name (VarHole s) = Isabelle.internal ("HOLE_" <> make_bytes s)
free_name VarSlot = Isabelle.internal "SLOT"
free_name (VarU s) = "u" <> make_bytes s
free_name (VarHidden n) = "h" <> Value.print_int n
free_name (VarAssume n) = "i" <> Value.print_int n
free_name (VarSkolem n) = "o" <> Value.print_int n
free_name (VarTask s) = "c" <> free_name s
free_name (VarZ s) = "z" <> make_bytes s
free_name (VarW s) = "w" <> make_bytes s
free_name VarEmpty = Isabelle.uu_
free_name (VarDefault s) = make_bytes s

bound_name :: VariableName -> Isabelle.Name
bound_name (VarConstant s) = make_bytes s
bound_name (VarHole s) = Isabelle.internal ("v" <> make_bytes s)
bound_name VarSlot = Isabelle.uu
bound_name (VarU s) = "u"
bound_name (VarHidden _) = "h"
bound_name (VarAssume _) = "i"
bound_name (VarSkolem _) = "o"
bound_name (VarTask s) = "c" <> bound_name s
bound_name (VarZ s) = "z"
bound_name (VarW s) = "w"
bound_name VarEmpty = Isabelle.uu
bound_name (VarDefault s) = make_bytes s

term_name :: TermName -> Isabelle.Name
term_name (TermName t) = make_bytes t
term_name (TermSymbolic t) = "s" <> make_bytes t
term_name (TermNotion t) = "a" <> make_bytes t
term_name (TermThe t) = "the" <> make_bytes t
term_name (TermUnaryAdjective t) = "is" <> make_bytes t
term_name (TermMultiAdjective t) = "mis" <> make_bytes t
term_name (TermUnaryVerb t) = "do" <> make_bytes t
term_name (TermMultiVerb t) = "mdo" <> make_bytes t
term_name (TermTask n) = "tsk " <> Value.print_int n
term_name TermEquality = undefined
term_name TermLess  = undefined
term_name TermSmall = undefined
term_name TermThesis = undefined
term_name TermEmpty = ""

consts :: Map TermName Bytes
consts =
  Map.fromList [
    (TermSmall, Isabelle.setsized_const),
    (termFun, Isabelle.fun_const),
    (termSet, Isabelle.set_const),
    (termClass, Isabelle.class_const),
    (termElem, Isabelle.elem_const),
    (termObj, Isabelle.obj_const),
    (TermLess, Isabelle.less_const),
    (termDom, Isabelle.dom_const),
    (termProd, Isabelle.prod_const),
    (termPair, Isabelle.pair_const),
    (termApp, Isabelle.app_const),
    (TermThesis, Isabelle.thesis_const)]

export_formula :: Formula -> Isabelle.Term
export_formula = Isabelle.mk_trueprop . form
  where
    form :: Formula -> Isabelle.Term
    form (All Decl{declName = x} b) = Isabelle.mk_all_op base_type (abs x (form b))
    form (Exi Decl{declName = x} b) = Isabelle.mk_ex_op base_type (abs x (form b))
    form (Iff a b) = Isabelle.mk_iff (form a) (form b)
    form (Imp a b) = Isabelle.mk_imp (form a) (form b)
    form (Or a b) = Isabelle.mk_disj (form a) (form b)
    form (And a b) = Isabelle.mk_conj (form a) (form b)
    form (Tag _ a) = form a
    form (Not a) = Isabelle.mk_not (form a)
    form Top = Isabelle.true
    form Bot = Isabelle.false
    form Trm{trmName = TermEquality, trmArgs = [a, b]} = Isabelle.mk_eq base_type (term a) (term b)
    form Trm{trmName = name, trmArgs = args} = app name (map term args) prop_type
    form Var{varName = x} = free x prop_type
    form Ind{indIndex = i} = Isabelle.Bound i
    form ThisT = Isabelle.mk_this prop_type

    term :: Formula -> Isabelle.Term
    term Trm{trmName = name, trmArgs = args} = app name (map term args) base_type
    term Var{varName = x} = free x base_type
    term Ind{indIndex = i} = Isabelle.Bound i
    term ThisT = Isabelle.mk_this base_type
    term (Tag _ a) = term a
    term _ = error "Bad formula as term"

    free :: VariableName -> Isabelle.Typ -> Isabelle.Term
    free x ty = Isabelle.Free (free_name x, ty)

    abs :: VariableName -> Isabelle.Term -> Isabelle.Term
    abs x body = Isabelle.Abs (bound_name x, base_type, body)

    app :: TermName -> [Isabelle.Term] -> Isabelle.Typ -> Isabelle.Term
    app name args res_type = Isabelle.list_comb op args
      where
        ty = replicate (length args) base_type ---> res_type
        op =
          case Map.lookup name consts of
            Just c -> Isabelle.Const (c, [])
            Nothing -> Isabelle.Free (term_name name, ty)


{- Isabelle term operations -}

cert_terms :: Program.Context -> [Isabelle.Term] -> IO [Isabelle.Typ]
cert_terms = Program.yxml_pide_command Encode.term Decode.typ Isabelle.cert_terms_command

cert_term :: Program.Context -> Isabelle.Term -> IO Isabelle.Typ
cert_term = singletonM . cert_terms

print_terms :: Program.Context -> [Isabelle.Term] -> IO [Bytes]
print_terms = Program.yxml_pide_command Encode.term YXML.string_of_body Isabelle.print_terms_command

print_term :: Program.Context -> Isabelle.Term -> IO Bytes
print_term = singletonM . print_terms

print_sequents :: Program.Context -> [([Formula], [Formula])] -> IO [Bytes]
print_sequents =
  let
    encode1 = Encode.list (Encode.term . export_formula)
    encode2 = Encode.pair encode1 encode1
  in
    Program.yxml_pide_command encode2 YXML.string_of_body Isabelle.print_sequents_command

print_sequent :: Program.Context -> ([Formula], [Formula]) -> IO Bytes
print_sequent = singletonM . print_sequents
