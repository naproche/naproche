-- |
-- Authors: Anton Lorenzen (2020)
--
-- TODO: Add description.


{-# LANGUAGE OverloadedStrings #-}

module SAD.Structures.Translate where

import Data.Text.Lazy (Text, pack)

import SAD.Structures.Formula
import qualified SAD.Structures.Type as Type
import SAD.Structures.Type ((-->), (/\), (\/), (<@>))


translateDoc :: Document -> [Type.Decl]
translateDoc (Document decls) =
  let names = fmap (("h" <>) . pack . show) [1 .. length decls]
  in zipWith translateDecl names decls

translateDecl :: Text -> Declaration -> Type.Decl
translateDecl fallback decl = case decl of
  Inductive asm asms -> case asm of
    All _v ((TyPredicate typ :@ Variable _w) :-> Top) ->
      Type.Inductive typ (Type.Const "Type") (makeConstructors asms)
    _asm -> error "malformed inductive declaration"
  Hypothesis declared asms -> case asms of
    [] -> Type.Axiom name Type.Top
    -- Translation of notions to types.
    [All _v ((TyPredicate typ :@ Variable _w) :-> Top)] ->
      Type.Axiom typ (Type.Const "Type")
    -- Translation of subnotions to subtypes.
    [TyPredicate ty :@ Variable _v,(TyPredicate subty :@ Variable _v') :-> Top] ->
      Type.Subtype ty subty
    [All _v ((TyPredicate subty :@ Variable _v') :-> (TyPredicate ty :@ Variable _v''))] ->
      Type.Subtype ty subty
    -- Translation of constants.
    [All _v ((Variable _v' :== Variable c) :-> (TyPredicate ty :@ Variable _v''))] ->
      Type.Axiom c (Type.Const ty)
    -- Translation of unary operations.
    [ TyPredicate ty :@ Variable _w,
      All _v ((Variable _v' :== (Const op :@ Variable _v'')) :-> (TyPredicate ty' :@ Variable _v'''))] ->
        Type.Axiom op (Type.Const ty --> Type.Const ty')
    -- Translation of binary operations.
    [ TyPredicate ty :@ Variable _v :/\ TyPredicate ty' :@ Variable _w,
      All _b ((Variable _b' :== ((Const op :@ Variable _v') :@ Variable _w')) :-> (TyPredicate ty'' :@ Variable _v''))] ->
      Type.Axiom op (Type.Const ty --> Type.Const ty' --> Type.Const ty'')
      -- Translation of unary predicates
    [ TyPredicate ty1 :@ Variable v1, Predicate p :@ Variable _a1 :<-> f ] ->
      Type.Def p Type.Hole (Type.Abs v1 (Type.Const ty1) (transl f))
    -- Translation of binary predicates
    [ TyPredicate ty1 :@ Variable v1 :/\ TyPredicate ty2 :@ Variable v2,
      Predicate p :@ Variable _a1 :@ Variable _a2 :<-> f ] ->
        Type.Def p Type.Hole (Type.Abs v1 (Type.Const ty1) (Type.Abs v2 (Type.Const ty2) (transl f)))
    [ TyPredicate ty1 :@ Variable v1 :/\ TyPredicate ty2 :@ Variable v2,
      Const p :@ Variable _a1 :@ Variable _a2 :<-> f] ->
        Type.Def p Type.Hole (Type.Abs v1 (Type.Const ty1) (Type.Abs v2 (Type.Const ty2) (transl f)))
    -- Translation of ternary predicates.
    [ TyPredicate ty1 :@ Variable v1 :/\ TyPredicate ty2 :@ Variable v2 :/\
      TyPredicate ty3 :@ Variable v3,
      Predicate p :@ Variable _a1 :@ Variable _a2 :@ Variable _a3 :<-> f] ->
      Type.Def p Type.Hole (Type.Abs v1 (Type.Const ty1) (Type.Abs v2 (Type.Const ty2) (Type.Abs v3 (Type.Const ty3) (transl f))))
    -- Translation of senary predicates
    [ TyPredicate ty1 :@ Variable v1 :/\ TyPredicate ty2 :@ Variable v2 :/\
      TyPredicate ty3 :@ Variable v3 :/\ TyPredicate ty4 :@ Variable v4 :/\
      TyPredicate ty5 :@ Variable v5 :/\ TyPredicate ty6 :@ Variable v6,
      Predicate p :@ Variable _a1 :@ Variable _a2 :@ Variable _a3 :@ Variable _a4 :@
      Variable _a5 :@ Variable _a6 :<-> f ] ->
        Type.Def p Type.Hole (Type.Abs v1 (Type.Const ty1) (Type.Abs v2 (Type.Const ty2) (Type.Abs v3 (Type.Const ty3) (Type.Abs v4 (Type.Const ty4) (Type.Abs v5 (Type.Const ty5) (Type.Abs v6 (Type.Const ty6)  (transl f)))))))
    -- Translation of septenary predicates
    [ TyPredicate ty1 :@ Variable v1 :/\ TyPredicate ty2 :@ Variable v2 :/\
      TyPredicate ty3 :@ Variable v3 :/\ TyPredicate ty4 :@ Variable v4 :/\
      TyPredicate ty5 :@ Variable v5 :/\ TyPredicate ty6 :@ Variable v6 :/\
      TyPredicate ty7 :@ Variable v7,
      Predicate p :@ Variable _a1 :@ Variable _a2 :@ Variable _a3 :@ Variable _a4 :@
      Variable _a5 :@ Variable _a6 :@ Variable _a7 :<-> f ] ->
        Type.Def p Type.Hole (Type.Abs v1 (Type.Const ty1) (Type.Abs v2 (Type.Const ty2) (Type.Abs v3 (Type.Const ty3) (Type.Abs v4 (Type.Const ty4) (Type.Abs v5 (Type.Const ty5) (Type.Abs v6 (Type.Const ty6) (Type.Abs v7 (Type.Const ty7) (transl f))))))))
    -- Translation of octonary predicates.
    [ TyPredicate ty1 :@ Variable v1 :/\ TyPredicate ty2 :@ Variable v2 :/\
      TyPredicate ty3 :@ Variable v3 :/\ TyPredicate ty4 :@ Variable v4 :/\
      TyPredicate ty5 :@ Variable v5 :/\ TyPredicate ty6 :@ Variable v6 :/\
      TyPredicate ty7 :@ Variable v7 :/\ TyPredicate ty8 :@ Variable v8,
      Predicate p :@ Variable _a1 :@ Variable _a2 :@ Variable _a3 :@ Variable _a4 :@
      Variable _a5 :@ Variable _a6 :@ Variable _a7 :@ Variable _a8 :<-> f ] ->
        Type.Def p Type.Hole (Type.Abs v1 (Type.Const ty1) (Type.Abs v2 (Type.Const ty2) (Type.Abs v3 (Type.Const ty3) (Type.Abs v4 (Type.Const ty4) (Type.Abs v5 (Type.Const ty5) (Type.Abs v6 (Type.Const ty6) (Type.Abs v7 (Type.Const ty7) (Type.Abs v8 (Type.Const ty8) (transl f)))))))))
    -- Translation of axiomatic ternary predicates (e.g. between-ness).
    [ TyPredicate ty1 :@ Variable _v1 :/\ TyPredicate ty2 :@ Variable _v2 :/\
      TyPredicate ty3 :@ Variable _v3,
      Predicate p :@ Variable _a1 :@ Variable _a2 :@ Variable _a3 :-> Top] ->
        Type.Axiom p (Type.Const ty1 --> Type.Const ty2 --> Type.Const ty3 --> Type.Const "Prop")
    -- translation of axiomatic quaternary predicates (e.g. congruence)
    [ TyPredicate ty1 :@ Variable _v1 :/\ TyPredicate ty2 :@ Variable _v2 :/\
      TyPredicate ty3 :@ Variable _v3 :/\ TyPredicate ty4 :@ Variable _v4,
      Predicate p :@ Variable _a1 :@ Variable _a2 :@ Variable _a3 :@
      Variable _a4 :-> Top] ->
        Type.Axiom p (Type.Const ty1 --> Type.Const ty2 --> Type.Const ty3 --> Type.Const ty4 --> Type.Const "Prop")
    -- Translations of simple hypotheses.
    [asm] -> Type.Axiom name (transl asm)
    -- Translations of hypotheses with typed variables.
    [typing, asm] ->
      Type.Axiom name (unrollConj typing (transl asm))
    _asms -> error "malformed typings in assumption"
    where
      name = if declared == "" then fallback else declared
  Conjecture declared asms conj -> case asms of
    [] -> Type.Theorem name (transl conj) Type.Omit
    [typing] -> Type.Theorem name (unrollConj typing (transl conj)) Type.Omit
    _asms -> error "malformed typings in assumption"
    where
      name = if declared == "" then fallback else declared

unrollConj :: Formula -> Type.Expr -> Type.Expr
unrollConj typing expr = case typing of
  -- These type assumptions nest left in the `-T` output for some reason.
  typing' :/\ (TyPredicate p :@ Variable v) ->
    let expr' = Type.All v (transl (Predicate p)) expr
    in unrollConj typing' expr'
  TyPredicate p :@ Variable v :/\ info@(Predicate _ :@ Variable v') ->
    if v == v'
      then Type.All v (transl (Predicate p)) (transl info --> expr)
      else error "typing and predconditions have differing variables"
  TyPredicate p :@ Variable v ->
    Type.All v (transl (Predicate p)) expr
  _badlyFormedTyping -> error "malformed typings in assumption"

makeConstructors :: [[Formula]] -> [Type.Constr]
makeConstructors = fmap makeConstructor

makeConstructor :: [Formula] -> Type.Constr
makeConstructor fs = case fs of
  -- Translation of constants.
  [ All _v ((Variable _v' :== Variable c) :-> TyPredicate ty :@ Variable _v'')] ->
    Type.Constr c (Type.Const ty)
  -- Translation of unary operations.
  [ TyPredicate ty :@ Variable _w,
    All _v ((Variable _v' :== (Const op :@ Variable _v'')) :-> (TyPredicate ty' :@ Variable _v'''))] ->
      Type.Constr op (Type.Const ty --> Type.Const ty')
  -- Translation of binary operations.
  [ TyPredicate ty :@ Variable _v :/\ TyPredicate ty' :@ Variable _w,
    All _b ((Variable _b' :== (Const op :@ Variable _v' :@ Variable _w')) :->
    TyPredicate ty'' :@ Variable _v'')] ->
    Type.Constr op (Type.Const ty --> Type.Const ty' --> Type.Const ty'')
  _fs -> error "malformed constructor"

transl :: Formula -> Type.Expr
transl expr = case expr of
    All v (TyPredicate p :@ Variable v' :/\ restConj :-> restImpl)
      -> if v == v'
            then Type.All v (transl (Predicate p)) (transl restConj --> transl restImpl)
            else transl expr
    All v (TyPredicate p :@ Variable v' :-> restImpl)
      -> if v == v'
            then Type.All v (transl (Predicate p)) (transl restImpl)
            else transl expr
    Exists v (TyPredicate p :@ Variable v' :/\ restConj)
      -> if v == v'
            then Type.Exists v (transl (Predicate p)) (transl restConj)
            else transl expr
    -- Chains of existence statements unfortunately group typing assumptions,
    -- so the require special handling.
    Exists v1 (Exists v2 (((TyPredicate ty1 :@ Variable v1') :/\ (TyPredicate ty2 :@ Variable v2')) :/\ restConj))
      -> if v1 == v1' && v2 == v2'
          then Type.Exists v1 (transl (Predicate ty1)) (Type.Exists v2 (transl (Predicate ty2)) (transl restConj))
          else error "mismatched variables in existential statement"
    Exists v0 (Exists v1 (Exists v2 ((((TyPredicate ty0 :@ Variable _v0') :/\ (TyPredicate ty1 :@ Variable _v1')) :/\ (TyPredicate ty2 :@ Variable _v2')) :/\ restConj)))
      -> Type.Exists v0 (transl (Predicate ty0)) (Type.Exists v1 (transl (Predicate ty1)) (Type.Exists v2 (transl (Predicate ty2)) (transl restConj)))
    Top         -> Type.Top
    Bot         -> Type.Bot
    Variable v  -> Type.Variable v
    All v f     -> Type.All v Type.Hole (transl f)
    Exists v f  -> Type.Exists v Type.Hole (transl f)
    Predicate t -> Type.Const t
    TyPredicate t -> Type.Const ("is" <> t)
    Const t     -> Type.Const t
    f1 :== f2   -> Type.Const "eq" <@> transl f1 <@> transl f2
    f1 :@ f2    -> transl f1 <@> transl f2
    f1 :/\ f2   -> transl f1 /\ transl f2
    f1 :\/ f2   -> transl f1 \/ transl f2
    f1 :-> f2   -> transl f1 --> transl f2
    f1 :<-> f2  -> (Type.:<->) (transl f1) (transl f2)
