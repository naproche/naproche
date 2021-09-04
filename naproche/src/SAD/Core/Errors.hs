{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}

-- | Store all errors and their rendering in one place
-- to make the type-checking code look friendlier.

module SAD.Core.Errors where

import Data.Set (Set)
import Data.Text.Prettyprint.Doc
import SAD.Data.SourcePos (SourcePos, noSourcePos)
import SAD.Core.AST
import SAD.Data.Identifier
import SAD.Data.Formula (Formula)
import SAD.Data.Text.Block (Block)
import Data.Sequence (Seq)

data TransformError = TransformError
  { transformErrorLocation :: TransformErrorLocation
  , transformErrorMessage :: TransformErrorMessage
  } deriving (Eq, Ord, Show)

instance Pretty TransformError where
  pretty (TransformError loc m)
    = pretty loc <> "I encountered the error: " <> pretty m

data TypeError = TypeError
  { typeErrorLocation :: TypeErrorLocation
  , typeErrorMessage :: TypeErrorMessage
  } deriving (Eq, Ord, Show)

type TypeErrors = Seq TypeError

instance Pretty TypeError where
  pretty (TypeError loc m)
    = pretty loc <> "I encountered the error: " <> pretty m

data ErrorLocation b f = ErrorLocation
  { errorBlock :: Maybe b
  , errorFormula :: Maybe f
  , errorPosition :: SourcePos
  } deriving (Eq, Ord, Show)

type TransformErrorLocation = ErrorLocation Block Formula
type TypeErrorLocation = ErrorLocation Stmt Term

instance Pretty (ErrorLocation Block Formula) where
  pretty (ErrorLocation b f p)
    = "[" <> pretty (show p) <> "]" <> line
    <> case b of Just b' -> "While checking: " <> line <> pretty (show b') <> line; Nothing -> ""
    <> case f of Just f' -> "more specifically the term: "<> line <> pretty (show f') <> line; Nothing -> ""

instance Pretty (ErrorLocation Stmt Term) where
  pretty (ErrorLocation b f p)
    = "[" <> pretty (show p) <> "]" <> line
    <> case b of Just b' -> "While checking: " <> line <> pretty b' <> line <> line; Nothing -> ""
    <> case f of Just f' -> "more specifically the term: "<> line <> pretty f' <> line <> line; Nothing -> ""

noLocation :: ErrorLocation b f
noLocation = ErrorLocation Nothing Nothing noSourcePos 

data TransformErrorMessage
  = DuplicateForallBind (Ident, Set InType) (Ident, Set InType)
  | FunDefUnboundVariable Identifier Ident
  | FunDefTermNotVariable Identifier Term
  | CoercionsBetweenNonNotions
  | CoercionFromNotUnique [InType]
  | CoercionFromNotProvided
  | CoercionToNotUnique [InType]
  | CoercionToNotProvided
  | MalformedTypeDecl NFTerm
  | MalformedSignatureDecl NFTerm
  | OverloadedNotion Identifier
  deriving (Eq, Ord, Show)

instance Pretty TransformErrorMessage where
  pretty (DuplicateForallBind x y)
    = "Two variables with the same name were bound: " <> pretty x <> " and " <> pretty y
  pretty (FunDefUnboundVariable name v)
    = "In a definition for " <> pretty name
        <> ", the variable " <> pretty v <> " was found to be unbound."
  pretty (FunDefTermNotVariable name e)
    = "In a definition for " <> pretty name
        <> ", I expected a variable, but got:\n" <> pretty e
  pretty CoercionsBetweenNonNotions
    = "Coercions may only be formed between notions"
  pretty (CoercionFromNotUnique xs)
    = "The 'from' side of the coercion must have a unique type, but there are several: " <> pretty xs
  pretty CoercionFromNotProvided
    = "The type of the 'from' side of the coercion was not provided."
  pretty (CoercionToNotUnique xs)
    = "The 'to' side of the coercion must have a unique type, but there are several: " <> pretty xs
  pretty CoercionToNotProvided
    = "The type of the 'to' side of the coercion was not provided."
  pretty (MalformedTypeDecl nf)
    = "The type declaration was malformed: " <> pretty nf
  pretty (MalformedSignatureDecl nf)
    = "The signature definition was malformed: " <> pretty nf
  pretty (OverloadedNotion i)
    = "There are multiple definitions for the notion: " <> pretty i

data TypeErrorMessage
  = ResolveFailed Identifier Type
  | ResolveAmbigous Identifier Type [Type]
  | WfTermTypeOfVarNotGiven Ident
  | WrongReturnValue OutType ReturnValue
  | CouldntInferTypeOf Ident
  | SortInTerm Ident
  | PropAsArgOf Identifier
  | WrongNumberOfArgumentsFor Ident
  | NoCoercionFound Int Ident (Set InType) (Set InType)
  | ForallOfValue Ident
  | ExistsOfValue Ident
  | ClassOfValue Ident
  | PropInFiniteClass
  | FiniteClassOfNonObjects Term (Set InType)
  | FiniteClassNoLeastGeneral Term [[Set InType]]
  | ClassOfNonObjects Term (Set InType)
  | InClassIsProp
  | InClassIsNotClass (Maybe Term) (Set InType)
  | VarAppliedTo Ident [Term]
  | UnknownFunction Identifier
  | PropInEquality Term Term
  | NonCoercibleEquality Term (Set InType) Term (Set InType)
  | IntroNotApplicable Ident Prf Term
  | AssumptionNotApplicable Term Term
  | DefinitionWronglyTyped Ident (Set InType) (Set InType)
  | EmptyCases
  deriving (Eq, Ord, Show)

instance Pretty TypeErrorMessage where
  pretty (ResolveFailed name typ)
    = "Couldn't resolve " <> pretty name <> " of type " <> pretty typ
  pretty (ResolveAmbigous name typ xs)
    = "Resolve ambigous: " <> pretty name <> " of type\n  " <> nest 2 (pretty typ)
        <> "\ncan be resolved as any of:\n  " <> nest 2 (vsep (map pretty xs))
  pretty (WfTermTypeOfVarNotGiven i) 
    = "Type of variable " <> pretty i <> " not given for wf-term."
  pretty (WrongReturnValue o retval)
    = "The term has type " <> pretty o <> " but was expected to return a " <> pretty (show retval)
  pretty (CouldntInferTypeOf v)
    = "Couldn't infer type of " <> pretty v
  pretty (SortInTerm name)
    = "Sort in a term: " <> pretty name
  pretty (PropAsArgOf name)
    = "A truth value cannot be passed to a function!"
  pretty (WrongNumberOfArgumentsFor name)
    = "The number of arguments passed to " <> pretty name <> " is wrong!"
  pretty (NoCoercionFound i name exp have)
    = "The " <> pretty i <> th i <> " argument of "
        <> pretty name <> " could not be coerced into the correct type!\n"
        <> pretty name <> " expects: " <> pretty exp
        <> " but we got: " <> pretty have
  pretty (ForallOfValue v)
    = "Read ∀" <> pretty v <> " _ and expected a proposition but got a value!"
  pretty (ExistsOfValue v)
    = "Read ∃" <> pretty v <> " _ and expected a proposition but got a value!"
  pretty (ClassOfValue v)
    = "Read {" <> pretty v <> " | _ } and expected a proposition but got a value!"
  pretty PropInFiniteClass
    = "Propositions are not allowed in finite class syntax!"
  pretty (FiniteClassOfNonObjects cls tt)
    = "The finite class: " <> pretty cls 
        <> "\n contains elements of type " <> pretty tt <> " but those can't be coerced to objects!"
  pretty (FiniteClassNoLeastGeneral cls ts)
    = "Finite class " <> pretty cls <> " contains elements which are of different types\n"
        <> "and a least general one couldn't be found among: " <> pretty ts
  pretty (ClassOfNonObjects cls tt)
    = "The class: " <> pretty cls 
        <> "\n contains elements of type " <> pretty tt <> " but those can't be coerced to objects!"
  pretty InClassIsProp
    = "Prop can't be used as 'in' class."
  pretty (InClassIsNotClass incls tt)
    = "The " <> pretty tt <> " given as " <> pretty incls 
        <> " can't be coerced into a class despite being used as an 'in' term."
  pretty (VarAppliedTo v t)
    = pretty v <> " is a variable but is was applied to " <> pretty t
  pretty (UnknownFunction name)
    = "Unknown function: " <> pretty name
  pretty (PropInEquality a b)
    = "Proposition in equality: " <> pretty (App Eq [a, b])
  pretty (NonCoercibleEquality a ia b ib)
    = "Can't coerce one side of equality into the other: " <> pretty (App Eq [a, b]) <> line
        <> pretty a <> " : " <> pretty ia <> line
        <> pretty b <> " : " <> pretty ib
  pretty (IntroNotApplicable i t goal)
    = "Malformed Intro(" <> pretty i <> ", " <> pretty t
        <> ") could not be applied to goal: " <> pretty goal
  pretty (AssumptionNotApplicable as goal)
    = "Couldn't introduce the assumption " <> pretty as
        <> " for the goal: " <> pretty goal
  pretty (DefinitionWronglyTyped x given inferred)
    = "In a tactic definition of " <> pretty x <> " the type " <> pretty given
        <> " was given but we inferred it has type " <> pretty inferred
  pretty EmptyCases
    = "Cases must contain tactics!"

th :: Int -> Doc ann
th 1 = "st"; th 21 = "st"; th 31 = "st"
th 2 = "nd"; th 22 = "nd"; th 32 = "nd"
th _ = "th"