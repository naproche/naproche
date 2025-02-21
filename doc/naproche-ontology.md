# The ontology of Naproche

## 1 Signature

```
SIGNATURE:

TYP = {
  "aClass(.)",        # Class
  "aSet(.)",          # Set
  "aMap(.)",          # Map
  "aFunction(.)",     # Function
  "aObject(.)",       # Object
  "aElementOf(.,.)"   # Element of a class
}
```

```
SIGNATURE:

FUN = {
  "Dom(.)",   # Domain
  ".(.)",     # Map application
  "(.,.)"     # Ordered pair
}
```

```
SIGNATURE:

REL = {
  ". -<- ."   # Induction
}
```


## 2 Ontological axioms

In this section we use expressions of the form `Γ ▶ φ` to denote that a term or
(atomic) formula `φ` is well-defined in a context `Γ`.


### 2.1 Types

```
AXIOM:

Γ ▶ aClass(x)
```

```
AXIOM:

Γ ▶ aSet(x)
```

```
AXIOM:

Γ ▶ aObject(x)
```

```
AXIOM:

Γ ▶ aFunction(x)
```

```
AXIOM:

Γ ▶ aMap(x)
```

```
AXIOM:

Γ ⊢ Class(X)
-------------------
Γ ▶ aElementOf(x,X)
```


### 2.2 Terms

```
AXIOM:

Γ ⊢ aMap(f)
-----------
Γ ▶ Dom(f)
```

```
AXIOM:

Γ ⊢ aMap(f)
Γ ⊢ aElementOf(x, Dom(f))
-------------------------
Γ ▶ f(x)
```

```
AXIOM:

Γ ⊢ aObject(x)
Γ ⊢ aObject(y)
--------------
Γ ▶ (x,y)
```


### 2.3 Predicates

```
AXIOM:

Γ ▶ x -<- y
```


## 3 Logical axioms

```
AXIOM (Function definition):

Γ ⊢ aFunction(f) ⟺ (aMap(f) ʌ aObject(f))
```

```
AXIOM (Set definition):

Γ ⊢ aSet(x) ⟺ (aClass(x) ʌ aObject(x))
```

```
AXIOM:

Γ ⊢ aElementOf(x,X)
-------------------
Γ ⊢ aObject(x)
```

```
AXIOM:

Γ ⊢ aClass(Dom(f))
```

```
AXIOM:

Γ ⊢ aObject((x,y))
```

```
AXIOM:

Γ ⊢ aObject(f(x))
```

```
AXIOM (Set extensionality):

Γ ⊢ aSet(X) ʌ aSet(Y)
---------------------------------------------------
Γ ⊢ ∀x(aElementOf(x,X) ⟺ aElementOf(x,Y)) ⟹ X = Y
```

```
AXIOM (Function extensionality):

Γ ⊢ aFunction(f) ʌ aFunction(g)
------------------------------------------------------------------------
Γ ⊢ (Dom(f) = Dom(g) ʌ ∀x(aElementOf(x,Dom(f)) ⟹ f(x) = g(x))) ⟹ f = g
```

```
AXIOM SCHEMA (Induction):

FORMULAS = {
  ψ₁(v₁),
  ...,
  ψₙ(v₁,...,vₙ),
  φ(v₁,...,vₙ)
}

TERMS = {
  t(v₁,...,vₙ)
}

Γ ⊢ ∀x₁ψ₁(x₁) ⟹ ... ⟹ ∀xₙψₙ(x₁,...,xₙ) ⟹ (InductionHypothesis :: ∀y₁ψ₁(y₁) ⟹  ... ⟹ ∀yₙψₙ(y₁,...,yₙ) ⟹ t(y₁,...,yₙ) -<- t(x₁,...,xₙ) ⟹ φ(y₁,...,yₙ)) ⟹ φ(x₁,...,xₙ)
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
Γ ⊢ ∀x₁ψ₁(x₁) ⟹ ... ⟹ ∀xₙψₙ(x₁,...,xₙ) ⟹ φ(x₁,...,xₙ)
```

As a special case we get the "usual" induction schema:

```
Γ ⊢ ∀x. (InductionHypothesis :: ∀y. y -<- x ⟹ φ(y)) ⟹ φ(x)
-------------------------------------------------------------
Γ ⊢ ∀x. φ(x)
```

Examples:

1.  Natural numbers induction:

    ```ftl
    Signature. A natural number is an object. Let n,m denote natural numbers
    Signature. 0 is a natural number.
    Signature. \Succ{n} is a natural number.

    Definition. A successor is a natural number n such that n = \Succ{m} for some m.

    Axiom. n = 0 or n is a successor.
    Axiom. n -<- \Succ{n}.

    Theorem. φ(n) for all n.
    Proof by induction on n.
      # Implicit assumption: ∀m. m -<- n ⟹ φ(m)
      # Show: φ(n)

      Case n = 0.
        # Show: φ(0)
      End.

      Case n is a successor.
        Consider some m such that n = \succ{m}.
        We have m -<- n.
        Thus φ(m).

        # Show: φ(\succ{m})
      End.
    Qed.
    ```

2.  Structural induction on untyped λ-terms:

    ```ftl
    Signature. A variable is an object. Let x denote variables.
    Signature. A term is an object. s,s',t denote terms.

    Signature. \app{s}{t}:TERM.
    Signature. \abs{x}{t}:TERM.

    Definition. An application term is a term t such that t = \app{s}{s'} for some s,s'.
    Definition. An abstraction term is a term t such that t = \abs{x}{s} for some x.

    Axiom. t is a variable or t is an application term or t is an abstraction term.
    Axiom. s,t -<- \app{s}{t}.
    Axiom. t -<- \abs{x}{t}.

    Theorem. φ(t) for all t.
    Proof by induction on t.
      # Implicit assumption: ∀s. s -<- t ⟹ φ(s)
      # Show: φ(t)

      Case t is a variable.
        # Show: φ(t)
      End.

      Case t is an application term.
        Consider some s,s' such that t = \app{s}{s'}.
        We have s,s' -<- t.
        Thus φ(s) and φ(s').

        # Show: φ(\app{s}{s'})
      End.

      Case t is an abstraction term.
        Consider some x,s such that t = \abs{x}{s}.
        We have s -<- t.
        Thus φ(s).

        # Show: φ(\abs{x}{s})
      End.
    Qed.
    ```

3.  Transfinite induction:

    ```ftl
    Signature. An ordinal number is an object. Let α,β denote ordinal numbers.

    Let A denote sets such that every element of A is an ordinal number.

    Signature. \Succ{α} is an ordinal number.
    Signature. \Limit{A} is an ordinal number.

    Definition. 0 = \Limit{∅}.

    Definition. A successor ordinal is an α such that α = \Succ{β} for some β.
    Definition. A limit ordinal is an α such that α = \Limit{A} for some nonempty A.

    Axiom. α = 0 or α is a successor ordinal or α is a limit ordinal.
    Axiom. α -<- \Succ{α}.
    Axiom. Let α \in A. Then α -<- \Limit{A}.
    ```

4.  ∈-induction:

    ```ftl
    Axiom. Let x be a set and y \in x. Then y -<- x.
    ```


## 4 Low-level definability

The formula image `φ` of any low-level definition must pass a proof task which
ensures the well-formedness of that definition. This proof task is denoted by
the expression `PROOF_TASK(φ)` which must be derived from the context `Γ` in
which the definition occurs. Thus the definition to which `φ` corresponds is
well-formed iff `Γ ⊢ PROOF_TASK(φ)`. Note that the derivability of the proof
task depends in general on the one hand on the syntax of `φ` and on the other
hand on the derivability of certain further proof tasks. In the following that
syntax condition is denoted by `φ ≡ Σ`, where `Σ` is a certain schema
representing a class of formulas. Such an expession can be read as "`φ` is
syntactically equivalent to an instance of `Σ`". For example `φ ≡ aClass(…) ∧ …`
expresses that `φ` is syntactically equal to a formula `aClass(t) ∧ ψ` for some
term `t` and some formula `ψ`.


### 4.1 General proof task

```
PROOF TASK:

φ ≡ aClass(...) ʌ ...
Γ ⊢ CLASS_TASK(φ)
---------------------
Γ ▷ φ
```

```
PROOF TASK:

φ ≡ aSet(...) ʌ ...
Γ ⊢ CLASS_TASK(φ)
-------------------
Γ ▷ φ
```

```
PROOF TASK:

φ ≡ aMap(...) ʌ ... ʌ ...
Γ ⊢ MAP_TASK(φ)
-------------------------
Γ ▷ φ
```


### 4.2 Class task

`{x₁, ..., xₙ}`:

```
PROOF TASK:

φ ≡ ... ʌ (∀x (... ⟺ (aObject(...) ʌ ...)))
--------------------------------------------
Γ ⊢ CLASS_TASK(φ)
```

`{t | ...}`:

```
PROOF TASK:

φ ≡ ... ʌ ∀x(... ⟺ (Replacement :: ...))
-----------------------------------------
Γ ⊢ CLASS_TASK(φ)
```

`{t in X | ...}`:

```
PROOF TASK:

φ ≡ ... ʌ ∀x(... ⟺ ...)
------------------------
Γ ⊢ CLASS_TASK(φ)
```


### 4.3 Map task

```
PROOF TASK:

φ ≡ ... ʌ ψ ʌ χ
Γ ⊢ (DomainTask :: DOMAIN_TASK(ψ)) ʌ (ChoiceTask :: CHOICE_TASK(χ)) ʌ (ExistenceTask :: EXISTENCE_TASK(χ)) ʌ (UniquenessTask :: UNIQUENESS_TASK(χ))
---------------------------------------------------------------------------------------------------------------------------------------------------
Γ ⊢ FUNCTION_TASK(φ)
```


### 4.4 Separation task

`{t in X | ...}`:

```
ψ(x) ≡ ... ʌ aElementOf(...,X) ʌ ...
Γ ⊢ aClass(X)
------------------------------------
Γ ⊢ SEPARATION_TASK(ψ(x))
```

```
ψ(x) ≡ aElementOf(...,X) ʌ ...
Γ ⊢ aSet(X)
------------------------------
Γ ⊢ SEPARATION_TASK(ψ(x))
```


### 4.5 Domain task

```
ψ ≡ Domain :: ∀x(... ⟺ χ(x))
Γ ⊢ SEPARATION_TASK(χ(x))
----------------------------------
Γ ⊢ (DomainTask :: DOMAIN_TASK(ψ))
```

```
ψ ≡ Domain :: ... = t
Γ ⊢ aClass(t)
----------------------------------
Γ ⊢ (DomainTask :: DOMAIN_TASK(ψ))
```


### 4.6 Choice task

A choice task is applied to a function in order to make sure that all choices
and definition within the function body are well-defined:

```-axiom
χ ≡ ∀x(… ⟶ ζ(x))
Γ ⊢ CHOICE_TASK(ζ(x))
––––––––––––––––––––––––––––––––
Γ ⊢ ChoiceTask :: CHOICE_TASK(χ)
```

1.  In case a function definition does not involve any `choose` or `define`
    operator the choice task of this definition is trivial:

    ```-axiom
    ζ(x) ≡ Evaluation :: f(x) = t(x,̄y)
    ––––––––––––––––––––––––––––––––––
    Γ ⊢ CHOICE_TASK(ζ(x))
    ```

2.  In case a function body is of the form `define …` a choice task ensures
    that the defined object indeed exists:

    ```-axiom
    ζ(x) ≡ ∃g((Defined :: η(g,x)) ∧ …)
    Γ ⊢ PROOF_TASK(η(g,x)))
    ––––––––––––––––––––––––––––––––––
    Γ ⊢ CHOICE_TASK(ζ(x))
    ```

3.  In case a function body is of the form `choose η(̄y) in t(x,̄y)` a choice
    task ensures that there indeed exist objects `y₁,…,yₙ` which satisfy `η`:

    ```-axiom
    ζ(x) ≡ ∃̄y(η(x,̄y) ∧ (Evaluation :: f(x) = t(x,̄y)))
    Γ ⊢ ∃̄yη(x,̄y))
    –––––––––––––––––––––––––––––––––––––––––––––––––
    Γ ⊢ CHOICE_TASK(ζ(x))
    ```

4.  In case a function body is of the form
    ```
    case ξ₁(x) -> η₁(x),
     ⋮
    case ξₙ(x) -> ηₙ(x)
    ```
    a choice task is applied to each `ηᵢ` under the assumption that `ξᵢ`
    holds:

    ```-axiom
    ζ(x) ≡ (Condition :: (ξ₁(x) ⟶ η₁(x))) ∧ … ∧ (Condition :: (ξₙ(x) ⟶ ηₙ(x)))))
    Γ ⊢ ⋀ᵢ(ξᵢ(x) ⟶ CHOICE_TASK(ηᵢ(x)))
    ––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––
    Γ ⊢ CHOICE_TASK(ζ(x))
    ```


### 4.7 Existence task

```-axiom
χ ≡ ∀x(… ⟶ ζ(x))
Γ ⊢ EXISTENCE_TASK(ζ(x))
––––––––––––––––––––––––––––––––––––––
Γ ⊢ ExistenceTask :: EXISTENCE_TASK(χ)
```

1.  In case a function body is of the form `f(x) = t(x)` an existence task
    ensures that `t(x)` indeed exists (?):

    ```-axiom
    ζ(x) ≡ Evaluation :: f(x) = t(x)
    Γ ⊢ ∃z(z = t(x))
    ––––––––––––––––––––––––––––––––
    Γ ⊢ EXISTENCE_TASK(ζ(x))
    ```

2.  In case a function body is of the form `define …` an existence task
    ensures there the defined object indeed exists (?):

    ```-axiom
    ζ(x) ≡ ∃g((Defined :: η(g,x)) ∧ …)
    Γ ⊢ ∃z((Defined :: η(g,x)) ⟶ z = g)
    ––––––––––––––––––––––––––––––––––––
    Γ ⊢ EXISTENCE_TASK(ζ(x))
    ```

3.  In case a function body is of the form `choose η(̄y) in t(x,̄y)` an
    existence task ensures that there indeed exist objects `y₁,…,yₙ` which
    satisfy `η` (?):

    ```-axiom
    ζ(x) ≡ ∃̄y(η(x,̄y) ∧ (Evaluation :: f(x) = t(x,̄y)))
    Γ ⊢ ∃z(η(x,̄y) ⟶ z = t(x,̄y))
    –––––––––––––––––––––––––––––––––––––––––––––––––
    Γ ⊢ EXISTENCE_TASK(ζ(x))
    ```

4.  In case a function body is of the form
    ```
    case ξ₁(x) -> η₁(x),
     ⋮
    case ξₙ(x) -> ηₙ(x)
    ```
    an existence task is applied to each `ηᵢ` under the assumption that `ξᵢ`
    holds (?):

    ```-axiom
    ζ(x) ≡ (Condition :: (ξ₁(x) ⟶ η₁(x))) ∧ … ∧ (Condition :: (ξₙ(x) ⟶ ηₙ(x)))))
    Γ ⊢ ∃z(⋁ᵢ(ξᵢ(x) ⟶ (ηᵢ(x) ⟶ tᵢ(x,̄y))))
    ––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––
    Γ ⊢ EXISTENCE_TASK(ζ(x))
    ```

    Here `tᵢ(x,̄y)` is the RHS of the part of the function definition tagged
    with `Evaluation` with can contain some free variables `̄y` in case choices
    are involved in the function's definition in the `i`-th case.


### 4.8 Uniqueness task

```-axiom
χ ≡ ∀x(… ⟶ ζ(x))
Γ ⊢ UNIQUENESS_TASK(ζ(x))
––––––––––––––––––––––––––––––––––––––––
Γ ⊢ UniquenessTask :: UNIQUENESS_TASK(χ)
```

1.  In case a function body is of the form `f(x) = t(x)` a uniqueness task is
    trivial:

    ```-axiom
    ζ(x) ≡ Evaluation :: f(x) = t(x)
    Γ ⊢ ∀z,z'((z = t(x) ∧ z' = t(x)) ⟶ z = z')
    –––––––––––––––––––––––––––––––––––––––––––
    Γ ⊢ UNIQUENESS_TASK(ζ(x))
    ```

2.  In case a function body is of the form `define …` a uniqueness task is
    trivial:

    ```-axiom
    ζ(x) ≡ ∃g((Defined :: …) ∧ …)
    Γ ⊢ ∀z,z'((z = g ∧ z' = g) ⟶ z = z')
    –––––––––––––––––––––––––––––––––––––
    Γ ⊢ UNIQUENESS_TASK(ζ(x))
    ```

3.  In case a function body is of the form `choose η(̄y) in t(x,̄y)` a
    uniqueness task is trivial:

    ```-axiom
    ζ(x) ≡ ∃̄y(η(x,̄y) ∧ (Evaluation :: f(x) = t(x,̄y)))
    Γ ⊢ ∀z,z'((z = t(x,̄y) ∧ z' = t(x,̄y)) ⟶ z = z')
    –––––––––––––––––––––––––––––––––––––––––––––––––
    Γ ⊢ UNIQUENESS_TASK(ζ(x))
    ```

4.  In case a function body is of the form
    ```
    case ξ₁(x) -> η₁(x),
     ⋮
    case ξₙ(x) -> ηₙ(x)
    ```
    a uniqueness task ensures that the evaluation of the function does not
    yield two (or more) different values when two (or more) of the cases `ξᵢ`
    overlap:

    ```-axiom
    ζ(x) ≡ (Condition :: (ξ₁(x) ⟶ η₁(x))) ∧ … ∧ (Condition :: (ξₙ(x) ⟶ ηₙ(x)))))
    Γ ⊢ ∀z,z'((⋁ᵢ(ξᵢ(x) ∧ ηᵢ(x,̄y) ∧ z = tᵢ(x,̄y)) ∧ ⋁ᵢ(ξᵢ(x) ∧ ηᵢ(x,̄y) ∧ z' = t₁(x,̄y))) ⟶ z = z')
    ––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––
    Γ ⊢ UNIQUENESS_TASK(ζ(x))
    ```

    Here `tᵢ(x,̄y)` is the RHS of the part of the function definition tagged
    with `Evaluation` with can contain some free variables `̄y` in case choices
    are involved in the function's definition in the `i`-th case.
