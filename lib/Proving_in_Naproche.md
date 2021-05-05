# Proving in Naproche

Naproche is a proof system that accepts a version of natural language as input and produces proof obligations
from it that is checked by an external automatic theorem prover (ATP) like `eprover`.
It uses [typed first order logic](http://users.cecs.anu.edu.au/~baumgart/publications/TFFArith.pdf) with automatic inference of coercions.
This document describes the structure of a Naproche proof. The syntax (called `ForTheL`) is best learned through experience:
examples can be found in the `lib/examples` directory.
Naproche supports both an `ftl` mode of plain text and a `tex` mode where ForTheL blocks are embedded in a regular (La)TeX document.
Using the `tex` mode is recommended.

## Toplevel structure

A Naproche text consists of top-level statements and blocks like `axiom, lemma, signature`.
Top-level statements are only used for convenience in the parser and allow you to import new
files with `[readtex file.ftl.tex]` or `[read file.ftl]`, introduce the types of variables
`Let x,y be objects.` and define aliases `Let .. stand for ..`.

When reading a file, Naproche will import all signatures, definitions, axioms
and *named* claims. It will not import top-level aliases and unnamed claims.
This can help with big formalizations that span multiple files.

There are the following top-level blocks:

 -  `signature`s introduce a new type, predicate or function; the latter two without a body.
    Introducing `natural number` as a type:
    ```latex
    \begin{signature}
      A natural number is an object.
    \end{signature}
    ```
    This will also add a coercion (see below) to `object`.
    If you don't want a coercion you can write `notion` in the place of `object`.

    Introducing a new predicate without a body:
    ```latex
    \begin{signature}[Prime]
      $a$ is prime is an atom.
    \end{signature}
    ```

    Introducing a new function without a body:
    ```latex
    \begin{signature}
        Assume $x$ is a square.
        $\Swap{x}$ is a square.
    \end{signature}
    ```

 -  `definition` introduces a predicate or function definition:
    ```latex
    \begin{definition}
        Let $F$ be a function.
        Let $A,B$ be sets.
        $F : A \to B$ iff $\Dom{F} = A$ and
        $F(x)$ is an element of $B$ for all elements $x$ of $A$.
    \end{definition}
    ```
    This will create a new predicate `. : . \to .` with three explicit arguments.
    A definition may also have assumptions and may use variables in them that are
    not used as explicit arguments. These variables become implicit variables then
    and are represented by curly brackets in the output.

 -  `axiom`s are statements that we assume are true.

 -  `lemma`, `corollary`, `theorem` are statements that need to be proven.
    If they are followed by a `proof` block, Naproche will use the tactics (see below)
    to prove the claim. Else Naproche will give the problem to an ATP like `eprover`
    and tell you if the claim could be shown or not.

## Type system

Every variable in Naproche has an associated `type`. Possible types are introduced by signatures.
When you define a term `X(a, b)`, Naproche will consider the types
of the variables `a,b` during definition and check that they match the types of `c,d` when using `X(c,d)`.
Here, we allow *coercions* that were defined before like `Every natural number is a rational number`.
That means that if you define an addition `+` on rationals it will also work with natural numbers
(but the result of `n + m` is then always a rational number!).
Advanced coersions that depend on several conditions to hold (e.g. `Every integer that is non-negative is a natural number`)
can not be inferred automatically (though this may change in the future).

It is also possible to define functions with the same name several times. For example, we might
add an addition `+` for natural numbers as well so that `n + m` is a natural number.
Now Naproche will try to find out which addition you meant: It will find the types of the arguments
and then choose the *least-general* function that matches these.
For example: For rationals `p,q` and natural numbers `n,m` Naproche will choose:

  - `n + q`, `p + m`, `p + q` -> rational addition
  - `n + m` -> natural addition

It is even possible to check two variables of different types for equality: We can write `p = n`.
But to make this less surprising we demand that at least one side of the equality can be coerced
to the type of the other. When we write `p = n` we are therefore checking the equality in the type
of the rational numbers of `p` and `rationalNumberFromNaturalNumber(n)`. We also add the injectivity
of coercions as an axiom so that `n = p` and `m = p` implies `n = m`.

## Set Theory

Naproche uses von Neumann-Bernays-Gödel set theory, which you can access by including `prelude.ftl.tex`,
or for a more complete formalization `nbg.ftl.tex`.
The axiom of class comprehension is built-in: Any use of the syntax `z = { x | f(x) }` will be 
translated as `∀x in(x, z) iff f(x)`.
There are two special syntactic forms: `{a,b,c}` will create *set* of three elements `a,b,c`
and `{x "in" M | f(x)}` will create a sub-collection of the same type as `M`.
You can assert that `x` is an element of a class `C` by writing `x is an element of C`. For this,
however, `x` needs to be coercible to the type object. Sets are coercible to object, but classes
are obviously not.

Crucially this is also used for induction in the new version. While Naproche had a primitve for
induction built-in for a long time, this version instead champions an approach based on classes:
For example, the induction principle over the natural numbers looks like this:
`∀ [c : class] 0 \in c and (∀ [n : nat] n \in c implies (n + 1) \in c) \implies (∀ [n : nat] n \in c)`.

## Proofs and Tactics

A proof block in Naproche will consist of several *tactics*. There are a few useful tactics implemented in Naproche:

First, you can state a claim `h` which will then by proven by the ATP and afterwards be added as a hypothesis.
This is especially useful if the proof contains several big steps which you would like to guide the ATP through.
It is possible to add a term `(by thm1)` at the end of the claim. Then we will instruct the ATP to consider this
`thm1` as important. That is useful if `thm1` as very dissimilar (in terms of occurring terms in this theorem)
from the claim and will thus likely not be chosen by the heuristics in the ATP. You can often find more information
about the heuristic in the ATPs manual.

Second, you can write `Take a natural number n such that ..` to prove that there is a natural number
that fulfills `..` and use it in the rest of the text.

Third, you can write `Define S = ..` to define `S` to be an expression.

Fourth, you can write `Case c1. .. end. Case c2. .. end.` to handle the first
the case that `c1` holds and then the case that `c2` holds. In the end, Naproche
will try to prove that `c1 or c2` holds.

Fifth, you can write `Assume the contrary.` to start a proof by contradiction.
This will take the negation of the claim as a hypothesis and set `false` as the current goal.
You should always use this if you intend to do a proof by contradiction,
since otherwise Naproche will complain that you are using Contradictory Axioms!