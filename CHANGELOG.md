# Changelog

A complete listing of all changes on Naproche since naproche-20211211 (Isabelle
2021-1)

**NOTE:** In the following, "FTL" and "TEX" refer to the ASCII and the TeX
dialect of ForTheL, respectively.


--------------------------------------------------------------------------------

## Current development version

### Changes on the example files

  * **Changed:** Preliminary files like `preliminaries.ftl(.tex)` or
    `macros.ftl(.tex)` have been moved to `examples/preliminaries/`

  * **New:** New formalization of Hilbert's Paradox.

  * **Changed:** Paradoxes have been moved to `examples/paradoxes/` which
    constitutes an sTeX archive.

  * **Changed:** Puzzles have been moved to `examples/puzzles/` which
    constitutes an sTeX archive.

  * **Changed:** Style files have been moved from `lib/tex/` to
    `examples/meta-inf/lib` to facilitate their usage with sTeX.

  * **New:** Common Bibtex file `examples/meta-inf/lib/references.bib` for all
    example files.


### Changes on ForTheL

  * **Changed:** The following keywords are no longer allowed as variable names
    to avoid certain ambiguity errors:

    `is`, `be`, `are`, `does`, `do`, `has`, `have`, `that`, `with`, `of`,
    `having`, `such`, `so`, `if`, `iff`, `when`, `and`, `or`

--------------------------------------------------------------------------------

## naproche-20230902 (Isabelle 2023)

### Changes on the example files

  * **New:** New formalization of Wiedijk's "100 Theorems" (`100_theorems.ftl.tex`)

  * **New:** Naproche's built-in separation principle was added to `axioms.ftl`
    and `axioms.ftl.tex`.

  * **New:** New chapter about cardinality in the arithmetic library.

--------------------------------------------------------------------------------

## naproche-20221024 (Isabelle 2022)

### Changes on ForTheL

  * **Changed:** The old syntax `Define f((x,y)) = ...` for low-level map
    definitions with two arguments is replaced by `Define f(x,y) = ...`.    

  * **New:** (TEX) Unnumbered top-level environments are now supported via

    ```
    \begin{<environment-name>*}
      ...
    \end{<environment-name>*}
    ```

    where `<environment-name>` is one of the usual top-level environment names,
    e.g. `theorem` or `definition`.

    **Deprecation notice:** This change makes the option `unnumbered` of the
    LaTeX package `naproche` obsolete.

  * **New:** In low-level definitions `choose` and `define` terms can now be
    enclosed within ``` `` ``` and `''`, e.g.:

    ```
    Define $f(n) =$ ``choose a prime $p$ greater than $n$ in $p^{2}$'' for $n \in \Nat$.
    ```

  * **New:** To label a top-level section you can now use `\printlabel{...}`
    instead of `\label{...}` if you want the label to be printed in the PDF.
    `\printlabel` behaves exactly as `\label` (apart from the fact that its
    label is printed); in particular you can use it in conjunction with `\ref`
    or other referencing commands.

  * **New:** To reference top-level sections you can now use `\cref` besides
    `\ref` and `\nameref`.

  * **New:** (TEX) `\left`, `\middle` and `\right` are tokenized away.

  * **Changed:** (TEX) Primitive expressions inherited from FTL (e.g. `!=` or
    `-<-`) are no longer provided.

  * **Changed:** (TEX) A proof method for proofs of top-level theorems is
    now given via `\begin{proof}[by <method>]` instead of
    `\begin{proof} Proof by <method>.`.

  * **Fixed:** (TEX) `#` is a regular character now.


### Changes on the ontology of Naproche

  * **Fixed:** The translation of low-level function definitions now ensures
    that the arguments of defined functions are objects. This is in particular
    important when the function is given two parameters which are considered as
    an ordered pair whose entries must always be objects.


### Changes on the example files

  * **New:** `zermelo.ftl.tex`, a formalization of Zermelo's well-ordering
    theorem.

  * **Changed:** The set theory library (now stored at `examples/foundations`)
    was completely rewritten to provides better support for classes.
    Moreover, the paths of the source files of all chapters and the labels of
    any definitions, theorems etc. are now displayed in the PDF, making
    importing and referencing a bit easier.

  * **New:** A new library on set theory (stored at `examples/set-theory`).

  * **New:** The formalizations of König's theorem (`koenig.ftl(.tex)`) and
    Hausdorff's theorem (`hausdorff.ftl(.tex)`, formerly
    `regular_successor.ftl(.tex)`) are back!

  * **New:** New file `paradoxes.ftl.tex` which contains formalizations about
    some famous paradoxes. (Note that Russell's paradox was moved to this
    collection.)

  * **New:** New files `axioms.ftl` and `axioms.ftl.tex` that list Naproche's
    built-in axioms.

  * **New:** The arithmetic library was connected to the foundations library to
    provide more robust definitions of the arithmetical operations it provides.
    Moreover, the paths of the source files of all chapters and the labels of
    any definitions, theorems etc. are now displayed in the PDF, making
    importing and referencing a bit easier.

--------------------------------------------------------------------------------

## naproche-20211211 (Isabelle 2021-1)

### Changes on the ontology of Naproche

  * **New:** `collection` is a new synonym for `class`.

  * **Changed:** `object` (together with its new synonyms `element` and
    `mathematical object`) is a proper notion now and does not undergo an
    "object elimination" process during parsing.

  * **New:** New built-in notion `map`.

  * **Removed:** The built-in predicate `setsized`.

  * **Changed:** New well-definedness conditions:

      - An expression of the form `Dom(f)` is only well-defined if `aMap(f)` can
        be derived.
      - An expression of the form `f(x)` is only well-defined if `aMap(f)` and
        `aElementOf(x,Dom(f))` can be derived.
      - An expression of the form `(x,y)` is only well-defined if `aObject(x)`
        and `aObject(y)` can be derived.

  * **New:** The following axioms are hard-coded into Naproche:

      - Functions are maps which are objects:
        ```
        Γ ⊢ aFunction(f) ⟷ (aMap(f) ∧ aObject(f))
        ```

      - Sets are classes which are objects:
        ```
        Γ ⊢ aSet(x) ⟷ (aClass(x) ∧ aObject(x))
        ```

      - Elements of classes are objects:
        ```
        (Γ ⊢ aElementOf(x,X)) ⟹ (Γ ⊢ aObject(x))
        ```

      - Domains are classes:
        ```
        Γ ⊢ aClass(Dom(f))
        ```

      - Ordered pairs are objects:
        ```
        Γ ⊢ aObject((x,y))
        ```

      - Values of maps are objects:
        ```
        Γ ⊢ aObject(f(x))
        ```

      * Class extensionality:
        ```
        (Γ ⊢ aClass(X) ∧ aClass(Y)) ⟹ (Γ ⊢ ∀x(aElementOf(x,X) ⟷ aElementOf(x,Y)) ⟶ X = Y)
        ```

      * Map extensionality:
        ```
        (Γ ⊢ aMap(f) ∧ aMap(g)) ⟹ (Γ ⊢ (Dom(f) = Dom(g) ∧ ∀x(aElementOf(x,Dom(f)) ⟶ f(x) = g(x))) ⟶ f = g)
        ```

    Note that set and function extensionality are still built-in.

  * **Changed:** Low-level function definitions (now better called "low-level
    map definitions") define maps instead of functions.

  * **Changed:** Equality for class terms is restricted to objects, i.e.
    `X = {y | P(y)}` means `∀u(aObject(u) ⟶ (aElementOf(u,X) ⟷ P(u)))` and
    `{x | P(x)} = {y | Q(y)}` means `∀u(aObject(u) ⟶ (P(u) ⟷ Q(u)))`.

  * **Changed:** Low-level class definitions do not produce any proof tasks.

  * **Fixed:** Enumerative class terms (e.g. such of the form `{x_1, ..., x_n}`)
    throwing errors when used in low-level class and map definitions.


### Changes on ForTheL

  * **New:** (TEX) Top-level sections can now be labeled with the `\label{...}`
    command.
    There are now four ways the header of a top-level section can look like:

      - **Name and identifier:**
        ```
        \begin{...}[<name>]\label{<identifier>}
        ```
        `<name>` is the section's name as it appears in the PDF generated by
        LaTeX.
        It has no semantic meaning for Naproche and can contain any arbitrary
        character.
        `<identifier>` is the label of the section which can be referred to in
        proofs, e.g. via `(by <identifier>)`, and must not contain any other
        characters than letters, digits, spaces and `_`.

      - **Identifier only:**
        ```
        \begin{...}\label{<identifier>}
        ```
        The same as in _Name and identifier_ but without a name.

      - **Name only:**
        ```
        \begin{...}[<name>]
        ```
        In this case `<name>` takes the role of the label of the section.
        Its behaviour and syntax conditions are the same as those of
        `<identifier>` in _Name and identifier_.

      - **Neither identifier nor name:**
        ```
        \begin{...}
        ```
        Just a top-level section without name and label.

  * **New:** (TEX) References to named assertions now support LaTeX's
    `\ref{...}` and `\nameref{...}` commands.
    I.e. you can now refer to an assertion also via `(by \ref{<identifier>})` or
    `(by \nameref{<identifier>})` besides `(by <identifier>)`, where
    `<identifier>` is the assertion's label.

  * **New:** (TEX) Arguments of argument instructions can be wrapped in
    `\path{...}`, e.g. `[read \path{some/forthel/text.ftl}]`

  * **New:** (TEX) An alternative syntax for class terms is available now:
    `\class{... | ...}`.
    In Naproche it behaves exactly as the common `\{ ... \mid ... \}` notation,
    but in LaTeX (when using the style file `naproche.sty`) it provides
    additional support for flexible sizes of the braces and the vertical bar.

  * **New:** (TEX) Expressions of the following kinds can be enclosed within
    `\text{...}`:

      - Function bodies, e.g.:
        ```
        Define $f(x) = \text{choose an integer $n$ such that $x = [n]$ in $[n + 1]$}$ for $x \in \mathbb{Z}_{4}$.
        ```

      - The LHS and RHS of class terms, e.g.:
        ```
        \{ p \mid \text{$p$ is a prime number such that $p + 2$ is prime} \}
        ```
        ```
        \class{x | \text{$x$ is a set such that $x \notin x$}}
        ```
      - The content of parenthesized statements in symbolic formulas, e.g.:
        ```
        y \in \bigcup x \iff (\text{$y$ is contained in some element of $x$})
        ```

  * **New:** The RHS of a class term constructed via `\class{... | ...}` can be
    enclosed within `\classtext{...}`.
    When using the style file `naproche.sty`, `\classtext{...}` behaves like
    `\text{...}` but supports automatic line breaks within the class term.
    Example:

    ```
    \class{p | \classtext{$p$ is a prime number such that $2 < p$ and $p$ is a divisor of some natural number that is less or equal than $5^{2}$}}
    ```

  * **New:** `the collection of` as an alternative to the expression `the class
    of`.
    Moreover, both of them can be followed by an optional `all`.
    I.e. for instance the following formulations are accepted now:

      - `the collection of sets`
      - `the collection of all prime numbers`
      - `the class of subsets of x`
      - `the class of all sets x such that x is not an element of x`

  * **New:** (TEX) `\[` and `\]` are a new kind of whitetokens, i.e. like
    `$` they are completely ignored by Naproche.

  * **Changed:** `_` and `"` are regular characters now, i.e. they are treated
    like any other (ASCII) symbol.

  * **Changed:** Notion separation in descriptive class terms (e.g. something
    like `{set x | ...}`) is no longer supported.

  * **New:** (TEX) In case splits in low-level map definitions the function
    value and the case condition can be separated by an optional `:`, e.g.:
    ```
    Define \[ f(x) =
    \begin{cases}
      \bigcap x & : \text{x is nonempty}
      \emptyset & : \text{x is empty}
    \end{cases} \]
    for $x in X$.
    ```


### Changes on the example files

  * **New:** Additional example files in `examples`:

      - `arithmetic`:
        Basic Peano arithmetic
      - `set-theory`:
        Basic set theory        
      - `agatha.ftl.tex`, `dwarfs.ftl`, `dwarfs.ftl.tex`:
        Some logic puzzles
      - `cantor-schroeder-bernstein.ftl.tex`:
        The Cantor-Schröder-Bernstein theorem
      - `group.lean.ftl.tex`:
        Naproche rendering of a Lean file on groups
      - `hilbert-calculus.ftl`, `hilber-calculus.ftl.tex`:
        Derivations in a Hilbert calculus
      - `numbers.ftl.tex`:
        Number systems for Rudin's Principles of Mathematical Analysis
      - `russell.ftl`, `russell.ftl.tex`:
        Russell's paradox

  * **New:** New technical files on which some examples are based:

      - `classes.ftl`:
        Basic notions about classes.
      - `macros.ftl`, `macros.ftl.tex`:
        Collections of commonly used synonyms for notions hard-coded into
        Naproche.
      - `preliminaries.ftl`, `preliminaries.ftl.tex`:
        Basic notions about sets and classes.
      - `vocabulary.ftl`, `vocabulary.ftl.tex`:
        Lists of singular/plural pairs.

  * **Changed:** The example files are adapted to the new ontology of Naproche.

  * **Removed:** The following example files are removed:

      - `furstenberg.ftl`
      - `koenig.ftl`, `koenig.ftl.tex`
      - `regular_successor.ftl`, `regular_successor.ftl.tex`


### Changes on the LaTeX styles

  * **New:** Additional style files:

      - `basic-notions.sty`
        (used e.g. in `examples/arithmetic` and `examples/set-theory`)
      - `naproche-puzzle.sty`
        (used e.g. in `examples/agatha.ftl.tex` and `examples/dwarfs.ftl.tex`)

  * **New:** The style file `naproche.sty` provides a new command `\Naproche` to
    print the word "Naproche" with a 'blackbord N'

  * **Removed:** The obsolete style file `forthel.sty` is removed.

  * **Changed:** Wrapping text in quotation marks as a replacement for LaTeX's
    `\text{...}` command is no longer supported.


### Misc changes

  * **Changed:** The test file directory `examples/test` is moved to
  `test/examples`.

  * **New:** `test/examples/text.ftl.tex`: Tests for the new `\class{...}`,
    `\text{...}` and `\classtext{...}` features.

  * **Changed:** Automatic consistency checking is disabled by default, i.e. the
    default value of `checkconsistency` is `off`.
