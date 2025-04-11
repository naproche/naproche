# Changelog

A complete listing of all changes on Naproche since naproche-20211211 (Isabelle
2021-1)

**NOTES:**

* Each change is tagged with one of the following keywords:

  - `Changed`: Something in the behaviour or  was changed in Naproche. Such
    changes may break backward compatibility.

  - `New`: A new feature was added to Naproche. In particular, new features
    should not break backward compatibility.

  - `Fixed`: A bug was fixed.

  - `Removed`: A feature of Naproche or a component of its code base was
    removed.

* Additionally, each change can be annotated with the keywords `FTL` and `TEX`
  which note that the change only affects the code/behaviour of Naproche w.r.t.
  ForTheL texts written in the ASCII or in the TeX dialect of ForTheL, resp.


--------------------------------------------------------------------------------

## Current development version

### Changes on ForTheL

  * **New:** Isabelle symbols (e.g. `\<in>`) are now allowed in ForTheL texts.


### Changes on the Naproche Ontology

  * **New:** The axiom that every map with a set-sized domain is a function that
    has been provided by the libraries is now hard-coded in Naproche.


### Misc

  * **Removed:** The file `CONTRIBUTING.md` was removed. Its content is now
  available in the [Naproche Wiki](https://github.com/naproche/naproche/wiki).


--------------------------------------------------------------------------------

## naproche-20250328 (Isabelle_Naproche-20250328)

### Changes on the parser

  * **Changed:** A separate lexing stage was added to the parser before its
    tokenizing stage (for both FTL and TEX), that are based on the
    [FTLex](https://github.com/mcearl/ftlex) library.

  * **Changed:** The tokenizing stage of the parser is now based on
    `Megaparsec`.


### Changes on ForTheL

  * **New:** Subproofs can now be wrapped in `proof` environments just like
    top-level proofs, e.g.:

    ```
    \begin{lemma}
      Every successor cardinal is regular.
    \end{lemma}
    \begin{proof}
      Let $\kappa$ be a cardinal.
      Assume that $\kappa$ is not regular.

      Then there exists a map that is surjective onto $\kappa^+$.
      \begin{proof}
        ...
      \end{proof}
    \end{proof}
    ```

  * **New:** Case distinctions can now be written up via a LaTeX environment:

    ```
    \begin{case}{<case hypothesis>}
      <proof text>
    \end{case}
    ```

    E.g.:

    ```
    \begin{case}{$n$ is even.}
      Then there exists a natural number $m$ such that $n = 2 \cdot m$.
      ...
    \end{case}
    ```

  * **New:** Outside of `forthel` groups `verbatim` environments as well as
    `\\url{...}`, `\\path{...}`, `\\verb<char>...<char>` and
    `\\verb*<char>...<char>` commands (for any TeX character `<char>`) are
    ignored by Naproche's parser. In particular no errors arise if invalid
    ForTheL expressions or unbalanced braces or `\begin`/`\end` commands
    occur in these environments/commands.
    
    *WARNING:* Unlike LaTeX, Naproche recognizes `%` characters in those
    environments/commands as comment prefixes. E.g. even though
    `\verb|foo%bar|` is a valid LaTeX expression, Naproche does not accept it as
    it regards the subexpression `%bar|` as a comment and complains about the
    group opened by `\verb|` not being closed.

  * **New:** Macro introductions and variable pretypings can now be wrapped in
    `convention` and `convention*` environments which are rendered in the same
    style as the top-level sections, e.g.:

    ```
    \begin{convention}
      Let $n,m$ denote natural numbers.
      Let $n\mid m$ stand for $n$ divides $m$.
    \end{convention}
    ```

  * **New:** Relation chains can now be typeset with the `align*` environment,
    e.g.:

    ```
    We have
    \begin{align*}
      n \cdot (n + 1)
        &= (n \cdot n) + n \\
        &= n^2 + n
    \end{align*}.
    ```

    Note the dot *after* the environment. In the future, Naproche should expect
    it *inside* the environment instead, but implementing this would require
    some fundamental changes on the parser.

  * **Changed:** `\\` is no longer tokenized away (because it must occur in,
    e.g., `cases` environments). As an alternative, `\newline` macros are
    tokenized away instead (i.e. to insert a line break before, e.g., low-level
    proofs, we must insert a `\newline` instead of a `\\` now).

  * **New:** sTeX's `\inputref[<archive path>]{<file path>}` commands
    are recognized by Naproche and behave like the instruction
    `[read <archive path>/source/<file path>]`.

  * **New:** sTeX's `\importmodule[<archive path>]{<module path>?<module file>}`
    and `\usemodule[<archive path>]{<module path>?<module file>}` commands
    are recognized by Naproche and behave like the new `importmodule`
    instruction (see below).

  * **New:** A new instruction
    `[importmodule <archive path>?<module path>?<module name>]` (where
    the part `<module path>?` can be omitted and in TEX mode the part
    `<archive path>?<module path>?<module name>` may be wrapped in a
    `\path{...}` command) which mimics sTeX's `\importmodule` command by reading
    the file
    `$NAPROCHE_FORMALIZATIONS/<archive path>/source/<module path>/<module name>`
    (in FTL mode) or
    `$NAPROCHE_FORMALIZATIONS/<archive path>/source/<module path>/<module name>.tex`
    (in TEX mode).

    Examples:

    ```
    [importmodule meta-inf?vocabulary.ftl]

    [importmodule \path{libraries?arithmetics?division.ftl}]
    ```

  * **Changed:** The `readtex` instruction was renamed to `read`, i.e. instead
    of two separate instructions `read` and `readtex` to import FTL and TEX
    files, resp., there is only one instruction `read` now. Moreover, in FTL
    texts, TEX texts can no longer be imported and, vice versa, in TEX texts,
    FTL texts can no longer be imported. (This feature was never used and was
    too error-prone since the FTL and TEX tokenizers are too different.)

  * **New:** (TEX) `\text{...}` commands can occur anywhere in a ForTheL text
    and only the content of their argument is processed by the parser.

    Example:

    ```
    $A \cup B = \{ x \mid x \in A \text{ or } x \in B \}$.
    ```

  * **New:** (TEX) The optional argument of proof environments can now contain
    (any subset of) the following arguments, given as a comma-separated list:

    - `forthel`: Allows the top-level section to be recognized by the parser
      even if it is not contained in a `forthel` environment. Note that if the
      `forthel` argument is listed, it must be the first argument.

    - `method=<proof method>`: Passes `<proof method>` as proof method to the
      checker.

    Example:

    ```
    \begin{proof}[forthel,method=induction on $n$]
      ...
    \end{proof}
    ```

  * **New:** (TEX) Macro introductions and variable pretypings can now occur
    at the bottom of signature, definiton and axiom environments. (Theorem
    environments are excluded only because of certain technical difficulties
    involved in their implementation).

    Example:

    ```
    \begin{definition}
      An ordinal number is a transitive set $\alpha$ such that every element of
      $\alpha$ is a transitive set.

      Let an ordinal stand for an ordinal number.

      Let $\alpha,\beta,\gamma$ denote ordinals.
    \end{definition}
    ```

  * **New:** (TEX) A new command `\inlineforthel{...}` which behaves like the
    `forthel` environment (i.e. in the PDF it renders its content with a gray
    background and its content is parsed by Naproche), but to be used in-line.

    Example:

    ```
    In the following, \inlineforthel{let $n$ and $m$ denote natural numbers} and
    \inlineforthel{let $n\mid m$ stand for $n$ divides $m$}.
    ```

  * **New:** (TEX) The optional argument of top-level section environments can
    now contain (any subset of) the following arguments, given as a
    comma-separated list:

    - `forthel`: Allows the top-level section to be recognized by the parser
      even if it is not contained in a `forthel` environment. Note that if the
      `forthel` argument is listed, it must be the first argument.

    - `title=<title>`: Prints `<title>` as the title of the top-level section.

    - `id=<id>`: Creates a label `<id>` which can be used to reference the
      top-level section via `\ref` and friends. (Replaces `\label`)
      (In the `naproche-library` document class, `<id>` is printed in the margin
      of the document.)

    Example:

    ```
    \begin{axiom*}[forthel,title=Separation Axiom,id=sepAx]
      ...
    \end{axiom*}
    ```

  * **New:** In `definition` and `signature` environments and in
    `let ... stand for` expressions newly introduced notions can be wrapped in an
    `\emph{...}` command. Examples:

    ```
    \begin{definition}
      $x$ is \emph{empty} iff $x$ has no elements.
    \end{definition}
    
    \begin{signature}
      A \emph{natural number} is a notion.
    \end{signature}

    Let an \emph{integer} stand for a natural number.

    \begin{signature}
      A \emph{function from $A$ to $B$} is a set.
    \end{signature}

    \begin{signature}
      $n$ \emph{divides $m$} is an atom.
    \end{signature}
    ```

  * **New:** Instead of `if A then B` we can now also write `A implies B` or
    `A implies that B`.


### Changes on the example formalizations

  * **Changed:** The formalizations that ship with Naproche are organized in a
    new directory structure:

    - `naproche/math/examples` contains stand-alone example formalizations.

    - `naproche/math/libraries` contains structured libraries whose content is
      intended to be imported in other formalizations.

    - `naproche/math/archive` contains example formalizations that depend on
      the files in `naproche/math/libraries`.

    - `naproche/math/latex` contains files that are required to translate the
      formalizations in `naproche/math` to PDF and HTML.


### Changes on Naproche's LaTeX package

  * **New:** Two commands `\showtlsnumbers` and `\hidetlsnumbers` to show and
    hide, resp., the numbers of top-level sections. Useful to supress the
    numbers of `inputref`ed top-level sections.

    For instance if the file `some-archive/source/some-file.ftl.tex` consists of
    the top-level section

    ```
    \begin{axiom}[title=Infinity]
      There exists an infinite set.
    \end{axiom}
    ```

    then `\inputref[some-archive]{some-file.ftl}` would be rendered as
    "Axiom 1 (Infinity). There exists an infinite set.". If we prepend
    `\hidetlsnumbers` to the `\inputref` command, it would be rendered as
    "Axiom (Infinity). There exists an infinite set." (without the "1") instead.

  * **New:** The `naproche` package now supports to render Naproche
    formalizations via RusTeX as HTML.

  * **New:** A new document class `naproche-library` for libraries.

  * **Changed:** The package `puzzles` was merged into the package `naproche`
    and can be invoked by importing the `naproche` package with the argument
    `puzzle`.


### Misc

  * **Changed:** ForTheL texts that are imported are no longer checked for
    logical or ontological correctness which makes importing files significantly
    faster.

    *NOTE:* This does *not* bypass the test for any imported file when running
    `isabelle naproche_test`: Since `isabelle naproche_test` tests *every* file
    in the `math` directory, every file that *can* be imported will be
    tested at some point.

  * **New:** The command line interface provides a new parameter
    `--mode=<mode>`, where `<mode>` can be one of the following words which
    determines the behaviour of Naproche:
    
    - `lex`: Naproche tries to lex the input text.
    - `tokenize`: Naproche tries to tokenize the input text.
    - `translate`: Naproche tries to translate the input text to TPTP.
    - `verify`: Naproch tries to verify the input text.
    - `render`: Render the input text (if given as a file) with pdflatex and
      bibtex to PDF.
    
    If the `mode` parameter is not specified, Naproche behaves as if it were set
    to `verify`.

    NOTE: This change deprecates the `--onlytranslate`/`-T` flag.

  * **Changed:** The Naproche executable has been renamed from `Naproche-SAD`
    to `Naproche`.
    
    *NOTE:* You might have to delete the file `Naproche-SAD.cabal` which
    has been generated when Naproche was compiled before this change to be able
    to compile Naproche after this change as well.

  * **Removed:** The (deprecated) `init.opt` file was removed.

  * **New:** Instructions etc. regarding Haskell have been added/moved to
    `CONTRIBUTING.md`.

  * **Removed:** The (meanigless) drop instructions for commands were removed.

  * **Changed:** Formulas are now pretty printed by using symbolic notation of
    logical symbols.


--------------------------------------------------------------------------------

## naproche-20240519 (Isabelle 2024)

### Changes on the example files

  * **Changed:** The LaTeX style file `naproche.sty` was moved to
    `examples/meta-inf/lib/naproche.sty`.

  * **Changed:** All examples were adapted to the new section wise variable
    pretyping.

  * **Changed:** `euclid.ftl.tex` was renamed to `euclid_primes.ftl.tex`.

  * **Changed:** The files `macros.ftl`, `macros.ftl.tex`, `vocabulary.ftl` and
    `vocabulary.ftl.tex` were moved to `examples/meta-inf/source/`

  * **Changed:** The files `axioms.ftl` and `axioms.ftl.tex` were removed as it
    is no longer necessary to state the in-built axioms of Naproche explicitly
    at the beginning of each formalization.

  * **New:** All bibliography entries used in the `.tex` files are collected in
    a global bibliography file `examples/meta-inf/lib/bibliography.bib`.

  * **Changed:** The arithmetics, foundations and set theory libraries were
    moved to `examples/libraries/source/`.

  * **Changed:** Some formalizations were moved from the libraries to
    stand-alone files:

    - Dedekind's Recursion Theorem: `dedekind.ftl.tex`
    - Euclid's Division Theorem: `euclid_division.ftl.tex`
    - Transfinite Recursion Theorem: `transfinite-recursion.ftl.tex`

  * **Changed:** Paradoxes were moved to stand-alone files:

    - Drinker Paradox: `drinker-paradox.ftl.tex`
    - Russell's Paradox: `russell-paradox.ftl.tex`
    - Russell-Myhill Paradox: `russell-myhill-paradox.ftl.tex`
    - Barber Paradox: `barber-paradox.ftl.tex`
    - Burali-Forti Paradox: `burali-forti-paradox.ftl.tex`
    - Cantor's Paradoxes: `cantor-paradox.ftl.tex`

  * **New:** New formalizations:
  
    - "Little Gauß' Theorem": `gauss.ftl.tex`
    - Curry's Paradox: `curry-paradox.ftl.tex`
    - Hilbert's Paradox: `hilbert-paradox.ftl.tex`
    - Library about lists: `libraries/source/lists/`

  * **Changed:** The following formalizations were revised:

    - `agatha.ftl.tex`
    - `cantor.ftl.tex`
    - `dwarfs.ftl.tex`
    - `furstenberg.ftl.tex`
    - `hausdorff.ftl.tex`
    - `koenig.ftl.tex`
    - `zermelo.ftl.tex`


### Changes on ForTheL

  * **New:** Variable pretyings can be reset using the new `[resetpretyping]`
    instruction.

  * **New:** (TEX) `\section` triggers a reset of the variable pretypings. Thus
    the pretyping of variables is now per section and no longer for the whole
    document.

  * **New:** Imports of formalizations using the `[read ..]` and `[readtex ..]`
    instruction are now relative to the environment variable
    `NAPROCHE_FORMALIZATIONS`. For Isabelle/Naproche `NAPROCHE_FORMALIZATIONS`
    defaults to `$NAPROCHE_HOME/examples`, which resembles the old behavior. For
    command-line use, `NAPROCHE_FORMALIZATIONS` needs to be explicitly set to
    the examples folder of the Naproche checkout to mimic the old behavior.

  * **Fixed:** (TEX) Commented out `forthel` environments are now ignored by the
    parser.

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
