# Contributing to Naproche

## Contents

  1. [Resources](#resources)
  2. [Changelog](#changelog)
  3. [File and Directory Name Conventions](#file-and-directory-name-conventions)
  4. [Release Process](#release-process)
  5. [Abbreviations](#abbreviations)
  6. [Haskell](#haskell)
  7. [LaTeX](#latex)
  8. [Managing Naproche Formalizations With FLAMS](#managing-naproche-formalizations-with-flams)
  9. [Ideas for Further Development](#ideas-for-further-development)


## Resources

  - **[An argument for controlled natural languages in Mathematics](https://jiggerwit.files.wordpress.com/2019/06/header.pdf)**:
    Motivation for and future direction of CNLs in general.
  - **[Automatic Proof-Checking of Ordinary Mathematical Texts](http://ceur-ws.org/Vol-2307/paper13.pdf)**:
    A short introduction to this project.
  - **[The syntax and semantics of the ForTheL language, 2007](http://nevidal.org/download/forthel.pdf)**:
    In-depth paper on the ForTheL language.
  - **[Méthodes de formalisation des connaissances et des raisonnements mathématiques: aspects appliqués et théoriques](http://tertium.org/papers/thesis-07.fr.pdf)**:
    Andrei Paskevich's PhD thesis on this topic (in French)
  - **[Handbook of Practical Logic and Automated Reasoning](https://www.cl.cam.ac.uk/~jrh13/atp/)**:
    Textbook on logic and automated theorem proving. Some functions in the code
    base are literal translations of the OCaml code presented in the book.


## Changelog

It is highly encouraged to document all notable changes on Naproche in the file
[CHANGELOG.md](CHAMGELOG.md).


## File and Directory Name Conventions

In this section you find a list of conventions that the files and directories in
the Naproche repository are expected to follow.
In particular, these conventions guarantee that the file and directory names in
the Naproche repository are both POSIX and Microsoft Windows compatible.


### Preliminary Definitions

We say that two strings *s* and *t* are **equal modulo case-insensitivity** if
we can obtain *t* by replacing zero or more letters in *s* with their upper- or
lower-case counterparts.
If *s* and *t* are equal modulo case-insensitivity, we call *s* and *t* **case-
insensitive equivalents** of each other.


### Conventions

  * No two files/directories whose names are equal modulo case-insensitivity must occur in the same directory (including the root directory of the Naproche repository).

  * A file/directory name may only consist of the following ASCII characters:
  
      - Lower-case letters (`a` - `z`)
      - Upper-case letters (`A` - `Z`)
      - Digits (`0` - `9`)
      - Period (`.`)
      - Underscore (`_`)
      - Hyphen (`-`)

  * A file/directory name must not be any of the following strings or their case-insensitive equivalents:

      - `CON`
      - `PRN`
      - `AUX`
      - `COM0`, `COM1`, `COM2`, `COM3`, `COM4`, `COM5`, `COM6`, `COM7`, `COM8`, `COM9`
      - `LPT0`, `LPT1`, `LPT2`, `LPT3`, `LPT4`, `LPT5`, `LPT6`, `LPT7`, `LPT8`, `LPT9`

    Moreover, a file/directory name must not be of the form
    `<reserved string>.<arbitrary string>`, where `<reserved string>` is any of
    the above strings (or their case-insensitive equivalents) and
    `<arbitrary string>` is an arbitrary string.

  * A file/directory name must not be the empty string.

  * A file/directory name must not end with the character `.`.

  * A file/directory name must not start with the character `-`.


### Further Reading

  * File, path and namespace conventions on Microsoft Windows:
    <https://learn.microsoft.com/en-us/windows/win32/fileio/naming-a-file>

  * Common problems with unrestricted file names on Unix/Linux/POSIX systems:
    <https://dwheeler.com/essays/fixing-unix-linux-filenames.html>


## Release Process

Naproche is distributed as a component of
[Isabelle](https://isabelle.in.tum.de/) and thus depends on Isabelle's release
cycles.


### Isabelle's Release Process

The release process of Isabelle is usually divide into several stages:

  1.  A fixed release date is announced via the
      [isabelle-dev@in.tum.de](mailto:isabelle-dev@in.tum.de) mailing list,
      together with a release schedule.
  2.  Approx. two month before the release date an informal preview of the new
      release, called *RC 0* ("RC" stands for "release candidate"), is
      published.
  3.  Six weeks before the release date a first formal release candidate
      (*RC 1*) is published.
  4.  Usually, after RC 1 several more release candidates are published.
  5.  At the release date a final and unchangeable Isabelle release is
      published.

Thus, the release process of Isabelle has some implications for the release
process of Naproche:

  - Any new features of Naproche (i.e. changes on the code base, new
    formalizations, etc.) that are intended to be part of the new Isabelle
    release must be ready for RC 1.
  - Between RC 1 and RC 2 there is some time to fix critical bugs in Naproche.
  - If Naproche works without any critical bugs in RC 2 then the version of
    Naproche that is part of RC 2 will be adopted to the final Isabelle release.
    In this case no further changes on Naproche that happen after RC 2 will be
    adopted to the final Isabelle release.
  - If Naproche does *not* work properly in RC 2, it might be excluded from the
    final Isabelle release.


### Naproche's Release Process

To ensure that the integration of Naproche into Isabelle works smoothly, the
following guideline should be adhered to.

  1.  The version of Naproche that is considered as the Naproche component of
      an Isabelle release candidate is the one on the `master` branch of the
      Naproche repository (<https://github.com/naproche/naproche>) at the state
      of its latest commit.
  2.  Ensure that Naproche is finalized until a couple of days before the
      release of RC1, which includes:

        - The development of the new Naproche version must be finished, i.e.
          implementing new features, fixing bugs, providing documentation,
          adding formalizations, etc.
        - The following tests must pass:
          ```
          isabelle naproche_build
          isabelle naproche_test -j2
          isabelle naproche_component -P
          ```
          See the [README](https://github.com/naproche/naproche/blob/master/README.md)
          in the Naproche repository for details and potential changes or
          additions to these tests.
        - The test file `Isabelle/Test/Test.thy` must not throw any errors in
          Isabelle/jEdit (on Linux, macOS and Windows).
        - These tests do not (and cannot) include checks whether the PDFs that
          are generated by `isabelle naproche_component -P` from the example
          formalizations shipped with Naproche look as intended. This has to be
          checked manually!
        - The file and directory name conventions listed
          [here](https://github.com/naproche/naproche/wiki/File-and-Directory-Name-Conventions)
          must be followed to ensure interoperability between different
          operating systems.
        - Ensure that the description of Naproche in `Isabelle/Intro.thy` and
          the list of example formalizations in `math/README.md` are up to date.

  3.  When Naproche eventually got released as a component of Isabelle, don't
      forget to update the "Download" section on the Naproche home page
      (<https://naproche.github.io/download.html>).


## Abbreviations

Using these abbreviations is encouraged when writing/rewriting code, especially
for local variables.

Abbrev | Meaning
------ | -----------------------------
adj    | adjective
aff    | affirm/affirmation
asm    | assume/assumption
cont   | continuation
dec    | decrement
decl   | declaration
def    | definition
eps    | epsilon
eq     | equal/equality
err    | error
expr   | expression
fun    | function
hypo   | hypothesis
inc    | increment
instr  | instruction
pat    | pattern
predi  | predicate
prim   | primitive
sig    | signature
st     | state
sub    | substitution/substitute
symb   | symbol/symbolic
var    | variable


## Haskell

Naproche is written in the functional programming language
[*Haskell*](https://www.haskell.org/).
In this section you find information about the Haskell setup that is
required/recommended to develop Naproche.


### Learning Haskell

There are many textbooks and tutorials about Haskell freely available on the
web. See e.g. <https://www.haskell.org/documentation/> for an overview.


### Basic Setup

Make sure, you set up Naproche according to the instructions given at
<https://github.com/naproche/naproche/blob/master/README.md>.

If you just want to build Naproche from its sources code and run it without
getting involved in editing the Haskell source files, no further setup is
needed.
Just follow the instructions given at
<https://github.com/naproche/naproche/blob/master/README.md>.
In this case, you can ignore the remaining sections on this page.

However, if you want to dive into the development of Naproche's source code, it
is highly recommended to set up a Haskell development environment as described
at <https://www.haskell.org/get-started/>.
In this case, you should also read the remaining sections on this page.


### Stack

Naproche is provided as a [*Stack*](https://docs.haskellstack.org/en/stable/)
project.
Stack is a tool to build Haskell projects and manage their dependencies.

Note that Isabelle automatically downloads Stack to
`$HOME/.isabelle/contrib/stack-...` when you build Naproche for the first time.
It is highly recommended to use this automatically downloaded version of Stack
if you ever have to run Stack (in the context of Naproche) manually.

If you have good reasons to use a different version of Stack though, see
<https://docs.haskellstack.org/en/stable/#how-to-install-stack> for
installation instructions.


### Hoogle

[*Hoogle*](https://hoogle.haskell.org/) is a search engine for many Haskell
libraries.
These libraries can be searched by either function name or by (approximate)
type signature via Hoogle's web interface: <https://hoogle.haskell.org/>

To be able to use Hoogle also on the code base of Naproche, you have to set up
a local Hoogle server (via Stack, see [above](#stack)) via the following steps:

  1.  Generate a local Hoogle database for the Naproche code and the libraries
      it depends on (from within the root directory of your local Naproche
      repository):

      ```
      stack hoogle -- generate --local
      ```

  2.  Start a local Hoogle server (from within the root directory of your local
      Naproche repository):

      ```
      stack hoogle -- server --local --port=8080
      ```

  3.  Open <http://localhost:8080> in your favourite web browser.


### Haddock

[*Haddock*](https://haskell-haddock.readthedocs.io/latest/) is a tool for
automatically generating documentation from annotated Haskell source code.
When editing the source code of Naproche, it is highly recommended to equip all
Haskell source files you add or change with Haddock annotations.

See <https://haskell-haddock.readthedocs.io/latest/markup.html> for a guide on
how to annotate Haskell code with Haddock.


## LaTeX

Naproche formalizations can be embedded into
[LaTeX](https://www.latex-project.org/) documents.
To this end, Naproche provides two LaTeX packages for typesetting Naproche
formalizations in LaTeX:

  1.  A "beginner-friendly" package ([`math/examples/latex/naproche.sty`](https://github.com/naproche/naproche/blob/master/math/examples/latex/naproche.sty),
      documented in [`math/examples/latex/naproche.sty`](https://github.com/naproche/naproche/blob/master/math/examples/latex/naproche.pdf))
       intended to be used for small example formalizations that

         - do **not** depend on libraries of Naproche formalizations *and*
         - are **not** intended to be converted to interactive HTML.

  2.  An "advanced" [sTeX](https://ctan.org/pkg/stex)-based package
      (`math/latex/lib/naproche.sty`) intended to be used for larger
      formalization projects that

        - may depend on libraries of Naproche formalizations *or*
        - are intended to be converted to interactive HTML.


### Prerequisites

Before contributing to any of the LaTeX packages listed above, ensure that you
have an up-to-date version of [TeX Live](https://tug.org/texlive/) set up on
your system. It is strongly recommended to set up TeX Live
manually and *not* via a package manager. Installation instructions for Linux,
macOS and Windows can be found via the following links:

  - Linux: <https://tug.org/texlive/quickinstall.html>
  - macOS: <https://tug.org/texlive/quickinstall.html> or
    <https://tug.org/mactex/>
  - Windows: <https://tug.org/texlive/windows.html>

Note that downloading all required LaTeX packages during the setup of TeX Live
may take some time.

For details and more information about TeX Live see
[*The TeX Live Guide*](https://tug.org/texlive/doc/texlive-en/texlive-en.pdf).

Moreover, ensure you are familiar with the content of the following documents:

  - [*LaTeX for authors*](https://www.latex-project.org/help/documentation/usrguide.pdf)
  - [*LaTeX for package and class authors*](https://www.latex-project.org/help/documentation/clsguide.pdf)
  - [*How to Package Your LaTeX Package*](https://latex.org.uk/info/dtxtut/dtxtut.pdf)

Before contributing to the "advanced" LaTeX package, also ensure that you are
familiar with LaTeX's L3 programming layer (expl3). The below list provides
some useful references for expl3.

  - [*The expl3 package and LaTeX3 programming*](https://texdoc.org/serve/expl3.pdf/0):
    A short introduction to expl3
  - [*The LaTeX3 Interfaces*](https://texdoc.org/serve/interface3.pdf/0):
    The reference documentation for expl3
  - [*The LaTeX3 Sources*](https://texdoc.org/serve/source3.pdf/0):
    The typset sources for expl3


## Managing Naproche Formalizations With FLAMS

[FLAMS](https://github.com/kwarc/flams) – the Flexiformal Annotation Management
System – can be used to manage Naproche formalizations that are based on
[sTeX](https://github.com/slatex/stex) and to convert them to PDF and HTML..

### Setup

#### FLAMS

Download and unpack FLAMS:

  - Linux: <https://github.com/KWARC/FLAMS/releases/download/latest/linux.zip>
  - macOS: <https://github.com/KWARC/FLAMS/releases/download/latest/mac.zip>
  - Windows: <https://github.com/KWARC/FLAMS/releases/download/latest/windows.zip>


#### sTeX

  1.  Clone the sTeX repository, e.g.:

      ```
      git clone https://github.com/slatex/sTeX.git
      ```

  2.  Clone the `FTML/meta` repository to `naproche/math/archive/FTML/meta`,
      e.g.:

      ```
      cd .../naproche/math/archive
      mkdir FTML
      cd FTML
      git clone https://gl.mathhub.info/FTML/meta.git
      ```

### Starting the FLAMS Dashboard

  1.  Run the `flams` (Linux/macOS) or `flams.exe` (Windows) executable in the
      directory you obtained in step 2 in the 𝖥𝖫∀𝖬∫ setup with

      - the `MATHHUB` variable set to `.../naproche/math/archive`, and
      - the `TEXINPUTS` variable set to `.../sTeX//`,

      e.g.:

      ```
      MATHHUB="/home/user/naproche/math/archive" TEXINPUTS="/home/user/sTeX//" flams
      ```

      This starts a web server at `http://localhost:8095`.
      (The port number may vary if the port `8095` is already in use.
      In this case the port used by 𝖥𝖫∀𝖬∫ will be shown in the command line
      interface.)

  2.  Navigate to `http://localhost:8095` in your web browser to open the
      *FLAMS dashboard*.

  3.  To close the web server again, press `CTRL+C` in the command line
      interface.


### Converting Naproche Formalizations to PDF and HTML

  1.  In the FLAMS dashboard, navigate to the `MathHub` tab.

  2.  Click on an sTeX group/archive listed there to expand it (e.g.
      `articles`).

  3.  Click on the `i` icon beneath an `.ftl.en.tex` file name (e.g.
      `russell-paradox.ftl.en.tex`) which opens a pop-up window.

  4.  Click on the `all` button in the upper-right corner of the pop-up window.
      The message `1 new build task queued` should appear.

  5.  Navigate to the `Queue` tab.

  6.  Click on the `Run` button beneath the file name you selected in step 3
      (e.g. `[articles]russell-paradox.ftl.en.tex`).
      This starts a process to convert the selected file to PDF, HTML and OMDoc.

  7.  If no error occured in the last step, you can view the generated HTML by
      navigating to the `MathHub` tab and clicking on the
      file name you selected in step 3. In the hamburger menu in the upper-
      right corner of the HTML preview you can switch to the
      OMDoc preview and open the generated PDF file.


## Ideas for Further Development

### Better Type Checking

We currently type check using an approach similar to
[A Second Look at Overloading](http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.27.2072&rep=rep1&type=pdf)
with coercions. This works very well also for exporting but there are
a few cases were we can do better:

Assume `f` was introduced as a function that maps sets to sets. Then saying
`x \in f(y)` is totally natural, but our current approach can't handle it.
Instead of making the type system more complex, I propose that we add something
similar to type classes: We gather facts about our objects as we check the
statements and then solve type-based questions using a type class algorithm.
That would also be more similar to the behaviour of the old Naproche-SAD.

  - See [Tabled Typeclass Resolution](https://arxiv.org/abs/2001.04301)
  - How do we turn typeclass-based typings (`isSet`) back into types for
    exporting?


#### Error slices 

A paper I found by chance, that seems very promising
[Type error slicing in implicitly typed higher-order languages](https://www.sciencedirect.com/science/article/pii/S016764230400005X).
This could be really nice in a natural language context.


### How to Implement Theories

Options:

  1.  Don't implement theories. "Little Theories" are sufficient: 
      it refers to the organizational principle that mathematical theories
      should be based on small axiom systems that are proved consistent by a
      model in a different axiom system (which ultimately should be modeled by
      ZFC or a similar theory).

  2.  Something, something module systems:
      [an overview](https://apps.dtic.mil/dtic/tr/fulltext/u2/a457064.pdf).


### Move Naproche Documents to the Web

It would be nice if one could edit lecture notes online with Naproche.
There are a few possibilities:

  1.  Edit Naproche directly on the Web: Certainly preferable but currently too
      slow for real workloads (~8x slower than on commandline
      and provers are problematic as well). A nice editor for this would be
      [React Page](https://github.com/react-page/react-page).

  2.  Export Naproche Documents into a nice webinterface. This could work
      better, because we can do all the hard lifting locally.
      Normal text could be made to [look like Latex](https://latex.now.sh/).
      Diagrams could be rendered by
      [this](https://github.com/kisonecat/tikzjax),
      but probably it is better if we convert all this into images.

This could be really great for students that want to step through the proofs,
because we can give them at any level of granularity! Also, one can link
notions to their definition site and do fancy things like exporting flash cards
for all definitions in a script.


### Proof Reconstruction

Naproche has historically made many transformations in the backend
which has sometimes lead to inconsistencies and has made it harder to trust
the results verified by Naproche. With the new backend *[reference needed]*,
however, we are close
to fixing these problems once and for all by emitting proofs in a widely
accepted format (TSTP).

Naproche now *[reference needed]* does two big transformation steps: One from
the ForTheL language to an internal type theory and another from that type
theory to proof tasks given
to the E prover. The first transformation cannot be checked for correctness, but
one can usually verify this manually by looking at the `-T` output or the hints
in Isabelle/Naproche.

The second transformation now happens exclusively in the `SAD/Core/Task.hs`
file. It takes the tactics which are introduced as constructors of the `Proof`
type and  turns them into tasks given to the external prover. Since the
external prover emits proof objects, we can parse these objects and stitch them
together in a way of undoing
the tactics. For example given a case distinction:

```
Case x = y. stmt
Case x != y. stmt
```

We would get three proofs from eprover: P1: `x = y => stmt`, P2:
`x != y => stmt` and P3:`x = y or x != y`.
We can then construct a proof object for `stmt` by adding `x != y or` to each
clause of P1,
adding `x = y or` to each clause of P2 and then add a final inference step at
the bottom of the proof.
We can then give an explicit proof object in TSTP syntax for each lemma using
just the stated axioms,
which would eliminate all doubts about the correctness of the backend.

Required knowledge:

  - First order logic
  - Haskell: general programming skill including monads and parsers.

Necessary steps:

  - understand the `-p` output from the eprover
  - write a parser for the `-p` output
  - Extend the `SAD/Core/Tactic.hs` code to unroll tactics as described above

Possible directions for further work:

  - Find the used axioms/lemmata of each proof and use this for better caching:
    At the moment a proof leaves the cache when any definition/axiom/lemma above
    it changes, but it would be better if this only happened when the changed
    declaration was used in the proof.
  - Store the proof object in the cache and "warm-start" eprover when one of its
    lemma-dependencies changes.


### Query-Based Compilers

There are two cases for query-based compilers:

  1.  Naproche will always be slow. Even when we optimize more, with everything
      we want to do we are looking at
      roughly 100-300 ms for every 1000 lines. Which is okay, but not great. If
      we cache the intermediate results
      of type checking, we can potentially in a LSP context check only the
      block where the user changed stuff and
      then we will get pretty good performance.

  2.  LSP in general seems to require lots of query-based stuff. See
      <https://github.com/haskell/lsp>.

Interesting approaches:

  - [Salsa](https://salsa-rs.github.io/salsa/videos.html) based on the rust
    type-checker
  - [Build systems](https://www.microsoft.com/en-us/research/uploads/prod/2018/03/build-systems-final.pdf)
    similar to the Haskell tooling
