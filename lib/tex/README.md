# Typesetting formalizations

Currently there are three style files for LaTeX available to render a Naproche
formalization:

  * `naproche.sty`
  * `basicnotions.sty`
  * `naproche-puzzle.sty`


## "naproche"

The `naproche` package provides basic support for typesetting Naproche formalizations in LaTeX.
It is used by almost all example files that ship with Naproche and is the
recommended one for custom formalizations.


### Install and basic usage (incomplete)

To use the package, add

```TeX
\usepackage{../lib/tex/naproche}
```

to the preamble of your document.
You may need to compile the latex files from the appropriate relative directory.
For instance, to compile `examples/tarski.ftl.tex` you may need to call
`pdflatex` from within the `examples/` folder.


Alternatively, you can [manually install][1] the package and write
`\usepackage{naproche}`.


### Suggested template

A basic starting template for a formalization could be the following.
This uses the STIX fonts for better on-screen readability and licenses the
document as `CC0`.

```TeX
\documentclass{article}

\usepackage[utf8]{inputenc}
\usepackage[british]{babel}
\usepackage{stix2}
\usepackage[type={CC},modifier={zero},version={1.0},imagemodifier=-80x15]{doclicense}

\usepackage{../lib/tex/naproche}

\begin{document}
    ···
    \doclicenseThis
\end{document}
```

For XeTeX/LuaTex use

```TeX
\documentclass{article}

\usepackage[british]{babel}
\usepackage{stix2}
\usepackage[type={CC},modifier={zero},version={1.0},imagemodifier=-80x15]{doclicense}

\usepackage{../lib/tex/naproche}

\begin{document}
    ···
    \doclicenseThis
\end{document}
```

instead.


### Features

* Content within the `forthel` environment is marked with a grey background.

* Top-level environments for `axiom`, `definition`, `theorem`,
  `proposition`, `lemma`, `corollary`, `signature` and `proof`.

* A length `ftlparskip` with which the space between paragraphs in proofs within
  `forthel` environments can be controlled (default: 0.5em).
  Can be changed via `\setlength{\ftlparskip}{<new length>}`.

* Alternative syntax for comprehension terms:
  `\class{... | ...}` behaves like `\{... \mid ...\}` with additional support
  for flexible sizes of the braces and the vertical bar.

* `\classtext{...}` as an alternative for `\text{...}`. Can be used (in
  display math mode) in the RHS of `\class{... | ...}` to achieve automatic
  line breaks within a comprehension term.

* Predefined symbols:

  * `\dom` for the domain of a map
  * `\fun` for lambda abstraction in low-level map definitions

* `\Naproche`: The word "Naproche" with a 'blackbord N'


### Additional options

Options can be enabled in the following form.

```TeX
\usepackage[opt1,opt2]{naproche}
```

| Option                    | Effect
| ------------------------- | --------------------------------------------------
| `nonumbers`               | Turn off numbering for theorem-like environments.
| `numberswithinsection`    | Reset theorem numbers for each section.
| `numberswithinsubsection` | Reset theorem numbers for each subsection.


### Compilation errors

The usage of `\classtext{...}` can cause the compilation error
`latexmk: Failure in some part of making files.`. It might vanish by compiling
the document a second time.


## "basic-notions"

Required by Naproche's set theory and arithmetic libraries and by any
formalizations based on then.


## "libraries"

`libraries` is used by Naproche's set theory and arithmetic libraries to
provide a document layout that is rather suitable for libraries than for
stand-alone files.


## "naproche-puzzle"

Used by the puzzles `agatha` and `dwarves` in the Naproche examples.




[1]: <https://en.wikibooks.org/wiki/LaTeX/Installing_Extra_Packages#Manual_installation>
