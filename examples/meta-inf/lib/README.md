# Typesetting formalizations

## "naproche"

The `naproche` package provides basic support for typesetting Naproche formalizations in LaTeX.
It is used by almost all example files that ship with Naproche and is the
recommended one for custom formalizations.


### Install and basic usage (incomplete)

To use the package, add

```TeX
\usepackage{meta-inf/lib/naproche}
```

to the preamble of your document (provided that your document is stored in the
`naproche/examples` directory).
You may need to compile the latex files from the appropriate relative directory.
For instance, to compile `examples/tarski.ftl.tex` you may need to call
`pdflatex` from within the `examples/` folder.


Alternatively, you can [manually install][1] the package and write
`\usepackage{naproche}`.

Or, using the [sTeX][2] package you can use the `naproche` package via
`\libusepackage{naproche}` (provided that the sTeX archive your document belongs
to lives within the `naproche/examples` directory).


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

\usepackage{meta-inf/lib/naproche}

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

\usepackage{meta-inf/lib/naproche}

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


### Additional options

Options can be enabled in the following form.

```TeX
\usepackage[opt1,opt2]{naproche}
```

| Option                    | Effect
| ------------------------- | -----------------------------------------------------
| `numberswithinsection`    | Reset theorem numbers for each section.
| `numberswithinsubsection` | Reset theorem numbers for each subsection.


### Compilation errors

The usage of `\classtext{...}` can cause the compilation error
`latexmk: Failure in some part of making files.`. It might vanish by compiling
the document a second time.


## "naproche-logo"

The only purpose of this package is to provide the command `\Naproche` which
typesets the Naproche logo.


## "libraries"

The `libraries` package is used by Naproche's libraries to provide a document
layout that is rather suitable for libraries than for stand-alone
formalizations.



[1]: <https://en.wikibooks.org/wiki/LaTeX/Installing_Extra_Packages#Manual_installation>
[2]: <https://www.ctan.org/pkg/stex>
