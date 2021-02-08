# Typesetting formalizations with `naproche.sty`

The `naproche` package provides basic support for typesetting Naproche formalizations in LaTeX.


## Install and basic usage (incomplete)

To use the package, add

```TeX
\usepackage{../lib/tex/naproche}
```

to the preamble of your document.
You may need to compile the latex files from the appropriate relative directory. For instance, to compile
`examples/tarski.ftl.tex` you may need to call `pdflatex` from within the `examples/` folder.


Alternatively, you can [manually install](https://en.wikibooks.org/wiki/LaTeX/Installing_Extra_Packages#Manual_installation) the package and write `\usepackage{naproche}`.

## Suggested template


A basic starting template for a formalization could be the following.
This uses the STIX fonts for better on-screen readability
and licenses the document as `CC0`.

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




## Features

The `naproche` package defines all necessary top-level environments such as `axiom`, `definition`, `theorem`, and `proof`.
Content within the `forthel` environment is marked with a grey background.
The package also adjust the spacing in proofs for improved readability and includes a workaround for quoted terms in comprehensions, such as
```TeX
$R = \{ x \mid x " is not an element of " x \}$
```
to render the text properly.


## Additional options

Options can be enabled in the following form.

```TeX
\usepackage[opt1,opt2]{naproche}
```

| Option | Effect |
| ----- | ------ |
| `nonumbers` | Turn off numbering for theorem-like environments. |
| `numberswithinsection` | Reset theorem numbers for each section. |
| `numberswithinsubsection` | Reset theorem numbers for each subsection. |
| `noquoteworkaround` | Sometimes the quote workaround breaks other packages. Changing the load order of the packages might suffice, but the workaround can also be disabled with this option. |
