# Typesetting formalizations with `naproche.sty`

The `naproche` package provides basic support for typesetting Naproche formalizations in LaTeX.


## Install and basic usage (incomplete)

To use the package, add

```TeX
\usepackage{naproche}
```

to the preamble of your document.



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

\usepackage[numberswithinsection]{naproche}

\begin{document}
    ···
    \doclicenseThis
\end{document}
```

For XeTeX/LuaTex use
```TeX
\documentclass{article}

\usepackage{polyglossia}
\defaultlanguage[variant=british]{english}
\usepackage{stix2}
\usepackage[type={CC},modifier={zero},version={1.0},imagemodifier=-80x15]{doclicense}

\usepackage[numberswithinsection]{naproche}

\begin{document}
    ···
    \doclicenseThis
\end{document}
```
instead.



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
