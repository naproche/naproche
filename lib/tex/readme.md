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

```TeX
\documentclass{article}

\usepackage[utf8]{inputenc}
\usepackage[british]{babel}
\usepackage{naproche}

\begin{document}
    ···
\end{document}
```

For XeTeX/LuaTex use
```TeX
\documentclass{article}

\usepackage{polyglossia}
\defaultlanguage[variant=british]{english}
\usepackage{naproche}

\begin{document}
    ···
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
| `nonumber` | Turn off numbering for theorem-like environments. |