# The `naproche` LaTeX Package

## Contents

- `naproche.dtx`: Bundled code and documentation of the `naproche` package
- `naproche.ins`: Script to generate the style file `naproche.sty` (see below)
- `naproche.pdf`: Documentation of the `naproche` package (automatically
  generated from `naproche.dtx`, see below)
- `naproche.sty`: Style file (automatically generated from `naproche.dtx`, see
  below)

To experiment with the typesetting provided by this package, you can of course
locally change your `naproche.sty`. But note that such changes will be
overwritten whenever you run `latex naproche.ins` (see below). To make those
changes persistent, add them to `naproche.dtx` instead and re-generate
`naproche.sty` from this file. In particular, if you intend to commit changes of
this package to the GitHub repository of Naproche, perform those changes in
`naproche.dtx` – don't forget to document them! –, re-generate both
`naproche.sty` and `naproche.pdf` and commit all changes on those three files.


## Generating the Style File

To generate the style file `naproche.sty`, run `latex naproche.ins`.


## Generating Documentation

To generate the package documentation `naproche.pdf` which consists of a user
manual and notes on the implementation, run the following commands:

```
pdflatex naproche.dtx
makeindex -s gglo.ist -o naproche.gls naproche.glo
makeindex -s gind.ist -o naproche.ind naproche.idx
pdflatex naproche.dtx
pdflatex naproche.dtx
```

(The two calls of of `makeindex` generate the change history and the index,
resp.)
