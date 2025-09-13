# The `naproche` LaTeX Package

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
