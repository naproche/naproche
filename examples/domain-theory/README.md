# Domain Theory

An **experimental** formalization of basic topics from domain theory using
[sTeX](https://github.com/slatex/sTeX/blob/main/doc/stex-doc.pdf) to handle
mathematical structures in LaTeX.


## Compiling the TeX Sources to PDF

This directory is an sTeX archive. To compile the TeX files in the `source`
directory via `pdflatex` some preliminary setup is required:

  1.  Select or create a new directory that contains all your sTeX archives
      and set an environment variable `MATHHUB` pointing to it. (In the
      following we refer to this directory by `~/MathHub` but any other
      location and name of your choice for that directory also works.) E.g.
      put the line

      ```
      export MATHHUB="$HOME/MathHub"
      ```

      in your `~/.bash_profile` file (or whatever file corresponds to it on your
      system) and log out and in again to make the `MATHHUB` variable available
      on your system.

  2.  Create a new directory `~/MathHub/naproche`.

  3.  Create a (soft) link named `~/MathHub/naproche/domain-theory` that
      points to *this* directory, e.g.:
      
      ```
      ln -s ~/naproche/examples/domain-theory ~/MathHub/naproche/domain-theory
      ```

The TeX files in the `source` directory can then be compiled to PDF by running
`pdflatex` from within `~/MathHub/naproche/domain-theory/source`, e.g.:

```
cd ~/MathHub/naproche/domain-theory/source
pdflatex lattices.ftl.tex
```
