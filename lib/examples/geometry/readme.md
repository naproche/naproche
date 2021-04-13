# Tarskian geometry formalized in Naproche

This note is an early draft of a self-contained formalization of Tarskian geometry.
It demonstrates how Naproche could be used integrated into ordinary mathematical documents.



## Checking the formalization

To check the formalization with a local build of Naproche run
the following commands in the root of the Naproche repository.

```bash
stack build
stack exec Naproche-SAD -- examples/geometry/formalization.ftl.tex
```

Parsing and checking the document takes about 15 to 20 seconds with an i5-8400 (as of 2021-02).

## Building the PDF

The PDF for the paper requires XeLaTeX.
It should work with any reasonably recent version of TeX Live.
Run the following from `$NAPROCHEDIR/examples/geometry/`, where `$NAPROCHEDIR` is your Naproche directory.

```bash
xelatex formalization.ftl.tex
```
