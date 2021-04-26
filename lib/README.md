# The Naproche Library

This is the standard library of Naproche. It contains

  1. tex sources for prettier documents under `tex/`
  2. A short formalization of Tarskian geometry under `geometry/`
  3. Several examples of various Naproche features as part of longer formalizations under `examples/`
  4. A 20-file long formalization of set theory up to Silvers Theorem in `SetTheory/`

Furthermore it includes a `prelude.ftl.tex` which implements the built-in axioms of
Isabelle Naproche 2021 and a file `MorseKelley.ftl.tex` which extends these to include
more useful notions.

Currently, not all of these files have been ported to the new code.
This is the current state of progress:

Can be proof-checked:

  - `prelude.ftl.tex`
  - `MorseKelley.ftl.tex`
  - `geometry/formalisation.ftl.tex` (except for two lemmas and two others take very long)

Can be type-checked:
  
  - `examples/cantor.ftl.tex`
  - `examples/prime_no_square.ftl.tex`

Can be transformed into the new representation:

  - `examples/fuerstenberg.ftl.tex`
  - `examples/checkerboard.ftl.tex`