# The Naproche Library

This is the standard library of Naproche. It contains

  1. tex sources for prettier documents under `tex/`
  2. A short formalization of Tarskian geometry under `geometry/`
  3. Several examples of various Naproche features as part of longer formalizations under `examples/`
  4. A 20-file long formalization of set theory up to Silvers Theorem in `SetTheory/`

Furthermore it includes a `prelude.ftl.tex` which implements the built-in axioms of
Isabelle Naproche 2021 and a file `nbg.ftl.tex` which extends these to include
more useful notions.

Currently, not all of these files have been ported to the new code.
This is the current state of progress:

Can be proof-checked (with 1 second time):

  - `prelude.ftl.tex`
  - `nbg.ftl.tex`
  - `examples/cantor.ftl.tex`
  - `examples/prime_no_square.ftl.tex`

Can be type-checked (number of failing goals with one second time):

  - `geometry/formalisation.ftl.tex` (4)
  - `examples/fuerstenberg.ftl.tex` (20)
  - `examples/euclid.ftl.tex` (13)
  - `examples/checkerboard.ftl.tex` (33)

Can be transformed into the new representation:

  - `examples/maximum_modulus.ftl.tex`