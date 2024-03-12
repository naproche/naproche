# On the Examples

This folder contains a selection of example formalizations in the Naproche
natural language proof checking system. The examples come in two dialects of the
ForTheL controlled natural language: `.ftl` files use an ASCII formatted
language that is close to the original ForTheL language of the System for
Automated Deduction (SAD); `.ftl.tex` files use standard LaTeX commands and can
directly be typeset by LaTeX using appropriate preambles and style files.
Some examples are formalized in both formats.

The examples are chosen to demonstrate possibilities of the current Naproche
which is included as a component in the Isabelle2022 platform. A main
emphasis is on the presentation of naturally readable formalizations in LaTeX
for which we also include PDF-printouts. Putting arbitrary LaTeX material around
the actual formalizations allows a literary style of documents which includes
explanations and even graphics. The examples include single files as well as
folders of formalizations that are interlinked by "`read`" commands. The
spectrum reaches from recreational puzzles to undergraduate-level theorems:

* arithmetic - elementary Peano arithmetic

* foundations - Kelley-Morse like foundations of mathematics

* geometry - beginnings of Tarski geometry

* set-theory - elementary set theory

* agatha - a logic puzzle set in "Dreadsbury Mansion"

* cantor - Cantor diagonal argument

* cantor-schroeder-bernstein - classical result in cardinality theory

* checkerboard - the mutilated checkerboard

* chinese - Chinese remainder theorem

* dwarfs - a "hat puzzle"

* euclid - classical proof of infinity of primes

* furstenberg - topological proof of infinity of primes

* group - Naproche rendering of a Lean file on groups

* hausdorff - theorem on the regularity of successor cardinals

* hilbert-calculus - proving derivations in a Hilbert calculus

* koenig - theorem about sequences of cardinals

* maximum_modulus - theorem from complex analysis

* newman - Newman's theorem on rewriting systems

* numbers - introduction of number systems for Rudin's Principles of Mathematical Analysis

* paradoxes - collection of (mathematical) paradoxes

* preliminaries - basic theory of classes and sets

* prime no square - irrationality of square roots

* tarski - Tarski fixpoint theorem for lattices

* zermelo - Zermelo's well-ordering theorem

The further development of Naproche will focus on the `.ftl.tex` format in order
to build readable libraries of computer-verifiable mathematics. The classical
`.ftl` format will be kept up for some time since it allows rapid experiments
without worrying about LaTeX particulars. Over time, however, the formats will
diverge, as we are going to extract semantic context out of typesetting
information (parsing depending on LaTeX text versus math mode, matrix notation,
...).


## Requirements

Note that Naproche requires significant computing resources,
since its checking mechanisms involve the continuous operation of an ATP.
Checking longer documents from the collection of examples can take up to half an
hour.
Please observe the progress of the processing in the Isabelle buffers.
Computers satisfying the recommendations for running the current Isabelle
release should be able to run the example formalizations.
All examples were tested on an Intel i5-8400 (mid-range hexa-core desktop CPU
from 2017, 65 W TDP) with 16 GB of RAM.
But most examples should also work with slightly older or lower-end hardware.
For example, an Intel Pentium N3710 (quad-core mobile CPU from 2016, 6 W TDP)
with 8GB RAM can still check most examples without the accomodations outlined
below.

On weaker systems successful checking of texts may require stopping other
resource-heavy processes or even adding intermediate proof steps.
One can also increase the time-out for the external ATP
or the internal reasoner by Naproche commands like
`[timelimit XXX]` (default = 5 sec) or `[checktime XXX]` (default = 1 sec) resp..
These commands can be inserted into the formalization where required.
Parts of the text may also be exempted from checking by surrounding them with
`[prove off]` ... `[prove on]` or `[check off]` ... `[check on]` commands.
