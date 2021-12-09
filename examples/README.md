# On the Examples

This folder contains a selection of example formalizations in the Naproche natural language proof checking system. The examples come in two dialects of the ForTheL controlled natural language: `.ftl` files use ASCII formating and are close to the original ForTheL language of the System for Automated Deduction (SAD); `.ftl.tex` files use standard LaTeX commands and can directly be typeset by LaTeX using appropriate preambles and style files.

The examples are chosen to demonstrate possibilities of the current Naproche which is included as a component in the Isabelle 2021-1 platform. The examples include single files devoted to single theorems from mathematical fields like number theory or analysis as well as groups of formalizations on arithmetic or set theory interlinked by "`read`" commands. There are also some odd examples about a mutilated checkerboard or recreational puzzles.

A main emphasis is on the presentation of naturally readable formalizations in LaTeX which we include as PDF-printouts. Putting arbitrary LaTeX material around the actual formalizations allows a literary style of documents which includes explanations and even graphics. 
The further development of Naproche will focus on the `.ftl.tex` format in order to build readable libraries of computer-verifiable mathematics. The classical `.ftl` format will be kept up for some time since it allows rapid experiments without worrying about LaTeX particulars. Over time, however, the formats will diverge, as we are going to extract semantic context out of typesetting information (parsing depending on LaTeX text versus math mode, matrix notation, ...).


Note that Naproche requires significant computing resources, 
since its checking mechanisms involve the continuous operation of an ATP server.
Checking longer documents from the collection of examples can take up to half an hour.
Please observe the progress of the processing in the Isabelle buffers. 
Computers satisfying the recommendations for running the current Isabelle release
should be able to run the example formalizations.
All examples were tested on an Intel i5-8400 (mid-range hexa-core desktop CPU from 2017, 65 W TDP) with 16 GB of RAM.
but most examples should also work with slightly older or lower-end hardware.
For example, an Intel Pentium N3710 (quad-core mobile CPU from 2016, 6 W TDP) with 8GB RAM can
still check most examples without the accomodations outlined below.

On weaker systems successful checking of texts may require stopping other resource-heavy processes or even adding intermediate proof steps.
One can also increase the time-out for the internal reasoner or the external ATP by Naproche commands like
`[timelimit XXX]` (default = 5 sec) or `[checktime XXX]` (default = 1 sec).
These commands can be inserted into the formalization where required.
Parts of the text may also be exempted from checking by surrounding them with
`[prove off]` ... `[prove on]` or `[check off]` ... `[check on]` commands. 
