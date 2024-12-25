# General

* Discontinue used TermEmpty!?

* Prefer compact Isabelle.Bytes (ShortByteString) for symbolic names,
  instead of String, Text, Lazy.Text!?

* Use Program.serial to identify Decl: but this requires IO monad, or to modify
  pro-forma serial numbers produced during parsing.

* More robust treatment of prover errors (return code): genuine error vs. timeout!?


# Isabelle/Naproche integration

* Clarify connection (or non-connection) of Isabelle.Pretty vs. Hackage prettyprinter (1.7.0).


# PIDE markup reports

* def/ref markup fact names (!?)

* instructions: completion on errors -- more robust syntax for synonyms (!??)

* more robust parsing: recover from errors (e.g. via ProofTextError construction) (!??)


# General

* formulate underlying logic + set-theory in Isabelle (syntax only, no rules):
  thus formulas can be pretty-printed via Isabelle notation

* more robust and scalable library handling (imports) (!?)

* clarify treatment of non-ASCII text: Latex vs. Isabelle symbols (!?!)

* parallel checking: internal and/or external provers (??)


# Misc

* Disambiguate chains of existential quantifications: currently writing something
  along the line of `there exist x,y,z such that ...` results in an ambiguity error.

* Handle math mode delimiters during parsing instead of during tokenizing.

* Add TeX commands for instructions.

* Add a variant of the `read` instructions that reads a file without
  checking it.

* Add LaTeX environments for subproofs, cases etc.
