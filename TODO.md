## TODO ##

# Isabelle/Naproche integration

* Isabelle/ML vs. Isabelle/Haskell/Naproche should always use TCP server
  (not command-line tool), and allow to augment the enclosing theory / proof context.

* The Isabelle/Scala prover_server should become general bash_process server, for arbitrary
  executables (name, bash script).

* Clarify connection (or non-connection) of Isabelle.Pretty vs. Hackage prettyprinter (1.7.0).


# PIDE markup reports #

* def/ref markup fact names (!?)

* instructions: completion on errors -- more robust syntax for synonyms (!??)

* more robust parsing: recover from errors (e.g. via ProofTextError construction) (!??)


# General #

* formulate underlying logic + set-theory in Isabelle (syntax only, no rules):
  thus formulas can be pretty-printed via Isabelle notation

* more robust and scalable library handling (imports) (!?)

* clarify treatment of non-ASCII text: Latex vs. Isabelle symbols (!?!)

* parallel checking: internal and/or external provers (??)


# Misc #

* more robust (less redundant) specification of options with their defaults:
  avoid duplicate information in Haskell sources, comments, init.opt

* Disambiguate chains of existential quantifications: currently writing something
  along the line of `there exist x,y,z such that ...` results in an ambiguity error.
