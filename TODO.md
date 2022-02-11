## Questions ##

* Is there a remaining purpose of the init.opt file (prelude for parameters)?
  It dilutes the notion of default values for parameters and "drop" instructions.
  In the past it might have been useful to specify the prover executable, but
  this is now done via environment variables like NAPROCHE_EPROVER.

* Is there a purpose for DropCommand instructions?

## TODO ##

# General

* Discontinue symEncode / symDecode!? TPTP can handle arbitrary names via
  single quoted string literals.

* E prover 2.6 (re-used from Isabelle) breaks examples/koenig.ftl.tex while examples/koenig.ftl
  still works. What is going on here?

* Discontinue used TermEmpty!?

* Prefer compact Isabelle.Bytes (ShortByteString) for symbolic names,
  instead of String, Text, Lazy.Text!?

* Use Program.serial to identify Decl: but this requires IO monad, or to modify
  pro-forma serial numbers produced during parsing.

* More robust treatment of prover errors (return code): genuine error vs. timeout!?


# Isabelle/Naproche integration

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

* Disambiguate chains of existential quantifications: currently writing something
  along the line of `there exist x,y,z such that ...` results in an ambiguity error.
