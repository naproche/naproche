# General

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

* In the `render-library` mode, sort the `inputref` commands topologically
  (relative to the `importmodule` dependencies between the `inputref`ed files):

  - Use
    `getAllTextMatches (<string> =~ "\\\\importmodule\\[.*?\\]{.*?}") :: [String]`
    from
    [`Text.Regex.TDFA`](https://hackage-content.haskell.org/package/regex-tdfa-1.3.2.4/docs/Text-Regex-TDFA.html)
    to extract all `\importmodule[...]{...}` commands from the string `<string>`
    that constitutes the content of an `inputref`ed file.

  - Use `topSort` from
    [`Data.Graph`](https://hackage-content.haskell.org/package/containers-0.8/docs/Data-Graph.html)
    to sort the dependency graph.

* Track the current archive and/or file path during parsing and use it to
  provide a name space for top-level section identifiers. This would allow to

  - disambiguate identical top-level section idendifiers that stem from
    different files/modules.

  - use `by \sref[archive=<archive>,file=<file>]{<id>}` to reference a top-level
    section that lives in a file that was imported from an sTeX archive (e.g. a
    library) into the current formalization.

* Use `\NewDocumentCommand` and friends for more robust LaTeX
  commands/environments in our LaTeX packages.
