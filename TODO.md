## TODO ##

# Admin #

* systematic runs of "test" examples

* Isabelle-specific build (optional)

* semi-automated distribution builds for Linux, macOS, Windows
  (e.g. appveyor, travis)


# Misc #

* move provers/provers.dat to toplevel directory (no executables there) (??)

* make $SPASS_HOME/SPASS from Isabelle actually work (!?)

* proper names for instructions "setCtxt", "drpCtxt", "addCtxt" etc. (!?)


# markup reports #

* clarify Markup.expression "text block": duplicates!? sub-structure!?

* def/ref positions and unique id for declared variables, fact names etc.

* instructions: TI/PD position, completion on errors

* vacous keywords: "let us show that", "proof", "qed" etc.


# General #

* incremental output of Isabelle/ML Bash.process, e.g. via socket (?!)

* stay-resident server instead of command-line batch-tool (??)

* caching of old results from prefix of source, old versions etc. (??)

* parallel checking: internal and/or external provers (??)

* support for multiple (simultaneous) input files (??)

* more robust / scalable library handling (imports) (!?)

* clarify error handling in Main, e.g. for stay-resident server
  with multiple running requests, see also
  https://wiki.haskell.org/Error_vs._Exception
