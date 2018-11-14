## TODO ##

# Misc #

* make $SPASS_HOME/SPASS from Isabelle actually work (!?)

* proper names for instructions "setCtxt", "drpCtxt", "addCtxt" etc. (!?)

* more robust (less redundant) specification of options with their defaults:
  avoid duplicate information in Haskell sources, comments, init.opt


# PIDE markup reports #

* clarify Markup.expression "text block": duplicates!? sub-structure!?

* def/ref positions and unique id for declared variables, fact names etc.

* instructions: TI/PD position, completion on errors

* vacous keywords: "let us show that", "proof", "qed" etc.


# Admin #

* systematic runs of "test" examples

* Isabelle-specific build (optional)

* semi-automated distribution builds for Linux, macOS, Windows
  (e.g. appveyor, travis)


# General #

* support for multiple (simultaneous) input files (??)

* more robust and scalable library handling (imports) (!?)

* incremental output of Isabelle/ML Bash.process, e.g. via socket or fifo (?!)

* stay-resident server instead of command-line batch-tool (??)

* caching of old results from prefix of source, old versions etc. (??)

* parallel checking: internal and/or external provers (??)

* clarify treatment of non-ASCII text: Latex vs. Isabelle symbols vs. Unicode (!?!)
