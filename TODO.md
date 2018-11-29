## TODO ##

# Misc #

* eliminate odd crash of --prover spass examples/Maximum_principle.ftl:
  "Undefined symbol sdtcflbdtrb."

* proper names for instructions "setCtxt", "drpCtxt", "addCtxt" etc. (!?)

* more robust (less redundant) specification of options with their defaults:
  avoid duplicate information in Haskell sources, comments, init.opt


# PIDE markup reports #

* def/ref markup fact names

* instructions: completion on errors -- more robust syntax for synonyms!?


# Admin #

* systematic runs of "test" examples

* Isabelle-specific build (optional)

* semi-automated distribution builds for Linux, macOS, Windows
  (e.g. appveyor, travis)


# General #

* stay-resident server instead of command-line batch-tool (??)

* caching of old results from prefix of source, old versions etc. (??)

* support for multiple (simultaneous) input files (??)

* more robust and scalable library handling (imports) (!?)

* clarify treatment of non-ASCII text: Latex vs. Isabelle symbols (!?!)

* parallel checking: internal and/or external provers (??)

* incremental output of Isabelle/ML Bash.process, e.g. via socket or fifo (?!)

