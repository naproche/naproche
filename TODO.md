## TODO ##

# Admin #

* suppress generated files from repository (via .gitignore): SAD3.cabal (??)

* robust build process based on Haskell Tool Stack

* systematic runs of "test" examples

* Isabelle-specific build (optional)

* semi-automated distribution builds for Linux, macOS, Windows
  (e.g. appveyor, travis)


# Tokens and positions #

* EOF token with end position, instead of vacous EOF position (!?)

* keep comment tokens (as "improper") for syntax reports (!?)

* Block: body tokens, with "range" position for messages and reports (!?)


# Misc #

* eliminate informal `putStrLn` and `info` in favour of `putMessage`

* move provers/provers.dat to toplevel directory (no executables there) (??)

* make $SPASS_HOME/SPASS from Isabelle actually work (!?)


# Isabelle/jEdit #

* proper editor mode for .ftl files (not "FreeMarker Template Language") (!)


# Concepts #

* stay-resident server instead of command-line batch-tool (??)

* caching of old results from prefix of source, old versions etc. (??)

* parallel checking: internal and/or external provers (??)

* support for multiple (simultaneous) input files (??)

* more robust / scalable library handling (imports) (!?)

* clarify exceptions vs. errors vs. system exit, e.g. for stay-resident server
  with multiple running requests, see also
  https://wiki.haskell.org/Error_vs._Exception