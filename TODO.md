## TODO ##

# Admin #

* systematic runs of "test" examples

* Isabelle-specific build (optional)

* semi-automated distribution builds for Linux, macOS, Windows
  (e.g. appveyor, travis)


# Tokens and positions #

* keep comment tokens (as "improper") for syntax reports (!?)

* proper Block position/range based on input tokens, not output text

* more abstract type Block: no export of constructor, use makeBlock instead (!?)


# Misc #

* eliminate informal `putStr` in favour of `outputMessage`

* ensure UTF8 everywhere: stdin, stdout, files

* move provers/provers.dat to toplevel directory (no executables there) (??)

* make $SPASS_HOME/SPASS from Isabelle actually work (!?)


# General #

* clarify project / program name: "Alice" vs. "Naproche" vs. "ForTheL"

* stay-resident server instead of command-line batch-tool (??)

* caching of old results from prefix of source, old versions etc. (??)

* parallel checking: internal and/or external provers (??)

* support for multiple (simultaneous) input files (??)

* more robust / scalable library handling (imports) (!?)

* clarify exceptions vs. errors vs. system exit, e.g. for stay-resident server
  with multiple running requests, see also
  https://wiki.haskell.org/Error_vs._Exception
