## TODO ##

# Admin #

* suppress generated files from repository (via .gitignore): SAD3.cabal (??)

* robust build process based on Haskell Tool Stack

* systematic runs of "test" examples

* Isabelle-specific build (optional)

* semi-automated distribution builds for Linux, macOS, Windows
  (e.g. appveyor, travis)


# Misc #

* more coherent short/long command-line options (e.g. -h vs. --help)

* more robust treatment of external provers:
    + better error messages
    + avoid "fishing" from the user's PATH environment
      (e.g. by re-using E_HOME, SPASS_HOME from Isabelle distribution)


# Isabelle/jEdit #

* proper editor mode for .ftl files (not "FreeMarker Template Language") (!)


# Concepts #

* stay-resident server instead of command-line batch-tool (??)

* caching of old results from prefix of source, old versions etc. (??)

* parallel checking: internal and/or external provers (??)

* support for multiple (simultaneous) input files (??)

* more robust / scalable library handling (imports) (!?)
