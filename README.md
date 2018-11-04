## SAD3 ##

*System for Automated Deduction* (SAD 3rd generation) -- Proof Checking of Natural Mathematical Documents


# Build #

* Isabelle:

      isabelle build Haskell
      isabelle build -c -D Isabelle

* Haskell:

      stack build


# Test #

    for FILE in examples/*.ftl
    do
      stack exec SAD3-exe -- "$FILE"
    done


# Isabelle PIDE #

* edit $ISABELLE_HOME_USER/etc/settings to include this directory as component, e.g.:

      init_component "$HOME/isabelle/SAD3/repos"

* open theory with Isabelle/jEdit, e.g.

      isabelle jedit -l Pure Isabelle/Test.thy


# Development #

* The Haskell Tool Stack: https://www.haskellstack.org

* Haskell IDE within VSCode: https://github.com/haskell/haskell-ide-engine
