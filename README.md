## Naproche-SAD ##

*System for Automated Deduction* (Naproche branch) -- Proof Checking of
Natural Mathematical Documents


# Build #

* Isabelle:

      isabelle build Haskell
      isabelle build -c -D Isabelle

* Haskell:

      stack build


# Test #

    for FILE in examples/*.ftl
    do
      stack exec Naproche-SAD -- "$FILE"
    done


# Isabelle PIDE #

* edit $ISABELLE_HOME_USER/etc/settings to include this directory as
component, e.g.:

      init_component "$HOME/isabelle/Naproche/repos"

* open theory with Isabelle/jEdit, e.g.

      isabelle jedit -l Pure Isabelle/Test.thy

* open ForTheL file with implicit theory context, e.g.

      isabelle jedit -l Pure examples/powerset.ftl


# Development #

* The Haskell Tool Stack: https://www.haskellstack.org

* Haskell IDE within VSCode: https://github.com/haskell/haskell-ide-engine


# Reference #

This program is based on the System for Automated Deduction by Andrei
Paskevich, see https://github.com/tertium/SAD
