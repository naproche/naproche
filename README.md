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
component, e.g. like this:

      init_component "$HOME/Naproche-SAD"

* open ForTheL examples in Isabelle/jEdit, e.g.

      isabelle jedit examples/powerset.ftl

* open Isabelle development environment with ForTheL examples, e.g.

      isabelle jedit -l Pure Isabelle/Test.thy


# Development #

* The Haskell Tool Stack: https://www.haskellstack.org

* Haskell IDE within VSCode: https://github.com/haskell/haskell-ide-engine


# Reference #

This program is based on the System for Automated Deduction by Andrei
Paskevich, see https://github.com/tertium/SAD
