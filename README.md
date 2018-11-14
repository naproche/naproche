# Naproche-SAD

Proof Checking of Natural Mathematical Documents, with optional support
for Isabelle Prover IDE.


## Command-line tool

### Prerequisites

  * Supported OS platforms: Linux, macOS, Windows (e.g. with Cygwin terminal)

  * The Haskell Tool Stack: https://www.haskellstack.org

  * The E Theorem Prover as executable "eprover" in the shell PATH (e.g. the
    multi-platform version provided by Isabelle: "isabelle getenv -b E_HOME")

  * Optional (for development): Haskell IDE within VSCode:
    https://github.com/haskell/haskell-ide-engine


### Build

    stack build


### Test

    for FILE in examples/*.ftl
    do
      stack exec Naproche-SAD -- "$FILE"
    done


## Isabelle Prover IDE (Isabelle/jEdit)

### Prerequisites

  * Isabelle repository clone from https://isabelle.in.tum.de/repos/isabelle

  * "Quick start in 30min" according to README_REPOSITORY
    (https://isabelle.in.tum.de/repos/isabelle/raw-file/tip/README_REPOSITORY)

  * Use Isabelle/jEdit to edit $ISABELLE_HOME_USER/etc/settings to include
    the Naproche-SAD directory as Isabelle component. E.g. like this:

        init_component "$USER_HOME/Naproche-SAD"

  * Shutdown Isabelle/jEdit before building Isabelle/Naproche as follows.


### Build

    isabelle build Haskell
    isabelle build -c -D Isabelle
    stack build


### Test

* Open ForTheL examples in Isabelle/jEdit, e.g.

      isabelle jedit examples/powerset.ftl

* Open Isabelle development environment with ForTheL examples, e.g.

      isabelle jedit -l Pure Isabelle/Test.thy


## Reference ##

This program is based on the System for Automated Deduction (SAD) by
Andrei Paskevich, see https://github.com/tertium/SAD
