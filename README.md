## SAD3 ##

*System for Automated Deduction* (SAD 3rd generation) -- Proof Checking of Natural Mathematical Documents


# Build #

* Isabelle:

      isabelle build -D Isabelle

* Haskell:

      stack build


# Test #

    for FILE in examples/*.ftl
    do
      stack exec SAD3-exe -- "$FILE"
    done


# Development #

* The Haskell Tool Stack: https://www.haskellstack.org

* Haskell IDE within VSCode: https://github.com/haskell/haskell-ide-engine
