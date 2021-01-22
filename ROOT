chapter "Naproche"

session "Naproche-Build" in "Isabelle" = Haskell +
  description "Build Isabelle/Naproche modules."
  sessions
    Naproche
  theories [condition = NAPROCHE_HOME]
    Build
  export_files (in src) [1] "*:**.hs"
  export_files (in ".") [1] "*:**.jar"

session "Naproche" in "Isabelle/Main" = Pure +
  description "Isabelle Prover IDE support for NaProChe / ForTheL."
  sessions
    Haskell
  theories [condition = NAPROCHE_HOME]
    Naproche

session "Naproche-Test" in "Isabelle/Test" = Naproche +
  description "Some Isabelle/Naproche examples for testing."
  theories [condition = NAPROCHE_HOME]
    Test
