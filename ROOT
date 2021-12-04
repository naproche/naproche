chapter "Naproche"

session "Naproche" in "Isabelle/Main" = HOL +
  description "Isabelle/Naproche main session"
  sessions
    Haskell
  theories [condition = NAPROCHE_HOME]
    Naproche
    Build

session "Naproche-Test" in "Isabelle/Test" = Naproche +
  description "Isabelle/Naproche test session"
  theories [condition = NAPROCHE_HOME]
    Test
