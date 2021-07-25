chapter "Naproche"

session "Naproche" in "Isabelle/Main" = Pure +
  description "Isabelle/Naproche main session"
  options [naproche_server = false]
  sessions
    Haskell
  theories [condition = NAPROCHE_HOME]
    Naproche
    Build

session "Naproche-Test" in "Isabelle/Test" = Naproche +
  description "Isabelle/Naproche test session"
  theories [condition = NAPROCHE_HOME]
    Test
