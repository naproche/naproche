/*
Authors: Makarius (2021)

Command-line tools for Isabelle/Naproche.
*/

package isabelle.naproche


class Admin_Tools extends isabelle.Isabelle_Scala_Tools(
  Naproche_Build.isabelle_tool,
  Naproche_Component.isabelle_tool,
  Naproche_Test.isabelle_tool)
