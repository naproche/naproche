/*
Authors: Makarius (2021)

Isabelle/Naproche names and resources.
*/

package isabelle.naproche

import isabelle._


object Naproche {
  val ISABELLE_NAPROCHE: Path = Path.explode("$ISABELLE_NAPROCHE")
  val jar: Path = ISABELLE_NAPROCHE + Path.explode("naproche.jar")

  val NAPROCHE_HOME: Path = Path.explode("$NAPROCHE_HOME")
  val NAPROCHE_EXE: Path = Path.explode("$NAPROCHE_EXE")
  val NAPROCHE_EXE_DIR: Path = Path.explode("$NAPROCHE_EXE_DIR")
  val NAPROCHE_MATH: Path = Path.explode("$NAPROCHE_MATH")

  def platform: String = NAPROCHE_EXE_DIR.expand.base.implode
  val session = "Naproche"
}
