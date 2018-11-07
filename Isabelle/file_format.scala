/*
Authors: Makarius (2018)

Support for NaProChe / ForTheL files in Isabelle/PIDE.
*/

package isabelle.naproche

import isabelle._

class File_Format extends isabelle.File_Format
{
  val format_name: String = "forthel"
  val file_ext: String = "ftl"

  override def theory_suffix: String = "forthel_file"
  override def theory_content(name: String): String =
    """theory "ftl" imports Naproche.Naproche begin forthel_file """ + quote(name) + """ end"""
}
