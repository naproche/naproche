/*
Authors: Makarius (2018)

Support for NaProChe / ForTheL files in Isabelle/PIDE.
*/

package isabelle.naproche

import isabelle._


object Naproche_File_Format {
  class Agent(session_options: => Options) extends File_Format.Agent {
    private def debugging: Boolean = session_options.bool("naproche_server_debugging")

    private val process: Bash.Process =
      Bash.process(""""$NAPROCHE_EXE" --server""", cwd = Path.explode("$NAPROCHE_HOME").file)

    private val server_info: Option[Server.Info] =
      for {
        line <- File.read_line(process.stdout)
        info <- Server.Info.parse(line)
      } yield info

    private val process_result = Future.thread("Naproche") {
      process.result(
        progress_stdout = (line) => if (debugging) Output.writeln(line),
        progress_stderr = (line) => if (debugging) Output.writeln(line),
        strict = false)
    }

    if (server_info.isEmpty) {
      Thread.sleep(50)
      process.terminate()
      val errs = process_result.join.err_lines
      error(cat_lines("Naproche server failure" :: errs))
    }

    override def toString: String = server_info.get.toString

    override def prover_options(options: Options): Options =
      options +
        ("naproche_server_address=" + server_info.get.address) +
        ("naproche_server_password=" + server_info.get.password)

    override def stop(): Unit = {
      process.terminate()
      process_result.join
    }
  }
}

class Naproche_File_Format extends File_Format {
  override def format_name: String = "forthel"

  val file_ext = ""
  def detect_tex(name: String): Boolean = name.endsWith(".ftl.tex")
  override def detect(name: String): Boolean = name.endsWith(".ftl") || detect_tex(name)

  override def theory_suffix: String = "forthel_file"
  override def theory_content(name: String): String =
    "theory " + quote(if (detect_tex(name)) "tex" else "ftl") +
    " imports Naproche.Naproche begin forthel_file " + quote("../" + name) + " end"
  override def theory_excluded(name: String): Boolean = name == "tex" || name == "ftl"

  override def start(session: Session): File_Format.Agent = {
    val enabled =
      Isabelle_System.getenv("NAPROCHE_EXE").nonEmpty &&
      session.session_options.bool("naproche_server")
    if (enabled) new Naproche_File_Format.Agent(session.session_options)
    else File_Format.No_Agent
  }
}
