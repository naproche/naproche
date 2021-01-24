/*
Authors: Makarius (2018)

Support for NaProChe / ForTheL files in Isabelle/PIDE.
*/

package isabelle.naproche

import isabelle._


object File_Format
{
  class Agent(session_options: => Options) extends isabelle.File_Format.Agent
  {
    private def debugging: Boolean = session_options.bool("naproche_server_debugging")

    private val prover_server: Prover_Server = Prover_Server.start(debugging = debugging)

    private val process: Bash.Process =
      Bash.process("""export PATH="$E_HOME:$SPASS_HOME:$PATH"; exec "$NAPROCHE_EXE" --server""",
        cwd = Path.explode("$NAPROCHE_HOME").file)

    private val server_info: Option[Server.Info] =
      for {
        line <- File.read_line(process.stdout)
        info <- Server.Info.parse(line)
      } yield info

    private val process_result = Future.thread("Naproche-SAD") {
      process.result(
        progress_stdout = (line) => if (debugging) Output.writeln(line),
        progress_stderr = (line) => if (debugging) Output.writeln(line),
        strict = false)
    }

    if (server_info.isEmpty) {
      Thread.sleep(50)
      process.terminate
      val errs = process_result.join.err_lines
      error(cat_lines("Naproche-SAD server failure" :: errs))
    }

    override def toString: String = server_info.get.toString

    override def prover_options(options: Options): Options =
      options +
        ("naproche_server_address", server_info.get.address) +
        ("naproche_server_password", server_info.get.password) +
        ("naproche_prover_server_port", prover_server.port.toString) +
        ("naproche_prover_server_password", prover_server.password)

    override def stop
    {
      process.terminate
      prover_server.stop
      process_result.join
    }
  }
}

class File_Format extends isabelle.File_Format
{
  override def format_name: String = "forthel"

  val file_ext = ""
  def detect_tex(name: String): Boolean = name.endsWith(".ftl.tex")
  override def detect(name: String): Boolean = name.endsWith(".ftl") || detect_tex(name)

  override def theory_suffix: String = "forthel_file"
  override def theory_content(name: String): String =
    "theory " + quote(if (detect_tex(name)) "tex" else "ftl") +
    " imports Naproche.Naproche begin forthel_file " + quote(name) + " end"

  override def start(session: Session): isabelle.File_Format.Agent =
    if (session.session_options.bool("naproche_server")) {
      new File_Format.Agent(session.session_options)
    }
    else isabelle.File_Format.No_Agent
}
