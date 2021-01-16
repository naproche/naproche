/*
Authors: Makarius (2021)

Server for external provers, managed as Isabelle bash process
(multiplatform support: Linux, macOS, Windows/Cygwin).

Commands:

  * start prover:
    IN: <prover name=NAME command_args=LINES timeout=SECONDS>INPUT</>
    OUT: UUID
    OUT: <result return_code=RC TIMING_PROPERTIES>OUTPUT</result>

    where
     RC: 0=OK, 1=ERROR, 2=FAILURE, ..., 130=INTERRUPT, 142=TIMEOUT
     INPUT: text for stdin
     OUTPUT: text from stdout ++ stderr

  * kill prover:
    IN: <kill>UUID</kill>
*/

package isabelle.naproche

import isabelle._


object Prover_Server
{
  /* literals for XML protocol */

  val PROVER = "prover"
  val KILL = "kill"
  val RESULT = "result"

  val Command_Args = new Properties.String("command_args")
  val Timeout = new Properties.Double("timeout")


  /* executables */

  val default_provers: Map[String, Path] =
    Map("eprover" -> Path.explode("$E_HOME/eprover"),
      "SPASS" -> Path.explode("$SPASS_HOME/SPASS"),
      "vampire" -> Path.explode("$VAMPIRE_HOME/vampire"))

  def apply(port: Int = 0, provers: Map[String, Path] = default_provers): Prover_Server =
    new Prover_Server(port, provers)
}

class Prover_Server private(port: Int, provers: Map[String, Path]) extends Server.Handler(port)
{
  server =>

  private val _provers = Synchronized(Map.empty[UUID.T, Bash.Process])

  override def handle(connection: Server.Connection)
  {
    def return_result(
      return_code: Int,
      timing: Timing = Timing.zero,
      output: String = "")
    {
      val props =
        Markup.Return_Code(return_code) :::
        (if (!timing.is_zero) Markup.Timing_Properties(timing) else Nil)
      val xml = XML.Elem(Markup(Prover_Server.RESULT, props), List(XML.Text(output)))

      connection.write_message(YXML.string_of_body(List(xml)))
    }

    def return_failure(output: String): Unit =
      return_result(return_code = 2, output = output)

    def start_prover(uuid: UUID.T, exe: Path, args: List[String], timeout: Time, input: String)
    {
      val process_start =
        Exn.capture {
          val tmp_dir = Isabelle_System.tmp_dir("prover")
          val input_file = File.path(tmp_dir) + Path.explode("input")
          File.write(input_file, input)
          val script =
            File.bash_path(exe) + " " + Bash.strings(args) + " < " + File.bash_path(input_file)
          val process = Bash.process(script, cwd = tmp_dir)
          (tmp_dir, process)
        }

      process_start match {
        case Exn.Exn(exn) => return_failure(Exn.message(exn))
        case Exn.Res((tmp_dir, process)) =>
          _provers.change(provers => provers + (uuid -> process))

          Isabelle_Thread.fork(name = "prover") {
            @volatile var was_timeout = false
            val result =
              Exn.capture {
                process.result(
                  watchdog =
                    if (timeout.is_zero) None
                    else Some((timeout, _ => { was_timeout = true; true })),
                  strict = false)
              }

            result match {
              case Exn.Exn(exn) => return_failure(Exn.message(exn))
              case Exn.Res(res) =>
                val rc = if (!res.ok && was_timeout) Process_Result.timeout_rc else res.rc
                val output = cat_lines(res.out_lines ::: res.err_lines)
                return_result(rc, timing = res.timing, output = output)
            }

            _provers.change(provers => provers - uuid)
            Isabelle_System.rm_tree(tmp_dir)
          }
      }
    }

    connection.read_message() match {
      case None =>
      case Some(text) =>
        YXML.parse_body(text) match {
          case List(XML.Elem(Markup(Prover_Server.PROVER, props), body)) =>
            val name = Markup.Name.unapply(props).getOrElse("")
            val args = split_lines(Prover_Server.Command_Args.unapply(props).getOrElse(""))
            val timeout = Time.seconds(Prover_Server.Timeout.unapply(props).getOrElse(0))

            val uuid = UUID.random()
            connection.write_message(uuid.toString)

            provers.get(name) match {
              case None => return_failure("Unknown prover: " + quote(name))
              case Some(exe) => start_prover(uuid, exe, args, timeout, XML.content(body))
            }

            connection.await_close()

          case List(XML.Elem(Markup(Prover_Server.KILL, _), UUID(uuid))) =>
            _provers.value.get(uuid).foreach(_.terminate)

          case _ =>
        }
    }
  }
}
