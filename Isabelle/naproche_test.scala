/*
Authors: Makarius (2021)

Run Naproche tests.
*/

package isabelle.naproche

import isabelle._


object Naproche_Test
{
  val examples: Path = Path.explode("$NAPROCHE_HOME/examples")

  def run_tests(progress: Progress = new Progress): Unit =
  {
    val file_format = new isabelle.naproche.File_Format
    val tests = File.find_files(examples.file, file => file_format.detect(file.getName))

    var bad = List.empty[Path]
    for (test <- tests) {
      val path = File.path(test)
      val text = File.read(path)

      val test_failure = text.containsSlice("# test: FAILURE")
      val test_ignore = text.containsSlice("# test: IGNORE")

      if (test_ignore) {
        progress.echo("Ignoring " + path.base)
      }
      else {
        progress.echo("Checking " + path.base + " ...")
        val start = Time.now()
        val result = Isabelle_System.bash("\"$NAPROCHE_EXE\" -- " + File.bash_path(path))
        val stop = Time.now()
        val timing = stop - start

        val expect_ok = !test_failure
        progress.echo(
          (if (result.ok) "OK" else "FAILURE") +
            (if (result.ok == expect_ok) ""
            else ", but expected " + (if (expect_ok) "OK" else "FAILURE")) +
            (" (" + timing.message + " elapsed time)"))
        if (result.ok != expect_ok) bad ::= path.base
      }
    }
    if (bad.nonEmpty) error("Bad tests: " + bad.mkString(", "))
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("naproche_test", "run Naproche tests",
      Scala_Project.here, args =>
    {
      val getopts = Getopts("""
Usage: isabelle naproche_test

  Run Naproche tests.
""")

      val more_args = getopts(args)
      if (more_args.nonEmpty) getopts.usage()

      val progress = new Console_Progress()

      run_tests(progress = progress)
    })
}
