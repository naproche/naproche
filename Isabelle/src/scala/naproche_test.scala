/*
Authors: Makarius (2021)

Run Naproche tests.
*/

package isabelle.naproche

import isabelle._


import java.io.{File => JFile}
import java.util.concurrent.Executors
import java.util.concurrent.TimeUnit


object Naproche_Test
{
  val naproche_home: Path = Path.explode("$NAPROCHE_HOME")
  val examples: Path = naproche_home + Path.explode("examples")

  def run_tests(
    options: Options,
    progress: Progress = new Progress,
    max_jobs: Int = 1,
    timeout: Time = Time.zero): Unit =
  {
    val file_format = new Naproche_File_Format

    def relative(file: JFile): Path = File.relative_path(examples, File.path(file)).get
    def relative_name(file: JFile): String = relative(file).implode
    val tests =
      File.find_files(examples.file, file => file_format.detect(file.getName)).sortBy(relative_name)

    val bad = Synchronized(List.empty[Path])

    val executor = Executors.newFixedThreadPool(max_jobs max 1)
    for (test <- tests) {
      executor.submit(new Runnable {
        def run =
        {
          val path = File.path(test)
          val text = File.read(path)

          val test_failure = text.containsSlice("# test: FAILURE")
          val test_ignore = text.containsSlice("# test: IGNORE")

          val path_relative = relative(test)
          if (test_ignore) {
            progress.echo("Ignoring " + path_relative)
          }
          else {
            progress.expose_interrupt()
            progress.echo("Checking " + path_relative + " ...")
            val start = Time.now()
            @volatile var was_timeout: Boolean = false
            def check_timeout: Boolean =
              Time.now() > start + timeout && { was_timeout = true; true }
            val result =
              Isabelle_System.bash(
                "export PATH=\"$E_HOME:$SPASS_HOME:$PATH\"\n" +
                "\"$NAPROCHE_EXE\" " +
                " -- " + File.bash_platform_path(path),
                cwd = naproche_home.file,
                strict = false,
                watchdog =
                  if (timeout == Time.zero) None
                  else Some((Time.seconds(0.1), _ => progress.stopped || check_timeout)))
            val stop = Time.now()
            val timing = stop - start

            val expect_ok = !test_failure
            progress.echo("Finished " + path_relative + ": " +
              (if (was_timeout) "TIMEOUT"
               else if (result.rc == 130) "INTERRUPT"
               else
                (if (result.ok) "OK" else "FAILURE") +
                (if (result.ok == expect_ok) ""
                else ", but expected " + (if (expect_ok) "OK" else "FAILURE"))) +
                (" (" + timing.message + " elapsed time)" +
                (if (result.ok != expect_ok) "\n" + result.err else "")))
            if (result.ok != expect_ok) bad.change(path_relative :: _)
          }
        }
      })
    }
    executor.shutdown()
    executor.awaitTermination(Long.MaxValue, TimeUnit.SECONDS)

    bad.value match {
      case Nil =>
      case bad_tests => error("Bad tests: " + bad_tests.mkString(", "))
    }
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("naproche_test", "run Naproche tests",
      Scala_Project.here, args =>
    {
      var max_jobs = 1
      var options = Options.init()
      var timeout = Time.zero

      val getopts = Getopts("""
Usage: isabelle naproche_test

  Options are:
    -j JOBS      maximum number of parallel jobs (default: 1)
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -t SECONDS   timeout in seconds (default: 0, which means disabled)

  Run Naproche tests.
""",
        "j:" -> (arg => max_jobs = Value.Int.parse(arg)),
        "o:" -> (arg => options = options + arg),
        "t:" -> (arg => timeout = Time.seconds(Value.Double.parse(arg))))

      val more_args = getopts(args)
      if (more_args.nonEmpty) getopts.usage()

      val progress = new Console_Progress()

      val results =
        Build.build(options, select_dirs = List(naproche_home),
          progress = progress, max_jobs = max_jobs)
      if (!results.ok) sys.exit(results.rc)

      run_tests(options, progress = progress, max_jobs = max_jobs, timeout = timeout)
    })
}
