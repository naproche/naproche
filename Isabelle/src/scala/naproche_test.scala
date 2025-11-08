/*
Authors: Makarius (2021)

Run Naproche tests.
*/

package isabelle.naproche

import isabelle._


import java.io.{File => JFile}
import java.util.concurrent.Executors
import java.util.concurrent.TimeUnit


object Naproche_Test {
  def run_tests(
    progress: Progress = new Progress,
    log_dir: Option[Path] = None,
    max_jobs: Option[Int] = None,
    timeout: Time = Time.zero
  ): Unit = {
    val file_format = new Naproche_File_Format

    def relative(file: JFile): Path = File.relative_path(Naproche.NAPROCHE_MATH, File.path(file)).get
    def relative_name(file: JFile): String = relative(file).implode
    def contains_flams_dir(path: String): Boolean = path.containsSlice("/.flams/")
    val tests =
      File.find_files(Naproche.NAPROCHE_MATH.file, file => file_format.detect(file.getName) && !contains_flams_dir(relative(file).implode))
        .sortBy(relative_name)

    val bad = Synchronized(List.empty[Path])

    val executor = Executors.newFixedThreadPool(max_jobs.getOrElse(1) max 1)
    for (test <- tests) {
      executor.submit(new Runnable {
        def run(): Unit = {
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
              Isabelle_System.bash(""""$NAPROCHE_EXE" -v -- """ + File.bash_platform_path(path),
                cwd = Naproche.NAPROCHE_HOME,
                strict = false,
                watchdog =
                  if (timeout == Time.zero) Bash.Watchdog.none
                  else Bash.Watchdog(Time.seconds(0.1), _ => progress.stopped || check_timeout))
            val stop = Time.now()
            val timing = stop - start

            val expect_ok = !test_failure
            val status =
              "Finished " + path_relative + ": " +
                (if (was_timeout) "TIMEOUT"
                else if (result.interrupted) "INTERRUPT"
                else
                  (if (result.ok) "OK" else "FAILURE") +
                    (if (result.ok == expect_ok) ""
                    else ", but expected " + (if (expect_ok) "OK" else "FAILURE"))) +
                (" (" + timing.message + " elapsed time)" +
                  (if (result.ok != expect_ok) "\n" + result.err else ""))
            progress.echo(status)
            log_dir.foreach { dir0 =>
              val dir = Isabelle_System.make_directory(dir0 + path_relative)
              File.write(dir + Path.basic("status"), status)
              File.write(dir + Path.basic("output"), result.out)
              File.write(dir + Path.basic("error"), result.err)
            }
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
    Isabelle_Tool("naproche_test", "run Naproche tests", Scala_Project.here,
      { args =>
        var log_dir: Option[Path] = None
        var max_jobs: Option[Int] = None
        var options = Options.init()
        var timeout = Time.zero

        val getopts = Getopts("""
Usage: isabelle naproche_test

  Options are:
    -D DIR       directory for log files (default: none)
    -j JOBS      maximum number of parallel jobs (default: 1)
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -t SECONDS   timeout in seconds (default: 0, which means disabled)

  Run Naproche tests.
""",
          "D:" -> (arg => log_dir = Some(Path.explode(arg))),
          "j:" -> (arg => max_jobs = Some(Value.Nat.parse(arg))),
          "o:" -> (arg => options = options + arg),
          "t:" -> (arg => timeout = Time.seconds(Value.Double.parse(arg))))

        val more_args = getopts(args)
        if (more_args.nonEmpty) getopts.usage()

        val progress = new Console_Progress()

        val results =
          Build.build(options, select_dirs = List(Naproche.NAPROCHE_HOME),
            progress = progress, max_jobs = max_jobs)
        if (!results.ok) sys.exit(results.rc)

        run_tests(progress = progress, log_dir = log_dir, max_jobs = max_jobs, timeout = timeout)
      })
}
