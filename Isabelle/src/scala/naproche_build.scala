/*
Authors: Makarius (2021)

Build Isabelle/Naproche executable.
*/

package isabelle.naproche

import isabelle._


object Naproche_Build {
  def build(options: Options, progress: Progress = new Progress): Unit = {
    /* build session */

    val build_options = options + "naproche_server=false"

    val rc =
      Build.build_logic(build_options, Naproche.session, progress = progress,
        dirs = List(Naproche.NAPROCHE_HOME))
    if (rc != 0) error("Failed to build session " + quote(Naproche.session))


    /* export Haskell sources */

    val export_dir = Naproche.ISABELLE_NAPROCHE + Path.explode("src")
    progress.echo("Exporting Isabelle/Naproche Haskell modules: ")
    Export.export_files(Store(options), Naproche.session, export_dir.expand,
      progress = progress, export_prune = 1, export_patterns = List("Naproche.Build:**.hs"))


    /* build executable */

    progress.echo("Building executable program")

    val cwd = Naproche.NAPROCHE_HOME.file
    progress.bash("isabelle ghc_stack build", cwd = cwd, echo = true).check

    val path = progress.bash("isabelle ghc_stack path --local-install-root", cwd = cwd).check.out
    Isabelle_System.copy_file(
      Path.explode(File.standard_path(path)) + Path.explode("bin/Naproche").platform_exe,
      Isabelle_System.make_directory(Naproche.NAPROCHE_EXE_DIR))
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("naproche_build", "build Isabelle/Naproche executable", Scala_Project.here,
      { args =>
        val getopts = Getopts("""
Usage: isabelle naproche_build

  Build Isabelle/Naproche executable.
""")

        val more_args = getopts(args)
        if (more_args.nonEmpty) getopts.usage()

        val options = Options.init()
        val progress = new Console_Progress

        build(options, progress = progress)
      })
}
