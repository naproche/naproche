/*
Authors: Makarius (2021)

Build Isabelle/Naproche component from repository.
*/

package isabelle.naproche

import isabelle._


object Naproche_Component
{
  val naproche_home: Path = Path.explode("$NAPROCHE_HOME")
  val naproche_jar: Path = Path.explode("$NAPROCHE_JAR")
  val naproche_exe_dir: Path = Path.explode("$NAPROCHE_EXE_DIR")
  def naproche_platform: String = naproche_exe_dir.expand.base.implode

  val cleanup_names: List[String] = List("_config.yml")
  val cleanup_trees: List[String] =
    List(".git", ".gitignore", ".travis.yml", "examples_pdf", "examples/test")

  val output_tail = 20


  /* build component */

  def build_component(
    progress: Progress = new Progress,
    target_dir: Path = Path.current,
    pdf_documents: Boolean = false): Unit =
  {
    Isabelle_System.require_command("git")


    /* repository version */

    val version =
    {
      val git_show = progress.bash("git show", cwd = naproche_home.file).check
      val opt_version =
        for {
          line <- git_show.out_lines.headOption
          id <- Library.try_unprefix("commit ", line)
        } yield id.substring(0, 12)
      opt_version.getOrElse(
        error("Malformed output of git show:\n" + cat_lines(git_show.out_lines.take(1))))
    }


    /* component directory */

    val component = "naproche-" + version
    val component_dir = Isabelle_System.new_directory(target_dir + Path.basic(component))
    progress.echo("Component directory " + component_dir)


    /* copy content */

    Isabelle_System.with_tmp_file("archive", "tar")(archive =>
    {
      progress.bash(
        "git archive --output=" + File.bash_path(archive) + " -- " + Bash.string(version),
        cwd = naproche_home.file).check
      progress.bash("tar -x -f " + File.bash_path(archive), cwd = component_dir.file).check
    })

    progress.echo("Copying " + naproche_exe_dir.expand)
    Isabelle_System.copy_dir(naproche_exe_dir, component_dir)

    progress.echo("Copying " + naproche_jar.expand)
    File.copy(naproche_jar, component_dir + Path.explode("Isabelle"))


    /* PDF documents */

    if (pdf_documents) {
      val examples = component_dir + Path.explode("examples")
      val examples_pdf = component_dir + Path.explode("examples_pdf")
      Isabelle_System.copy_dir(examples, examples_pdf)
      for {
        name <- File.read_dir(examples)
        base_name <- Library.try_unsuffix(".tex", name)
        text = File.read(examples + Path.explode(name))
        if text.containsSlice("\\documentclass")
      } {
        val pdf_name = Path.basic(base_name).pdf
        progress.expose_interrupt()
        progress.echo("Building " + pdf_name)
        for (_ <- 1 to 2) {
          val result = progress.bash("pdflatex " + Bash.string(name), cwd = examples_pdf.file)
          if (!result.ok) {
            error(cat_lines("LaTeX failed:"
              :: result.out_lines.drop(result.out_lines.length - output_tail max 0)))
          }
        }
        File.copy(examples_pdf + pdf_name, examples)
      }
    }


    /* cleanup */

    File.find_files(component_dir.absolute_file,
      pred = file => cleanup_names.contains(file.getName)).foreach(_.delete)

    cleanup_trees.foreach(name =>
      Isabelle_System.rm_tree(component_dir + Path.explode(name)))

    File.write(component_dir + Path.explode("etc/no_admin"), "")


    /* component archive */

    val component_archive = Path.explode(component + "_" + naproche_platform + ".tar.gz")

    progress.echo("Component archive " + (target_dir + component_archive))
    progress.bash("tar -czf " + File.bash_path(component_archive) + " " + Bash.string(component),
      cwd = target_dir.file).check
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("naproche_component", "build Isabelle/Naproche component from repository",
      Scala_Project.here, args =>
    {
      var target_dir = Path.current
      var pdf_documents = false

      val getopts = Getopts("""
Usage: isabelle naproche_component [OPTIONS]

  Options are:
    -D DIR       target directory (default ".")
    -P           produce PDF documents

  Build Isabelle/Naproche component from repository.
""",
        "D:" -> (arg => target_dir = Path.explode(arg)),
        "P" -> (_ => pdf_documents = true))

      val more_args = getopts(args)
      if (more_args.nonEmpty) getopts.usage()

      val progress = new Console_Progress()

      build_component(progress = progress, target_dir = target_dir, pdf_documents = pdf_documents)
    })
}
