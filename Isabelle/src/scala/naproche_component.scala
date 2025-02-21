/*
Authors: Makarius (2021)

Build Isabelle/Naproche component from repository.
*/

package isabelle.naproche

import isabelle._

import java.io.{File => JFile}


object Naproche_Component {
  val cleanup_names: List[String] = List("_config.yml")
  val cleanup_trees: List[String] =
    List(".git", ".gitignore", ".travis.yml", "math_pdf", "examples/test", "Isabelle/Admin")

  val output_tail = 20


  /* build component */

  def build_component(
    progress: Progress = new Progress,
    target_dir: Path = Path.current,
    pdf_documents: Boolean = false
  ): Unit = {
    Isabelle_System.require_command("git")


    /* repository version */

    val version = {
      val git_show = progress.bash("git show", cwd = Naproche.NAPROCHE_HOME).check
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

    Isabelle_System.with_tmp_file("archive", "tar") { archive =>
      progress.bash(
        "git archive --output=" + File.bash_path(archive) + " -- " + Bash.string(version),
        cwd = Naproche.NAPROCHE_HOME).check
      progress.bash("tar -x -f " + File.bash_path(archive), cwd = component_dir).check
    }

    progress.echo("Copying " + Naproche.NAPROCHE_EXE_DIR.expand)
    Isabelle_System.copy_dir(Naproche.NAPROCHE_EXE_DIR, component_dir)

    progress.echo("Copying " + Naproche.jar.expand)
    Isabelle_System.copy_file(Naproche.jar, component_dir + Path.explode("Isabelle"))

    File.change(component_dir + Path.explode("etc/build.props")) {
      s => s.replaceAll("no_build\\s*=.*", "no_build = true")
    }

    File.change(component_dir + Path.explode("etc/settings")) {
      s => s + "\nclasspath \"$ISABELLE_NAPROCHE/naproche.jar\"\n"
    }


    /* PDF documents */

    var tex_failed = Set.empty[Path]

    if (pdf_documents) {
      val TeX_Program = """^% +!TEX +program += +(\w+) *$""".r

      val math = component_dir + Path.explode("math")
      val math_pdf = component_dir + Path.explode("math_pdf")
      Isabelle_System.copy_dir(math, math_pdf)
      val currentDirectory = System.getProperty("user.dir")

      // Value of the MATTHUB variable used by sTeX.
      // `replaceAll("\"", "")` is used as a quick'n'dirty hack to remove the
      // leading and trailing quotation mark produced by `toString`.
      val mathhub = (Path.explode(currentDirectory) + math_pdf).toString.replaceAll("\"", "")

      def relative(file: JFile): Path = File.relative_path(math_pdf, File.path(file)).get
      def relative_name(file: JFile): String = relative(file).implode

      for {
        file <- File.find_files(math_pdf.file, _.getName.endsWith(".tex")).sortBy(relative_name)
        text = File.read(file)
        if text.containsSlice("\\documentclass")
      } {
        val tex_path = relative(file)
        val tex_dir = File.path(file).dir
        val tex_name = tex_path.base.implode
        val tex_program =
          split_lines(text).collectFirst({ case TeX_Program(prg) => prg }).getOrElse("pdflatex")
        val tex_env =
          List("TEXINPUTS" -> Naproche.TEXINPUTS, "MATHHUB" -> mathhub)

        val pdf_path = Path.explode(Library.try_unsuffix(".tex", tex_path.implode).get).pdf

        progress.expose_interrupt()
        progress.echo("Building " + pdf_path + " with " + tex_program)
        for (_ <- 1 to 2 if !tex_failed(tex_path)) {
          val result =
            progress.bash(Bash.string(tex_program) + " " + Bash.string(tex_name),
              cwd = tex_dir, env = Isabelle_System.settings(tex_env))
          if (!result.ok) {
            tex_failed += tex_path
            progress.echo_error_message(cat_lines("LaTeX failed:"
              :: result.out_lines.drop(result.out_lines.length - output_tail max 0)))
          }
        }
        if (!tex_failed(tex_path)) {
          Isabelle_System.copy_file(math_pdf + pdf_path, math + pdf_path.dir)
        }
      }
    }


    /* cleanup */

    File.find_files(component_dir.absolute_file,
      pred = file => cleanup_names.contains(file.getName)).foreach(_.delete)

    cleanup_trees.foreach(name =>
      Isabelle_System.rm_tree(component_dir + Path.explode(name)))


    /* component archive */

    val component_archive = Path.explode(component + "_" + Naproche.platform + ".tar.gz")

    progress.echo("Component archive " + (target_dir + component_archive))
    progress.bash("tar -czf " + File.bash_path(component_archive) + " " + Bash.string(component),
      cwd = target_dir).check


    /* postponed TeX failures */

    if (tex_failed.nonEmpty) {
      error("LaTeX failed for " + tex_failed.size + " files:\n  " +
        tex_failed.toList.map(_.implode).sorted.mkString("\n  "))
    }
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("naproche_component", "build Isabelle/Naproche component from repository",
      Scala_Project.here,
      { args =>
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
