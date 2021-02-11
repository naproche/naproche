chapter \<open>Isabelle/Naproche Examples\<close>

theory Ex
  imports Naproche.Naproche
begin

section \<open>The Naproche project\<close>

text \<open>
  Naproche is a project managed by Prof. Peter Koepke, from the Mathematical
  Institute, University of Bonn. The aim is to check mathematical texts,
  written in controlled natural language.

  The source code repository is \<^url>\<open>https://github.com/anfelor/Naproche-SAD\<close>
\<close>


section \<open>Examples\<close>

text \<open>
  The directory \<^dir>\<open>$NAPROCHE_HOME/examples\<close> contains various examples, to be
  checked in the Isabelle/jEdit Prover IDE: both \<^verbatim>\<open>.ftl\<close> and \<^verbatim>\<open>.ftl.tex\<close> are
  supported; \<^verbatim>\<open>.pdf\<close> files have been produced by regular \<^verbatim>\<open>pdflatex\<close>.

  For example:

    \<^enum> \<^file>\<open>$NAPROCHE_HOME/examples/tarski.ftl\<close>
                     
    \<^enum> \<^file>\<open>$NAPROCHE_HOME/examples/tarski.ftl.tex\<close>

    \<^enum> \<^file>\<open>$NAPROCHE_HOME/examples/tarski.ftl.pdf\<close>
\<close>


section \<open>Tutorial\<close>

text \<open>
  See:

    \<^enum> \<^file>\<open>$NAPROCHE_HOME/examples/TUTORIAL.ftl.tex\<close>

    \<^enum> \<^file>\<open>$NAPROCHE_HOME/examples/TUTORIAL.ftl.pdf\<close>
\<close>


section \<open>Implementation and system integration\<close>

text \<open>
  Isabelle/Naproche integrates various tools and components as follows:

    \<^item> \<^verbatim>\<open>Naproche-SAD\<close> as command-line tool and TCP server, written in
    Haskell: \<^dir>\<open>$NAPROCHE_HOME/src/SAD\<close>

    \<^item> Isabelle/Haskell modules to help connecting the main executable to the
    Isabelle/PIDE framework: \<^file>\<open>~~/src/Tools/Haskell/Haskell.thy\<close> --- the
    generated sources appear in \<^dir>\<open>$NAPROCHE_HOME/Isabelle/src/Isabelle\<close>

    \<^item> Isabelle/ML definitions of Isar commands for checking the Formal Theory
    Language (ForTheL): \<^file>\<open>$NAPROCHE_HOME/Isabelle/Main/naproche.ML\<close>

    \<^item> Isabelle/Scala integration for the \<^verbatim>\<open>.ftl\<close> and \<^verbatim>\<open>.ftl.tex\<close>
    file-formats: \<^file>\<open>$NAPROCHE_HOME/Isabelle/file_format.scala\<close>

    \<^item> Isabelle/Scala integration for external provers managed by Isabelle
    (with robust interrupts/timeouts for all platforms):
    \<^file>\<open>$NAPROCHE_HOME/Isabelle/prover_server.scala\<close>

    \<^item> Isabelle component settings to glue everything together:
    \<^file>\<open>$NAPROCHE_HOME/etc/settings\<close>
\<close>

end

(* :maxLineLen=78: *)
