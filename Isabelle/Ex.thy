chapter \<open>Isabelle/Naproche Examples\<close>

theory Ex
  imports Naproche.Naproche
begin

text \<open>
  Naproche-SAD is a project managed by Prof. Peter Koepke, from the
  Mathematical Institute, University of Bonn.

  The aim is to check mathematical texts, written in controlled natural
  language. There are two input formats:

    \<^enum> The Formal Theory Language (ForTheL), e.g. see
      \<^file>\<open>$NAPROCHE_HOME/examples/tarski.ftl\<close>

    \<^enum> A variant of LaTeX that is structured like ForTheL, e.g. see
      \<^file>\<open>$NAPROCHE_HOME/examples/tarski.ftl.tex\<close>

  Further examples are available in the directory \<^dir>\<open>$NAPROCHE_HOME/examples\<close>.

  The Isabelle/jEdit Prover IDE understands both \<^verbatim>\<open>.ftl\<close> and \<^verbatim>\<open>.ftl.tex\<close>
  files, with spontaneous checking by the Naproche-SAD server process
  running in the background.
\<close>

end
