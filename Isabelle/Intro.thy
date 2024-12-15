chapter \<open>Introduction to Isabelle/Naproche\<close>

text \<open>
  Note: Isabelle/jEdit allows to open hyperlinks (URLs, files, directories)
  via CONTROL-mouse-click (Linux, Windows) or COMMAND-mouse-click (macOS).

  PDF files can be opened directly by these hyperlinks, while the jEdit File
  Browser requires the action "Open in Desktop" via the right-click menu.
\<close>

theory Intro
  imports Naproche.Naproche
begin

section \<open>Isabelle/Naproche\<close>

text \<open>
  The Isabelle/Naproche system provides interactive editing and concurrent
  automatic checking of mathematical texts, written in the controlled natural
  language ForTheL. Input files are parsed and transformed into a series of
  first-order proof tasks to be discharged by external ATPs. Naproche employs
  the provers E and Vampire that are components of Isabelle.

  ForTheL files in \<^verbatim>\<open>.ftl.tex\<close> format use LaTeX symbols and constructs, and
  may be turned into \<^verbatim>\<open>.pdf\<close> files that resemble ordinary mathematical texts.
  The development of the Naproche proof checker is carried out at the
  University of Bonn, coordinated by Peter Koepke (koepke@math.uni-bonn.de).
  The source code repository is \<^url>\<open>https://github.com/naproche/naproche\<close>

  The homepage of the Isabelle/Naproche system is located at
  \<^url>\<open>https://naproche.github.io/\<close>. It includes general information, a tutorial,
  and features a web interface for Naproche, which can be used to try Naproche
  on any device (even mobile phones). The web interface is located at
  \<^url>\<open>https://naproche.github.io/try\<close>.

  The Naproche system is part of the long-term Naproche (Natural Proof
  Checking) project with Bernhard Schröder, at the Universities of Bonn and
  Duisburg-Essen (\<^url>\<open>http://naproche.net\<close>). Andrei Paskevich kindly let us
  take over his source code of SAD (System for Automated Deduction,
  \<^url>\<open>http://nevidal.org/sad.en.html\<close>) and gave essential advice.
  Development of the program and examples was carried out by:

    \<^item> Adrian De Lon
    \<^item> Adrian Marti
    \<^item> Anton Lorenzen
    \<^item> Makarius Wenzel
    \<^item> Marcel Schütz
    \<^item> Peter Koepke
    \<^item> Steffen Frerix

  Note that the Naproche system is research quality experimental software
  which may exhibit unexpected behaviour and bugs. Naproche does not yet
  produce independently checkable correctness certificates for checked texts,
  but \<^system_option>\<open>naproche_isabelle\<close> enables limited integration with
  Isabelle/HOL.

  The following CADE System description covers an earlier version of
  Isabelle/Naproche, according to Isabelle2021 (February 2021):

    De Lon A., Koepke P., Lorenzen A., Marti A., Schütz M., Wenzel M. (2021)
    The Isabelle/Naproche Natural Language Proof Assistant. In: Platzer A.,
    Sutcliffe G. (eds) Automated Deduction – CADE 28. CADE 2021. Lecture Notes
    in Computer Science, vol 12699. Springer, Cham.
    \<^url>\<open>https://doi.org/10.1007/978-3-030-79876-5_36\<close>
\<close>


section \<open>Examples\<close>

text \<open>
  The folder \<^dir>\<open>$NAPROCHE_HOME/examples\<close> contains a selection of
  formalizations which demonstrate the naturalness and coverage of Naproche.
  These examples have been checked successfully on mid-range consumer laptops.
  Checking times vary from a few seconds to up to half an hour, depending on
  the number and difficulty of proof tasks sent out to an ATP. Checking,
  however, may fail, because ATP proof searches are restricted by wallclock
  timeouts and depend significantly on system speeds and states. It may be
  necessary to increase the standard ATP timeout of 3 seconds to X = 10, 20,
  or more seconds by inserting \<^verbatim>\<open>[timelimit X]\<close> commands. In stubborn cases,
  one can try to insert further proof steps.

  The Isabelle/jEdit Prover IDE can check \<^verbatim>\<open>.ftl\<close> and \<^verbatim>\<open>.ftl.tex\<close> files;
  corresponding \<^verbatim>\<open>.pdf\<close> files have been produced by regular \<^verbatim>\<open>pdflatex\<close>. Some
  of the examples have been taken over from SAD and are rewritten in the LaTeX
  dialect \<^verbatim>\<open>.ftl.tex\<close>. For example:

    \<^enum> \<^file>\<open>$NAPROCHE_HOME/examples/tarski.ftl\<close>

    \<^enum> \<^file>\<open>$NAPROCHE_HOME/examples/tarski.ftl.tex\<close>

    \<^enum> \<^file>\<open>$NAPROCHE_HOME/examples/tarski.ftl.pdf\<close>

  In LaTeX mode, only material in \begin{forthel} ... \end{forthel}
  environments is fed to the parser and proof checker. Putting comments
  outside those environments allows a ``literate'' formalization style where
  forthel environments are accentuated in the pdf output by, e.g., a light
  gray background. See

    \<^enum> \<^file>\<open>$NAPROCHE_HOME/examples/checkerboard.ftl.tex\<close>

  which is a chapter from a conference submission on a proof-checked
  formalization of the Mutilated Checkerboard Problem in Naproche.
\<close>


section \<open>Tutorial\<close>

text \<open>
  A brief introduction to Naproche is contained in

    \<^enum> \<^file>\<open>$NAPROCHE_HOME/examples/TUTORIAL.ftl.pdf\<close>.

  Practical formalization experiments can carried out by playing with the
  source code of the tutorial which itself is a proof-checked ForTheL text:

    \<^enum> \<^file>\<open>$NAPROCHE_HOME/examples/TUTORIAL.ftl.tex\<close>.

  Andrei Paskevich's ``The syntax and semantics of the ForTheL language''

    \<^enum> \<^url>\<open>http://nevidal.org/download/forthel.pdf\<close>

  is still recommended as a guide to the principles of ForTheL.
\<close>


section \<open>Implementation\<close>

text \<open>
  The Isabelle/Naproche implementation integrates various tools and components
  as follows:

    \<^item> \<^verbatim>\<open>Naproche\<close> as command-line tool and TCP server, written in
      Haskell: \<^dir>\<open>$NAPROCHE_HOME/src/Naproche\<close> and \<^dir>\<open>$NAPROCHE_HOME/src/SAD\<close>

    \<^item> Isabelle/Haskell modules to help connecting the main executable to the
      Isabelle/PIDE framework: \<^file>\<open>~~/src/Tools/Haskell/Haskell.thy\<close> --- the
      generated sources appear in \<^dir>\<open>$NAPROCHE_HOME/Isabelle/src/Isabelle\<close>

    \<^item> Isabelle/ML definitions of Isar commands for checking the Formal Theory
      Language (ForTheL): \<^file>\<open>$NAPROCHE_HOME/Isabelle/Main/naproche.ML\<close>

    \<^item> Isabelle/Scala integration for the \<^verbatim>\<open>.ftl\<close> and \<^verbatim>\<open>.ftl.tex\<close> file-formats:
      \<^file>\<open>$NAPROCHE_HOME/Isabelle/src/scala/naproche_file_format.scala\<close>

    \<^item> Isabelle component setup to glue everything together:
      \<^file>\<open>$NAPROCHE_HOME/etc/build.props\<close> and \<^file>\<open>$NAPROCHE_HOME/etc/settings\<close>
\<close>

end

(* :maxLineLen=78: *)
