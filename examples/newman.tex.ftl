\documentclass{document}

\usepackage[utf8]{inputenc}
\usepackage[english]{babel}
\usepackage{forthel}

\title{Newman's lemma}
\author{}
\date{}

\begin{document}
  \pagenumbering{gobble}

  \maketitle

  \begin{forthel}
    [synonym element/-s]
    [synonym system/-s]
    [synonym reduct/-s]

    \begin{signature}[ElmSort]
      An element is a notion.
    \end{signature}

    \begin{signature}[RelSort]
      A rewriting system is a notion.
    \end{signature}

    Let a,b,c,d,u,v,w,x,y,z denote elements. Let R,S,T denote rewriting systems.

    \begin{signature}[Reduct]
      A reduct of x in R is an element.
    \end{signature}

    Let x -R> y stand for y is a reduct of x in R.

    \begin{signature}
      x -R+> y is a relation.
    \end{signature}

    \begin{axiom}[TCDef]
      x -R+> y <=> x -R> y \/ exists z : x -R> z -R+> y.
    \end{axiom}

    \begin{axiom}[TCTrans]
      x -R+> y -R+> z => x -R+> z.
    \end{axiom}

    \begin{definition}[TCRDef]
      x -R*> y <=> x = y \/ x -R+> y.
    \end{definition}

    \begin{lemma}[TCRTrans]
      x -R*> y -R*> z => x -R*> z.
    \end{lemma}

    \begin{definition}[CRDef]
      R is confluent iff for all a,b,c  such that a -R*> b,c there exists d such
      that b,c -R*> d.
    \end{definition}

    \begin{definition}[WCRDef]
      R is locally confluent iff for all a,b,c such that a -R> b,c there exists
      d such that b,c -R*> d.
    \end{definition}

    \begin{definition}[Termin]
      R is terminating iff for all a,b a -R+> b => b -<- a.
    \end{definition}

    \begin{definition}[NFRDef]
      A normal form of x in R is an element y such that x -R*> y and y has no
      reducts in R.
    \end{definition}

    \begin{lemma}[TermNF]
      Let R be a terminating rewriting system. Every element x has a normal form
      in R.
    \end{lemma}
    \begin{proof}
      Proof by induction.
    \end{proof}


    \begin{lemma}[Newman]
      Any locally confluent terminating rewriting system is confluent.
    \end{lemma}
    \begin{proof}
      Let R be a rewriting system. Assume R is locally confluent and
      terminating.

      Let us demonstrate by induction that for all a,b,c such that a -R*> b,c
        there exists d such that b,c -R*> d. Let a,b,c be elements. Assume
        a -R+> b,c.

        Take u such that a -R> u -R*> b.
        Take v such that a -R> v -R*> c.
        Take w such that u,v -R*> w.
        Take a normal form d of w in R.

        b -R*> d. Indeed take x such that b,d -R*> x.
        c -R*> d. Indeed take y such that c,d -R*> y.
      end.
    \end{proof}
  \end{forthel}

\end{document}
