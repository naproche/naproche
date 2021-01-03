\documentclass{document}

\usepackage[utf8]{inputenc}
\usepackage[english]{babel}
\usepackage{forthel}

\title{Regularity of successor cardinals}
\author{}
\date{}

\begin{document}
  \pagenumbering{gobble}

  \maketitle

  \begin{forthel}
    [synonym cardinal/-s]
    [synonym ordinal/-s]

    Let M,N denote sets.

    \begin{axiom}
      For any objects a,b,c,d if (a,b) = (c,d) then a = c and b = d.
    \end{axiom}

    \begin{definition}
      Prod(M,N) = {(x,y) | x is an element of M and y is an element of N}.
    \end{definition}

    \begin{lemma}
      Let x,y be objects. If (x,y) is an element of Prod(M,N) then x is an
      element of M and y is an element of N.
    \end{lemma}

    Let f denote a function.

    \begin{definition}
      A subset of M is a set N such that every element of N is an element of M.
    \end{definition}

    \begin{definition}
      Assume M is a subset of Dom(f). f^[M] = {f[x] | x is an element of M}.
    \end{definition}

    Let f is surjective from M onto N stand for Dom(f) = M and f^[M] = N.

    \begin{signature}
      An ordinal is a set.
    \end{signature}

    Let alpha, beta denote ordinals.

    \begin{axiom}
      Every element of alpha is an ordinal.
    \end{axiom}

    \begin{signature}
      A cardinal is an ordinal.
    \end{signature}

    Let A,B,C denote cardinals.

    \begin{signature}
      alpha < beta is an atom.
    \end{signature}

    \begin{axiom}
      If alpha < beta then alpha is an element of beta.
    \end{axiom}

    Let a =< b stand for a = b or a < b.

    \begin{definition}
      Assume M is a subset of A. M is cofinal in A iff for every element x of A
      there exists an element y of M such that x < y.
    \end{definition}

    Let a cofinal subset of A stand for a subset of A that is cofinal in A.

    \begin{signature}
      The cardinality of M is a cardinal.
    \end{Signature}

    Let card(M) stand for the cardinality of M.

    \begin{axiom}[Surj_Exi]
      Assume M has an element. card(M) =< card(N) iff there exists a function f
      such that Dom(f) = N and f^[N] = M.
    \end{axiom}

    \begin{axiom}[Transitivity]
      Let M be an element of A. Assume N is an element of M. N is an element of
      A.
    \end{axiom}

    \begin{axiom}
      card(Prod(M,M)) = card(M).
    \end{axiom}

    \begin{axiom}
      card(A) = A.
    \end{axiom}

    \begin{axiom}
      Let N be a subset of M. card(N) =< card(M).
    \end{axiom}

    \begin{definition}
      A is regular iff card(M) = A for every cofinal subset M of A.
    \end{definition}

    \begin{signature}
      Succ(A) is a cardinal.
    \end{signature}

    \begin{axiom}
      alpha < beta or beta < alpha or beta = alpha.
    \end{axiom}

    \begin{axiom}
      A < Succ(A).
    \end{axiom}

    \begin{axiom}
      card(i) =< A for every element i of Succ(A).
    \end{axiom}

    \begin{axiom}
      For no cardinals A,B we have A < B and B < A.
    \end{axiom}

    \begin{axiom}
      There is no cardinal B such that A < B < Succ(A).
    \end{axiom}

    \begin{definition}
      The empty set is a cardinal E such that E is an element of (every ordinal
      that has an element).
    \end{definition}

    \begin{definition}
      The constant zero on M is a function f such that Dom(f) = M and f[x] is
      the empty set for every element x of M.
    \end{definition}

    Let 0^M stand for the constant zero on M.

    \begin{theorem}
      Succ(A) is regular.
    \end{theorem}
    \begin{proof}
      Proof by contradiction. Assume the contrary. Take a cofinal subset x of
      Succ(A) such that card(x) != Succ(A). Then card(x) =< A. Take a function f
      that is surjective from A onto x (by Surj_Exi). Indeed x has an element
      and card(A) = A.

      Define g[i] =
        Case i has an element -> Choose a function h that is surjective from A
          onto i in h,
        Case i has no element -> 0^A
      for i in Succ(A).

      Define h[(xi,zeta)] = g[f[xi]][zeta] for (xi,zeta) in Prod(A,A).

      Let us show that h is surjective from Prod(A,A) onto Succ(A). Dom(h) =
        Prod(A,A).

        Every element of Succ(A) is an element of h^[Prod(A,A)].
        proof.
          Let n be an element of Succ(A). Take an element xi of A such that
          n < f[xi]. Take an element zeta of A such that g[f[xi]][zeta] = n.
          Then n = h[(xi,zeta)]. Therefore the thesis. Indeed (xi,zeta) is an
          element of Prod(A,A).
        end.

        Every element of h^[Prod(A,A)] is an element of Succ(A).
        proof.
		      Let n be an element of h^[Prod(A,A)]. We can take elements a,b of A
          such that n = h[(a,b)].

          Case f[a] has an element. Obvious (by Transitivity).

          Case f[a] has no element. Obvious (by Transitivity).
        end.
      end.

      Therefore Succ(A) =< A. Contradiction.
    \end{proof}
  \end{forthel}

\end{document}
