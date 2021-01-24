\documentclass{document}

\usepackage[utf8]{inputenc}
\usepackage[english]{babel}
\usepackage{forthel}

\title{No prime is a square number}
\author{}
\date{}

\begin{document}
  \pagenumbering{gobble}

  \maketitle

  \begin{forthel}
    [synonym number/-s]
    [synonym devide/-s]

    \begin{signature}
      A rational number is a notion.
    \end{signature}

    Let $s,r,q$ stand for rational numbers.

    \begin{signature}
      $r * q$ is a rational number.
    \end{signature}

    \begin{axiom}
      $r * q = q * r$.
    \end{axiom}

    \begin{axiom}
      $r * (q * s) = (r * q) * s$.
    \end{axiom}

    \begin{axiom}
      $q * s = q * r => s = r$.
    \end{axiom}

    \begin{signature}
      A natural number is a rational number.
    \end{signature}

    Let $n,m,k$ denote natural numbers.

    \begin{axiom}
      $n * m$ is a natural number.
    \end{axiom}

    \begin{definition}
      $n | q$ iff there exists $k$ such that $k * n = q$.
    \end{definition}

    Let $n$ divides $m$ stand for $n | m$. Let a divisor of $m$ stand for a natural number that divides $m$.

    \begin{definition}
      $n$ and $m$ are coprime iff $n$ and $m$ have no common divisor.
    \end{definition}

    \begin{signature}
      A prime number is a natural number.
    \end{signature}

    Let $p$ denote a prime number.

    \begin{axiom}
      $p | n * m => p | n \/ p | m$.
    \end{axiom}

    \begin{axiom}
      There exist coprime $m,n$ such that $m * q = n$.
    \end{axiom}

    Let $q^{2}$ stand for $q * q$.


    \begin{proposition}
      $q^{2} = p$ for no rational number $q$.
    \end{proposition}
    \begin{proof}
      Proof by contradiction. Assume the contrary. Take a rational number $q$ such that $p = q^{2}$. Take coprime $m,n$ such that $m * q = n$. Then $p * m^{2} = n^{2}$. Therefore $p$ divides $n$. Take a natural number $k$ such that $n = k * p$. Then $p * m^{2} = p * (k * n)$. Therefore $m * m$ is equal to $p * k^{2}$. Hence $p$ divides $m$. Contradiction.
    \end{proof}
  \end{forthel}

\end{document}
