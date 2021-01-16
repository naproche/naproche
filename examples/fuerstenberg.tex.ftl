\documentclass{document}

\usepackage[utf8]{inputenc}
\usepackage[english]{babel}
\usepackage{forthel}

\title{Fürstenberg's proof of the infinitude of primes}
\author{}
\date{}

\begin{document}
  \pagenumbering{gobble}

  \maketitle

  \section{Integers}

  \begin{forthel}
    [unfoldlow on]
    [synonym integer/-s]

    \begin{signature}[Integers]
      An integer is a notion.
    \end{signature}

    Let a,b,c,d,i,j,k,l,m,n stand for integers.

    \begin{signature}[IntZero]
      0 is an integer.
    \end{signature}

    \begin{signature}[IntOne]
      1 is an integer.
    \end{signature}

    \begin{signature}[IntNeg]
      -a is an integer.
    \end{signature}

    \begin{signature}[IntPlus]
      a + b is an integer.
    \end{signature}

    \begin{signature}[IntMult]
      a * b is an integer.
    \end{signature}

    Let a - b stand for a + (-b).

    \begin{axiom}[AddAsso]
      a + (b + c) = (a + b) + c.
    \end{axiom}

    \begin{axiom}[AddComm]
      a + b = b + a.
    \end{axiom}

    \begin{axiom}[AddZero]
      a + 0 = a = 0 + a.
    \end{axiom}

    \begin{axiom}[AddNeg]
      a - a = 0 = -a + a.
    \end{axiom}

    \begin{axiom}[MulAsso]
      a * (b * c) = (a * b) * c.
    \end{axiom}

    \begin{axiom}[MulComm]
      a * b = b * a.
    \end{axiom}

    \begin{axiom}[MulOne]
      a * 1 = a = 1 * a.
    \end{axiom}

    \begin{axiom}[Distrib]
      a * (b + c) = (a*b) + (a*c) and
      (a + b) * c = (a*c) + (b*c).
    \end{axiom}

    \begin{lemma}[MulZero]
      a * 0 = 0 = 0 * a.
    \end{lemma}

    \begin{lemma}[MulMinOne]
      -1 * a = -a = a * -1.
    \end{lemma}
    \begin{proof}
      (-1 * a) + a = 0.
    \end{proof}

    \begin{axiom}[ZeroDiv]
      a != 0 /\ b != 0 => a * b != 0.
    \end{axiom}

    \begin{lemma}
      --a is an integer.
    \end{lemma}

    Let a is nonzero stand for a != 0.
    Let p,q stand for nonzero integers.

    [synonym divisor/-s] [synonym divide/-s]

    \begin{definition}[Divisor]
      A divisor of b is a nonzero integer a such that for some n (a * n = b).
    \end{definition}

    Let a divides b stand for a is a divisor of b.
    Let a | b stand for a is a divisor of b.

    \begin{definition}[EquMod]
      a = b (mod q) iff q | a-b.
    \end{definition}

    \begin{lemma}[EquModRef]
      a = a (mod q).
    \end{lemma}

    \begin{lemma}[EquModSym]
      a = b (mod q) => b = a (mod q).
    \end{lemma}
    \begin{proof}
      Assume that a = b (mod q).

      (1) Take n such that q * n = a - b.

      q * -n .= (-1) * (q * n) (by MulMinOne, MulAsso,MulComm,MulBubble)
             .= (-1) * (a - b) (by 1).
    \end{proof}

    \begin{lemma}[EquModTrn]
      a = b (mod q) /\ b = c (mod q) => a = c (mod q).
    \end{lemma}
    \begin{proof}
      Assume that a = b (mod q) /\ b = c (mod q).
      Take n such that q * n = a - b.
      Take m such that q * m = b - c.
      We have q * (n + m) = a - c.
    \end{proof}

    \begin{lemma}[EquModMul]
      a = b (mod p * q) => a = b (mod p) /\ a = b (mod q).
    \end{lemma}
    \begin{proof}
      Assume that a = b (mod p * q).
      Take m such that (p * q) * m = a - b.
      We have p * (q * m) = a - b = q * (p * m).
    \end{proof}

    \begin{signature}[Prime]
      a is prime is an atom.
    \end{signature}

    Let a prime stand for a prime nonzero integer.

    \begin{axiom}[PrimeDivisor]
      n has a prime divisor iff n != 1 /\ n != -1.
    \end{axiom}
  \end{forthel}


  \section{Generic sets}

  \begin{forthel}
    [synonym belong/-s] [synonym subset/-s]

    Let S,T stand for sets.

    Let x belongs to S stand for x is an element of S.
    Let x << S stand for x is an element of S.

    \begin{definition}[Subset]
      A subset of S is a set T such that every element of T belongs to S.
    \end{definition}

    Let S [= T stand for S is a subset of T.

    \begin{signature}[FinSet]
      S is finite is an atom.
    \end{signature}

    Let x is infinite stand for x is not finite.
  \end{forthel}


  \section{Sets of integers}

  \begin{forthel}
    \begin{definition}
      INT is the set of integers.
    \end{definition}

    Let A,B,C,D stand for subsets of INT.

    \begin{definition}[Union]
      A \-/ B = { integer x | x << A \/ x << B }.
    \end{definition}

    \begin{definition}[Intersection]
      A /-\ B = { integer x | x << A /\ x << B }.
    \end{definition}

    \begin{definition}[IntegerSets]
      A family of integer sets is a set S such that every element of S is a
      subset of INT.
    \end{definition}

    \begin{definition}[UnionSet]
      Let S be a family of integer sets.
      \-/ S = { integer x | x belongs to some element of S }.
    \end{definition}

    \begin{lemma}
      Let S be a family of integer sets. \-/S is a subset of INT.
    \end{lemma}

    \begin{definition}[Complement]
      ~ A = { integer x | x does not belong to A }.
    \end{definition}

    \begin{lemma}
      ~ A is a subset of INT.
    \end{lemma}
   \end{forthel}


  \section{Introducing topology}

  \begin{forthel}

    \begin{definition}[ArSeq]
      ArSeq(a,q) = { integer b | b = a (mod q) }.
    \end{definition}

    \begin{definition}[Open]
      A is open iff for any a << A there exists q such that ArSeq(a,q) [= A.
    \end{definition}

    \begin{definition}[Closed]
      A is closed iff ~A is open.
    \end{definition}

    \begin{definition}[OpenIntegerSets]
      An open family is a family of integer sets S such that every element of S
      is open.
    \end{definition}

    \begin{lemma}[UnionOpen]
      Let S be an open family. \-/ S is open.
    \end{lemma}
    \begin{proof}
      Let x << \-/ S. Take a set M such that( M is an element of S and x << M).
      Take q such that ArSeq(x,q) [= M. Then ArSeq(x,q) [= \-/ S.
    \end{proof}

    \begin{lemma}[InterOpen]
      Let A,B be open subsets of INT. Then A /-\ B is a subset of INT and
      A /-\ B is open.
    \end{lemma}
    \begin{proof}
      A /-\ B is a subset of INT. Let x << A /-\ B. Then x is an integer. Take q
      such that ArSeq(x,q) [= A. Take p such that ArSeq(x,p) [= B.

      Let us show that p*q is a nonzero integer and ArSeq(x, p * q) [= A /-\ B.
        p*q is a nonzero integer. Let a << ArSeq(x, p * q).

        a << ArSeq (x, p) and a << ArSeq (x, q).
        proof.
          x is an integer and a = x (mod p * q). a = x (mod p) and a = x (mod q)
          (by EquModMul).
        end.

        Therefore a << A and a << B. Hence a << A /-\ B.
      end.
    \end{proof}

    \begin{lemma}[UnionClosed]
      Let A,B be closed subsets of INT. A \-/ B is closed.
    \end{lemma}
    \begin{proof}
      We have ~A,~B [= INT. ~(A \-/ B) = ~A /-\ ~B.
    \end{proof}

    \begin{axiom}[UnionSClosed]
      Let S be a finite family of integer sets such that all elements of S are
      closed subsets of INT. \-/ S is closed.
    \end{axiom}

    \begin{lemma}[ArSeqClosed]
      ArSeq(a,q) is a closed subset of INT.
    \end{lemma}
    \begin{proof}
      Proof by contradiction. ArSeq (a,q) is a subset of INT. Let
      b << ~ArSeq (a,q).

      Let us show that ArSeq(b,q) [= ~ArSeq(a,q). Let c << ArSeq(b,q). Assume
        not c << ~ArSeq(a,q). Then c = b (mod q) and a = c (mod q). Hence
        b = a (mod q). Therefore b << ArSeq(a,q). Contradiction.
      end.
    \end{proof}

    \begin{theorem}[Fuerstenberg]
      Let S = {ArSeq(0,r) | r is a prime}. S is infinite.
    \end{theorem}
    \begin{proof}
      Proof by contradiction. S is a family of integer sets.

      We have ~ \-/ S = {1, -1}.
      proof.
        Let us show that for any integer n n belongs to \-/ S iff n has a prime
          divisor. Let n be an integer.

          If n has a prime divisor then n belongs to \-/ S.
          proof.
            Assume n has a prime divisor. Take a prime divisor p of n.
            ArSeq(0,p) << S. n << ArSeq(0,p).
          end.

          If n belongs to \-/ S then n has a prime divisor.
          proof.
            Assume n belongs to \-/S. Take a prime r such that n << ArSeq(0,r).
            Then r is a prime divisor of n.
          end.
        end.
      end.

      Assume that S is finite. Then \-/ S is closed and ~ \-/ S is open.

      Take p such that ArSeq(1,p) [= ~ \-/ S.

      ArSeq(1,p) has an element x such that neither x = 1 nor x = -1.
      proof.
        1 + p and 1 - p belong to ArSeq(1,p).
        1 + p !=  1 /\ 1 - p !=  1.
        1 + p != -1 \/ 1 - p != -1.
      end.

      We have a contradiction.
    \end{proof}
  \end{forthel}

\end{document}
