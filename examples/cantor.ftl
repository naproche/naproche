[synonym subset/-s] [synonym surject/-s]

Let M denote a set.
Let f denote a function.
Let the value of f at x stand for f(x).
Let f is defined on M stand for Dom(f) = M.
Let the domain of f stand for Dom(f).

Axiom. The value of f at any element of the domain of f is a set.

Definition.
  A subset of M is a set N such that every element of N is an element of M.

Definition.
  The powerset of M is the class of subsets of M.

Axiom. The powerset of M is a set.

Definition.
  f surjects onto M iff every element of M 
  is equal to the value of f at some element of the domain of f.

Axiom. Every set is a class.

Proposition.
  No function that is defined on M surjects onto the powerset of M.
Proof by contradiction.
  Assume the contrary.
  Take a function f that is defined on M and surjects onto the powerset of M.
  Define N = { x in M | x is not an element of f(x) }.
  N is a subset of M.
  Take an element y of M such that f(y) is equal to N.
  If y is an element of N then y is not an element of N.
  If y is not an element of N then y is an element of N.
  Contradiction.
Qed.

Theorem. The value of f at any element of the domain of f is a set.
