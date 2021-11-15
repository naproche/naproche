[synonym subset/-s] [synonym surject/-s]
[prover vampire][printfulltask on][printprover on][printcheck on][dump on]

##########################################
Lemma. Every set is a class.

Let M denote a class.

Definition.
A subset of M is a set N such that every element of N is an element of M.

Let the value of f at x stand for f(x).
Let the domain of f stand for Dom(f).
Let f is defined on M stand for the domain of f is equal to M.
##########################################

Let M denote a set.
Let f denote a function.

Definition.
The powerset of M is the collection of subsets of M.

Axiom. The powerset of M is a set.

Definition.
f surjects onto M iff every element of M 
is equal to the value of f at some element of the domain of f.

Proposition.
  No function that is defined on M surjects onto the powerset of M.
Proof by contradiction.
  Assume the contrary.
  Take a function f that is defined on M and surjects onto the powerset of M.
  Define N = { x in M | f(x) is a set and x is not an element of f(x) }.
  N is a subset of M.
  Take an element y of M such that f(y) is equal to N.
  Then y is an element of N  iff y is not an element of N. 
  Contradiction.
Qed.