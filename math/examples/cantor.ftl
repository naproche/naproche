# Cantor's Theorem

[read examples/preliminaries.ftl]

Definition. Let X be a set.
A function of X is a function f such that Dom(f) = X.

Definition. Let f be a function and Y be a set.
f surjects onto Y iff Y = {f(x) | x \in Dom(f)}.

Definition. Let X,Y be sets.
A function from X onto Y is a function of X that surjects onto Y.

Definition. Let X be a set.
The powerset of X is the collection of subsets of X.

Axiom. The powerset of any set is a set.


Theorem Cantor. Let M be a set.
No function of M surjects onto the powerset of M.

Proof by contradiction.
  Assume the contrary.
  Take a function f from M onto the powerset of M.
  The value of f at any element of M is a set.
  Define N = {x in M | x is not an element of f(x)}.
  N is a subset of M.
  Consider an element z of M such that f(z) = N.
  Then z \in N iff z \notin f(z) = N.
  Contradiction.
Qed.
