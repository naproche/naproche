# Cantor's Theorem

[readtex basic-notions/sets-and-functions/sections/01_sets/02_powerset.ftl.tex]
[readtex basic-notions/sets-and-functions/sections/02_functions/01_functions.ftl.tex]

Let x \in y stand for x is an element of y.
Let x \notin y stand for x is not an element of y.

Theorem Cantor.
  Let M be a set.
  No function of M surjects onto the powerset of M.

Proof by contradiction.
  Assume the contrary.
  Take a function f from M onto the powerset of M.
  The value of f at any element of M is a set.
  Define N = {x in M | x is not an element of f(x)}.
  N is a subset of M.
  Take an element z of M such that f(z) = N.
  Then z \in N iff z \notin f(z) = N.
  Contradiction.
Qed.
