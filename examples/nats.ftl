# This module implements a simple theory of natural numbers via the Peano Axioms.

[read nbg.ftl]
[synonym number/-s]

Signature. A natural number is a notion.
Signature. Zero is a natural number.

Let n, m, k denote a natural numbers.

Axiom. n is a setobject.

Signature. Succ(n) is a natural number.

Axiom. If n is not equal to m then Succ(n) is not equal to Succ(m).

Axiom. There is no n such that Succ(n) = Zero.

Definition. Nat = { natural number n | n = n }.
Axiom NatSetSized. Nat is a set.
Axiom Ind. Let C be a class. If Zero is in C
  and for all n such that n is in C
  Succ(n) is in C then Nat is a subclass of C.

Signature. n < m is an atom.
Axiom. If n is not equal to Zero then Zero < n.
Axiom. n < m iff Succ(n) < Succ(m).
Axiom. There is no n such that n < Zero.
Axiom. not Zero < Zero.