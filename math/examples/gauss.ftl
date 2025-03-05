[read examples/preliminaries.ftl]


# Natural Numbers

Signature. A natural number is an object.
Let n, m, k denote natural numbers.

Definition. \Nat is the class of all natural numbers.

Axiom Infinity_Axiom. \Nat is a set.

Signature. 0 is a natural number.
Let n is nonzero stand for n \neq 0.

Signature. 1 is a natural number.


## Addition

Signature. n + m is a natural number.

Axiom. n + 0 = n.

Axiom. n + (m + 1) = (n + m) + 1.


Axiom Commutativity_of_Addition. n + m = m + n.

Axiom Associativity_of_Addition. n + (m + k) = (n + m) + k.


## Multiplication

Signature. n * m is a natural number.

Axiom. n * 0 = 0.

Axiom. n * (m + 1) = (n * m) + n.


Axiom Commutativity of Multiplication. n * m = m * n.

Axiom Associativity of Multiplication. n * (m * k) = (n * m) * k.

Axiom Left Distributivity. n * (m + k) = (n * m) + (n * k).

Axiom Right Distributivity. (n + m) * k = (n * k) + (m * k).


## The Peano Axioms

Axiom Peano_Axiom_I. If n + 1 =  m + 1 then n = m.

Axiom Peano_Axiom_II. There exists no natural number n such that n + 1 = 0.

Axiom Peano_Axiom_III. n = 0 or n = m + 1 for some natural number m.

Axiom Induction_Axiom. n -<- n + 1.


## Additional Numbers

Definition. 2 = 1 + 1.


# Little Gauß' Theorem

Signature. \gauss(n) is a natural number.

Axiom. \gauss(0) = 0.

Axiom. \gauss(n + 1) = \gauss(n) + (n + 1).


Theorem Little_Gauß.
For all natural numbers n we have 2 * \gauss(n) = n * (n + 1).

Proof by induction on n.
  Let n be a natural number.

  Case n = 0. Trivial.

  Case n \neq 0.
    Take an element m of \Nat such that n = m + 1.
    Then 2 * \gauss(m) = m * n.
    Hence
        2 * \gauss(n)
      = 2 * (\gauss(m) + n)
      = (2 * \gauss(m)) + (2 * n)
      = (m * n) + (2 * n)
      = (m + 2) * n
      = n * (n + 1).
  End.
Qed.
