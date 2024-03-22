# Little Gauß'es Theorem (Christian Schöner, 2024)
# ================================================

[read natural-numbers.ftl]

Let n denote a natural number.

# S(n) := 1 + 2 + ... + n
Signature. S(n) is a natural number. 

Axiom. S(0) = 0.
Axiom. S(n + 1) = S(n) + (n + 1).

Let 2 stand for 1 + 1.


# S(n) = (n * (n + 1)) / 2
Theorem Little_Gauss. 2 * S(n) = n * (n + 1) for all natural numbers n. 
Proof by induction on n.
  Let n be a natural number.

  Case n = 0. Trivial.

  Case n = m + 1 for some natural number m.
    Consider a natural number m such that n = m + 1.
    Then m -<- n.
    Hence 2 * S(m) = m * (m + 1).
    Thus 2 * S(n) = 2 * S(m + 1) 
       = (2 * S(m)) + (2 * (m + 1))
       = (m * (m + 1)) + (2 * (m + 1))
       = ((m + 1) * m) + ((m + 1) * 2)
       = (m + 1) * (m + 2) 
       = n * (n + 1).
  End.
Qed.
