# Natural Number Arithmetic (Christian Schöner & Marcel Schütz, 2024)
# ===================================================================

# Natural Numbers
# ---------------

[synonym number/-s]
Signature. A natural number is an object.

Let n, m, k denote natural numbers.

Signature. 0 is a natural number.
Signature. 1 is a natural number.


# Addition
# --------

Signature. n + m is a natural number.

Axiom. n + 0 = n.
Axiom. n + (m + 1) = (n + m) + 1.


# Multiplication
# --------------

Signature. m * n is a natural number.

Axiom. m * 0 = 0.
Axiom. m * (n + 1) = (m * n) + m.


# Exponentiation
# --------------

Signature. m^n is a natural number.

Axiom. m^0 = 1.
Axiom. m^(n + 1) = (m^n) * m.


# Peano Axioms
# ------------

Axiom. If n + 1 = m + 1 then n = m.
Axiom. n = 0 or n = m + 1 for some natural number m.
Axiom. n + 1 != 0.
Axiom. n -<- n + 1.


# Computation Laws
# ----------------

Lemma associativity_of_addition. n + (m + k) = (n + m) + k for all natural numbers n, m, k.
Proof by induction on k.
  Let n, m, k be natural numbers.

  Case k = 0. Trivial.

  Case k = p + 1 for some natural number p.
    Consider a natural number p such that k = p + 1.
    Then p -<- k.
    Hence n + (m + p) = (n + m) + p.
    Thus
      n + (m + k)
      = n + (m + (p + 1))
      = n + ((m + p) + 1)
      = (n + (m + p)) + 1
      = ((n + m) + p) + 1
      = (n + m) + (p + 1)
      = (n + m) + k.
  End.
Qed.


Lemma commutativity_of_addition. n + m = m + n for all natural numbers m, n.
Proof by induction on n.
  Let us show by induction on n that n + 1 = 1 + n for all natural numbers n.
    Let n be a natural number.

    Case n = 0. Trivial.

    Case n = k + 1 for some natural number k.
      Consider a natural number k such that n = k + 1.
      Then k -<- n.
      Hence k + 1 = 1 + k.
      Thus
        n + 1
        = (k + 1) + 1
        = (1 + k) + 1
        = 1 + (k + 1)
        = 1 + n.
    End.
  End.

  Let m,n be natural numbers.

  Case n = 0. Trivial.

  Case n = k + 1 for some natural number k.
    Consider a natural number k such that n = k + 1.
    Then k -<- n.
    Hence k + m = m + k.
    Thus
      n + m
      = (k + 1) + m
      = k + (1 + m)
      = k + (m + 1)
      = (k + m) + 1
      = (m + k) + 1
      = m + (k + 1)
      = m + n.
  End.
Qed.


Lemma left_distributivity. m * (n + k) = (m * n) + (m * k) for all natural numbers m, n, k.
Proof by induction on k.
  Let m, n, k be natural numbers.

  Case k = 0. Trivial.

  Case k = p + 1 for some natural number p.
    Consider a natural number p such that k = p + 1.
    Then p -<- k.
    Hence m * (n + p) = (m * n) + (m * p).
    Thus
      m * (n + k)
      = m * (n + (p + 1))
      = m * ((n + p) + 1)
      = (m * (n + p)) + m
      = ((m * n) + (m * p)) + m
      = (m * n) + ((m * p) + m)
      = (m * n) + (m * (p + 1))
      = (m * n) + (m * k).
  End.
Qed.


Lemma associativity_of_multiplication. (m * n) * k = m * (n * k) for all natural number m, n, k.
Proof by induction on k.
  Let m, n, k be natural numbers.

  Case k = 0. Trivial.

  Case k = p + 1 for some natural number p.
    Consider a natural number p such that k = p + 1.
    Then p -<- k.
    Hence (m * n) * p = m * (n * p).
    Thus
      m * (n * k)
      = m * (n * (p + 1))
      = m * ((n * p) + (n * 1))
      = m * ((n * p) + n)
      = ((m * n) * p) + (m * n)
      = ((m * n) * p) + ((m * n) * 1)
      = (m * n) * (p + 1)
      = (m * n) * k.
  End.
Qed.


Lemma commutativity_of_multiplication. m * n = n * m for all natural numbers m,n.
Proof by induction on n.
  Let us show by induction on m that  m * 0 = 0 * m for all natural numbers m.
    Let m be a natural number.

    Case m = 0. Trivial.

    Case m = k + 1 for some natural number k.
      Consider a natural number k such that m = k + 1.
      Then k -<- m.
      Hence k * 0 = 0 * k.
      Thus
        0 * m
        = 0 * (k + 1)
        = (0 * k) + (0 * 1)
        = m * 0.
    End.
  End.

  Let us show by induction on m that m * 1 = 1 * m for all natural numbers m.
    Let m be a natural number.

    Case m = 0. Trivial.

    Case m = p + 1 for some natural number p.
      Consider a natural number p such that m = p + 1.
      Then p -<- m.
      Hence p * 1 = 1 * p.
      Thus
        1 * m
        = 1 * (p + 1)
        = (1 * p) + 1
        = (p * 1) + 1
        = p + 1
        = m
        = m * 1.
    End.
  End.

  Let us show by induction on n that (m + 1) * n = (m * n) + (1 * n) for all natural numbers m, n.
    Let m, n be natural numbers.

    Case n = 0. Trivial.

    Case n = k + 1 for some natural number k.
      Consider a natural number k such that n = k + 1.
      Then k -<- n.
      Hence (m + 1) * k = (m * k) + (1 * k).
      Thus
        (m + 1) * n
        = (m + 1) * (k + 1)
        = ((m + 1) * k) + ((m + 1) * 1)
        = ((m * k) + (1 * k)) + (m + 1)
        = (m * k) + ((1 * k) + (m + 1))
        = (m * k) + ((m + 1) + k)
        = (m * k) + (m + n)
        = ((m * k) + m) + (1 * n)
        = (m * n) + (1 * n).
    End.
  End.

  Let m, n be natural numbers.

  Case n = 0. Trivial.

  Case n = k + 1 for some natural number k.
    Consider a natural number k such that n = k + 1.
    Then k -<- n.
    Hence m * k = k * m.
    Thus
      n * m
      = (k + 1) * m
      = (k * m) + (1 * m)
      = (m * k) + (m * 1)
      = m * n.
  End.
Qed.


Corollary right_distributivity. (m + n) * k = (m * k) + (n * k) for all natural numbers m, n, k.


Lemma. (m^n) * (m^k) = m^(n + k) for all natural numbers m, n, k.
Proof by induction on k.
  Let m, n, k be natural numbers.

  Case k = 0. Trivial.

  Case k = p + 1 for some natural number p.
   Consider a natural number p such that k = p + 1.
   Then p -<- k.
   Hence (m^n) * (m^p) = m^(n + p).
   Thus
     (m^n) * (m^k)
     = (m^n) * (m^(p + 1))
     = (m^n) * ((m^p) * m)
     = ((m^n) * (m^p)) * m
     = (m^(n + p)) * m
     = m^((n + p) + 1)
     = m^(n + k).
  End.
Qed.

Lemma. (m^n)^k = m^(n * k) for all natural numbers m, n, k.
Proof by induction on k.
  Let m, n, k be natural numbers.

  Case k = 0. Trivial.

  Case k = p + 1 for some natural number p.
   Consider a natural number p such that k = p + 1.
   Then p -<- k.
   Hence (m^n)^p = m^(n * p).
   Thus
     (m^n)^k
     = (m^n)^(p + 1)
     = ((m^n)^p) * (m^n)
     = (m^(n * p)) * (m^n)
     = m^((n * p) + n)
     = m^(n * (p + 1))
     = m^(n * k).
  End.
Qed.
