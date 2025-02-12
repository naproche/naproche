[read libraries/meta-inf/source/vocabulary.ftl]

Signature. A positive rational number is an object.

Let q, s, r stand for positive rational numbers.

Signature. r * q is a positive rational number.
Axiom. r * q = q * r.
Axiom. r * (q * s) = (r * q) * s.

Definition. q is left cancellative iff
    for all r, s we have q * s = q * r => s = r.

Axiom. Every positive rational number is left cancellative.


Signature. A natural number is a positive rational number.

Let m, n, k denote natural numbers.

Signature. 1 is a natural number.
Axiom. n * m is a natural number.

Definition. n | m iff there exists k such that k * n = m.

Let n divides m stand for n | m.
Let a divisor of m stand for a natural number that divides m.

Definition.
    Let p be a natural number.
    p is prime iff p != 1 and for all m, n we have p | n * m => (p | n \/ p | m).

Let a prime number stand for a prime natural number.

Let p denote a prime number.

Definition. n and m are coprime iff n and m have no common prime divisor.


Axiom. There exist coprime m, n such that m * q = n.

Let q^2 stand for q * q.


Proposition. q^2 = p for no positive rational number q.
Proof by contradiction.
Assume the contrary. 
Take a positive rational number q such that p = q^2.
Take coprime m,n such that m * q = n. Then p * m^2 = n^2.
Therefore p divides n. Take a natural number k such that n = k * p.
Then p * m^2 = p * (k * n).
Therefore m * m is equal to p * k^2.
Hence p divides m. Contradiction.
QED.
