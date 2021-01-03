#
# Integers
#
[unfoldlow on]
[synonym integer/-s]

Signature Integers. An integer is a notion.

Let a,b,c,d,i,j,k,l,m,n stand for integers.

Signature IntZero.  0 is an integer.
Signature IntOne.   1 is an integer.
Signature IntNeg.   -a is an integer.
Signature IntPlus.  a + b is an integer.
Signature IntMult.  a * b is an integer.

Let a - b stand for a + (-b).

Axiom AddAsso.      a + (b + c) = (a + b) + c.
Axiom AddComm.      a + b = b + a.
Axiom AddZero.      a + 0 = a = 0 + a.
Axiom AddNeg.       a - a = 0 = -a + a.

Axiom MulAsso.      a * (b * c) = (a * b) * c.
Axiom MulComm.      a * b = b * a.
Axiom MulOne.       a * 1 = a = 1 * a.


Axiom Distrib.      a * (b + c) = (a*b) + (a*c) and
                    (a + b) * c = (a*c) + (b*c).

Lemma MulZero.      a * 0 = 0 = 0 * a.
Lemma MulMinOne.    -1 * a = -a = a * -1.

Axiom ZeroDiv.      a != 0 /\ b != 0 => a * b != 0.

Lemma. --a is an integer.

Let a is nonzero stand for a != 0.
Let p,q stand for nonzero integers.

[synonym divisor/-s] [synonym divide/-s]

Definition Divisor. A divisor of b is a nonzero integer a
                    such that for some n (a * n = b).

Let a divides b stand for a is a divisor of b.
Let a | b stand for a is a divisor of b.

Definition EquMod.  a = b (mod q) iff q | a-b.

Lemma EquModRef.    a = a (mod q).

Lemma EquModSym.    a = b (mod q) => b = a (mod q).
Proof.
    Assume that a = b (mod q).
    (1) Take n such that q * n = a - b.
    q * -n .= (-1) * (q * n) (by MulMinOne, MulAsso,MulComm,MulBubble)
                   .= (-1) * (a - b) (by 1).
qed.

Lemma EquModTrn.    a = b (mod q) /\ b = c (mod q) => a = c (mod q).
Proof.
    Assume that a = b (mod q) /\ b = c (mod q).
    Take n such that q * n = a - b.
    Take m such that q * m = b - c.
    We have q * (n + m) = a - c.
qed.

Lemma EquModMul. a = b (mod p * q) => a = b (mod p) /\ a = b (mod q).
Proof.
    Assume that a = b (mod p * q).
    Take m such that (p * q) * m = a - b.
    We have p * (q * m) = a - b = q * (p * m).
qed.

Signature Prime.    a is prime is an atom.

Let a prime stand for a prime nonzero integer.

Axiom PrimeDivisor. n has a prime divisor iff n != 1 /\ n != -1.


#
# Generic sets
#
[synonym belong/-s] [synonym subset/-s]


Let S,T stand for sets.

Let x belongs to S stand for x is an element of S.
Let x << S stand for x is an element of S.

Definition Subset.  A subset of S is a set T such that
                        every element of T belongs to S.

Let S [= T stand for S is a subset of T.

Signature FinSet.   S is finite is an atom.

Let x is infinite stand for x is not finite.


#
# Sets of integers
#
Definition.
INT is the set of integers.

Let A,B,C,D stand for subsets of INT.

Definition Union.
    A \-/ B = { integer x | x << A \/ x << B }.

Definition Intersection.
    A /-\ B = { integer x | x << A /\ x << B }.

Definition IntegerSets.
A family of integer sets is a set S such that every element of S is a subset of INT.

Definition UnionSet.
    Let S be a family of integer sets.
    \-/ S = { integer x | x belongs to some element of S }.
Lemma.
    Let S be a family of integer sets. \-/S is a subset of INT.

Definition Complement.
    ~ A = { integer x | x does not belong to A }.

Lemma.
 ~ A is a subset of INT.


#
# Introducing topology
#

Definition ArSeq.   ArSeq(a,q) = { integer b | b = a (mod q) }.

Definition Open.    A is open iff for any a << A
                        there exists q such that ArSeq(a,q) [= A.

Definition Closed.  A is closed iff ~A is open.

Definition OpenIntegerSets.
An open family is a family of integer sets S such that every element of S is open.

Lemma UnionOpen.   Let S be an open family.
                    \-/ S is open.
Proof.
 Let x << \-/ S. Take a set M such that( M is an element of S and x << M). Take q such that ArSeq(x,q) [= M.
 Then ArSeq(x,q) [= \-/ S.
 qed.

Lemma InterOpen.    Let A,B be open subsets of INT. Then A /-\ B is a subset of INT and
                    A /-\ B is open.
Proof.
A /-\ B is a subset of INT. Let x << A /-\ B. Then x is an integer. Take q such that ArSeq(x,q) [= A. Take p such that ArSeq(x,p) [= B.
Let us show that p*q is a nonzero integer and ArSeq(x, p * q) [= A /-\ B. p*q is a nonzero integer.
  Let a << ArSeq(x, p * q). a << ArSeq (x, p) and a << ArSeq (x, q). proof. x is an integer and a = x (mod p * q). a = x (mod p) and a = x (mod q) (by EquModMul).end.
  Therefore a << A and a << B. Hence a << A /-\ B. end.
qed.

Lemma UnionClosed.  Let A,B be closed subsets of INT.
                    A \-/ B is closed.
Proof.
    We have ~A,~B [= INT. ~(A \-/ B) = ~A /-\ ~B.
qed.

Axiom UnionSClosed. Let S be a finite family of integer sets such that
                        all elements of S are closed subsets of INT.
                    \-/ S is closed.

Lemma ArSeqClosed.  ArSeq(a,q) is a closed subset of INT.
Proof by contradiction.
ArSeq (a,q) is a subset of INT.
Let b << ~ArSeq (a,q). Let us show that ArSeq(b,q) [= ~ArSeq(a,q).
  Let c << ArSeq(b,q). Assume not c << ~ArSeq(a,q). Then c = b (mod q) and a = c (mod q).
  Hence b = a (mod q). Therefore b << ArSeq(a,q). Contradiction. end.
qed.

Theorem Fuerstenberg.   Let S = { ArSeq(0,r) | r is a prime }.
                        S is infinite.
Proof by contradiction.
    S is a family of integer sets.
    We have ~ \-/ S = {1, -1}.
    proof.
        Let us show that for any integer n n belongs to \-/ S iff n has a prime divisor. Let n be an integer.
        If n has a prime divisor then n belongs to \-/ S.
        proof.
        Assume n has a prime divisor. Take a prime divisor p of n.
        ArSeq(0,p) << S. n << ArSeq(0,p). end.
        If n belongs to \-/ S then n has a prime divisor.
        proof.
        Assume n belongs to \-/S. Take a prime r such that n << ArSeq(0,r).
        Then r is a prime divisor of n. end.
        end.
    end.

    Assume that S is finite.
    Then \-/ S is closed and ~ \-/ S is open.

    Take p such that ArSeq(1,p) [= ~ \-/ S.
    ArSeq(1,p) has an element x such that neither x = 1 nor x = -1.
    proof.
        1 + p and 1 - p belong to ArSeq(1,p).
        1 + p !=  1 /\ 1 - p !=  1.
        1 + p != -1 \/ 1 - p != -1.
    end.
    We have a contradiction.
qed.
