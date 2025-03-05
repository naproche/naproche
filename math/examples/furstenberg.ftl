#
# Integers
#

[read examples/preliminaries.ftl]

Signature Integers. An integer is an object.

Let a,b,c,d,i,j,k,l,m,n stand for integers.

Signature IntZero. 0 is an integer.
Signature IntOne. 1 is an integer.
Signature IntNeg. -a is an integer.
Signature IntPlus. a + b is an integer.
Signature IntMult. a * b is an integer.

Let a - b stand for a + (-b).

Axiom AddAsso. a + (b + c) = (a + b) + c.
Axiom AddComm. a + b = b + a.
Axiom AddZero. a + 0 = a = 0 + a.
Axiom AddNeg. a - a = 0 = -a + a.

Axiom MulAsso. a * (b * c) = (a * b) * c.
Axiom MulComm. a * b = b * a.
Axiom MulOne. a * 1 = a = 1 * a.


Axiom Distrib. a * (b + c) = (a*b) + (a*c) and (a + b) * c = (a*c) + (b*c).

Lemma MulZero. a * 0 = 0 = 0 * a. Indeed a * 0 = a * (1 - 1) = a - a = 0.
Lemma MulMinOne. -1 * a = -a = a * -1. Indeed (-1 * a) + a = 0.

Axiom NonTriv. 0 != 1.
Axiom ZeroDiv. a != 0 /\ b != 0 => a * b != 0.

Lemma. --a is an integer.

Let a is nonzero stand for a != 0.
Let p,q stand for nonzero integers.

Definition Divisor. A divisor of b is a nonzero integer a
such that for some n (a * n = b).

Let a divides b stand for a is a divisor of b.
Let a | b stand for a is a divisor of b.

Definition EquMod. a = b (mod q) iff q | a-b.

Lemma EquModRef. a = a (mod q).

Lemma EquModSym. a = b (mod q) => b = a (mod q).
Proof.
  Assume that a = b (mod q).
  (1) Take n such that q * n = a - b.
  q * -n .= (-1) * (q * n) (by MulMinOne, MulAsso,MulComm)
         .= (-1) * (a - b) (by 1).
Qed.

Lemma EquModTrn. a = b (mod q) /\ b = c (mod q) => a = c (mod q).
Proof.
  Assume that a = b (mod q) /\ b = c (mod q).
  Take n such that q * n = a - b.
  Take m such that q * m = b - c.
  We have q * (n + m) = a - c.
Qed.

Lemma EquModMul. a = b (mod p * q) => a = b (mod p) /\ a = b (mod q).
Proof.
  Assume that a = b (mod p * q).
  Take m such that (p * q) * m = a - b.
  We have p * (q * m) = a - b = q * (p * m).
Qed.

Signature Prime. a is prime is an atom.

Let a prime stand for a prime nonzero integer.

Axiom PrimeDivisor. n has a prime divisor iff n != 1 /\ n != -1.


#
# Finite classes
#

Let S,T stand for classes.

Signature FinSet. S is finite is an atom.

Let S is infinite stand for S is not finite.


#
# Sets of integers
#

Definition. INT is the class of integers.

Axiom. INT is a set.

Let A,B,C,D stand for subclasses of INT.

Definition IntegerSets. A family of integer sets is a class S such that every element of S is a subset of INT.

Definition UnionSet. Let S be a family of integer sets.
\bigcup S = { x in INT | x belongs to some element of S }.

Lemma. Let S be a family of integer sets.
\bigcup S is a subset of INT.

Definition Complement. ~ A = { x in INT | x does not belong to A }.

Lemma. ~ A is a subset of INT.


#
# Introducing topology
#

Definition ArSeq. ArSeq(a,q) = { b in INT | b = a (mod q) }.

Lemma. ArSeq(a, q) is a set.

Definition Open. A is open iff A = INT or for any element a of A there exists q such that ArSeq(a,q) \subseteq A.

Definition Closed. A is closed iff ~A is open.

Definition OpenIntegerSets.
An family of open sets is a family of integer sets S such that every element of S is open.

Lemma UnionOpen. Let S be an family of open sets.
\bigcup S is open.
Proof.
  Let x \in \bigcup S.
  Take a set M such that( M is an element of S and x \in M).
  Take q such that ArSeq(x,q) \subseteq M.
  Then ArSeq(x,q) \subseteq \bigcup S.
Qed.

Lemma InterOpen. Let A,B be open subsets of INT.
Then A \cap B is a subset of INT and A \cap B is open.
Proof.
  A \cap B is a subset of INT.
  Let x \in A \cap B.
  Then x is an integer.
  Take q such that ArSeq(x,q) \subseteq A.
  Take p such that ArSeq(x,p) \subseteq B.

  Let us show that p*q is a nonzero integer and ArSeq(x, p * q) \subseteq A \cap B.
    p*q is a nonzero integer.
    Let a \in ArSeq(x, p * q).

    a \in ArSeq (x, p) and a \in ArSeq (x, q).
    Proof.
      x is an integer and a = x (mod p * q).
      a = x (mod p) and a = x (mod q) (by EquModMul).
    End.

    Therefore a \in A and a \in B.
    Hence a \in A \cap B.
  End.
Qed.

Lemma UnionClosed. Let A,B be closed subsets of INT.
A \cup B is closed.
Proof.
  We have ~A,~B \subseteq INT.
  ~(A \cup B) = ~A \cap ~B.
qed.

Axiom UnionSClosed. Let S be a finite family of integer sets such that all elements of S are closed subsets of INT.
\bigcup S is closed.

Lemma ArSeqClosed.  ArSeq(a,q) is a closed subset of INT.
Proof by contradiction.
  ArSeq (a,q) is a subset of INT.
  Let b \in ~ArSeq (a,q).

  Let us show that ArSeq(b,q) \subseteq ~ArSeq(a,q).
    Let c \in ArSeq(b,q).
    Assume not c \in ~ArSeq(a,q).
    Then c = b (mod q) and a = c (mod q).
    Hence b = a (mod q).
    Therefore b \in ArSeq(a,q).
    Contradiction.
  End.
Qed.

Theorem Fuerstenberg. Let S = { ArSeq(0,r) | r is a prime }.
S is infinite.
Proof by contradiction.
  S is a family of integer sets.
  We have ~ \bigcup S = {1, -1}.
  Proof.
    Let us show that for any integer n n belongs to \bigcup S iff n has a prime divisor.
      Let n be an integer.
      
      If n has a prime divisor then n belongs to \bigcup S.
      Proof.
        Assume n has a prime divisor.
        Take a prime divisor p of n.
        ArSeq(0,p) is a set.
        ArSeq(0,p) \in S.
        n \in ArSeq(0,p).
      End.
      
      If n belongs to \bigcup S then n has a prime divisor.
      Proof.
        Assume n belongs to \bigcup S.
        Take a prime r such that n \in ArSeq(0,r).
        Then r is a prime divisor of n.
      End.
    End.
  End.

  Assume that S is finite.
  Then \bigcup S is closed and ~ \bigcup S is open.
  Take p such that ArSeq(1,p) \subseteq ~ \bigcup S.

  ArSeq(1,p) has an element x such that neither x = 1 nor x = -1.
  Proof.
    1 + p and 1 - p are integers.
    1 + p and 1 - p belong to ArSeq(1,p).
    Indeed 1 + p = 1 (mod p) and 1 - p = 1 (mod p).
    1 + p !=  1 /\ 1 - p !=  1.
    1 + p != -1 \/ 1 - p != -1.
  End.
  
  We have a contradiction.
Qed.
