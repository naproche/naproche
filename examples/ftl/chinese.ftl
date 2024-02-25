# Chinese Remainder Theorem
# =========================

[read ftl/preliminaries.ftl]


Let a, b, c, x, y, z, u, v, w denote elements.

Signature SortsC.
0 is an element.

Signature SortsC.
1 is an element.

Signature SortsU.
-x is an element.

Signature SortsB.
x + y is an element.

Signature SortsB.
x * y is an element.

Let x is nonzero stand for x \neq 0.
Let x - y stand for x + -y.

Axiom AddComm.
x + y = y + x.

Axiom AddAsso.
(x + y) + z = x + (y + z).

Axiom AddBubble.
x + (y + z) = y + (x + z).

Axiom AddZero.
x + 0 = x = 0 + x.

Axiom AddInvr.
x + -x = 0 = -x + x.

Axiom MulComm.
x * y = y * x.

Axiom MulAsso.
(x * y) * z = x * (y * z).

Axiom MulBubble.
x * (y * z) = y * (x * z).

Axiom MulUnit.
x * 1 = x = 1 * x.

Axiom AMDistr1.
x * (y + z) = (x * y) + (x * z).

Axiom AMDistr2.
(y + z) * x = (y * x) + (z * x).

Axiom MulMnOne.
-1 * x = -x = x * -1.

Lemma MulZero.
x * 0 = 0 = 0 * x.
Proof.
  Let us show that x * 0 = 0.
    x * 0
    .= x * (0 + 0) (by AddZero)
    .= (x * 0) + (x * 0) (by AMDistr1).
  End.

  Let us show that 0 * x = 0.
    0 * x
    .= (0 + 0) * x (by AddZero)
    .= (0 * x) + (0 * x) (by AMDistr2).
  End.
Qed.

Axiom Cancel.
x \neq 0 /\ y \neq 0 => x * y \neq 0.

Axiom UnNeZr.
1 \neq 0.


Let X,Y,Z,U,V,W denote sets.

Axiom.
Every element of X is an element.

Definition DefSum.
X +' Y is a set such that for every element z (z \in X +' Y) iff there exist
x \in X and y \in Y such that z = x + y.

Definition DefSInt.
X ** Y is a set such that for every element z (z \in X ** Y) iff z \in X
and z \in Y.

Definition DefIdeal.
An ideal is a set X such that for every x \in X
forall y \in X (x + y) \in X and
forall z (z * x) \in X.

Let I,J denote ideals.

Lemma IdeSum.
I +' J is an ideal.
Proof.
  Let x belong to (I +' J).

  For all y \in (I +' J) (x + y) \in (I +' J).
  Proof.
    Let y \in (I +' J).
    (1) Take k \in I and  l \in J such that x = k + l.
    (2) Take m \in I and  n \in J such that y = m + n.
    k + m belongs to I and l + n belongs to J.
    x + y = (k + m) + (l + n) (by 1, 2, AddComm, AddAsso, AddBubble).
    Therefore the thesis.
  End.

  For every element z (z * x) \in (I +' J).
  Proof.
    Let z be an element.
    (1) Take k \in I and l \in J such that x = k + l.
    z * k belongs to I and z * l belongs to J .
    z * x = (z * k) + (z * l) (by AMDistr1, 1).
    Therefore the thesis.
  End.
Qed.

Lemma IdeInt.
I ** J is an ideal (by DefIdeal).
Proof.
  Let x belong to I ** J.
  forall y \in (I ** J) (x + y) \in (I ** J).
  For every element z (z * x) \in (I** J).
Qed.

Definition DefMod.
x = y (mod I) iff x - y \in I.

Theorem ChineseRemainder.
Suppose that every element belongs to I +' J. Let x, y be elements.
There exists an element w such that w = x (mod I) and w = y (mod J).
Proof.
  Take a \in I and b \in J such that a + b = 1 (by DefSum).
  (1) Take w = (y * a) + (x * b).

  Let us show that w = x (mod I) and w = y (mod J).
    w - x belongs to I.
    Proof.
      w - x = (y * a) + ((x * b) - x).
      x * (b - 1) belongs to I.
      x * (b - 1) = (x * b) - x.
    End.

    w - y belongs to J.
    Proof.
      w - y = (x * b) + ((y * a) - y).
      y * (a - 1) belongs to J.
      y * (a - 1) = (y * a) - y.
    End.
  End.
Qed.


Signature NatSort.
A natural number is an object.

Signature EucSort.
Let x be a nonzero element.
|x| is a natural number.

Axiom Division.
Let x, y be elements and y \neq 0.
There exist elements q,r such that x = (q * y) + r and (r \neq 0 => |r| -<- |y|).


Definition DefDiv.
x divides y iff for some z (x * z = y).

Let x | y stand for x divides y.
Let x is divided by y stand for y | x.

Definition DefDvs.
A divisor of x is an element that divides x.

Definition DefGCD.
A gcd of x and y is a common divisor c of x and y such that any common divisor
of x and y divides c.

Definition DefRel.
x, y are relatively prime iff 1 is a gcd of x and y.

Definition DefPrIdeal.
 <c> is a set such that for every z z is an element of <c> iff there exists an
element x such that z = c * x.

Lemma PrIdeal.
<c> is an ideal.
Proof.
  Let x belong to <c>.
  
  For all y \in <c> x + y \in <c>.
  Proof.
    Let y \in <c>.
    (1) Take an element u such that c * u = x.
    (2) Take an element v such that c * v = y.
    x + y = c * (u + v) (by 1, 2, AMDistr1).
    Therefore the thesis.
  End.
  
  For all z z * x \in <c>.
  Proof.
    Let z be an element.
    (1) Take an element u such that c * u = x.
    z * x .= c * (u * z) (by 1, MulComm, MulAsso, MulBubble).
    Therefore the thesis.
  End.
Qed.

Theorem GCDin.
Let a, b be elements.
Assume that a is nonzero or b is nonzero.
Let c be a gcd of a and b.
Then c belongs to <a> +' <b>.
Proof.
  Take an ideal I equal to <a> +' <b>.
  We have 0,a \in <a> and 0,b \in <b> (by MulZero, MulUnit).
  Hence there exists a nonzero element of <a> +' <b>.
  Indeed a \in <a> +' <b> and b \in <a> +' <b> (by AddZero).

  Take a nonzero u \in I such that for no nonzero v \in I (|v| -<- |u|).
  Proof.
    We can show by induction on |w| that for every nonzero w \in I there exists
    nonzero u \in I such that for no nonzero v \in I (|v| -<- |u|). Obvious.
  Qed.

  u is a common divisor of a and b.
  Proof by contradiction.
    Assume the contrary.

    For some elements x,y  u = (a * x) + (b * y).
    Proof.
      Take k \in <a> and l \in <b> such that u = k + l.
      Take elements x,y such that (k = a * x and l = b * y).
      Hence the thesis.
    End.

    Case u does not divide a.
      Take elements q,r such that a = (q * u) + r
      and (r = 0 \/ |r| -<- |u|) (by Division).
      r is nonzero.
      - (q * u) belongs to I.
      a belongs to I (by AddZero).
      r = - (q * u) + a.
      Hence r belongs to I (by DefIdeal).
    End.

    Case u does not divide b.
      Take elements q,r such that b = (q * u) + r
      and (r = 0 \/ |r| -<- |u|) (by Division).
      r is nonzero.
      - (q * u) belongs to I.
      b belongs to I (by AddZero).
      r = - (q * u) + b.
      Hence r belongs to I (by DefIdeal).
    End.
  End.

  Hence u divides c.
  
  Hence the thesis.
  Proof.
    Take an element z such that c = z * u.
    Then c \in I (by DefIdeal).
  End.
Qed.
