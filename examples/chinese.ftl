[synonym element/-s]

Signature ElmSort. An element is a notion.

Let a,b,c,x,y,z,u,v,w denote elements.

Signature SortsC.  0 is an element.
Signature SortsC.  1 is an element.
Signature SortsU.  -x is an element.
Signature SortsB.  x + y is an element.
Signature SortsB.  x * y is an element.

Let x is nonzero stand for x != 0.
Let x - y stand for x + -y.

Axiom AddComm.  x + y = y + x.
Axiom AddAsso.  (x + y) + z = x + (y + z).
Axiom AddBubble. x + (y + z) = y + (x + z).
Axiom AddZero.  x + 0 = x = 0 + x.
Axiom AddInvr.  x + -x = 0 = -x + x.

Axiom MulComm.  x * y = y * x.
Axiom MulAsso.  (x * y) * z = x * (y * z).
Axiom MulBubble. x * (y * z) = y * (x * z).
Axiom MulUnit.  x * 1 = x = 1 * x.

Axiom AMDistr1.  x * (y + z) = (x * y) + (x * z).
Axiom AMDistr2.  (y + z) * x = (y * x) + (z * x).

Axiom MulMnOne. -1 * x = -x = x * -1.

Lemma MulZero.  x * 0 = 0 = 0 * x.
Proof.
  Let us show that x * 0 = 0.
  x * 0 .= x * (0 + 0) (by AddZero) .= (x * 0) + (x * 0) (by AMDistr1).
  end.
  Let us show that 0 * x = 0.
  0 * x .= (0 + 0) * x (by AddZero) .= (0 * x) + (0 * x) (by AMDistr2).
  end.
qed.

Axiom Cancel.  x != 0 /\ y != 0 => x * y != 0.

Axiom UnNeZr.  1 != 0.

[synonym set/-s] [synonym belong/-s]

Let X,Y,Z,U,V,W denote sets.

Axiom. Every element of X is an element.

Let x << W denote x is an element of W.
Let x belongs to W denote x is an element of W.

Axiom SetEq.
If every element of X belongs to Y and every element of Y belongs to X
then X = Y.

Definition DefSSum.
X +' Y is a set such that for every element z (z << X +' Y) iff there exist
x << X, y << Y such that z = x + y.

Definition DefSInt.
X ** Y is a set such that for every element z (z << X +' Y) iff z << X
and z << Y.

[synonym ideal/-s]

Definition DefIdeal.
An ideal is a set X such that for every x << X
        forall y << X (x + y) << X and
        forall z (z * x) << X.

Let I,J denote ideals.

Lemma IdeSum.   I +' J is an ideal.
Proof.
Let x belong to (I +' J).
forall y << (I +' J) (x + y) << (I +' J).
proof.
    Let y << (I +' J).
    (1) Take k << I and  l << J such that x = k + l.
    (2) Take m << I and  n << J such that y = m + n.
    k + m belongs to I and l + n belongs to J.
    x + y .= (k + m) + (l + n) (by 1, 2, AddComm,AddAsso,AddBubble).
    Therefore the thesis.
    end.
For every element z (z * x) << (I +' J).
proof.
    Let z be an element. (1) Take k << I and l << J such that x = k + l.
    z * k belongs to I and z * l belongs to J .
    z * x .= (z * k) + (z * l) (by AMDistr1, 1).
    Therefore the thesis.
    end.
qed.


Lemma IdeInt.  I ** J is an ideal (by Definition).

Definition DefMod.  x = y (mod I)  iff  x - y << I.

Theorem ChineseRemainder.
Suppose that every element belongs to I +' J. Let x, y be elements.
There exists an element w such that w = x (mod I) and w = y (mod J).
Proof.
Take a << I and b << J such that a + b = 1 (by DefSum).
(1) Take w = (y * a) + (x * b).
Let us show that w = x (mod I) and w = y (mod J).
    w - x belongs to I.
    proof.
        w - x = (y * a) + ((x * b) - x).
        x * (b - 1) belongs to I.
        end.
    w - y belongs to J.
    proof.
        w - y = (x * b) + ((y * a) - y).
        y * (a - 1) belongs to J.
        end.
    end.
qed.


[synonym number/-s]

Signature NatSort.  A natural number is a notion.

Signature EucSort.  Let x be a nonzero element. |x| is a natural number.

Axiom Division.
Let x, y be elements and y != 0. There exist elements q,r such that
        x = (q * y) + r and (r != 0 => |r| -<- |y|).


[synonym divisor/-s] [synonym divide/-s]

Definition DefDiv.  x divides y  iff  for some z (x * z = y).

Let x | y stand for x divides y.
Let x is divided by y stand for y | x.

Definition DefDvs.  A divisor of x is an element that divides x.

Definition DefGCD.
A gcd of x and y is a common divisor c of x and y such that any common divisor
of x and y divides c.

Definition DefRel. x, y are relatively prime iff 1 is a gcd of x and y.


Definition DefPrIdeal.  <c> is a set such that for every z z is an element of <c>
iff there exists an element x such that z = c * x.

Lemma PrIdeal.  <c> is an ideal.
Proof.
Let x belong to <c>.
forall y << <c> x + y << <c>.
proof.
    Let y << <c>.
    (1) Take an element u such that c * u = x.
    (2) Take an element v such that c * v = y.
    x + y .= c * (u + v) (by 1, 2, AMDistr1).
    Therefore the thesis.
    end.
forall z z * x << <c>.
proof.
    Let z be an element.
    (1) Take an element u such that c * u = x.
    z * x .= c * (u * z) (by 1,MulComm,MulAsso, MulBubble).
    Therefore the thesis.
    end.
qed.

Theorem GCDin.  Let a, b be elements.
Assume that a is nonzero or b is nonzero. Let c be a gcd of a and b.
Then c belongs to <a> +' <b>.
Proof.
Take an ideal I equal to <a> +' <b>.
We have 0,a << <a> and 0,b << <b> (by MulZero, MulUnit).
Hence there exists a nonzero element of <a> +' <b>.
Indeed a << <a> +' <b> and b << <a> +' <b> (by AddZero).

Take a nonzero u << I such that for no nonzero v << I (|v| -<- |u|).
Proof.
    Assume the contrary.
    We can show by induction on |w| that for every nonzero w << I there exists
    nonzero u << I such that for no nonzero v << I (|v| -<- |u|). Obvious.
    qed.

u is a common divisor of a and b.
proof.
    Assume the contrary.
    For some elements x,y  u = (a * x) + (b * y).
    proof.
        Take k << <a> and l << <b> such that u = k + l.
        Take elements x,y such that (k = a * x and l = b * y).
        Hence the thesis.
        end.

    Case u does not divide a.
        Take elements q,r such that a = (q * u) + r
        and (r = 0 \/ |r| -<- |u|) (by Division).
        r is nonzero.
        - (q * u) belongs to I.
        a belongs to I (by AddZero).
        r = - (q * u) + a.
        Hence r belongs to I (by DefIdeal).
        end.

    Case u does not divide b.
        Take elements q,r such that b = (q * u) + r
        and (r = 0 \/ |r| -<- |u|) (by Division).
        r is nonzero.
        - (q * u) belongs to I.
        b belongs to I (by AddZero).
        r = - (q * u) + b.
        Hence r belongs to I (by DefIdeal).
        end.
    end.

Hence u divides c.
Hence the thesis.
proof.
    Take an element z such that c = z * u.
    Then c << I (by DefIdeal).
    end.
qed.
