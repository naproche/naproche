[synonym cardinal/-s][synonym ordinal/-s]



Let M,N denote sets.


Axiom.
For any objects a,b,c,d if (a,b) = (c,d) then a = c and b = d.

Axiom. Let x be an element of M. x is setsized.
Axiom. Let x,y be setsized objects. (x, y) is setsized.
Axiom. Let f be a function. Let M be a set. Assume Dom(f) = M.
  Let x be an element of M. Then f(x) is setsized.

Definition.
Prod(M,N) = {(x,y) | x is an element of M and y is an element of N}.

Axiom.
Prod(M, N) is a set.

Lemma.
Let x,y be objects.
If (x,y) is an element of Prod(M,N) then x is an element of M and y is an
element of N.


Let f denote a function.


Definition.
A subset of M is a set N such that every element of N is an element of M.

Axiom Ext. If M is a subset of N and N is a subset of M then M = N.

Definition.
Assume M is a subset of Dom(f). f^(M) = { f(x) | x is an element of M }.

Axiom. Assume M is a subset of Dom(f). Then f^(M) is a set.


Let f is surjective from M onto N stand for Dom(f) = M and f^(M) = N.

Signature.
An ordinal is a set.

Let alpha, beta denote ordinals.

Axiom.
Every element of alpha is an ordinal.

Signature.
A cardinal is an ordinal.

Let A,B,C denote cardinals.

Signature.
alpha < beta is an atom.

Axiom.
If alpha < beta then alpha is an element of beta.

Let a =< b stand for a = b or a < b.

Definition.
Assume M is a subset of A.
M is cofinal in A iff for every element x of A there exists an element y of M
such that x < y.

Let a cofinal subset of A stand for a subset of A that is cofinal in A.


Signature.
The cardinality of M is a cardinal.

Let card(M) stand for the cardinality of M.


Axiom Surj_Exi.
Assume M has an element. card(M) =< card(N) iff there exists a function f such
that Dom(f) = N and f^(N) = M.

Axiom Transitivity.
Let M be an element of A. Assume N is an element of M. N is an element of A.

Axiom.
card(Prod(M,M)) = card(M).

Axiom.
card(A) = A.

Axiom.
Let N be a subset of M. card(N) =< card(M).

Definition.
A is regular iff card(M) = A for every cofinal subset M of A.

Signature.
Succ(A) is a cardinal.

Axiom.
alpha < beta or beta < alpha or beta = alpha.

Axiom.
A < Succ(A).

Axiom.
card(i) =< A for every element i of Succ(A).

Axiom.
For no cardinals A,B we have A < B and B < A.

Axiom.
There is no cardinal B such that A < B < Succ(A).

Definition.
The empty set is a cardinal E such that E is an element of (every ordinal that
has an element).

Definition.
The constant zero on M is a function f such that Dom(f) = M and f(x) is the
empty set for every element x of M.

Let 0^M stand for the constant zero on M.


Theorem.
Succ(A) is regular.
Proof by contradiction.
Assume the contrary.
Take a cofinal subset x of Succ(A) such that card(x) != Succ(A).
Then card(x) =< A.
Take a function f that is surjective from A onto x (by Surj_Exi).
Indeed x has an element and card(A) = A.
Define g(i) =
	Case i has an element -> Choose a function h that is surjective from A onto i in h,
	Case i has no element -> 0^A
for i in Succ(A).
Define h((xi,zeta)) = g(f(xi))(zeta) for (xi,zeta) in Prod(A,A).
Let us show that h is surjective from Prod(A,A) onto Succ(A).
	Dom(h) = Prod(A,A).
	Every element of Succ(A) is an element of h^(Prod(A,A)).
	proof.
		Let n be an element of Succ(A). Take an element xi of A such that n < f(xi).
		Take an element zeta of A such that g(f(xi))(zeta) = n.
		Then n = h((xi,zeta)). Therefore the thesis. Indeed (xi,zeta) is an element of Prod(A,A).
		end.
	Every element of h^(Prod(A,A)) is an element of Succ(A).
		proof.
			Let n be an element of h^(Prod(A,A)).
			We can take elements a,b of A such that n = h((a,b)).
			Then n = g(f(a))(b). f(a) is an element of Succ(A).

			Case f(a) has an element. Obvious (by Transitivity).
			Case f(a) has no element. Obvious (by Transitivity).
		end.
	end.
	Therefore Succ(A) =< A. Contradiction.
qed.
