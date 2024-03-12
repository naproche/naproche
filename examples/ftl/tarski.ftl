# Tarski's Theorem
# ================

[read ftl/preliminaries.ftl]

Let S,T denote classes.
Let X,Y denote sets.
Let x,y,z,u,v,w denote objects.
Let f denote a function.

Signature LessRel.
x \leq y is an atom.

Axiom ARefl.
x \leq x.

Axiom ASymm.
x \leq y \leq x => x = y.

Axiom Trans.
x \leq y \leq z => x \leq z.


Definition DefLB.
Let S be a subset of T.
A lower bound of S in T is an element u of T such that for every x \in S
we have u \leq x.

Definition DefUB.
Let S be a subset of T.
An upper bound of S in T is an element u of T such that for every x \in S
we have x \leq u.

Definition DefInf.
Let S be a subset of T.
An infimum of S in T is an element u of T such that u is a lower bound of S in T
and for every lower bound v of S in T we have v \leq u.

Definition DefSup.
Let S be a subset of T.
A supremum of S in T is an element u of T such that u is a upper bound of S in T
and for every upper bound v of S in T we have u \leq v.

Lemma SupUn.
Let S be a subset of T.
Let u,v be suprema of S in T.
Then u = v.

Lemma InfUn.
Let S be a subset of T.
Let u,v be infima of S in T.
Then u = v.

Definition DefCLat.
A complete lattice is a set S such that every subset of S
has an infimum in S and a supremum in S.

Definition DefFix.
A fixed point of f is an element x of Dom(f) such that f(x) = x.

Definition DefMonot.
f is monotone iff for all x,y \in Dom(f)
x \leq y  =>  f(x) \leq f(y).

Theorem Tarski.
Let U be a complete lattice and f be an monotone function on U.
Let S be the collection of all fixed points of f.
Then S is a complete lattice.
Proof.
  U is a set and S is a subclass of U.
  Hence S is a set.
  Let T be a subset of S.
  
  Let us show that T has a supremum in S.
    Define P = { x in U | f(x) \leq x and x is an upper bound of T in U }.
    P is a set.
    Take an infimum p of P in U.
    f(p) is a lower bound of P in U and an upper bound of T in U.
    Hence p is a fixed point of f and a supremum of T in S.
  End.

  Let us show that T has an infimum in S.
    Define Q = { x in U | x \leq f(x) and x is a lower bound of T in U }.
    Take a supremum q of Q in U.
    f(q) is an upper bound of Q in U and a lower bound of T in U.
    Hence q is a fixed point of f and an infimum of T in S.
  End.
Qed.
