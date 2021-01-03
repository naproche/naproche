[synonym set/-s] [synonym subset/-s] [synonym element/-s] [synonym belong/-s]

Signature. An element is a notion.

Let S,T denote sets.
Let x,y,z,u,v,w denote elements.

Axiom. Every element of S is an element.

Let x << S denote (x is an element of S).
Let x belongs to S denote (x is an element of S).

Definition DefEmpty.    S is empty iff S has no elements.

Definition DefSub.
    A subset of S is a set T such that every (x << T) belongs to S.

Let S [= T denote S is a subset of T.

Signature LessRel.  x <= y is an atom.

Axiom ARefl. x <= x.
Axiom ASymm. x <= y <= x => x = y.
Axiom Trans. x <= y <= z => x <= z.

[synonym bound/-s] [synonym supremum/-s] [synonym infimum/-s] [synonym lattice/-s]

Definition DefLB.   Let S be a subset of T.
    A lower bound of S in T is an element u of T
        such that for every (x << S) u <= x.

Definition DefUB.   Let S be a subset of T.
    An upper bound of S in T is an element u of T
        such that for every (x << S) x <= u.

Definition DefInf.  Let S be a subset of T.
    An infimum of S in T is an element u of T
        such that u is a lower bound of S in T
        and for every lower bound v of S in T
        we have v <= u.

Definition DefSup.  Let S be a subset of T.
    A supremum of S in T is an element u of T
        such that u is a upper bound of S in T
        and for every upper bound v of S in T
        we have u <= v.

Lemma SupUn.    Let S be a subset of T.
    Let u,v be supremums of S in T. Then u = v.

Lemma InfUn.    Let S be a subset of T.
    Let u,v be infimums of S in T. Then u = v.

Definition DefCLat.
    A complete lattice is a set S such that every subset of S
        has an infimum in S and a supremum in S.


[synonym function/-s] [synonym point/-s]


Let f stand for a function.

Axiom. Dom(f) is a set.
Signature RanSort.  Ran(f) is a set.

Definition DefDom.  f is on S iff Dom(f) = Ran(f) = S.

Axiom ImgSort.  Let x belong to Dom(f).
    f[x] is an element of Ran(f).

Definition DefFix.
    A fixed point of f is an element x of Dom(f)
        such that f[x] = x.

Definition DefMonot.
    f is monotone iff for all x,y << Dom(f)
        x <= y  =>  f[x] <= f[y].


Theorem Tarski.
    Let U be a complete lattice and f be an monotone function on U.
    Let S be the set of fixed points of f.
    S is a complete lattice.
Proof.
    Let T be a subset of S.

    Let us show that T has a supremum in S.
        Define P = { x in U | f[x] <= x and x is an upper bound of T in U }.
        Take an infimum p of P in U.
        f[p] is a lower bound of P in U and an upper bound of T in U.
        Hence p is a fixed point of f and a supremum of T in S.
    end.

    Let us show that T has an infimum in S.
        Define Q = { x in U | x <= f[x] and x is a lower bound of T in U }.
        Take a supremum q of Q in U.
        f[q] is an upper bound of Q in U and a lower bound of T in U.
        Hence q is a fixed point of f and an infimum of T in S.
    end.
qed.
