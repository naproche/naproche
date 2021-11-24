[dump on]
[printcheck on]

Lemma. Every set is a class.
Lemma. Every set is an object.
Lemma. Every function is a map.

Let x << X stand for x is an element of X.
Let x !<< X stand for x is not an element of X.

Definition Subclass.
    Let A be a class.
    A subclass of A is a class B such that every element of B is an element of A.

Let a subset of X stand for a set that is a subclass of X.

Axiom.
    Let A be a set. 
    Let B be a subclass of A.
    Then B is a set.

Let a proper subclass of B stand for a subclass A of B such that A != B.
Let a proper subset of B stand for a subset A of B such that A != B.


Lemma. 
    Let f be a function.
    Let x be an element of Dom f.
    Then f(x) is an object.

Definition. 
    Let B, C be classes.
    B is disjoint from C iff there is no element of B that is an element of C.

Definition.
    A family is a set F such that every element of F is a set.

Definition.
    A disjoint family is a family F such that
    B is disjoint from C for all nonequal elements B, C of F.

Definition.
    Let B, C be classes.
    B /\ C = { x in B | x << C}.

Definition.
    Let B, C be classes.
    B -- C = { x in B | x !<< C}.

Axiom PairDefiningProperty.
      Let u, v, x, y be objects.
      If (x, y) = (u, v)
      then x = u and y = v.

Definition.
    Let F be a map.
    Let B, C be classes.
    F : B -> C iff Dom F = B and
    F(x) is an element of C for all elements x of B.

#Let F : B -> C stand for Dom F = B and F(x) is an element of C for all elements x of B.

Let g retracts f stand for g(f(x)) = x for all elements x of Dom f.
Let h sections f stand for f(h(y)) = y for all elements y of Dom h.
    
Definition.
    Let F be a map.
    Let B, C be classes.
    F : B <-> C iff F : B -> C and there exists a map G such that
    G : C -> B  and
    G retracts F and G sections F.

Definition.
    Let B, C be sets.
    B is equinumerous with C iff there exists a map F such that
    F : B <-> C.

Lemma.
    Let B, C be sets.
    Assume that B is equinumerous with C.
    Then C is equinumerous with B.

Lemma.
    Let A, B, C be sets.
    Assume A is equinumerous with B.
    Assume B is equinumerous with C.
    Then A is equinumerous with C.
Proof.
    Take a map F such that F : A <-> B.
    Take a map G such that G : B -> A  and (for all elements x of A we have G(F(x)) = x) and
    (for all elements y of B we have F(G(y))=y).
    Take a map H such that H : B <-> C.
    Take a map I such that I : C -> B and (for all elements x of B we have I(H(x)) = x) and
    (for all elements y of C we have H(I(y))=y).
    For every element x of A H(F(x)) is an object.
    Define J(x) = H(F(x)) for x in A.
    For every element y of C G(I(y)) is an object.
    J : A <-> C. Indeed define K(y) = G(I(y)) for y in C.
End.


Definition.
    Let X be a set.
    X is Dedekind finite iff every proper subset of X is not equinumerous with X.
#Let X is Dedekind finite stand for every proper subset of X is not equinumerous with X.