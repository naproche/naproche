### Preliminaries

[read preliminaries.ftl]

Let x, y, X, Y denote sets.
Let f denote a function.

Let f is surjective from X onto Y stand for Dom(f) = X and f[X] = Y.

Let f : X ->> Y stand for f is surjective from X onto Y.

Let X is nonempty stand for X has an element.


### Ordinals

Signature. An ordinal is a set.

Let alpha, beta denote ordinals.

Axiom. Every element of alpha is an ordinal.

Axiom Transitivity. Let x \in y \in alpha.
Then x \in alpha.

Signature. alpha < beta is a relation.


Axiom. alpha < beta or beta < alpha or beta = alpha.


Axiom. If alpha < beta then alpha is an element of beta.

Let a \leq b stand for a = b or a < b.


### Cardinals

Signature. A cardinal is an ordinal.

Let kappa, mu, nu denote cardinals.

Signature Cardinality. |X| is a cardinal.

Axiom Existence of surjection. Assume X has an element.
|X| \leq |Y| iff there exists a function f such that Dom(f) = Y and f[Y] = X.

Axiom. |X \times X| = |X|.


Axiom. |kappa| = kappa.

Axiom. Let Y be a subset of X.
|Y| \leq |X|.

Signature. Succ(kappa) is a cardinal.

Axiom. kappa < Succ(kappa).

Axiom. |alpha | \leq kappa for every element alpha of Succ(kappa).

Axiom. For no cardinals mu, nu we have mu < nu and nu < mu.

Axiom. There is no cardinal nu such that kappa < nu < Succ(kappa).

Axiom. The empty set is a cardinal eta such that eta is an element of every
nonempty ordinal.

Definition. The constant zero on X is the function f such that Dom(f) = X and
f(x) is the empty set for every element x of X.

Let 0^X stand for the constant zero on X.


### Cofinality and regular cardinals

Definition Cofinality. Let kappa be a cardinal.
Let Y be a subset of kappa.
Y is cofinal in kappa iff for every element x of kappa there exists an element
y of Y such that x < y.

Let a cofinal subset of K stand for a subset of K that is cofinal in K.

Definition. kappa is regular iff |x| = kappa for every cofinal subset x of
kappa.


### Hausdorff's theorem

Theorem Hausdorff. Succ(kappa) is regular.

Proof by contradiction.
  Assume the contrary.
  Take a cofinal subset x of Succ(kappa) such that |x| \neq Succ(kappa).
  Then |x| \leq kappa .
  Take a function f that is surjective from kappa onto x (by existence of
  surjection).
  Indeed x has an element and |kappa| = kappa.

  Define g(z) =
    case z has an element -> choose a function h such that h : kappa ->> z in h,
    case z has no element -> 0^kappa
  for z in Succ(kappa).

  For all xi, zeta \in kappa g(f(xi)) is a map such that zeta \in Dom(g(f(xi))).
  Define h((xi,zeta)) = g(f(xi))(zeta) for (xi,zeta) in kappa \times kappa.

  Let us show that h is surjective from kappa \times kappa onto Succ(kappa).

    Every element of Succ(kappa) is an element of h[kappa \times kappa].
    Proof.
      Let n be an element of Succ(kappa).
      Take an element xi of kappa such that n < f(xi).
      Take an element zeta of kappa such that g(f(xi))(zeta) = n.
      Indeed g(f(xi)) is a function that is surjective from kappa onto f(xi).
      Then n = h(xi,zeta).
      Therefore the thesis.
      Indeed (xi,zeta) is an element of kappa \times kappa.
    End.

    Every element of h[kappa \times kappa] is an element of Succ(kappa).
    Proof.
      Let n be an element of h[kappa \times kappa].
      We can take elements a, b of kappa such that n = h(a,b).
      Then n = g(f(a))(b).
      f(a) is an element of Succ(kappa).
      Every element of f(a) is an element of Succ(kappa).

      Case f(a) has an element.
        Then g(f(a)) is a function that is surjective from kappa onto f(a).
        Hence n \in f(a) \in Succ(kappa).
        Thus n \in Succ(kappa).
      End.

      Case f(a) has no element.
        Then g(f(a)) = 0^kappa.
        Hence n is the empty set.
        Thus n \in Succ(kappa).
      End.
    End.
  End.

  Therefore Succ(kappa) \leq kappa.
  Contradiction.
Qed.
