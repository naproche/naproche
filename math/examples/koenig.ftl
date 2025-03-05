### ForTheL setup

[read examples/preliminaries.ftl]

Let M, N denote a set.

Let f denote a function.


### Cardinals and Cardinality

Signature. A cardinal is a set.

Let A, B, C denote cardinals.

Signature. A < B is an atom.

Let A \leq B stand for A = B or A < B.

Axiom. A < B < C implies A < C.

Axiom. A < B or B < A or B = A.

Let A is less than B stand for A < B.

Signature. The cardinality of M is a cardinal.

Let card(M) denote the cardinality of M.

Axiom. Assume M is a subset of Dom(f).
card(f[M]) \leq card(M).

Axiom. Assume the cardinality of N is less than the cardinality of M.
Then M \ N has an element.

Axiom. Assume card(M) \leq card(N).
Assume M has an element.
There exists a function f such that N is the domain of f and M is the image of
f.

Axiom. card(A) = A.


### Product and Sum of cardinals

Let D denote a set.

Definition. A sequence of cardinals on D is a function f such that Dom(f) = D
and f(x) is a cardinal for every element x of D.

Definition. Let kappa be a sequence of cardinals on D.
SumSet(kappa,D) = {(n,i) | i is an element of D and n is an element of
kappa(i)}.

Axiom. Let kappa be a sequence of cardinals on D.
Then SumSet(kappa,D) is a set.

Definition. Let kappa be a sequence of cardinals on D.
Sum(kappa,D) = card(SumSet(kappa,D)).

Definition. Let kappa be a sequence of cardinals on D.
ProdSet(kappa,D) = {f | f is a function and Dom(f) = D  and f(i) is an element
of kappa(i) for every element i of D}.

Axiom. Let kappa be a sequence of cardinals on D.
Then ProdSet(kappa,D) is a set.

Definition. Let kappa be a sequence of cardinals on D.
Prod(kappa,D) = card(ProdSet(kappa,D)).

Lemma Choice. Let lambda be a sequence of cardinals on D.
Assume that lambda(i) has an element for every element i of D.
ProdSet(lambda, D) has an element.

Proof.
  Define f(i) = choose an element v of lambda(i) in v for i in D.
  Then f is an element of ProdSet(lambda,D).
Qed.


### Koenig's lemma

Theorem Koenig. Let kappa, lambda be sequences of cardinals on D.
Assume that for every element i of D kappa(i) < lambda(i).
Then Sum(kappa,D) < Prod (lambda,D).

Proof by contradiction.
  Assume the contrary.
  Then Prod(lambda,D) \leq Sum(kappa,D).
  Take a function G such that SumSet(kappa,D) is the domain of G and
  ProdSet(lambda,D) is the image of G.
  Indeed ProdSet(lambda,D) has an element.

  Define Diag(i) = {G((n,i))(i) | n is an element of kappa(i)} for i in D.

  For every element f of ProdSet(lambda,D) for every element i of D f(i) is an
  element of lambda(i).
  For every element i of D lambda(i) is a set.
  For every element i of D for every element d of Diag(i) d is an element of
  lambda(i).
  For every element i of D Diag(i) is a set.

  For every element i of D card(Diag(i)) < lambda(i).
  Proof.
    Let i be an element of D.
    Define F(n) = G((n,i))(i) for n in kappa(i).
    Then F[kappa(i)] = Diag(i).
  Qed.

  Define f(i) = choose an element v of lambda(i) \ Diag(i) in v for i in D.

  Then f is an element of ProdSet(lambda,D).
  Take an element j of D and an element m of kappa(j) such that G((m,j)) = f.
  G((m,j))(j) is an element of Diag(j) and f(j) is not an element of Diag(j).
  Contradiction.
Qed.
