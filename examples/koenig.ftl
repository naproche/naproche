[synonym cardinal/-s][synonym sequence/-s]
[read ZFC.ftl]
Let the domain of f stand for Dom(f).

Let M,N denote a set.

Let f denote a function.
Axiom. f is setsized.

### Some preliminary set theory

Definition.
A subset of M is a set N such that every element of N is an element of M.

Definition.
M \ N = { x ∈ M | x is not an element of N }.

Definition.
Assume M is a subset of the domain of f. f[M] = { f(x) | x is an element of M }.

Axiom.
Assume M is a subset of the domain of f. f[M] is a set.

Let the image of f stand for f[Dom(f)].

### Cardinals and Cardinality

Signature.
A cardinal is a set.

Let A,B,C denote cardinals.

Signature.
A < B is an atom.

Let A =< B stand for A = B or A < B.

Axiom.
A < B < C ⟹ A < C.

Axiom.
A < B or B < A or B = A.

Let A is less than B stand for A < B.

Signature.
The cardinality of M is a cardinal.

Let card(M) denote the cardinality of M.

Axiom Image_Card. Assume M is a subset of Dom(f). card(f[M]) =< card(M).

Axiom.
Assume the cardinality of N is less than the cardinality of M. Then M \ N has an element.

Axiom Surj_Exi.
Assume card(M) =< card(N). Assume M has an element. There exists a function f such that N is the
domain of f and M is the image of f.

Axiom.
card(A) = A.

### Product and Sum of cardinals

Let D denote a set.

Definition.
A sequence of cardinals on D is a function f such that Dom(f) = D and f(x) is a cardinal for every
element x of D.

Signature.
Let κ be a sequence of cardinals on D. SumSet(κ,D) is a set.

Axiom Sum_Def.
Let κ be a sequence of cardinals on D.
SumSet(κ,D) =
  { (n,i) | i is an element of D and n is an element of κ(i) }.
Axiom. Let κ be a sequence of cardinals on D. Then SumSet(κ, D) is a set.

Definition.
Let κ be a sequence of cardinals on D. Sum(κ,D) = card(SumSet(κ,D)).

Signature.
Let κ be a sequence of cardinals on D. ProdSet(κ,D) is a set.

Axiom Prod_Def.
let κ be a sequence of cardinals on D.
ProdSet(κ,D) =
  { function f | Dom(f) = D ∧ (f(i) is an element of κ(i) for every element i of D) }.
Axiom. Let κ be a sequence of cardinals on D. Then ProdSet(κ, D) is a set.

Definition.
Let κ be a sequence of cardinals on D. Prod(κ,D) = card(ProdSet(κ,D)).

Lemma Choice. Let λ be a sequence  of cardinals on D. Assume that λ(i) has an element
for every element i of D.  ProdSet(λ, D) has an element.
Proof.
Define f(i) = Choose an element v of λ(i) in v for i in D.
Then f is an element of ProdSet(λ,D). qed.

### Koenig's lemma

Theorem Koenig.
Let κ, λ be sequences of cardinals on D. Assume that for every element i of D
κ(i) < λ(i). Then Sum(κ,D) < Prod (λ,D).
Proof by contradiction.
Assume the contrary. Then Prod (λ,D) =< Sum(κ,D).
Take a function G such that SumSet(κ,D) is the domain of G and ProdSet(λ,D) is the image
of G.
  Indeed ProdSet(λ, D) has an element.
Define Δ(i) = { G((n,i))(i) | n is an element of κ(i) } for i in D.
For every element f of ProdSet(λ, D) for every element i of D f(i) is an element of λ(i).
For every element i of D λ(i) is a set.
For every element i of D for every element d of Δ(i) d is an element of λ(i).
For every element i of D Δ(i) is a set.
For every element i of D card(Δ(i)) < λ(i). Proof.
  Let i be an element of D. Define F(n) = G((n,i))(i) for n in κ(i).
  Then F[κ(i)] = Δ(i).qed.
Define f(i) = Choose an element v of λ(i) \ Δ(i) in v for i in D.
Then f is an element of ProdSet(λ,D).
Take an element j of D and an element m of κ(j) such that G((m,j)) = f. G((m,j))(j) is an
element of Δ(j) and f(j) is not an element of Δ(j).
Contradiction.
qed.
