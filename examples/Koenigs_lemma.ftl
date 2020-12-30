[synonym cardinal/-s][synonym sequence/-s]
Let the domain of f stand for Dom(f).


Let M,N denote a set.

Let f denote a function.

### Some preliminary set theory

Definition.
A subset of M is a set N such that every element of N is an element of M.

Definition.
M \ N = { x in M | x is not an element of N }.

Definition.
Assume M is a subset of the domain of f. f^[M] = { f[x] | x is an element of M }. Let the image of
f stand for f^[Dom(f)].

### Cardinals and Cardinality

Signature.
A cardinal is a set.

Let A,B,C denote cardinals.

Signature.
A < B is an atom.

Let A =< B stand for A = B or A < B.

Axiom.
A < B < C => A < C.

Axiom.
A < B or B < A or B = A.

Let A is less than B stand for A < B.

Signature.
The cardinality of M is a cardinal.

Let card(M) denote the cardinality of M.

Axiom Image_Card. Assume M is a subset of Dom(f). card(f^[M]) =< card(M).

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
A sequence of cardinals on D is a function f such that Dom(f) = D and f[x] is a cardinal for every
element x of D.

Signature.
Let kappa be a sequence of cardinals on D. SumSet(kappa,D) is a set.

Axiom Sum_Def.
Let kappa be a sequence of cardinals on D.
SumSet(kappa,D) =
  { (n,i) | i is an element of D and n is an element of kappa[i] }.

Definition.
Let kappa be a sequence of cardinals on D. Sum(kappa,D) = card(SumSet(kappa,D)).

Signature.
Let kappa be a sequence of cardinals on D. ProdSet(kappa,D) is a set.

Axiom Prod_Def.
let kappa be a sequence of cardinals on D.
ProdSet(kappa,D) =
  { function f | Dom(f) = D /\ (f[i] is an element of kappa[i] for every element i of D) }.

Definition.
Let kappa be a sequence of cardinals on D. Prod(kappa,D) = card(ProdSet(kappa,D)).

Lemma Choice. Let lambda be a sequence  of cardinals on D. Assume that lambda[i] has an element
for every element i of D.  ProdSet(lambda, D) has an element.
Proof.
Define f[i] = Choose an element v of lambda[i] in v for i in D.
Then f is an element of ProdSet(lambda,D). qed.

### Koenig's lemma

Theorem Koenig.
Let kappa, lambda be sequences of cardinals on D. Assume that for every element i of D
kappa[i] < lambda[i]. Then Sum(kappa,D) < Prod (lambda,D).
Proof by contradiction.
Assume the contrary. Then Prod (lambda,D) =< Sum(kappa,D).
Take a function G such that SumSet(kappa,D) is the domain of G and ProdSet(lambda,D) is the image
of G.
  Indeed ProdSet(lambda, D) has an element.
Define Diag[i] = { G[(n,i)][i] | n is an element of kappa[i] } for i in D.
For every element i of D card(Diag[i]) < lambda[i]. Proof.
  Let i be an element of D. Define F[n] = G[(n,i)][i] for n in kappa[i].
  Then F^[kappa[i]] = Diag[i].qed.
Define f[i] = Choose an element v of lambda[i] \ Diag[i] in v for i in D.
Then f is an element of ProdSet(lambda,D).
Take an element j of D and an element m of kappa[j] such that G[(m,j)] = f. G[(m,j)][j] is an
element of Diag[j] and f[j] is not an element of Diag[j].
Contradiction.
qed.
