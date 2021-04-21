[read Formalizations/Library/L16-Fodors_Lemma.ftl]

[prove off]

## Pretyped Variables

Let w,x,y,z,W,X,Y,Z stand for zfsets.
Let a,b,c,d,A,B,C,D,M stand for sets.
Let o,o1,o2 stand for objects.
Let alpha, beta, gamma stand for ordinals.
Let f,g,h,F,G,H stand for zffunction.
Let kappa, lambda stand for cardinals.




## Prerequisites

Lemma. Let kappa be a successor cardinal. Then kappa /in /BigCard.

Definition. Let kappa /in /BigCard. Let S be a set. The set of stationary subsets of kappa in S is
{x /in stat(kappa) | x /subset S}.
Let stat(k,S) stand for the set of stationary subsets of k in S.

Lemma. Let M be a set. Let lambda /in /Ord. Let f be a sequence of length lambda in M. Forall a /in lambda (f[a] is a zfset).

Definition. Let M be a set. Let lambda /in /Ord. Let f be a sequence of length lambda in M. f is pairwise disjoint on lambda in M iff
forall a,b /in lambda (a /neq b => f[a] /cap f[b] = /emptyset).

Signature. Let a,b,c be objects. (a,b,c) is an object.
Axiom. Let a1,a2,b1,b2,c1,c2 be objects. (a1,b1,c1) = (a2,b2,c2) => a1 = a2 /\ b1 = b2 /\ c1 = c2.

Definition. Let lambda be an ordinal. Let M be a set. A sequence of functions on M of length lambda is a zffunction f such that 
Dom(f) = lambda /\ forall i /in lambda ((f[i] is a zffunction) /\ Dom(f[i]) = M).

Signature. A functiontriple is a notion.

Axiom. Let f,lambda,M be objects. (f,lambda,M) is a functiontriple iff M is a set and lambda is an ordinal and f is a sequence of functions on M of length lambda.

Lemma. Let (f,lambda,M) be a functiontriple. Forall v /in lambda ((f is a zffunction) /\ v /in Dom(f) /\ (f[v] is a zffunction)).

Definition. Let (f,lambda,M) be a functiontriple. Let i /in M. Let alpha be a zfset.
The support of f in lambda on M at i over alpha is {v /in lambda | i /in Dom(f[v]) /\ alpha /subset (f[v])[i]}.
Let Supp(f,l,M){i,a} stand for the support of f in l on M at i over a.

Definition. Let (f,lambda,M) be a functiontriple. Let i /in M. Let alpha be a zfset.
The eqsupport of f in lambda on M at i at alpha is {v /in lambda | i /in Dom(f[v]) /\ alpha = (f[v])[i]}.
Let EqSupp(f,l,M){i,a} stand for the eqsupport of f in l on M at i at a.

Lemma. Let x be a zfset. Let M be a set. Then exists f (Dom(f) = M /\ forall i /in M f[i] = x).

Definition. Let x be a zfset. Let M be a set. const(x,M) is a zffunction f such that Dom(f) = M /\ forall i /in M f[i] = x.


## The Theorem

Theorem DisjStat. Let kappa be a successor cardinal. Let S /in stat(kappa). Then exists f (f is a sequence of length kappa in stat(kappa,S) and f is pairwise disjoint on kappa in stat(kappa,S)).




[prove on]
