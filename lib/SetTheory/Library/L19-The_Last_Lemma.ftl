[read Formalizations/Library/L18-Almost_Disjoint_Functions.ftl]

[prove off]

## Pretyped Variables

Let w,x,y,z,W,X,Y,Z stand for zfsets.
Let a,b,c,d,A,B,C,D,M stand for sets.
Let o,o1,o2 stand for objects.
Let alpha, beta, gamma stand for ordinals.
Let f,g,h,F,G,H stand for zffunction.
Let kappa, lambda stand for cardinals.



## General Lemmata

Lemma. Let f be a function. Let x be a zfset. Then f /caret [x] is a zfset.

Lemma. Let x be a zfset. Let x /neq /emptyset. Then x /in Dom(Choice).


## Prerequisites

Lemma. Let A be a zffunction. Forall i /in Dom(A) (A[i] is a zfset).

Lemma. Let kappa,x,kap be objects. Let (kappa,x,kap) be a coftriple. Then forall i /in cof(kappa) (Plus[kap[i]] is a zfset).

Definition. Let kappa,x,kap be objects. Let (kappa,x,kap) be a coftriple. Let A be a zffunction. A is silvercompatible with kap relative to kappa and x iff
Dom(A) = cof(kappa) /\ forall i /in cof(kappa) Card(A[i]) /subset Plus[kap[i]].

Definition. Let f,g be zffunctions. Let Dom(f) = Dom(g). Let X /subset Dom(f). g is smaller than f on X iff forall i /in X g[i] /subset f[i].
Let g <{X} f stand for g is smaller than f on X.

Definition. Let lambda be a zfset. Let S /subset lambda. Let F /subset ^{lambda}/VV. Let f /in ^{lambda}/VV. The set of bounded functions by f on S in F relative to lambda is
{g /in F | g <{S} f}.
Let F<{f,S,l} stand for the set of bounded functions by f on S in F relative to l.

Lemma. Let lambda /in /Lim. Let F be an almost disjoint family of functions on lambda. Let G /subset F. Then G is an almost disjoint family of functions on lambda.


## The last Lemma before Silver's Theorem

Lemma Silver2. Let kappa, x, kap, F be objects. Let (kappa,x,kap) be a coftriple. Let Silver below kappa. Let A be a zffunction. Let A be silvercompatible with kap relative to kappa and x.
Let F be almost disjoint relative to A. Then Card(F) /subset Plus[kappa].





[prove on]
