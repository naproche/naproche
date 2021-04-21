[read Formalizations/Library/L11-Gimel_Function.ftl]

[prove off]

## Pretyped Variables

Let w,x,y,z,W,X,Y,Z stand for zfsets.
Let a,b,c,d,A,B,C,D,M stand for sets.
Let o,o1,o2 stand for objects.
Let alpha, beta, gamma stand for ordinals.
Let f,g,h,F,G,H stand for zffunction.
Let kappa, lambda stand for cardinals.



## Prerequisites

Lemma. Forall a exists f (Dom(f) = /VV /\ forall b /in a f[b] = b /\ forall b /in /VV /setminus a f[b] = 0).

Lemma. Let a be a set. Let g be a zffunction. Let a /subset Dom(g). Then exists f (Dom(f) = /VV /\ forall b /in a f[b] = g[b] /\ forall b /in /VV /setminus a f[b] = 0).

Signature. Let a be a set. delta(a) is a zffunction.
Axiom. Let a be a set. Dom(delta(a)) = /VV.
Axiom. Let a be a set. (Forall b /in a (delta(a))[b] = b) /\ (forall b /in /VV /setminus a (delta(a))[b] = 0).

Signature. Let a be a set. Let g be a zffunction. Let a /subset Dom(g). delta(g,a) is a zffunction.
Axiom. Let a be a set. Let g be a zffunction. Let a /subset Dom(g). Dom(delta(g,a)) = /VV.
Axiom. Let a be a set. Let g be a zffunction. Let a /subset Dom(g). (Forall b /in a (delta(g,a))[b] = g[b]) /\ (forall b /in /VV /setminus a (delta(g,a))[b] = 0).


## Cardinal Exponentiation

Lemma. Let v /in /VV. Let b /in /Cd. Then Card(^{b}v) = Card(v) ^ b.

Lemma. Let lambda, kappa /in /Card. Let xi /in /Cd. Let lambda /in kappa. Let xi /in kappa. Let kappa /subset xi ^ lambda.
Then kappa ^ lambda = xi ^ lambda.

Lemma. Let kappa, lambda /in /Card. Let lambda /in kappa. Let forall xi /in /Cd /cap kappa (xi ^ lambda /in kappa). Let lambda /in cof(kappa).
Then kappa ^ lambda = kappa.

Definition. Let f,g be zffunctions. f and g are diagcomposable iff Dom(f) = Dom(g) /\ forall i /in Dom(f) ((f[i] is a zffunction) /\ g[i] /in Dom(f[i])).

Lemma. Let f,g be zffunction. Let f and g be diagcomposable. Then exists h (Dom(h) = Dom(f) /\ forall i /in Dom(f) h[i] = (f[i])[g[i]]).

Definition. Let f,g be zffunction. Let f and g be diagcomposable.
The diagcomposition of f and g is a zffunction h such that (Dom(h) = Dom(f) /\ forall i /in Dom(f) h[i] = (f[i])[g[i]]).
Let g /comp f stand for the diagcomposition of f and g.

Lemma. Let kappa, lambda /in /Card. Let lambda /in kappa. Let forall xi /in /Cd /cap kappa (xi ^ lambda /in kappa). Let cof(kappa) /subset lambda.
Then kappa ^ lambda = Gimel[kappa].




[prove on]
