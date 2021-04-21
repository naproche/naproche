[read Formalizations/Library/L14-Clubs.ftl]

[prove off]

## Pretyped Variables

Let w,x,y,z,W,X,Y,Z stand for zfsets.
Let a,b,c,d,A,B,C,D,M stand for sets.
Let o,o1,o2 stand for objects.
Let alpha, beta, gamma stand for ordinals.
Let f,g,h,F,G,H stand for zffunction.
Let kappa, lambda stand for cardinals.



## Stationary Sets

Definition. Let kappa /in /BigCard. Let X /subset kappa. X is nonstationary in kappa iff kappa /setminus X /in Club(kappa).

Definition. Let kappa /in /BigCard. The nonstationary ideal of kappa is {X /subset kappa | X is nonstationary in kappa}.
Let NS(k) stand for the nonstationary ideal of k.

Definition. Let kappa /in /BigCard. Let X /subset kappa. X is stationary in kappa iff X /notin NS(kappa).

Lemma stationary. Let kappa /in /BigCard. Let X /subset kappa. X is stationary in kappa iff (forall C /subset kappa (C /club kappa => X /cap C /neq /emptyset)).

Lemma. Let kappa /in /BigCard. Let X /in Club(kappa). Then X is stationary in kappa.

Lemma. Let kappa /in /BigCard. /emptyset /neq NS(kappa) /\ NS(kappa) /subset /PP kappa.

Lemma. Let kappa /in /BigCard. kappa /notin NS(kappa).

Lemma NSsubset. Let kappa /in /BigCard. Let X /in NS(kappa). Let Y /subset X. Then Y /in NS(kappa).

Lemma. Let kappa /in /BigCard. Let X,Y /in NS(kappa). Then X /cup Y /in NS(kappa).

Lemma. Let kappa /in /BigCard. Let lambda /in cof(kappa). Let lambda /neq /emptyset. Let X be a sequence of length lambda in NS(kappa). Then /bigcup X^[lambda] /in NS(kappa).

Lemma. Let kappa /in /BigCard. Let cof(kappa) = kappa. Let X be a sequence of length kappa in /PP kappa. Then forall i /in kappa X[i] /in /VV.

Definition. Let kappa /in /BigCard. Let cof(kappa) = kappa. Let X be a sequence of length kappa in /PP kappa.
The diagonal intersection of X of length kappa is {beta /in kappa | forall i /in beta (i /in kappa /\ X[i] /subset kappa /\ beta /in X[i])}.
Let /triangle(X,k) stand for the diagonal intersection of X of length k.

Definition. Let kappa /in /BigCard. Let cof(kappa) = kappa. Let X be a sequence of length kappa in /PP kappa.
The diagonal union of X of length kappa is {beta /in kappa | exists i /in beta (i /in kappa /\ X[i] /subset kappa /\ beta /in X[i])}.
Let /vartriangle(X,k) stand for the diagonal union of X of length k.

Lemma. Let kappa /in /BigCard. Let X be a sequence of length kappa in Club(kappa). Then X is a sequence of length kappa in /PP kappa.

Lemma. Let kappa /in /BigCard. Let X be a sequence of length kappa in Cl(kappa). Then X is a sequence of length kappa in /PP kappa.

Lemma. Let kappa /in /BigCard. Let X be a sequence of length kappa in NS(kappa). Then X is a sequence of length kappa in /PP kappa.

Lemma. Let kappa /in /BigCard. Let kappa be regular. Let X be a sequence of length kappa in Club(kappa). Then /triangle(X,kappa) /in Club(kappa).

Lemma. Let kappa /in /BigCard. Let kappa be regular. Let X be a sequence of length kappa in NS(kappa). Then /vartriangle(X,kappa) /in NS(kappa).



[prove on]
