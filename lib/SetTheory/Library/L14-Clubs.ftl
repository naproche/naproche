[read Formalizations/Library/L12-Cardinal_Exponentiation.ftl]

[prove off]

## Pretyped Variables

Let w,x,y,z,W,X,Y,Z stand for zfsets.
Let a,b,c,d,A,B,C,D,M stand for sets.
Let o,o1,o2 stand for objects.
Let alpha, beta, gamma stand for ordinals.
Let f,g,h,F,G,H stand for zffunction.
Let kappa, lambda stand for cardinals.





## Closed unbounded sets

Definition. The class of cardinals of uncountable cofinality is
{kappa /in /Card | Alef[1] /subset cof(kappa)}.
Let /BigCard stand for the class of cardinals of uncountable cofinality.

Lemma. Let kappa /in /BigCard. Then kappa /in /Card and Alef[1] /subset cof(kappa).

Definition. Let kappa /in /Lim. Let C /subset kappa. C is closed in kappa iff
(forall lambda /in /Lim /cap kappa (C /cap lambda /cof lambda => lambda /in C)).
Let C /closed k stand for C is closed in k.

Definition. Let kappa /in /Lim. Let C /subset kappa. C is closed unbounded in kappa iff
(C /cof kappa /\ (C is closed in kappa)).
Let C /club k stand for C is closed unbounded in k.

Definition. Let kappa /in /Lim. The set of clubs in kappa is
{X /subset kappa | X /club kappa}.
Let Cl(k) stand for the set of clubs in k.

Lemma. Let kappa /in /Lim. Let alpha /in kappa. Let X /in Cl(kappa). Then X /setminus alpha /in Cl(kappa).

Signature. Let M be a set. Let lambda /in /Ord. A sequence of length lambda in M is a zffunction.
Axiom sequence. Let M be a set. Let lambda /in /Ord. Let C be a zffunction. C is a sequence of length lambda in M iff Dom(C) = lambda /\ forall i /in lambda C[i] /in M.
Axiom. Let M be a set. Let lambda /in /Ord. Let C be a sequence of length lambda in M. Then (C is a zffunction) /\ Dom(C) = lambda /\ forall i /in lambda C[i] /in M.

Lemma clubintersection. Let kappa /in /BigCard. Let lambda /in cof(kappa). Let lambda /neq /emptyset. Let C be a sequence of length lambda in Cl(kappa).
Then (C is a zffunction) /\ /bigcap C^[lambda] /subset kappa /\ /bigcap C^[lambda] /club kappa.

Lemma. Let kappa /in /BigCard. Let C,D /subset kappa. Let C,D /club kappa. Then C /cap D /club kappa.

Definition. Let kappa /in /BigCard. The closed unbounded filter on kappa is
{X /subset kappa | exists C /subset X (C /club kappa)}.
Let Club(k) stand for the closed unbounded filter on k.

Lemma. Let kappa /in /BigCard. Let C /subset kappa. Let C /club kappa. Then C /in Club(kappa).

Lemma. Let kappa /in /BigCard. Then kappa /club kappa.

Lemma. Let kappa /in /BigCard. Then Club(kappa) /in /VV.

Lemma. Let kappa /in /BigCard. Then Club(kappa) /neq /emptyset /\ Club(kappa) /subset /PP kappa.

Lemma. Let kappa /in /BigCard. Then /emptyset /notin Club(kappa).

Lemma ClubSubset. Let kappa /in /BigCard. Let X /in Club(kappa). Let Y /subset kappa. Let X /subset Y. Then Y /in Club(kappa).

Lemma. Let kappa /in /BigCard. Let X,Y /in Club(kappa). Then X /cap Y /in Club(kappa).

Lemma. Let kappa /in /BigCard. Let lambda /in cof(kappa). Let lambda /neq /emptyset. Let X be a sequence of length lambda in Club(kappa). Then /bigcap X^[lambda] /in Club(kappa). 




[prove on]
