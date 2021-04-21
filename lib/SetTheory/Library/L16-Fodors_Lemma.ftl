[read Formalizations/Library/L15-Stationary_Sets.ftl]

[prove off]

## Pretyped Variables

Let w,x,y,z,W,X,Y,Z stand for zfsets.
Let a,b,c,d,A,B,C,D,M stand for sets.
Let o,o1,o2 stand for objects.
Let alpha, beta, gamma stand for ordinals.
Let f,g,h,F,G,H stand for zffunction.
Let kappa, lambda stand for cardinals.



## Prerequisites

Signature. A successor cardinal is a cardinal.

Signature. A limit cardinal is a cardinal.

Definition. Let kappa be a cardinal. kappa is infinite iff /NN /subset kappa.

Axiom. Let kappa be a cardinal. Then kappa is a successor cardinal iff exists alpha /in /Ord (kappa = Alef[alpha +' 1]).

Axiom. Let kappa be a cardinal. kappa is a limit cardinal iff exists lambda /in /Lim (kappa = Alef[lambda]).

Lemma. Let kappa be a successor cardinal. Then kappa /in /Lim.

Lemma. Let kappa be a limit cardinal. Then kappa /in /Lim.

Lemma. Let kappa be a successor cardinal. Then kappa is regular.

Lemma. Let f be an epsiso. Let alpha /in /Lim. Let alpha /subset Dom(f). Let ran(f) /subset /Ord. Then /bigcup f^[alpha] /in /Lim /\ cof(/bigcup f^[alpha]) = cof(alpha).


## Fodors Lemma

Definition. Let kappa /in /BigCard. The set of stationary subsets of kappa is
{C /subset kappa | C is stationary in kappa}.
Let stat(k) stand for the set of stationary subsets of k.

Definition. The set of regular uncountable cardinals is {kappa /in /BigCard | kappa is regular}.
Let /BigRegCard stand for the set of regular uncountable cardinals.

Definition. Let f be a zffunction. f is constant iff exists c /in /VV forall x /in Dom(f) f[x] = c.

Definition. Let f be a zffunction. Let Dom(f) /subset /Ord. f is regressive iff forall alpha /in Dom(f) /setminus <0> f[alpha] /in alpha.

Theorem Fodor. Let kappa /in /BigRegCard. Let f be a zffunction. Let Dom(f) /in stat(kappa). Let f be regressive.
Then exists i /in /Ord f^{-1}[[i]] /in stat(kappa).

Corollary Fodor2. Let kappa /in /BigRegCard. Let f be a zffunction. Let Dom(f) /in stat(kappa). Let f be regressive. 
Then exists T /subset Dom(f) (T /in stat(kappa) /\ (f /upharpoonright T is constant)).

Definition. Let kappa /in /BigCard. Let C /in Cl(kappa). The derivation of C in kappa is
{alpha /in kappa /cap /Lim | C /cap alpha /cof alpha}.
Let der(C,k) stand for the derivation of C in k.

Lemma. Let kappa /in /BigCard. Let C /in Cl(kappa). Then der(C,kappa) /subset C.

Lemma. Let kappa /in /BigCard. Let C /in Cl(kappa). Then der(C,kappa) /in Cl(kappa).

Lemma. Let kappa /in /BigCard. Let S /subset kappa. Let S be stationary in kappa. Then S /cap /Lim is stationary in kappa.

Lemma. Let kappa /in /BigCard. Let S /in stat(kappa). Then S /cap /Lim /in stat(kappa).

Definition. Let lambda, kappa /in /BigRegCard. Let lambda /in kappa. The subset of cofinality lambda in kappa is
{alpha /in kappa /cap /Lim | cof(alpha) = lambda}.
Let Estat(k,l) stand for the subset of cofinality l in k.

Lemma. Let lambda, kappa /in /BigRegCard. Let lambda /in kappa. Then Estat(kappa,lambda) is stationary in kappa.




[prove on]
