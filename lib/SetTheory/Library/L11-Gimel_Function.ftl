[read Formalizations/Library/L10-Koenigs_Lemma.ftl]

[prove off]

## Pretyped Variables

Let w,x,y,z,W,X,Y,Z stand for zfsets.
Let a,b,c,d,A,B,C,D,M stand for sets.
Let o,o1,o2 stand for objects.
Let alpha, beta, gamma, delta stand for ordinals.
Let f,g,h,F,G,H stand for zffunction.
Let kappa, lambda stand for cardinals.




## Beths

Signature. Beth is a function.
Axiom. Dom(Beth) = /Ord.
Axiom. Forall alpha /in /Ord Beth[alpha] /in /Cd.
Lemma. Beth is a zffunction.
Axiom. Beth[/emptyset] = /NN.
Axiom. Let alpha /in /Succ. Let beta /in /Ord. Let alpha = beta +' 1. Then Beth[beta] /in /Cd /\ Beth[alpha] = 2 ^ Beth[beta].
Axiom. Let alpha /in /Lim. Then Beth[alpha] = {zfset x | exists beta /in alpha x /in Beth[beta]}.

Lemma. Forall lambda /in /Lim Beth[lambda] = /bigcup Beth^[lambda].

Lemma. Forall alpha /in /Ord /NN /subset Beth[alpha].

Lemma. Forall alpha /in /Ord forall beta /in alpha (Beth[beta] /in Beth[alpha]).

Lemma. Forall alpha, beta /in /Ord (alpha /in beta iff Beth[alpha] /in Beth[beta]).

Lemma. Forall alpha, beta /in /Ord (alpha /subset beta iff Beth[alpha] /subset Beth[beta]).

Lemma. Beth is injective.

Signature. An inaccessible cardinal is a notion.
Axiom. Let kappa be an inaccessible cardinal. Then kappa is a cardinal.
Axiom. Let kappa be a cardinal. Then kappa is an inaccessible cardinal iff 
kappa = Alef[kappa] /\ cof(kappa) = kappa.

Signature. A strongly inaccessible cardinal is a notion.
Axiom. Let kappa be an inaccessible cardinal. Then kappa is a cardinal.
Axiom. Let kappa be a cardinal. Then kappa is an inaccessible cardinal iff 
kappa = Beth[kappa] /\ cof(kappa) = kappa.


## Gimel Function

Signature. Gimel is a function.

Axiom. Dom(Gimel) = /Card.

Axiom. Forall kappa /in /Card Gimel[kappa] = kappa ^ cof(kappa).

Lemma. Let kappa /in /Card. Then kappa ^ cof(kappa) /in /Card.

Lemma. Gimel : /Card /rightarrow /Card.

Signature. Let kappa /in /Cd. Let lambda /in /Card. kappa ^< lambda is a set.

Axiom. Let kappa /in /Cd. Let lambda /in /Card. kappa ^< lambda = {zfset x | exists v /in lambda x /in kappa ^ Card(v)}.

Signature. Exp is a function.

Axiom. Dom(Exp) = /Cd /times /Ord.

Lemma. Forall o1,o2 ((o1,o2) /in /Cd /times /Ord => o1 /in /Cd /\ o2 /in /Ord).

Axiom. Let a,b be objects. Let (a,b) /in /Cd /times /Ord. Then Exp[(a,b)] = a ^ Card(b).

Lemma. Exp : /Cd /times /Ord /rightarrow /Cd.

Lemma. Let kappa /in /Cd. Then Exp{/Cd,/Ord}(kappa,-) : /Ord /rightarrow /Cd.

Signature. Let kappa /in /Cd. Cont(kappa) is a function.

Axiom. Let kappa /in /Cd. Dom(Cont(kappa)) = /Ord.

Axiom. Let kappa /in /Cd. Let alpha /in /Ord. Then (Cont(kappa))[alpha] = kappa ^ Card(alpha).

Lemma. Let kappa /in /Cd. Cont(kappa) : /Ord /rightarrow /Cd.

Lemma. Let kappa /in /Cd. Let lambda /in /Card. kappa ^< lambda = /bigcup (Cont(kappa))^[lambda].

Lemma. Let kappa /in /Cd. Let lambda /in /Card. Then kappa ^< lambda /in /Cd.

Lemma. Let kappa /in /Card. Then 2 ^< kappa /in /Card.

Lemma. Forall kappa /in /Card (Gimel[kappa] /in /Card /\ kappa /in Gimel[kappa]).

Lemma. Let kappa /in /Card. Let cof(kappa) = kappa. Then Gimel[kappa] = 2 ^ kappa.

Lemma. Let kappa /in /Card. Let cof(kappa) /in kappa. Then 2 ^ kappa /subset (2 ^< kappa) ^ cof(kappa).

Lemma. Let kappa /in /Card. Let cof(kappa) /in kappa. Let (exists kappap /in /Card /cap kappa forall lambda /in /Card
(kappap /subset lambda /\ lambda /in kappa => 2 ^ kappap = 2 ^ lambda)). Then 2 ^ kappa = 2 ^< kappa.

Lemma. Let kappa /in /Card. Let cof(kappa) /in kappa. Let (forall kappap /in /Cd /cap kappa exists lambda /in /Cd /cap kappa
(kappap /in lambda /\ 2 ^ kappap /in 2 ^ lambda)). Then 2 ^ kappa = Gimel[2 ^< kappa].




[prove on]
