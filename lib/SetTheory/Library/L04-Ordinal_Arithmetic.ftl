[read Formalizations/Library/L03-Von_Neumann_Hierarchy.ftl]

[prove off]

## Pretyped Variables

Let w,x,y,z,W,X,Y,Z stand for zfsets.
Let a,b,c,d,A,B,C,D,M stand for sets.
Let o,o1,o2 stand for objects.
Let alpha, beta, gamma, delta stand for ordinals.
Let k,l,m,n stand for natural numbers.
Let f,g,h,F,G,H stand for zffunction.
Let kappa, lambda stand for cardinals.


## Ordinal Arithmetic

Signature. alpha +' beta is an ordinal.
Signature. alpha *' beta is an ordinal.
Signature. alpha ^' beta is an ordinal.


## Addition

Axiom. Let alpha be an ordinal. Then alpha +' 0 = alpha.

Axiom. Let alpha, beta be ordinals. Let beta /in /Succ. Then alpha +' beta = (alpha +' beta--)++.

Lemma. Let alpha, beta be ordinals. Then alpha +' (beta++) = (alpha +' beta) +' 1.

Axiom AddLim. Let alpha, beta be ordinals. Let beta /in /Lim. 
Then alpha +' beta = {zfset x | exists gamma /in beta (x /in (alpha +' gamma))}.

Lemma. Forall alpha (alpha +' 1 = alpha++).

Lemma. Forall alpha ((alpha +' 1)-- = alpha).

Lemma. Forall alpha /in /Ord (0 +' alpha = alpha).

Lemma Add1. Forall alpha, beta, gamma /in /Ord (beta /in gamma => alpha +' beta /in alpha +' gamma).

Lemma. Forall alpha, beta /in /Ord (alpha /subset alpha +' beta).

Lemma. Forall alpha, beta /in /Ord (beta /subset alpha +' beta).

Lemma. Let alpha, beta be ordinals. Let beta /in /Lim. Then alpha +' beta /in /Lim.


## Multiplication

Axiom. Let alpha be an ordinal. Then alpha *' 0 = 0.

Axiom. Let alpha, beta be ordinals. Let beta /in /Succ. Then alpha *' beta = (alpha *' beta--) +' alpha.

Lemma. Let alpha, beta be ordinals. Then alpha *' (beta +' 1) = (alpha *' beta) +' alpha.

Axiom MultLim. Let alpha, beta be ordinals. Let beta /in /Lim. Then alpha *' beta = {zfset x | exists gamma /in beta (x /in alpha *' gamma)}.

Lemma. Forall alpha /in /Ord (alpha *' 1 = alpha).

Lemma. Forall alpha /in /Ord (0 *' alpha = 0).

Lemma. Forall alpha /in /Ord (1 *' alpha = alpha).

Lemma. Forall alpha, beta /in /Ord (beta /neq /emptyset => alpha /subset alpha *' beta).

Lemma. Forall alpha, beta /in /Ord (beta /neq 0 => alpha +' 1 /subset alpha +' beta).

Lemma. Forall alpha, beta /in /Ord (alpha /neq 0 => beta /subset alpha *' beta).


## Exponentiation

Axiom. Let alpha be an ordinal. Then alpha ^' 0 = 1.

Axiom. Let alpha, beta be ordinals. Let beta /in /Succ. Then alpha ^' beta = (alpha ^' beta--) *' alpha.

Lemma. Let alpha, beta be ordinals. Then alpha ^' (beta +' 1) = (alpha ^' beta) *' alpha.

Axiom ExpLim. Let alpha, beta be ordinals. Let beta /in /Lim. Then alpha +' beta = {zfset x | exists gamma /in beta (x /in alpha ^' gamma)}.

Lemma. Forall alpha /in /Ord alpha ^' 1 = alpha.


## Finite Arithmetic

Lemma AddFin. Forall m,n /in /NN forall x /in (m +' n) (x /in m \/ exists i /in n x = m +' i).

Lemma. Forall m,n /in /NN m+'n /in /NN.

Lemma. Forall m,n /in /NN m*'n /in /NN.

Lemma. Forall m,n /in /NN m^'n /in /NN.


## Finite Sets

Definition. Let x be a zfset. x is finite iff Card(x) /in /NN.

Lemma. Let x,y be zfsets. Let x be finite. Let y /subset x. Then y is finite.

Lemma. Let x,y be zfsets. Let x,y be finite. Then x /cup y is finite.

Lemma. Let a,b be zfsets. Let a,b be finite. Then (a /cap b is a zfset) and (a /cap b is finite).


## Alefs

Lemma. Let kappa be a cardinal. Let /NN /subset kappa. Then kappa /in /Lim.

Lemma. Forall kappa /in /Card kappa /in /Lim.

Signature. PlusCard(alpha) is a set.

Axiom. Let alpha /in /Ord. PlusCard(alpha) = {cardinal kappa | alpha /in kappa}.

Lemma. Forall alpha PlusCard(alpha) /neq /emptyset.

Signature. Plus is a function.

Axiom. Dom(Plus) = /Ord.

Axiom. Let alpha /in /Ord. Plus[alpha] = min(PlusCard(alpha)).

Lemma. Forall alpha /in /Ord Plus[alpha] /in PlusCard(alpha).

Lemma. Forall alpha /in /Ord Plus[alpha] /in /Cd.

Lemma. Forall alpha /in /Ord alpha /in Plus[alpha].

Lemma. Forall alpha forall kappa /in /Cd (alpha /in kappa => Plus[alpha] /subset kappa).

Lemma. Plus : /Ord /rightarrow /Cd.

Lemma. Let n /in /NN. Then Plus[n] = n+'1.

Signature. Alef is a function.
Axiom. Dom(Alef) = /Ord.
Axiom. Forall alpha /in /Ord Alef[alpha] /in /Ord.
Lemma. Alef is a zffunction.
Axiom. Alef[/emptyset] = /NN.
Axiom. Let alpha /in /Succ. Let beta /in /Ord. Let alpha = beta +' 1. Then Alef[beta] /in /Ord /\ Alef[alpha] = Plus[Alef[beta]].
Axiom. Let alpha /in /Lim. Then Alef[alpha] = /bigcup Alef^[alpha].

Lemma. Let x /in /VV. Let x /subset /Cd. Then Card(/bigcup x) = /bigcup x.

Lemma. Let x /in /VV. Let x /subset /Cd. Then (/bigcup x) /in /Cd.

Lemma. Forall alpha /in /Ord Alef[alpha] /in /Cd.

Lemma. Forall alpha /in /Ord forall beta /in alpha (Alef[beta] /in Alef[alpha]).

Lemma AlefIn. Forall alpha, beta /in /Ord (alpha /in beta iff Alef[alpha] /in Alef[beta]).

Lemma AlefSubset. Forall alpha, beta /in /Ord (beta /subset alpha iff Alef[beta] /subset Alef[alpha]).

Lemma. Alef is injective.

Lemma. Alef : /Ord /rightarrow /Card.

Lemma. Forall alpha /in /Ord (alpha /subset Alef[alpha]).

Lemma. Let kappa /in /Card. Then exists alpha (kappa = Alef[alpha]).

Lemma. ran(Alef) /subset Dom(Alef).

Lemma. Exists kappa (kappa = Alef[kappa]).




[prove on]
