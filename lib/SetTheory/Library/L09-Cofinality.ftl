[read Formalizations/Library/L08-Cardinal_Arithmetic.ftl]

[prove off]

## Pretyped Variables

Let w,x,y,z,W,X,Y,Z stand for zfsets.
Let a,b,c,d,A,B,C,D,M stand for sets.
Let o,o1,o2 stand for objects.
Let alpha, beta, gamma, delta stand for ordinals.
Let f,g,h,F,G,H stand for zffunction.
Let kappa, lambda stand for cardinals.



# Cofinality

Definition. Let lambda /in /Lim. Let x /subset lambda. x is cofinal in lambda iff
forall alpha /in lambda exists y /in x alpha /in y.
Let x /cof y stand for x is cofinal in y.

Lemma. Let lambda /in /Lim. Forall x /subset lambda (x /cof lambda => Card(x) /notin /NN).

Signature. Let lambda /in /Lim. The cofinality of lambda is a notion.
Let cof(x) stand for the cofinality of x.

Definition. Let lambda /in /Lim. The cofset of lambda is {otp(x) | x /subset lambda /\ x /cof lambda}.
Let cofset(x) stand for the cofset of x.

Lemma. Let lambda /in /Lim. Then cofset(lambda) /subset /Ord.

Lemma. Let lambda /in /Lim. cofset(lambda) /neq /emptyset.

Axiom. Let lambda /in /Lim. Then cof(lambda) = min(cofset(lambda)).

Lemma. Let lambda /in /Lim. Then cof(lambda) /in /Ord.

Lemma. Let lambda /in /Lim. cof(lambda) /in cofset(lambda).

Lemma. Let lambda /in /Lim. Then cof(lambda) /subset lambda.

Definition. Let lambda /in /Lim. lambda is regular iff cof(lambda) = lambda.

Definition. Let lambda /in /Lim. lambda is singular iff cof(lambda) /neq lambda.

Lemma. Let lambda /in /Lim. Let lambda be singular. Then cof(lambda) /in lambda.

Definition. Let lambda /in /Lim. The alternativecofset of lambda is {Card(x) | (x is a zfset) /\ x /subset lambda /\ x /cof lambda}.
Let cofset2(x) stand for the alternativecofset of x.

Lemma. Let lambda /in /Lim. Then cofset2(lambda) /neq /emptyset.

Lemma. Let lambda /in /Lim. Then cof(lambda) = min(cofset2(lambda)).

Lemma. Let lambda /in /Lim. Then cof(lambda) = min(cofset2(lambda)).

Lemma. Let lambda /in /Lim. Then cof(lambda) /in cofset2(lambda).

Lemma. Forall lambda /in /Lim cof(lambda) /subset Card(lambda).

Lemma. Forall lambda /in /Lim /NN /subset cof(lambda).

Lemma. cof(/NN) = /NN.

Lemma. Forall lambda /in /Lim cof(lambda) /in /Card.

Lemma. Let lambda /in /Lim. Exists x (x /subset lambda /\ x /cof lambda /\ otp(x) = cof(lambda)).

Lemma. Let lambda /in /Lim. Exists x (x /subset lambda /\ x /cof lambda /\ Card(x) = cof(lambda)).

Lemma. Forall lambda /in /Lim (cof(lambda) is regular).

Lemma. Forall alpha /in /Ord Alef[alpha] /in /Lim.

Lemma. Let alpha /in /Lim. Then cof(Alef[alpha]) = cof(alpha).

Lemma. cof(Alef[/NN]) = /NN.

Lemma exsurj. Let x be a zfset. Let x /neq /emptyset. Let alpha /in /Ord. Let Card(x) /subset alpha. Then exists f (f : alpha /rightarrow x /\ ran(f) = x).

Lemma. Forall alpha /in /Ord cof(Alef[alpha +' 1]) = Alef[alpha +' 1].

Lemma. Forall alpha /in /Succ (Alef[alpha] is regular).




[prove on]
