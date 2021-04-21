[read Formalizations/Library/L17-Disjoint_Stationary_Subsets.ftl]

[prove off]

## Pretyped Variables

Let w,x,y,z,W,X,Y,Z stand for zfsets.
Let a,b,c,d,A,B,C,D,M stand for sets.
Let o,o1,o2 stand for objects.
Let alpha, beta, gamma stand for ordinals.
Let f,g,h,F,G,H stand for zffunction.
Let kappa, lambda stand for cardinals.




## Almost disjoint functions

Definition. Let lambda /in /Lim. Let f,g be zffunctions. Let f,g /in ^{lambda}/VV. f and g are almost disjoint on lambda iff
exists alpha /in lambda forall beta /in lambda (alpha /in beta => f[beta] /neq g[beta]).

Signature. Let lambda /in /Lim. An almost disjoint family of functions on lambda is a notion.

Axiom. Let lambda /in /Lim. Let F be an almost disjoint family of functions on lambda. Then F /subset ^{lambda}/VV.

Lemma. Let lambda /in /Lim. Let F be an almost disjoint family of functions on lambda. Let f /in F. Then f is a zffunctions and f /in ^{lambda}/VV.

Axiom adfam. Let lambda /in /Lim. Let F be an almost disjoint family of functions on lambda. Then forall f,g /in F (f /neq g => (f and g are almost disjoint on lambda)).

Signature. An adfampair is a notion.

Axiom adfampair. Let a,b be objects. (a,b) is an adfampair iff b /in /Lim /\ a /subset ^{b}/VV.

Lemma. Let lambda /in /Lim. Let F be an almost disjoint family of functions on lambda. Then (F,lambda) is an adfampair.

Lemma. Let lambda, F be objects. Let (F,lambda) be an adfampair. Then forall f /in F (f is a zffunctions and f /in ^{lambda}/VV).

Axiom adfam2. Let lambda, F be objects. Let (F,lambda) be an adfampair. Let forall f,g /in F (f /neq g => (f and g are almost disjoint on lambda)).
Then F is an almost disjoint family of functions on lambda.

Lemma. Let lambda /in /Ord. Let A be a zffunction. Let Dom(A) = lambda. Let F /subset /prodset A. Then F /subset ^{lambda}/VV.

Definition. The class of singular cardinals of uncountable cofinality is
{kappa /in /BigCard | kappa is singular}.
Let /BigSingCard stand for the class of singular cardinals of uncountable cofinality.

Lemma. Let kappa /in /BigSingCard. Then exists alpha /in /Lim (kappa = Alef[alpha]).


## New notions to store information

Lemma. Let kappa /in /Lim. Then exists x /subset kappa (otp(x) = cof(kappa) /\ x /club  kappa).

Signature. A cofpair is a notion.

Axiom. Let kappa, x be objects. (kappa,x) is a cofpair iff kappa /in /BigSingCard /\ x /subset kappa /cap /Card /\ otp(x) = cof(kappa) /\ x /club kappa.

Lemma. Let kappa /in /BigSingCard. Then exists x ((kappa,x) is a cofpair).

Definition. Let f be an epsiso. Let Dom(f) /in /Ord \/ Dom(f) = /Ord. f is continuous iff forall lambda /in Dom(f) /cap /Lim (f[lambda] = /bigcup f^[lambda]).

Lemma clubcont. Let kappa /in /Lim. Let x /subset kappa. Let x /club kappa. Let f be an epsiso. Let f : otp(x) /leftrightarrow x. Then Dom(f) /in /Ord and f is continuous.

Signature. A coftriple is a notion.

Axiom. Let kappa, x, f be objects. (kappa,x,f) is a coftriple iff ((kappa,x) is a cofpair) /\ (f is an epsiso) /\ f : cof(kappa) /leftrightarrow x.

Lemma. Let kappa,x be objects. Let (kappa,x) be a cofpair. Then exists f ((kappa,x,f) is a coftriple).

Lemma. Let kappa,x,f be objects. Let (kappa,x,f) be a coftriple. Then f is a sequence of cardinals and Dom(f) = cof(kappa).

Lemma. Let kappa,x,f be objects. Let (kappa,x,f) be a coftriple. Then Dom(f) /in /Ord and f is continuous.

Lemma. Let kappa /in /BigSingCard. Then cof(kappa) /in /BigRegCard.

Definition. Let kappa,x,kap be objects. Let (kappa,x,kap) be a coftriple. Let A be a zffunction. Let Dom(A) = cof(kappa). The cofsupport of A relative to kap and kappa and x is
{alpha /in Dom(A) | kap[alpha] /in /VV /\ Card(A[alpha]) /subset kap[alpha]}.
Let CofSupp(k,x,f){g} stand for the cofsupport of g relative to f and k and x.

Definition. Let kappa,x,kap be objects. Let (kappa,x,kap) be a coftriple. Let A be a zffunction. A is compatible with kap relative to kappa and x iff
Dom(A) = cof(kappa) /\ CofSupp(kappa,x,kap){A} /in stat(cof(kappa)).

Definition. Let A be a zffunction. Let Dom(A) /in /Lim. Let F be an object. F is almost disjoint relative to A iff
F /subset /prodset A /\ (F is an almost disjoint family of functions on Dom(A)).

Lemma. Let A be a zffunction. Let Dom(A) /in /Lim. Let F be an object. Let F be almost disjoint relative to A. Then F /in /VV.


## New Cardinal Axioms

Signature. Let kappa /in /BigSingCard. Silver below kappa is an atom.

Axiom. Let kappa /in /BigSingCard. Silver below kappa iff forall lambda /in kappa /cap /Cd (lambda ^ cof(kappa) /in kappa).

Signature. Let kappa /in /BigSingCard. GCH below kappa is an atom.

Axiom. Let kappa /in /BigSingCard. GCH below kappa iff forall lambda /in kappa /cap /Card 2 ^ lambda = Plus[lambda].

Lemma. Let kappa /in /BigSingCard. Let GCH below kappa. Then Silver below kappa.


## The First Helping Lemma

Lemma Silver1. Let kappa, x, kap, F be objects. Let (kappa,x,kap) be a coftriple. Let Silver below kappa. Let A be a zffunction. Let A be compatible with kap relative to kappa and x.
Let F be almost disjoint relative to A. Then Card(F) /subset kappa.




[prove on]

