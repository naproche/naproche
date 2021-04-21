[read Formalizations/Library/L07-Cardinals_Part_2.ftl]

[prove off]

## Pretyped Variables

Let w,x,y,z,W,X,Y,Z stand for zfsets.
Let a,b,c,d,A,B,C,D,M stand for sets.
Let o,o1,o2 stand for objects.
Let alpha, beta, gamma, delta stand for ordinals.
Let f,g,h,F,G,H stand for zffunction.
Let kappa, lambda stand for cardinals.


## Cardinal Arithmetic

Axiom. Let f be a zffunction. Let Dom(f) /in /VV. Then f is a zfset.

Lemma. Let A,B /in /VV. Then ^{A}B /in /VV.

Lemma. Forall x1,x2,y1,y2 /in /VV ( x1 /tilde x2 /\ y1 /tilde y2 => ^{x1}y1 /tilde ^{x2}y2 ).

Signature. kappa + lambda is a cardinal.
Signature. kappa * lambda is a cardinal.
Signature. kappa ^ lambda is a cardinal.

Definition. Let kappa, lambda /in /Cd. Let x,y /in /VV. (kappa,lambda) IsAdditionCompatibleWith (x,y) iff (Card(x) = kappa /\ Card(y) = lambda /\ x /cap y = /emptyset).
Let (a,b) /sim (x, y) stand for (a,b) IsAdditionCompatibleWith (x, y).

Axiom. Let kappa, lambda /in /Cd. Let x,y /in /VV. Let (kappa,lambda) /sim (x, y).
Then kappa + lambda = Card(x /cup y).

Axiom. Let kappa, lambda /in /Cd. Then kappa * lambda = Card(kappa /times lambda).

Axiom. Let kappa, lambda /in /Cd. Then kappa ^ lambda = Card(^{lambda}kappa).

Lemma. Forall kappa, lambda /in /Cd exists x,y ((kappa,lambda) /sim (x,y)).


## Algebraic rules for Sum and Product

Lemma. Forall kappa, lambda /in /Cd (kappa + lambda = lambda + kappa).

Lemma. Forall kappa, lambda /in /Cd (kappa * lambda = lambda * kappa).

Lemma. Let alpha, beta /in /Cd. Let x be a zfset. Let Card(x) = alpha. Then exists y (alpha,beta) /sim (x,y).

Lemma. Forall alpha, beta, gamma /in /Cd ((alpha + beta) + gamma = alpha + (beta + gamma)).


## Basic Facts

Lemma. Forall kappa, lambda /in /Cd (kappa /subset kappa + lambda).

Lemma. Forall kappa /in /Cd (kappa ^ 0 = 1).

Lemma. Forall kappa /in /Cd (kappa /neq 0 => 0 ^ kappa = 0).

Lemma. Forall kappa /in /Cd (1 ^ kappa = 1).


## Cardinal = Ordinal Arithmetic for finite sets.

Lemma. Forall n /in /NN (n +' 1 = n + 1).

Lemma. Forall alpha /in /Cd (alpha + 0 = alpha).

Lemma. Forall alpha, beta /in /NN (alpha +' beta = alpha + beta).

Lemma. Forall alpha, beta /in /NN (alpha *' beta = alpha * beta).

Lemma. Forall alpha, beta /in /NN (alpha ^' beta = alpha ^ beta).


## Calculation Rules

Lemma. Let alpha, beta, gamma /in /Cd. Then alpha * (beta + gamma) = (alpha * beta) + (alpha * gamma).

Lemma. Let alpha, beta, gamma /in /Cd. Then (alpha ^ (beta + gamma) = (alpha ^ beta) * (alpha ^ gamma)).


# Partially applied functions

Signature. Let A,B be sets. Let F be a zffunction. Let Dom(F) = A /times B. Let a /in A. F{A,B}(a,-) is a function.
Axiom. Let A,B be sets. Let F be a zffunction. Let Dom(F) = A /times B. Let a /in A. Then Dom(F{A,B}(a,-)) = B.
Axiom. Let A,B be sets. Let F be a zffunction. Let Dom(F) = A /times B. Let a /in A. Then forall b /in B (F{A,B}(a,-))[b] = F[(a,b)].
Lemma. Let A,B be sets. Let F be a zffunction. Let Dom(F) = A /times B. Let a /in A. Then F{A,B}(a,-) is a zffunction.

Signature. Let A,B be sets. Let F be a zffunction. Let Dom(F) = A /times B. Let b /in B. F{A,B}(-,b) is a function.
Axiom. Let A,B be sets. Let F be a zffunction. Let Dom(F) = A /times B. Let b /in B. Then Dom(F{A,B}(-,b)) = A.
Axiom. Let A,B be sets. Let F be a zffunction. Let Dom(F) = A /times B. Let b /in B. Then forall a /in A (F{A,B}(-,b))[a] = F[(a,b)].
Lemma. Let A,B be sets. Let F be a zffunction. Let Dom(F) = A /times B. Let b /in B. Then F{A,B}(-,b) is a zffunction.

Lemma. Let A,B be sets. Let F be a zffunction. Let Dom(F) = A /times B. Let a /in A. Then ran(F{A,B}(a,-)) /subset ran(F).
Lemma. Let A,B be sets. Let F be a zffunction. Let Dom(F) = A /times B. Let b /in B. Then ran(F{A,B}(-,b)) /subset ran(F).

Definition. Let alpha, beta, gamma /in /VV. Let f /in ^{beta /times gamma}alpha. Let F be a zffunction.
F /partial (f,alpha,beta,gamma) iff (Dom(F) = gamma /\ forall b /in gamma F[b] = f{beta,gamma}(-,b)).

Lemma. Let alpha, beta, gamma /in /VV. Let f /in ^{beta /times gamma}alpha. Let F be a zffunction. Let F /partial (f,alpha,beta,gamma).
Then F /in ^{gamma}(^{beta}alpha).

Lemma partial. Let alpha, beta, gamma /in /VV. Let f /in ^{beta /times gamma}alpha. Let F be a zffunction. Let F /partial (f,alpha,beta,gamma).
Forall a /in beta forall b /in gamma (F[b])[a] = f[(a,b)].

Lemma. Let alpha, beta, gamma /in /Cd. Then (alpha ^ (beta * gamma) = (alpha ^ beta) ^ gamma).

Lemma. Forall kappa /in /Card (kappa * kappa = kappa).

Lemma. Let kappa /in /Card. Let lambda /in /Cd. Let lambda /neq 0. Then kappa * lambda = kappa /cup lambda.

Lemma. Let kappa /in /Card. Let lambda /in /Cd. Then kappa + lambda = kappa /cup lambda.

Lemma. Forall n /in /NN forall kappa /in /Card (n /neq 0 => kappa ^ n = kappa).

Lemma ExpEq. Let kappa /in /Card. Let lambda /in /Cd. Let 2 /subset lambda. Let lambda /subset (2 ^ kappa).
Then lambda ^ kappa = 2 ^ kappa.




[prove on]
