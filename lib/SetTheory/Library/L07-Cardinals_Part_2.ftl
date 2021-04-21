[read Formalizations/Library/L05-Mostowski_Collapse.ftl]

[prove off]

## Pretyped Variables

Let w,x,y,z,W,X,Y,Z stand for zfsets.
Let a,b,c,d,A,B,C,D,M stand for sets.
Let o,o1,o2 stand for objects.
Let alpha, beta, gamma, delta stand for ordinals.
Let f,g,h,F,G,H stand for zffunction.
Let kappa, lambda stand for cardinals.


## Cartesian Product

Lemma. Forall a,b /in /NN ((a /times b is a zfset) and (Card(a /times b) = a *' b)).

Lemma. Let a1,a2,b1,b2 be zfsets. Let Card(a1) = Card(a2) /\ Card(b1) = Card(b2). Then (a1 /times b1) /tilde (a2 /times b2).

Lemma. Let a,b be zfsets. Let a, b be finite. Then (a /times b is a zfset) and (a /times b is finite).


# Goedel Ordering

Definition. Let a1,a2,b1,b2 /in /Ord. (a1,b1) isgoedelsmallerthan (a2,b2) iff
(a1 /cup b1 /in a2 /cup b2) \/ (a1 /cup b1 = a2 /cup b2 /\ a1 /in a2)
\/ (a1 /cup b1 = a2 /cup b2 /\ a1 = a2 /\ b1 /in b2).
Let (a, b) <3 (c,d) stand for (a,b) isgoedelsmallerthan (c,d).

Signature. goedel is an object.

Axiom. goedel is a relation.

Axiom. relfield(goedel) = /Ord /times /Ord.

Axiom goedel. Forall a,b,c,d /in /Ord ( (a, b) - goedel - (c,d) iff (a, b) <3 (c,d)).

Lemma. goedel is a strict linear order.

Lemma. Forall alpha, beta (alpha /cup beta /in /Ord).

Lemma. reldomain(goedel) = /Ord /times /Ord.

Lemma. goedel is wellfounded.

Lemma. goedel is a strong wellorder.

Lemma. reldomain(goedel) is a proper class.

Lemma. MCol goedel : /Ord /times /Ord /leftrightarrow /Ord.

Signature. Goed is a function.

Axiom. Goed = MCol goedel.

Lemma. Goed is a zffunction.

Lemma. Goed : /Ord /times /Ord /leftrightarrow /Ord.

Lemma. Let a1,a2,b1,b2 /in /Ord. Then (a1,b1),(a2,b2) /in /Ord /times /Ord /\ Goed[(a1,b1)], Goed[(a2,b2)] /in /Ord.

Lemma. Let a1,a2,b1,b2 /in /Ord. Let (a1,b1) <3 (a2,b2). 
Then (a1,b1),(a2,b2) /in Dom(Goed) /\ Goed[(a1,b1)], Goed[(a2,b2)] /in /Ord /\ Goed[(a1,b1)] /in Goed[(a2,b2)].


# The Inverse of the Goedel Pairing

Lemma. Goed^{-1} : /Ord /leftrightarrow /Ord /times /Ord.

Signature. pr1 is a function.

Axiom. pr1 : /VV /times /VV /rightarrow /VV.

Lemma. Dom(pr1) = /VV /times /VV.

Lemma. Forall x,y /in /VV (x,y) /in Dom(pr1).

Axiom. Forall x,y /in /VV pr1[(x,y)] = x.

Signature. pr2 is a function.

Axiom. pr2 : /VV /times /VV /rightarrow /VV.

Lemma. Dom(pr2) = /VV /times /VV.

Lemma. Forall x,y /in /VV (x,y) /in Dom(pr2).

Axiom. Forall x,y /in /VV pr2[(x,y)] = y.

Signature. Goed1 is a function.

Lemma. /Ord /times /Ord /subset /VV /times /VV.

Axiom. Goed1 = pr1 /circ Goed^{-1}.

Signature. Goed2 is a function.

Axiom. Goed2 = pr2 /circ Goed^{-1}.

Lemma. Goed1 : /Ord /rightarrow /Ord.

Lemma. Goed2 : /Ord /rightarrow /Ord.

Lemma. Forall alpha /in /Ord (Goed1[alpha],Goed2[alpha]) /in /Ord /times /Ord.

Lemma. Forall alpha /in /Ord  Goed[(Goed1[alpha],Goed2[alpha])] = alpha.

Lemma. Forall alpha /in /Ord (sset(goedel,(0,alpha)) = alpha /times alpha).

Lemma. Forall alpha /in /Ord ((0,alpha) /in /Ord /times /Ord /\ sset(goedel,(0,alpha)) /subset Dom(Goed)  /\
Goed /upharpoonright sset(goedel,(0,alpha)) : sset(goedel,(0,alpha)) /leftrightarrow Goed[(0,alpha)]).

Lemma. Forall alpha /in /Ord (alpha /times alpha, Goed[(0,alpha)] /in /VV /\ alpha /times alpha /tilde Goed[(0,alpha)]).

Lemma. Goed[(0,/NN)] = /NN.

Lemma. Forall alpha /in /Ord (Goed[(0,Alef[alpha])] = Alef[alpha]).

Lemma. Forall alpha /in /Ord (Alef[alpha] /tilde Alef[alpha] /times Alef[alpha]).

Lemma. Forall kappa /in /Card (kappa /tilde kappa /times kappa).

Lemma. Forall x /in /VV (Card(x) /notin /NN => x /tilde x /times x).



[prove on]
