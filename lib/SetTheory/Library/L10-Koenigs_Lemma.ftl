[read Formalizations/Library/L09-Cofinality.ftl]

[prove off]

## Pretyped Variables

Let w,x,y,z,W,X,Y,Z stand for zfsets.
Let a,b,c,d,A,B,C,D,M stand for sets.
Let o,o1,o2 stand for objects.
Let alpha, beta, gamma, delta stand for ordinals.
Let f,g,h,F,G,H stand for zffunction.
Let kappa, lambda stand for cardinals.



## Cardinal Arithmetic

Lemma. Let kappa /in /Cd. Then 2 ^ kappa = Card(/PP kappa).

Lemma. Let x,y /in /VV. Let x /tilde y. Then /PP x /tilde /PP y.

Lemma. Let x /in /VV. Then Card(/PP x) = 2 ^ Card(x).

Lemma. Let kappa /in /Cd. Then kappa /in 2 ^ kappa.

Lemma. Let kappa /in /Cd. Then kappa * 1 = kappa.

Lemma ExpSubset. Let alpha, beta, gamma /in /Cd. Let beta /subset gamma. Let 0 /in alpha. Then alpha ^ beta /subset alpha ^ gamma.

Lemma BaseSubset. Let alpha, beta, gamma /in /Cd. Let alpha /subset beta. Then alpha ^ gamma /subset beta ^ gamma.

Lemma. Let kappa, lambda /in /Cd. Let 2 /subset kappa. Let /NN /subset lambda. Then /NN /subset kappa ^ lambda.

Lemma. Let kappa, lambda /in /Cd. Let 2 /subset kappa. Let /NN /subset lambda. Then kappa ^ lambda /in /Lim.


## Infinite sum and product

[synonym sequence/-s]

Signature. A sequence of cardinals is a notion.

Axiom. Let f be a sequence of cardinals. Then f is a zffunction.

Axiom. Let f be a zffunction. Then f is a sequence of cardinals iff Dom(f) /in /Ord /\ forall x /in Dom(f) f[x] /in /Cd.

Lemma. Let f be a zffunction. Let Dom(f) /in /Ord. Then exists g (Dom(g) = Dom(f) /\ forall i /in Dom(g) g[i] = Card(f[i])).

Definition. Let f be a zffunction. Let Dom(f) /in /Ord. The cardinalsequence of f is a zffunction g such that Dom(g) = Dom(f) /\ forall i /in Dom(g) g[i] = Card(f[i]).
Let cardseq(f) stand for the cardinalsequence of f.

Lemma. Let f be a zffunction. Let Dom(f) /in /Ord. Then cardseq(f) is a sequence of cardinals.


# Sum

Definition. Let f be a zffunction. The sumset of f is {(a,b) | b /in Dom(f) /\ a /in f[b]}.
Let /sumset f stand for the sumset of f.

Lemma. Let f be a zffunction. Let Dom(f) /in /VV. Then /sumset f /in /VV.

Lemma. Let f be a sequence of cardinals. Then /sumset f /in /VV.

Definition. Let f be a sequence of cardinals. The seqsum of f is
Card(/sumset f).
Let /sum f stand for the seqsum of f.

Lemma. Let f be a zffunction. Let Dom(f) /in /Ord. Then Card(/sumset f) = /sum cardseq(f).


# Product

Definition. Let f be a zffunction. Let Dom(f) /in /VV. The productset of f is 
{zffunction g | Dom(g) = Dom(f) /\ forall i /in Dom(g) g[i] /in f[i]}.
Let /prodset f stand for the productset of f.

Lemma. Let f be a zffunction. Let Dom(f) /in /VV. Then /prodset f /in /VV.

Lemma. Let f be a sequence of cardinals. Then /prodset f /in /VV.

Definition. Let f be a sequence of cardinals. The seqproduct of f is Card(/prodset f).
Let /prod f stand for the seqproduct of f.


## Koenigs Lemma

Theorem Koenig. Let kappa, lambda be sequences of cardinals. Let Dom(kappa) = Dom(lambda). Let forall i /in Dom(kappa) kappa[i] /in lambda[i].
Then /sum kappa /in /prod lambda.

Lemma. Let kappa, lambda /in /Cd. Let 2 /subset kappa. Let /NN /subset lambda. Then lambda /in cof(kappa ^ lambda).

Theorem HausdorffRecursion. Let alpha, beta /in /Ord. Then Alef[alpha +' 1] ^ Alef[beta] = (Alef[alpha] ^ Alef[beta]) * Alef[alpha +' 1].




[prove on]
