[read Formalizations/Library/L09-Cofinality.ftl]

## Pretyped Variables

Let w,x,y,z,W,X,Y,Z stand for zfsets.
Let a,b,c,d,A,B,C,D,M stand for sets.
Let o,o1,o2 stand for objects.
Let alpha, beta, gamma, delta stand for ordinals.
Let f,g,h,F,G,H stand for zffunction.
Let kappa, lambda stand for cardinals.




## Cardinal Arithmetic

Lemma. Let kappa /in /Cd. Then 2 ^ kappa = Card(/PP kappa).
Proof.
  Forall phi /in ^{kappa}2 forall x /in kappa (x /in Dom(phi)).
  Define f[phi] = {zfset x | x /in kappa /\ phi[x] = 1} for phi in ^{kappa}2.
  Then f : ^{kappa}2 /rightarrow /PP kappa.
  Proof.
    Let phi /in ^{kappa}2. Then f[phi] /subset kappa.
    Then f[phi] /in /PP kappa.
  end.
  f is injective.
  Proof.
    Let phi1, phi2 /in ^{kappa}2. Let phi1 /neq phi2.
    Then exists x /in kappa phi1[x] /neq phi2[x].
    Proof by contradiction. Assume the contrary.
      phi1, phi2 are functions.
      Dom(phi1) = Dom(phi2).
      Forall x /in Dom(phi1) phi1[x] = phi2[x].
      Then phi1 = phi2.
      Contradiction.
    end.
    Take a zfset x such that x /in kappa /\ phi1[x] /neq phi2[x].
    phi1[x], phi2[x] /in 2.
    Proof.
      phi1 : kappa /rightarrow 2.
      phi2 : kappa /rightarrow 2.
    end.
    Then (phi1[x] = 0 /\ phi2[x] = 1) \/ (phi1[x] = 1 /\ phi2[x] = 0).
    Then f[phi1] /neq f[phi2].
    Proof.
      Case phi1[x] = 0 /\ phi2[x] = 1. Then x /in f[phi2] /\ x /notin f[phi1]. end.
      Case phi2[x] = 0 /\ phi1[x] = 1. Then x /in f[phi1] /\ x /notin f[phi2]. end.
    end.
  end.
  ran(f) = /PP kappa.
  Proof.
    Let x /in /PP kappa.
    Define phi[n] =
      Case n /in x -> 1,
      Case n /notin x -> 0
    for n in kappa.
    Then phi : kappa /rightarrow 2.
    Proof.
      Let n /in kappa. Then phi[n] /in 2.
    end.
    f[phi] /subset x.
    x /subset f[phi].
    Then f[phi] = x.
    Then x /in ran(f).
  end.
  f : ^{kappa}2 /leftrightarrow /PP kappa.
qed.


Lemma. Let x,y /in /VV. Let x /tilde y. Then /PP x /tilde /PP y.
Proof.
  Take a zffunction f such that f : x /leftrightarrow y.
  Define g[M] = f^[M] for M in /PP x.
  Then g : /PP x /rightarrow /PP y.
  Proof.
    Let M /in /PP x.
    Then M /in /VV /\ M /subset x.
    Then f^[M] /in /VV /\ f^[M] /subset y.
    Then g[M] /in /PP y.
  end.
  g is injective.
  Proof.
    Let M1, M2 /in /PP x. Let M1 /neq M2.
    Then exists z (z /in M1 /setminus M2 \/ z /in M2 /setminus M1).
    Proof.
      Then (not (M1 /subset M2)) \/ (not (M2 /subset M1)).
      Proof by contradiction. Assume the contrary.
        Then M1 /subset M2 /\ M2 /subset M1.
        Then M1 = M2.
        Contradiction.
      end.
    end.
    Take a zfset z such that (z /in M1 /setminus M2 \/ z /in M2 /setminus M1).
    g[M1] /neq g[M2].
    Proof.
      Case z /in M1 /setminus M2.
        z /in x.
        f[z] /in g[M1].
        f[z] /notin g[M2].
      end.
      Case z /in M2 /setminus M1.
        z /in x.
        f[z] /in g[M2].
        f[z] /notin g[M1].
      end.
    end. 
  end.
  ran(g) = /PP y.
  Proof.
    Let N /in /PP y.
    N /subset y.
    Let M = (f^{-1})^[N].
    f^{-1} : y /leftrightarrow x.
    Then M /subset x.
    Proof.
      Let i /in N.
      Then i /in y.
      Then (f^{-1})[i] /in x.
    end.
    f^[M] /subset N.
    Proof.
      Let z /in f^[M].
      Take a zfset m such that m /in M /\ z = f[m].
      Take a zfset n such that n /in N /\ (f^{-1})[n] = m.
      Then f[m] = n.
      Then z /in N.
    end.
    N /subset f^[M].
    Proof.
      Let n /in N.
      Take a zfset m such that m /in M /\ m = (f^{-1})[n].
      Then f[m] = n.
      Then n /in f^[M].
    end.
    Then f^[M] = N.
    Then g[M] = N.
    Then N /in ran(g).
  end.
  Then g : /PP x /leftrightarrow /PP y.
qed.


Lemma. Let x /in /VV. Then Card(/PP x) = 2 ^ Card(x).
Proof.
  Take a cardinal kappa such that kappa = Card(x).
  kappa, x /in /VV.
  kappa /tilde x.
  Then /PP x /tilde /PP kappa.
  Then Card(/PP x) = Card(/PP kappa).
  Card(/PP kappa) = 2 ^ kappa.
qed.


Lemma. Let kappa /in /Cd. Then kappa /in 2 ^ kappa.
Proof.
  2 ^ kappa = Card(/PP kappa).
  kappa < /PP kappa.
  Forall x,y /in /VV (x < y => Card(x) /in Card(y)).
  Proof.
    Let x,y /in /VV. Let x < y.
    Then Card(x) /subset Card(y).
    Card(x) /neq Card(y).
  end.
  Then Card(kappa) /in Card(/PP kappa).
qed.


Lemma. Let kappa /in /Cd. Then kappa * 1 = kappa.
Proof.
  Define f[n] = (n,0) for n in kappa.
  Then f : kappa /rightarrow kappa /times 1.
  Proof.
    Let n /in kappa. Then f[n] /in kappa /times 1.
  end.
  f is injective.
  Proof.
    Let n1,n2 /in kappa. Let n1 /neq n2.
    Then f[n1] /neq f[n2].
  end.
  ran(f) = kappa /times 1.
  Proof.
    Let pair /in kappa /times 1.
    Take a zfset a such that a /in kappa /\ pair = (a,0).
    Then pair = f[a].
  end.
  Then f : kappa /leftrightarrow kappa /times 1.
  Then Card(kappa) = Card(kappa /times 1).
qed.


Lemma ExpSubset. Let alpha, beta, gamma /in /Cd. Let beta /subset gamma. Let 0 /in alpha. Then alpha ^ beta /subset alpha ^ gamma.
Proof.
  Forall f /in ^{beta}alpha exists g (g /in ^{gamma}alpha /\ g /upharpoonright beta = f).
  Proof.
    Let f /in ^{beta}alpha.
    Define g[x] =
      Case x /in beta -> f[x],
      Case x /notin beta -> 0
    for x in gamma.
    Then g : gamma /rightarrow alpha.
    Proof.
      Let x /in gamma. Then g[x] /in alpha.
      Proof.
        Case x /in beta. 
          f : beta /rightarrow alpha.
          Then f[x] /in alpha.
        end.
        Case x /notin beta. end.
      end.
    end.
    f, g /upharpoonright beta are functions.
    Dom(f) = Dom(g /upharpoonright beta).
    Forall x /in beta f[x] = g[x].
    Then f = g /upharpoonright beta.
  end.
  Define phi[f] = (choose a zffunction g such that g /in ^{gamma}alpha /\ (g /upharpoonright beta = f) in g)
  for f in ^{beta}alpha.
  Then phi : ^{beta}alpha /rightarrow ^{gamma}alpha.
  Proof.
    Let f /in ^{beta}alpha. Then phi[f] /in ^{gamma}alpha.
  end.
  phi is injective.
  Proof.
    Let f1, f2 /in ^{beta}alpha. Let f1 /neq f2.  
    Exists x /in beta (f1[x] /neq f2[x]).
    Proof by Contradiction. Assume the contrary.
      f1,f2 are functions.
      Dom(f1) = Dom(f2).
      Forall x /in Dom(f1) f1[x] = f2[x].
      Then f1 = f2.
      Contradiction.
    end.
    Take a zfset x such that x /in beta /\ f1[x] /neq f2[x].
    Then (phi[f1])[x] /neq (phi[f2])[x].
    Then phi[f1] /neq phi[f2].
  end.
  Then Card(^{beta}alpha) /subset Card(^{gamma}alpha).
qed.


Lemma BaseSubset. Let alpha, beta, gamma /in /Cd. Let alpha /subset beta. Then alpha ^ gamma /subset beta ^ gamma.
Proof.
  ^{gamma}alpha /subset ^{gamma}beta.
  Proof.
    Let f /in ^{gamma}alpha.
    Then f : gamma /rightarrow alpha.
    Then f : gamma /rightarrow alpha.
    Then f /in ^{gamma}beta.
  end.
  Then Card(^{gamma}alpha) /subset Card(^{gamma}beta).
qed.


Lemma. Let kappa, lambda /in /Cd. Let 2 /subset kappa. Let /NN /subset lambda. Then /NN /subset kappa ^ lambda.
Proof.
  Forall n /in /NN exists g (Dom(g) = lambda /\ g[n] = 1 /\ forall i /in lambda /setminus <n> g[i] = 0).
  Proof.
    Let n /in /NN.
    Define g[i] =
      Case i = n -> 1,
      Case i /neq n -> 0
    for i in lambda.
  end.
  Define f[n] = (choose a zffunction g such that Dom(g) = lambda /\ g[n] = 1 /\ forall i /in lambda /setminus <n> g[i] = 0 in g)
  for n in /NN.
  
  Then f : /NN /rightarrow ^{lambda}kappa.
  Proof.
    Dom(f) = /NN.
    Let n /in /NN.
    Then f[n] /in ^{lambda}kappa.
    f[n] /in /VV.
  end.
  f is injective.
  
  Then Card(/NN) /subset Card(^{lambda}kappa).
  Card(/NN) = /NN.
  Card(^{lambda}kappa) = kappa ^ lambda.  
qed.


Lemma. Let kappa, lambda /in /Cd. Let 2 /subset kappa. Let /NN /subset lambda. Then kappa ^ lambda /in /Lim.
Proof.
  kappa ^ lambda /in /Cd.
qed.



## Infinite sum and product

[synonym sequence/-s]

Signature. A sequence of cardinals is a notion.
Axiom. Let f be a sequence of cardinals. Then f is a zffunction.
Axiom. Let f be a zffunction. Then f is a sequence of cardinals iff Dom(f) /in /Ord /\ forall x /in Dom(f) f[x] /in /Cd.

Lemma. Let f be a zffunction. Let Dom(f) /in /Ord. Then exists g (Dom(g) = Dom(f) /\ forall i /in Dom(g) g[i] = Card(f[i])).
Proof.
  Define g[i] = Card(f[i]) for i in Dom(f).
qed.

Definition. Let f be a zffunction. Let Dom(f) /in /Ord. The cardinalsequence of f is a zffunction g such that Dom(g) = Dom(f) /\ forall i /in Dom(g) g[i] = Card(f[i]).
Let cardseq(f) stand for the cardinalsequence of f.

Lemma. Let f be a zffunction. Let Dom(f) /in /Ord. Then cardseq(f) is a sequence of cardinals.


# Sum

Definition. Let f be a zffunction. The sumset of f is {(a,b) | b /in Dom(f) /\ a /in f[b]}.
Let /sumset f stand for the sumset of f.

Lemma. Let f be a zffunction. Let Dom(f) /in /VV. Then /sumset f /in /VV.
Proof.
  Forall i /in Dom(f) (f[i] is a zfset).
  Define g[i] = {(a,i) | a /in f[i]} for i in Dom(f).
  Then g is a zffunction.
  Proof.
    Let i /in Dom(g).
    Then i /in Dom(f).
    Then g[i] /in /VV.
    Proof.
      Define h[a] = (a,i) for a in f[i].
      Then h is a zffunction.
      Proof.
        Let a /in f[i]. Then (a,i) /in /VV.
      end.
      Then h^[f[i]] /in /VV.
      g[i] /subset h^[f[i]].
    end.
  end.
  Then g^[Dom(f)] /in /VV.
  Then /bigcup g^[Dom(f)] /in /VV.
  /sumset f /subset /bigcup g^[Dom(f)].
qed.

Lemma. Let f be a sequence of cardinals. Then /sumset f /in /VV.
Proof.
  f is a zffunction.
  Dom(f) /in /VV.
  Then /sumset f /in /VV.
qed.

Definition. Let f be a sequence of cardinals. The seqsum of f is
Card(/sumset f).
Let /sum f stand for the seqsum of f.


Lemma. Let f be a zffunction. Let Dom(f) /in /Ord. Then Card(/sumset f) = /sum cardseq(f).
Proof.
  Take an ordinal alpha such that alpha = Dom(f).
  Forall i /in alpha exists g (g : f[i] /leftrightarrow (cardseq(f))[i]).
  Proof.
    Let i /in alpha.
    Then (cardseq(f))[i] = Card(f[i]).
    Then (cardseq(f))[i] /tilde f[i].
  end.
  Define bij[i] = (Choose a zffunction g such that g : f[i] /leftrightarrow (cardseq(f))[i] in g) for i in alpha.
  Forall o1,o2 ((o1,o2) /in /sumset f => o2 /in alpha /\ o1 /in f[o2]).
  Then forall o1,o2 ((o1,o2) /in /sumset f => o2 /in alpha /\ o1 /in Dom(bij[o2])).
  Define F[(a,b)] = ((bij[b])[a],b) for (a,b) in /sumset f.
  Then F : /sumset f /rightarrow /sumset cardseq(f).
  Proof.
    Let pair /in /sumset f.
    Take zfsets a,b such that b /in alpha /\ a /in f[b] /\ pair = (a,b).
    F[(a,b)] = ((bij[b])[a],b).
    b /in Dom(cardseq(f)).
    (bij[b])[a] /in (cardseq(f))[b].
    Then ((bij[b])[a],b) /in /sumset cardseq(f).
    Then F[pair] /in /sumset cardseq(f).
  end.
  F is injective.
  Proof.
    Let pair1, pair2 /in /sumset f.
    Let pair1 /neq pair2.
    Take zfsets a1,b1 such that b1 /in alpha /\ a1 /in f[b1] /\ pair1 = (a1,b1).
    Take zfsets a2,b2 such that b2 /in alpha /\ a2 /in f[b2] /\ pair2 = (a2,b2).
    F[pair1] /neq F[pair2].
    Proof.
      (a1,b1) /neq (a2,b2).
      Then b1 /neq b2 \/ (b1 = b2 /\ a1 /neq a2).
      Case b1 /neq b2.
        Then F[(a1,b1)] /neq F[(a2,b2)].
      end.
      Case (b1 = b2 /\ a1 /neq a2).
        bij[b1] is injective.
        a1,a2 /in Dom(bij[b1]).
        a1 /neq a2.
        Then (bij[b1])[a1] /neq (bij[b1])[a2].
        F[(a1,b1)] = ((bij[b1])[a1],b1).
        F[(a2,b2)] = ((bij[b1])[a2],b2).
        Then F[(a1,b2)] /neq F[(a2,b2)].
      end.
    end.
  end.
  ran(F) = /sumset cardseq(f).
  Proof.
    Let pair /in /sumset cardseq(f).
    /sumset cardseq(f) = {(a,b) | b /in Dom(cardseq(f)) /\ a /in (cardseq(f))[b]}.
    Take objects a,b such that b /in Dom(cardseq(f)) /\ a /in (cardseq(f))[b] /\ pair = (a,b).
    Then a,b are zfsets.
    b /in alpha.
    bij[b] : f[b] /leftrightarrow (cardseq(f))[b].
    Take a zfset aa such that aa /in f[b] /\ (bij[b])[aa] = a.
    Then F[(aa,b)] = (a,b).
    Then pair /in ran(F).
  end.
  Then F : /sumset f /leftrightarrow /sumset cardseq(f).
  Then Card(/sumset f) = Card(/sumset cardseq(f)).
qed.


# Product

Definition. Let f be a zffunction. Let Dom(f) /in /VV. The productset of f is 
{zffunction g | Dom(g) = Dom(f) /\ forall i /in Dom(g) g[i] /in f[i]}.
Let /prodset f stand for the productset of f.

Lemma. Let f be a zffunction. Let Dom(f) /in /VV. Then /prodset f /in /VV.
Proof.
  /bigcup f^[Dom(f)] /in /VV.
  Forall g /in /prodset f forall i /in Dom(g) g[i] /in /bigcup f^[Dom(f)].
  Then /prodset f /subset ^{Dom(f)}(/bigcup f^[Dom(f)]).
qed.

Lemma. Let f be a sequence of cardinals. Then /prodset f /in /VV.
Proof.
  f is a zffunction.
  Dom(f) /in /VV.
  Then /prodset f /in /VV.
qed.

Definition. Let f be a sequence of cardinals. The seqproduct of f is
Card(/prodset f).
Let /prod f stand for the seqproduct of f.



## Koenigs Lemma


Theorem Koenig. Let kappa, lambda be sequences of cardinals. Let Dom(kappa) = Dom(lambda). Let forall i /in Dom(kappa) kappa[i] /in lambda[i].
Then /sum kappa /in /prod lambda.
Proof by contradiction. Assume the contrary.  
  Then /prod lambda /subset /sum kappa.
  Proof.
    Take ordinals alpha, beta such that alpha = /sum kappa /\ beta = /prod lambda.
    Then alpha /notin beta.
    alpha /in beta \/ beta /in alpha \/ alpha = beta.
    Then beta /subset alpha.
  end.
  Take a zffunction f1 such that f1 : /sumset kappa /leftrightarrow /sum kappa.
  Exists f (f : /sum kappa /rightarrow /prodset lambda /\ ran(f) = /prodset lambda).
  Proof.
    /prodset lambda /neq /emptyset.
    Card(/prodset lambda) /subset /sum kappa.
    /sum kappa /in /Ord.
    /prodset lambda /in /VV.
  end.
  Take a zffunction f2 such that f2 : /sum kappa /rightarrow /prodset lambda /\ ran(f2) = /prodset lambda.
  
  Let G = f2 /circ f1.
  Then G : /sumset kappa /rightarrow /prodset lambda.
  Proof.
    Let pair /in /sumset kappa.
    Then f1[pair] /in /sum kappa.
    Then f2[f1[pair]] /in /prodset lambda.
    Then G[pair] /in /prodset lambda.
  end.
  ran(G) = /prodset lambda.
  Proof.
    /prodset lambda /subset ran(G).
    Proof.
      Let x /in /prodset lambda.
      Then x /in ran(f2).
      Take a zfset y such that y /in /sum kappa /\ f2[y] = x.
      Take a zfset z such that z /in /sumset kappa /\ f1[z] = y.
      Then G[z] = x.
    end.
  end.
  
  Take an ordinal delta such that delta = Dom(kappa).
  Define Diag[i] = {G[(v,i)][i] | v /in kappa[i]} for i in delta.
  Diag is a zffunction.
  Proof.
    Let i /in delta.
    Define f[v] = G[(v,i)][i] for v in kappa[i].
    Then f is a zffunction.
    Proof.
      Let v /in kappa[i].
      Then (v,i) /in /sumset kappa.
      Then G[(v,i)] /in /prodset lambda.
      Then G[(v,i)][i] /in /VV.
    end.
    Then f^[kappa[i]] /in /VV.
    Diag[i] /subset f^[kappa[i]].
  end.
  
  Forall i /in delta Card(Diag[i]) /subset kappa[i].
  Proof.
    Let i /in delta.
    Define f[v] = G[(v,i)][i] for v in kappa[i].
    Then f is a zffunction.
    Proof.
      Let v /in kappa[i].
      Then (v,i) /in /sumset kappa.
      Then G[(v,i)] /in /prodset lambda.
      Then G[(v,i)][i] /in /VV.
    end.
    f : kappa[i] /rightarrow Diag[i].
    Diag[i] /subset f^[kappa[i]].
    Then Card(Diag[i]) /subset Card(f^[kappa[i]]).
    Card(f^[kappa[i]]) /subset Card(kappa[i]).
    kappa[i] /in /Cd.
    Then Card(kappa[i]) = kappa[i].
    Then Card(Diag[i]) /subset kappa[i].
  end.
  
  Forall i /in delta (lambda[i],kappa[i] are zfsets).
  Forall i /in delta Diag[i] /subset lambda[i].
  Forall i /in delta lambda[i] /setminus Diag[i] /neq /emptyset.
  Proof by contradiction. Assume the contrary.
    Take a zfset i such that i /in delta /\ lambda[i] /setminus Diag[i] = /emptyset.
    Then lambda[i] /subset Diag[i].
    Diag[i] /subset lambda[i].
    lambda[i], Diag[i] are sets.
    Then lambda[i] = Diag[i].
    Card(Diag[i]) /subset kappa[i].
    Then lambda[i] /subset kappa[i].
    kappa[i] /in lambda[i].
    Contradiction.
  end.
  
  Define f[i] = (choose a zfset x such that x /in lambda[i] /setminus Diag[i] in x) for i in delta.
  Then f /in /prodset lambda.
  Forall i /in delta f[i] /notin Diag[i].
  Take a zfset pair such that pair /in /sumset kappa /\ G[pair] = f.
  Take zfsets a, b such that b /in delta /\ a /in kappa[b] /\ pair = (a,b).
  Then G[(a,b)][b] /in Diag[b].
  G[(a,b)][b] = f[b].
  f[b] /notin Diag[b].
  
  Contradiction.
qed.


Lemma. Let kappa, lambda /in /Cd. Let 2 /subset kappa. Let /NN /subset lambda. Then lambda /in cof(kappa ^ lambda).
Proof by contradiction. Assume the contrary.
  Then cof(kappa ^ lambda) /subset lambda.
  Proof.
    Take ordinals a,b such that a = lambda /\ b = cof(kappa ^ lambda).
    Then a /in b \/ b /in a \/ a = b.
    a /notin b.
  end.
  
  Take a zfset x such that x /subset kappa ^ lambda /\ x /cof kappa ^ lambda /\ Card(x) = cof(kappa ^ lambda).
  Then Card(x) /subset lambda.
  Take a zffunction f such that f : lambda /rightarrow x /\ ran(f) = x.
  
  Then /bigcup ran(f) = kappa ^ lambda.
  Proof.
    /bigcup ran(f) /subset kappa ^ lambda.
    Proof.
      Let alpha /in /bigcup ran(f).
      Take a zfset beta such that beta /in lambda /\ alpha /in f[beta].
      f[beta] /in x.
      Then f[beta] /subset kappa ^ lambda.
    end.
    kappa ^ lambda /subset /bigcup ran(f).
    Proof.
      Let alpha /in kappa ^ lambda.
      Take beta /in x such that alpha /in beta.
      Take gamma /in lambda such that f[gamma] = beta.
      Then alpha /in f[gamma].
      Then alpha /in /bigcup ran(f).
    end.
  end.
  
  Define phi[b] = {(a,b) | a /in f[b]} for b in lambda.
  Then phi is a zffunction.
  Proof.
    Let b /in lambda.
    Define g[a] = (a,b) for a in f[b].
    Then g is a zffunction.
    Proof.
      Let a /in f[b]. Then (a,b) /in /VV.
    end.
    Then g^[f[b]] /in /VV.
    phi[b] /subset g^[f[b]].
  end.
  Let M = /bigcup phi^[lambda].
  Define psi[a] = (choose a zfset i such that i /in lambda /\ a /in f[i] in (a,i)) for a in /bigcup ran(f).
  Then psi : /bigcup ran(f) /rightarrow M.
  Proof.
    Let a /in /bigcup ran(f).
    Take a zfset i such that i /in lambda /\ a /in f[i] /\ (a,i) = psi[a].
    Then (a,i) /in phi[i].
    Then psi[a] /in /bigcup phi^[lambda].
    Then psi[a] /in M.
  end.
  psi is injective.
  Proof.
    Let a1,a2 /in /bigcup ran(f). Let a1 /neq a2.
    Then psi[a1] /neq psi[a2].
    Proof.
      Take a zfset i1 such that i1 /in lambda /\ a1 /in f[i1] /\ (a1,i1) = psi[a1].
      Take a zfset i2 such that i2 /in lambda /\ a2 /in f[i2] /\ (a2,i2) = psi[a2].
      Then (a1,i1) /neq (a2,i2).
    end.
  end.
  Then Card(/bigcup ran(f)) /subset Card(M).
  Then kappa ^ lambda /subset Card(M).
  
  Define seq[i] = Card(f[i]) for i in lambda.
  Then seq is a sequence of cardinals.
  Proof.
    Dom(seq) = lambda.
    lambda is an ordinal.
    Forall i /in lambda seq[i] /in /Cd.
  end.
  
  Define bij[i] = (choose a zffunction g such that g : f[i] /leftrightarrow Card(f[i]) in g) for i in lambda.
  Forall o1,o2 ((o1,o2) /in M => o2 /in lambda /\ o1 /in f[o2]).
  Proof.
    Let o1,o2 be objects.
    Let (o1,o2) /in M.
    Take a zfset z such that z /in phi^[lambda] /\ (o1,o2) /in z.
    Take a zfset b such that b /in lambda /\ z = phi[b].
    Let pair = (o1,o2).
    Then pair /in phi[b].
    phi[b] = {(a,b) | a /in f[b]}.
    Take a zfset a such that a /in f[b] /\ pair = (a,b).
    Then (o1,o2) = (a,b).
    o1 = a.
    o2 = b.
  end.
  Forall pair /in M exists a,b /in /VV (b /in lambda /\ a /in f[b] /\ pair = (a,b)).
  Proof.
    Let pair /in M.
    Take a zfset z such that z /in phi^[lambda] /\ pair /in z.
    Take a zfset b such that b /in lambda /\ z = phi[b].
    Then pair /in phi[b].
    phi[b] = {(a,b) | a /in f[b]}.
    Take a zfset a such that a /in f[b] /\ pair = (a,b).
  end.  
  Forall b /in lambda forall a /in f[b] a /in Dom(bij[b]).
  Define chi[(a,b)] = ((bij[b])[a],b) for (a,b) in M.
    
  chi : M /rightarrow /sumset seq.
  Proof.
    Let pair /in M.
    Take zfsets a,b such that b /in lambda /\ a /in f[b] /\ pair = (a,b).
    Then chi[pair] = ((bij[b])[a],b).
    bij[b] : f[b] /leftrightarrow Card(f[b]).
    Then (bij[b])[a] /in seq[b].
    Then chi[pair] /in /sumset seq.
  end.
  chi is injective.
  Proof.
    Let pair1, pair2 /in M. Let pair1 /neq pair2.
    Take zfsets a1,b1 such that b1 /in lambda /\ a1 /in f[b1] /\ pair1 = (a1,b1).
    Take zfsets a2,b2 such that b2 /in lambda /\ a2 /in f[b2] /\ pair2 = (a2,b2).
    chi[pair1] = ((bij[b1])[a1],b1).
    chi[pair2] = ((bij[b2])[a2],b2).
    chi[pair1] /neq chi[pair2].
    Proof.
      a1 /neq a2 \/ b1 /neq b2.
      Case b1 /neq b2. Then ((bij[b1])[a1],b1) /neq ((bij[b2])[a2],b2). end.
      Case b1 = b2 /\ a1 /neq a2.
        Then (bij[b1])[a1] /neq (bij[b2])[a2].
        Then ((bij[b1])[a1],b1) /neq ((bij[b2])[a2],b2).
      end.
    end.
  end.
  Then Card(M) /subset /sum seq.
  Then kappa ^ lambda /subset /sum seq.
  
  Define kaplam[i] = kappa ^ lambda for i in lambda.
  Then kaplam is a sequence of cardinals.
  kappa ^ lambda = (kappa ^ lambda)^ lambda.
  Proof.
    lambda * lambda = lambda.
    Then kappa ^ lambda = kappa ^ (lambda * lambda).
    kappa ^ (lambda * lambda) = (kappa ^ lambda)^ lambda.
  end.
  ^{lambda}(kappa ^ lambda) = /prodset kaplam.
  Proof.
    ^{lambda}(kappa ^ lambda) /subset /prodset kaplam.
    Proof.
      Let func /in ^{lambda}(kappa ^ lambda).
      Then func : lambda /rightarrow kappa ^ lambda.
      Dom(func) = lambda.
      Forall i /in lambda func[i] /in kappa ^ lambda.
      Then forall i /in lambda func[i] /in kaplam[i].
      Then func /in /prodset kaplam.
    end.
    /prodset kaplam /subset ^{lambda}(kappa ^ lambda).
    Proof.
      Let func /in /prodset kaplam.
      Then Dom(func) = lambda.
      Forall i /in lambda func[i] /in kaplam[i].
      Then forall i /in lambda func[i] /in kappa ^ lambda.
      Then func /in ^{lambda}(kappa ^ lambda).
    end.
  end.
  Then kappa ^ lambda = /prod kaplam.
  
  /sum seq /in /prod kaplam.
  Proof.
    kaplam, seq are sequences of cardinals.
    Dom(kaplam) = Dom(seq).
    Forall i /in Dom(seq) seq[i] /in kaplam[i].
    Proof.
      Let i /in Dom(seq).
      Then seq[i] = Card(f[i]).
      f[i] /in kappa ^ lambda.
      Then Card(f[i]) /subset kappa ^ lambda.
      Card(f[i]) /neq kappa ^ lambda.
    end.
    Then /sum seq /in /prod kaplam (by Koenig).
  end.
  Then /sum seq /in kappa ^ lambda.
  
  Contradiction.
qed.


Theorem HausdorffRecursion. Let alpha, beta /in /Ord. Then Alef[alpha +' 1] ^ Alef[beta] = (Alef[alpha] ^ Alef[beta]) * Alef[alpha +' 1].
Proof.
  Alef[alpha +' 1] /subset 2 ^ Alef[beta] \/ 2 ^ Alef[beta] /in Alef[alpha +' 1].
  Proof.
    Take cardinals a,b such that a = Alef[alpha +' 1] /\ b = 2 ^ Alef[beta].
    a,b /in /Ord.
    Then a /in b \/ b /in a \/ a = b (by TotalOrder).
  end.
  
  Case Alef[alpha +' 1] /subset 2 ^ Alef[beta].
    Alef[alpha +' 1] ^ Alef[beta] = 2 ^ Alef[beta].
    Proof.
      Take a cardinal a such that a = Alef[alpha +' 1].
      Take a cardinal b such that b = Alef[beta].
      Then 2 /subset a.
      /NN /subset b.
      Proof.
        Alef[0] /subset Alef[beta].
        Alef[0] = /NN.
      end.
      a /subset 2 ^ b.
      Then a ^ b = 2 ^ b.
    end.  
    Alef[alpha] ^ Alef[beta] = 2 ^ Alef[beta].
    Proof.
      Take a cardinal a such that a = Alef[alpha].
      Take a cardinal b such that b = Alef[beta].
      Then 2 /subset a.
      /NN /subset b.
      Proof.
        Alef[0] /subset Alef[beta].
        Alef[0] = /NN.
      end.
      a /subset Alef[alpha +' 1].
      Alef[alpha +' 1] /subset 2 ^ b.
      Then a /subset 2 ^ b.
      Then a ^ b = 2 ^ b.
    end.
    
    Alef[alpha] ^ Alef[beta] = (Alef[alpha] ^ Alef[beta]) * Alef[alpha +' 1].
    Proof.
      Take a cardinal a such that a = Alef[alpha] ^ Alef[beta].
      Take a cardinal b such that b = Alef[alpha +' 1].
      Then b /subset a.
      Then a /times b /subset a /times a.
      Then a * b /subset a * a.
      a /in /Cd.
      /NN /subset a.
      a * a = a.
      Then a * b /subset a.
      a /subset a * b.
      Proof.
        Define f[i] = (i,0) for i in a.
        Then f : a /rightarrow a /times b.
        Proof.
          0 /in b.
          Let i /in a.
          Then f[i] /in a /times b.
        end.
        f is injective.
        Proof.
          Let i1,i2 /in a. Let i1 /neq i2.
          Then (i1,0) /neq (i2,0).
          Then f[i1]/neq f[i2].
        end.
        Then Card(a) /subset Card(a /times b).
      end.
      Then a = a * b.
    end.
    
    Then Alef[alpha +' 1] ^ Alef[beta] = (Alef[alpha] ^ Alef[beta]) * Alef[alpha +' 1].
    Proof.
      Take a cardinal a such that a = Alef[alpha +' 1] ^ Alef[beta].
      Take a cardinal b such that b = 2 ^ Alef[beta].
      Take a cardinal c such that c = Alef[alpha] ^ Alef[beta].
      Take a cardinal d such that d = (Alef[alpha] ^ Alef[beta]) * Alef[alpha +' 1].
      a = b. b = c. c = d.
      Then a = d.
    end.  
  end.
  
  Case 2 ^ Alef[beta] /in Alef[alpha +' 1].
    
    Take a cardinal a0 such that a0 = Alef[alpha].
    Take a cardinal a1 such that a1 = Alef[alpha +' 1].
    Take an ordinal b such that b = Alef[beta].
    Then b /in /Cd.
    
    b /in a1.
    Proof by contradiction. Assume the contrary.
      a1 /in b \/ b /in a1 \/ a1 = b.
      Then a1 /subset b.
      b /in 2 ^ b.
      Then a1 /in 2 ^ b.
      Contradiction.
    end.
    
    (a0 ^ b) * a1 /subset (a1 ^ b) * (a1 ^ b).
    Proof.
      a0 ^ b /subset a1 ^ b.
      Proof.
        ^{b}a0 /subset ^{b}a1.
        Proof.
          Let f /in ^{b}a0.
          Then f : b /rightarrow a0.
          a0 /subset a1.
          Proof.
            alpha /subset alpha +' 1.
            Then Alef[alpha] /subset Alef[alpha +' 1].
          end.
          Then f : b /rightarrow a1.
          Then f /in ^{b}a1.
        end.
        Then Card(^{b}a0) /subset Card(^{b}a1).
      end.
      a1 /subset (a1 ^ b).
      Proof.
        a1 = a1 ^ 1.
        1 /subset b.
        0 /in a1.
        a1, 1, b /in /Cd.
        Then a1 ^ 1 /subset a1 ^ b.
      end.
      Then (a0 ^ b) /times a1 /subset (a1 ^ b) /times (a1 ^ b).
      Proof.
        Let pair /in (a0 ^ b) /times a1.
        Take zfsets v1,v2 such that v1 /in a0 ^ b /\ v2 /in a1 /\ pair = (v1,v2).
        v1 /in a1 ^ b.
        v2 /in a1 ^ b.
        Then (v1,v2) /in (a1 ^ b) /times (a1 ^ b).
      end.
      Then Card((a0 ^ b) /times a1) /subset Card((a1 ^ b) /times (a1 ^ b)).
    end.
    
    (a1 ^ b) * (a1 ^ b) = a1 ^ b.
    Proof.
      /NN /subset a1 ^ b.
      Proof.
        /NN /subset a1.
        a1 /subset (a1 ^ b).
        Proof.
          a1 = a1 ^ 1.
          1 /subset b.
          0 /in a1.
          a1, 1, b /in /Cd.
          Then a1 ^ 1 /subset a1 ^ b.
        end.
      end.
    end.
    
    (a0 ^ b) * a1 /subset (a1 ^ b).
      
    cof(a1) = a1.  
    Forall f /in ^{b}a1 /bigcup ran(f) /in a1.
    Proof by contradiction. Assume the contrary.
      Take a zffunction f such that f /in ^{b}a1 /\ /bigcup ran(f) /notin a1.
      ran(f) /subset a1.
      /bigcup ran(f) /subset a1.
      /bigcup ran(f) /in /Ord.
      Proof.
        Trans(/bigcup ran(f)).
        ran(f) = f^[b].
        Then ran(f) /in /VV.
        Then /bigcup ran(f) /in /VV.
      end.
      Then /bigcup ran(f) = a1.
      Proof.
        Take ordinals aa,bb such that aa = /bigcup ran(f) /\ bb = a1.
        Then aa /in bb \/ bb /in aa \/ aa = bb.
        aa /notin bb.
        aa /subset bb.
        Then aa = bb.
      end.
      Then ran(f) /cof a1.
      
      ran(f) = f^[b].
      Then Card(ran(f)) /subset Card(b).
      Card(ran(f)) /in cofset2(a1).
      Then min(cofset2(a1)) /subset Card(b).
      Then a1 /subset b.
      
      Contradiction.
    end.
    
    Define M = {zffunction f | exists v /in a1 (f : b /rightarrow v)}.
    Then M = ^{b}a1.
    Proof.
      M /subset ^{b}a1.
      Proof.
        Let f /in M.
        Take a zfset v such that v /in a1 /\ f : b /rightarrow v.
        v /subset a1.
        Then f : b /rightarrow a1.
        Then f /in ^{b}a1.
      end.
      ^{b}a1 /subset M.
      Proof.
        Let f /in ^{b}a1.
        Then /bigcup ran(f) /in a1.
        Take a zfset v such that v /in a1 /\ v = /bigcup ran(f).
        Then v is an ordinal.
        ran(f) /subset v+'1.
        Proof.
          Let x /in ran(f).
          Then x /subset v.
          x,v are ordinals.
          Then x /in v \/ x = v.
          Then x /in v++.
        end.
        Then f : b /rightarrow v+'1.
        a1 /in /Lim.
        Then v+'1 /in a1.
        Then f /in M.      
      end.
    end.
    Then ^{b}a1, M are zfsets.
    Card(^{b}a1) = a1 ^ b.
    Then Card(M) = a1 ^ b.
    
    Forall v /in a1 (v,^{b}v are zfsets).
    Define seq[v] = Card(^{b}v) for v in a1.
    Then seq is a sequence of cardinals.
    Proof.
      Let v /in a1. Then seq[v] /in /Cd.
    end.

    Card(M) /subset Card(/sumset seq).
    Proof.
      Forall v /in a1 exists F (F : ^{b}v /leftrightarrow Card(^{b}v)).
      Define bij[v] = (choose a zffunction psi such that psi : ^{b}v /leftrightarrow Card(^{b}v) in psi)
      for v in a1.
      Forall v /in a1 forall f (f : b /rightarrow v => f /in Dom(bij[v])).
      Define phi[f] = (choose a zfset v such that v /in a1 /\ f : b /rightarrow v in ((bij[v])[f],v)) for f in M.
      Then phi : M /rightarrow /sumset seq.
      Proof.
        Let f /in M.
        Take a zfset v such that v /in a1 /\ f : b /rightarrow v /\ phi[f] = ((bij[v])[f],v).
        Then (bij[v])[f] /in seq[v].
        Then phi[f] /in /sumset seq.
      end.
      phi is injective.
      Proof.
        Let f1,f2 /in M. Let f1 /neq f2.
        Take a zfset v1 such that v1 /in a1 /\ f1 : b /rightarrow v1 /\ phi[f1] = ((bij[v1])[f1],v1).
        Take a zfset v2 such that v2 /in a1 /\ f2 : b /rightarrow v2 /\ phi[f2] = ((bij[v2])[f2],v2).
        Then phi[f1] /neq phi[f2].
        Proof.
          Case v1 /neq v2. Then ((bij[v1])[f1],v1) /neq ((bij[v2])[f2],v2). end.
          Case v1 = v2.
            bij[v1] is injective.
            Then (bij[v1])[f1] /neq (bij[v1])[f2].
            Then ((bij[v1])[f1],v1) /neq ((bij[v2])[f2],v2).
          end.
        end.
      end.
    end.
    Card(M) /subset /sum seq.
    
    Forall v /in a1 seq[v] = Card(v) ^ b.
    Proof.
      Let v /in a1.
      v,^{b}v are zfsets.
      seq[v] = Card(^{b}v).
      Take a zffunction bij such that bij : v /leftrightarrow Card(v).
      Define phi[f] = bij /circ f for f in ^{b}v.
      Then phi : ^{b}v /rightarrow ^{b}Card(v).
      Proof.
        Dom(phi) = ^{b}v.
        Forall f /in Dom(phi) (phi[f] /in /VV /\ phi[f] /in ^{b}Card(v)).
        Proof.
          Let f /in Dom(phi).
          Then f : b /rightarrow v.
          Then bij /circ f : b /rightarrow Card(v).
          Then bij /circ f /in ^{b}Card(v).
          Then phi[f] /in ^{b}Card(v).
          phi[f] /in /VV.
        end.
      end.
      phi is injective.
      Proof.
        Forall f1,f2 /in Dom(phi) (f1 /neq f2 => phi[f1] /neq phi[f2]).
        Proof.
          Let f1,f2 /in Dom(phi). Let f1 /neq f2.
          f1,f2 /in ^{b}v.
          Then exists x /in b (f1[x] /neq f2[x]).
          Proof by contradiction. Assume the contrary.
            f1,f2 are functions.
            Dom(f1) = Dom(f2).
            Forall x /in Dom(f1) f1[x] = f2[x].
            Then f1 = f2.
            Contradiction.
          end.
          Take a zfset x such that x /in b /\ f1[x] /neq f2[x].
          f1 : b /rightarrow v.
          f2 : b /rightarrow v.
          f1[x], f2[x] /in v.
          bij is injective.
          Then bij[f1[x]] /neq bij[f2[x]].
          Then (bij /circ f1)[x] /neq (bij /circ f2)[x].
          Then bij /circ f1 /neq bij /circ f2.
          Then phi[f1] /neq phi[f2].
        end.
      end.
      ^{b}Card(v) /subset ran(phi).
      Proof.
        Let f /in ^{b}Card(v).
        Then f : b /rightarrow Card(v).
        bij^{-1} : Card(v) /leftrightarrow v.
        Let g = (bij^{-1}) /circ f.
        Then g : b /rightarrow v.
        Proof.
          Let x /in b.
          ran(f) /subset Card(v).
          f[x] /in ran(f).
          Then f[x] /in Card(v).
          Take a zfset y such that y /in Card(v) /\ y = f[x].
          Then g[x] = (bij^{-1})[y].
          Then g[x] /in v.
        end.
        bij /circ g = f.
        Proof.
          (bij /circ g), f are functions.
          Dom(bij /circ g) = Dom(f).
          Forall x /in Dom(f) (bij /circ g)[x] = f[x].
          Proof.
            Let x /in Dom(f).
            ran(f) /subset Card(v).
            f[x] /in ran(f).
            f[x] /in Card(v).
            g[x] = (bij^{-1})[f[x]].
            Take a zfset y such that y = (bij^{-1})[f[x]].
            Then bij[y] = f[x].
            Then (bij /circ g)[x] = f[x].
          end.
        end.
        Then phi[g] = f.
        Then f /in ran(phi).
      end.
      Then ran(phi) = ^{b}Card(v).
      phi : ^{b}v /leftrightarrow ^{b}Card(v).
      Then Card(^{b}v) = Card(^{b}Card(v)).
      Then Card(^{b}v) = Card(v) ^ b.
    end.
  
    Forall v /in a1 ((v is a zfset) /\ Card(v) /subset a0).
    Proof.
      Let v /in a1.
      v is a zfset.
      Card(v) /subset a1.
      Card(v) /neq a1.
      Card(v) /subset a0.
      Proof.
        v /in /NN \/ /NN /subset v.
        Case v /in /NN. /NN /subset a0. end.
        Case /NN /subset v.
          Take an ordinal gamma such that Card(v) = Alef[gamma].
          Alef[gamma] /subset Alef[alpha +' 1].
          Then gamma /subset alpha +' 1.
          Proof.
            Take ordinals aa, bb such that aa = gamma /\ bb = alpha +' 1.
            Then aa /in bb \/ bb /in aa \/ aa = bb (by TotalOrder).
            Case aa /in bb. end.
            Case aa = bb. end.
            Case bb /in aa. Then Alef[bb] /in Alef[aa]. Contradiction. end.
          end.
          gamma /neq alpha +' 1.
          Then gamma /in alpha +' 1.
          Then gamma /in alpha \/ gamma = alpha.
          Then gamma /subset alpha.
          Then Alef[gamma] /subset Alef[alpha].
          Proof.
            gamma /in alpha \/ gamma = alpha.
            Case gamma /in alpha. Then Alef[gamma] /in Alef[alpha]. end.
            Case gamma = alpha. end.
          end.
        end.
      end.
    end.
    
    Forall v /in a1 ((v is a zfset) /\ Card(v) ^ b /subset a0 ^ b).
    Proof.
      Let v /in a1.
      v is a zfset.
      ^{b}Card(v) /subset ^{b}a0.
      Proof.
        Let f /in ^{b}Card(v).
        Then f : b /rightarrow Card(v).
        Card(v) /subset a0.
        Then f : b /rightarrow a0.
        Then f /in ^{b}a0.
      end.
    end.
      
    Define const[v] = a0 ^ b for v in a1.
    const is a sequence of cardinals.
    Proof.
      Let v /in a1.
      Then const[v] /in /Cd.
    end.
    
    /sumset(seq) /subset /sumset(const).
    Proof.
      Forall pair /in /sumset(seq) exists v1,v2 /in /VV (v2 /in Dom(seq) /\ v1 /in seq[v2] /\ pair = (v1,v2)).
      Let pair /in /sumset(seq).
      Take zfsets v1,v2 such that v2 /in Dom(seq) /\ v1 /in seq[v2] /\ pair = (v1,v2).
      Then v2 /in Dom(const).
      v1 /in const[v2].
      Then (v1,v2) /in /sumset(const).
    end.
    
    /sum seq /subset /sum const.
  
    /sumset(const) /subset (a0 ^ b) /times a1.
    Proof.
      Forall pair /in /sumset(const) exists v1,v2 /in /VV (v2 /in Dom(const) /\ v1 /in const[v2] /\ pair = (v1,v2)).
      Let pair /in /sumset(const).
      Take zfsets v1,v2 such that v2 /in Dom(const) /\ v1 /in const[v2] /\ pair = (v1,v2).
      Then v2 /in a1.
      v1 /in a0 ^ b.
      Then (v1,v2) /in (a0 ^ b) /times a1.
    end.
    Then Card(/sumset(const)) /subset Card((a0 ^ b) /times a1).  
    /sum const /subset (a0 ^ b) * a1.
    
    a1 ^ b /subset (a0 ^ b) * a1.
    Proof.
      a1 ^ b /subset Card(M).
      Card(M) /subset /sum seq.
      /sum seq /subset /sum const.
      /sum const /subset (a0 ^ b) * a1.
    end.   
  end.
qed.



