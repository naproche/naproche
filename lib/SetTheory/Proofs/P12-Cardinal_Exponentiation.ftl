[read Formalizations/Library/L11-Gimel_Function.ftl]

## Pretyped Variables

Let w,x,y,z,W,X,Y,Z stand for zfsets.
Let a,b,c,d,A,B,C,D,M stand for sets.
Let o,o1,o2 stand for objects.
Let alpha, beta, gamma stand for ordinals.
Let f,g,h,F,G,H stand for zffunction.
Let kappa, lambda stand for cardinals.




## Prerequisites


Lemma. Forall a exists f (Dom(f) = /VV /\ forall b /in a f[b] = b /\ forall b /in /VV /setminus a f[b] = 0).
Proof.
  Let a be a set.
  Define f[b] =
    Case b /in a -> b,
    Case b /notin a -> 0
  for b in /VV.
  Then Dom(f) = /VV.
  Forall b /in /VV ((b /in a => f[b] = b) /\ (b /notin a => f[b] = 0)).
end.

Lemma. Let a be a set. Let g be a zffunction. Let a /subset Dom(g). Then exists f (Dom(f) = /VV /\ forall b /in a f[b] = g[b] /\ forall b /in /VV /setminus a f[b] = 0).
Proof.
  Let a be a set.
  Let g be a zffunction.  
  Let a /subset Dom(g).
  Define f[b] =
    Case b /in a -> g[b],
    Case b /notin a -> 0
  for b in /VV.
  f is a zffunction.
  Proof.
    Let b /in /VV.
    Then f[b] /in /VV.
    Proof.
      Case b /in a.
        Then f[b] = g[b].
      end.
      Case b /notin a.
      end.
    end.
  end.
  Then Dom(f) = /VV.
  Forall b /in /VV ((b /in a => f[b] = g[b]) /\ (b /notin a => f[b] = 0)).
end.

Signature. Let a be a set. delta(a) is a zffunction.
Axiom. Let a be a set. Dom(delta(a)) = /VV.
Axiom. Let a be a set. (Forall b /in a (delta(a))[b] = b) /\ (forall b /in /VV /setminus a (delta(a))[b] = 0).

Signature. Let a be a set. Let g be a zffunction. Let a /subset Dom(g). delta(g,a) is a zffunction.
Axiom. Let a be a set. Let g be a zffunction. Let a /subset Dom(g). Dom(delta(g,a)) = /VV.
Axiom. Let a be a set. Let g be a zffunction. Let a /subset Dom(g). (Forall b /in a (delta(g,a))[b] = g[b]) /\ (forall b /in /VV /setminus a (delta(g,a))[b] = 0).




## Cardinal Exponentiation


Lemma. Let v /in /VV. Let b /in /Cd. Then Card(^{b}v) = Card(v) ^ b.
Proof.
  v /tilde Card(v).
  Then ^{b}v /tilde ^{b}Card(v).
  Card(^{b}Card(v)) = Card(v) ^ b.
qed.


Lemma. Let lambda, kappa /in /Card. Let xi /in /Cd. Let lambda /in kappa. Let xi /in kappa. Let kappa /subset xi ^ lambda.
Then kappa ^ lambda = xi ^ lambda.
Proof.
  xi /subset kappa.
  Then xi ^ lambda /subset kappa ^ lambda.
  kappa /subset xi ^ lambda.
  Then kappa ^ lambda /subset (xi ^ lambda) ^ lambda.
  (xi ^ lambda) ^ lambda = xi ^ (lambda * lambda).
  lambda * lambda = lambda.
  Then (xi ^ lambda) ^ lambda = xi ^ lambda.
  Then kappa ^ lambda /subset xi ^ lambda.
qed.


Lemma. Let kappa, lambda /in /Card. Let lambda /in kappa. Let forall xi /in /Cd /cap kappa (xi ^ lambda /in kappa). Let lambda /in cof(kappa).
Then kappa ^ lambda = kappa.
Proof.
  kappa = kappa ^ 1.
  1 /subset lambda.
  0 /in kappa.
  kappa,0,1 /in /Cd.
  Then kappa ^ 1 /subset kappa ^ lambda (by ExpSubset).
  Then kappa /subset kappa ^ lambda.

  
  Forall f /in ^{lambda}kappa /bigcup ran(f) /in kappa.
  Proof by contradiction. Assume the contrary.
    Take a zffunction f such that f /in ^{lambda}kappa /\ /bigcup ran(f) /notin kappa.
    Then f : lambda /rightarrow kappa.
    ran(f) /subset kappa.
    /bigcup ran(f) /subset kappa.
    /bigcup ran(f) /in /Ord.
    Proof.
      Trans(/bigcup ran(f)).
      ran(f) = f^[lambda].
      Then ran(f) /in /VV.
      Then /bigcup ran(f) /in /VV.
    end.
    Then /bigcup ran(f) = kappa.
    Proof.
      Take ordinals aa,bb such that aa = /bigcup ran(f) /\ bb = kappa.
      Then aa /in bb \/ bb /in aa \/ aa = bb.
      aa /notin bb.
      aa /subset bb.
      Then aa = bb.
    end.
    Then ran(f) /cof kappa.
      
    ran(f) = f^[lambda].
    Then Card(ran(f)) /subset Card(lambda).
    Card(ran(f)) /in cofset2(kappa).
    Then min(cofset2(kappa)) /subset lambda.
    Then cof(kappa) /subset lambda.
    Contradiction.
  end.
  
  Define M = {zffunction f | exists v /in kappa (f : lambda /rightarrow v)}.
  Then M = ^{lambda}kappa.
  Proof.
    M /subset ^{lambda}kappa.
    Proof.
      Let f /in M.
      Take a zfset v such that v /in kappa /\ f : lambda /rightarrow v.
      v /subset kappa.
      Then f : lambda /rightarrow kappa.
      Then f /in ^{lambda}kappa.
    end.
    ^{lambda}kappa /subset M.
    Proof.
      Let f /in ^{lambda}kappa.
      Then /bigcup ran(f) /in kappa.
      Take a zfset v such that v /in kappa /\ v = /bigcup ran(f).
      v is an ordinal.
      Then f : lambda /rightarrow v+'1.
      Proof.
        Dom(f) = lambda.
        Let a /in lambda.
        Then f[a] /in ran(f).
        Then f[a] /subset v.
        f[a],v /in /Ord.
        Then f[a] /in v \/ f[a] = v.
        Then f[a] /in v++.
      end.
      kappa /in /Lim.
      Then v++ /in kappa.
      Then f /in M.      
    end.
  end.
  kappa, lambda are cardinals.
  Card(^{lambda}kappa) = kappa ^ lambda.
  Then Card(M) = kappa ^ lambda.
  
  Define seq[v] = Card(^{lambda}v) for v in kappa.
  Then seq is a sequence of cardinals.
  Proof.
    Let v /in kappa. Then seq[v] /in /Cd.
  end.
  
  M, /sumset seq are zfsets.
  Card(M) /subset Card(/sumset seq).
  Proof.
    Forall v /in kappa exists f (f : ^{lambda}v /leftrightarrow Card(^{lambda}v)).
    Define bij[v] = (choose a zffunction psi such that psi : ^{lambda}v /leftrightarrow Card(^{lambda}v) in psi)
    for v in kappa.
    Forall v /in kappa forall f (f : lambda /rightarrow v => f /in Dom(bij[v])).
    Define phi[f] = (choose a zfset v such that v /in kappa /\ f : lambda /rightarrow v in ((bij[v])[f],v)) for f in M.
    Then phi : M /rightarrow /sumset seq.
    Proof.
      Let f /in M.
      Take a zfset v such that v /in kappa /\ f : lambda /rightarrow v /\ phi[f] = ((bij[v])[f],v).
      Then (bij[v])[f] /in seq[v].
      Then phi[f] /in /sumset seq.
    end.
    phi is injective.
    Proof.
      Let f1,f2 /in M. Let f1 /neq f2.
      Take a zfset v1 such that v1 /in kappa /\ f1 : lambda /rightarrow v1 /\ phi[f1] = ((bij[v1])[f1],v1).
      Take a zfset v2 such that v2 /in kappa /\ f2 : lambda /rightarrow v2 /\ phi[f2] = ((bij[v2])[f2],v2).
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
  
  /sumset seq /subset kappa /times kappa.
  Proof.
    Let pair /in /sumset seq.
    Take zfsets a,b such that b /in kappa /\ a /in seq[b] /\ pair = (a,b).
    ^{lambda}b is a zfset.
    seq[b] = Card(^{lambda}b).
    Card(^{lambda}b) = Card(b) ^ lambda.
    Card(b) /in /Cd /cap kappa.
    Then Card(b) ^ lambda /in kappa.
    Then seq[b] /in kappa.
    Then a /in kappa.
    Then (a,b) /in kappa /times kappa.
  end.
  Then Card(/sumset seq) /subset Card(kappa /times kappa).
  Card(kappa /times kappa) = kappa * kappa.
  kappa * kappa = kappa.
  Then Card(/sumset seq) /subset kappa.
  
  Then Card(M) /subset kappa.
  Then kappa ^ lambda /subset kappa.
  
qed.


Definition. Let f,g be zffunctions. f and g are diagcomposable iff Dom(f) = Dom(g) /\ forall i /in Dom(f) ((f[i] is a zffunction) /\ g[i] /in Dom(f[i])).


Lemma. Let f,g be zffunction. Let f and g be diagcomposable. Then exists h (Dom(h) = Dom(f) /\ forall i /in Dom(f) h[i] = (f[i])[g[i]]).
Proof.
  Define h[i] = (f[i])[g[i]] for i in Dom(f).
  Then h is a zffunction.
  Proof.
    Let i /in Dom(f).
    Then h[i] = (f[i])[g[i]].
    f[i] is a zffunction.
    Then (f[i])[g[i]] /in /VV.
  end.
qed.


Definition. Let f,g be zffunction. Let f and g be diagcomposable.
The diagcomposition of f and g is a zffunction h such that (Dom(h) = Dom(f) /\ forall i /in Dom(f) h[i] = (f[i])[g[i]]).
Let g /comp f stand for the diagcomposition of f and g.


Lemma. Let kappa, lambda /in /Card. Let lambda /in kappa. Let forall xi /in /Cd /cap kappa (xi ^ lambda /in kappa). Let cof(kappa) /subset lambda.
Then kappa ^ lambda = Gimel[kappa].
Proof.
  Gimel[kappa] /subset kappa ^ lambda.
  Proof.
    Gimel[kappa] = kappa ^ cof(kappa).
    kappa ^ cof(kappa) /subset kappa ^ lambda.
    Proof.
      kappa, cof(kappa), lambda /in /Cd.
      0 /in kappa.
      cof(kappa) /subset lambda.
      Then kappa ^ cof(kappa) /subset kappa ^ lambda (by ExpSubset).
    end.
  end.
  
  Take an ordinal alpha such that kappa = Alef[alpha].
  alpha /in /Lim.
  Proof by contradiction. Assume the contrary.
    alpha /neq 0.
    Then alpha /in /Succ.
    Take an ordinal beta such that alpha = beta +' 1.
    cof(Alef[beta +' 1]) = Alef[beta +' 1].
    Alef[beta +' 1] = kappa.
    Then cof(kappa) = kappa.
    Contradiction.
  end.
  Then cof(kappa) = cof(alpha).
  cof(alpha) /in cofset2(alpha).
  Take a zfset xa such that xa /subset alpha /\ xa /cof alpha /\ otp(xa) = cof(alpha).
  Let x = Alef^[xa].
  x /subset kappa.
  Proof.
    Let y /in x.
    Take a zfset ya such that ya /in xa /\ y = Alef[ya].
    Then ya /in alpha.
    Then Alef[ya] /in Alef[alpha].
    Then y /in kappa.
  end.
  x /cof kappa.
  Proof.
    Let lam /in kappa.
    alpha /in /Lim.
    Then Alef[alpha] = /bigcup Alef^[alpha].
    Take a zfset beta such that beta /in alpha /\ lam /in Alef[beta].
    Take a zfset b such that b /in xa /\ beta /in b.
    Then Alef[beta] /subset Alef[b].
    Then lam /in Alef[b].
    Alef[b] /in x.
  end.
  otp(x) = cof(kappa).
  Proof.
    cof(kappa) = otp(xa).
    Exists f (f : cof(kappa) /leftrightarrow xa /\ (f is an epsiso)).
    Proof.
      xa /in /VV. xa /subset /Ord. cof(kappa) = otp(xa).
    end.
    Take a zffunction f such that f : cof(kappa) /leftrightarrow xa /\ (f is an epsiso).
    Let g = Alef /circ f.
    g : cof(kappa) /rightarrow x.
    Proof.
      Dom(g) = cof(kappa).
      Let i /in cof(kappa).
      Then f[i] /in xa.
      Then Alef[f[i]] /in x.
      Then g[i] /in x.
    end.
    Alef is an epsiso.
    ran(f) /subset Dom(Alef).
    Then Alef /circ f is an epsiso.
    Then g is an epsiso.
    ran(g) = x.
    Proof.
      Let y /in x.  
      Take a zfset ya such that ya /in xa /\ y = Alef[ya].
      Take a zfset za such that za /in cof(kappa) /\ f[za] = ya.
      Then g[za] = y.
      Then y /in ran(g).
    end.
    Then g : cof(kappa) /leftrightarrow x.
    g^{-1} : x /leftrightarrow cof(kappa).
    x /subset /Ord.
    cof(kappa) /subset /Ord.
    g^{-1} is an epsiso.
    Then otp(x) = cof(kappa).
  end.
  Exists f (f : cof(kappa) /leftrightarrow x /\ (f is an epsiso)).
  Proof.
    x /in /VV. x /subset /Ord. cof(kappa) = otp(x).
  end.
  Take a zffunction xi such that xi : cof(kappa) /leftrightarrow x /\ (xi is an epsiso).
  Forall i1,i2 /in cof(kappa) (i1 /in i2 iff xi[i1] /in xi[i2]) (by epsiso).
  Forall i /in cof(kappa) xi[i] /in /Card.
  Proof.
    Let i /in cof(kappa).
    Then xi[i] /in x.
    Take a zfset j such that j /in xa /\ xi[i] = Alef[j].
    Alef[j] /in /Cd.
    /NN /subset Alef[j].
    Then Alef[j] /in /Card.
  end.
  Card(x) = cof(kappa).
  
  Forall o1,o2 ((o1,o2) /in cof(kappa) /times ^{lambda}kappa => (o1 /in cof(kappa) /\ o2 /in ^{lambda}kappa)).
  Forall i /in cof(kappa) forall f /in ^{lambda}kappa ran(f) /subset Dom(delta(xi[i])).
 
  Define F[(i,f)] = delta(xi[i]) /circ f for (i,f) in cof(kappa) /times ^{lambda}kappa.

  F is a zffunction.
  Proof.
    Let pair /in cof(kappa) /times ^{lambda}kappa.
    Take zfsets i,f such that i /in cof(kappa) /\ f /in ^{lambda}kappa /\ pair = (i,f).
    F[pair] = delta(xi[i]) /circ f.
    delta(xi[i]) /circ f is a zffunction.
    Dom(delta(xi[i]) /circ f) = lambda.
    Then Dom(delta(xi[i]) /circ f) /in /VV.
    Then (delta(xi[i]) /circ f) /in /VV.
    Then F[pair] /in /VV.
  end.  
  Forall i /in cof(kappa) forall f /in ^{lambda}kappa (i,f) /in Dom(F).
  Forall f /in ^{lambda}kappa (F{cof(kappa),^{lambda}kappa}(-,f) is a zffunction).
  
  Define G[f] = F{cof(kappa),^{lambda}kappa}(-,f) for f in ^{lambda}kappa.

  Forall f /in ^{lambda}kappa forall i /in cof(kappa) F[(i,f)] /in ^{lambda}(xi[i]).
  Proof.
    Let f /in ^{lambda}kappa.
    Let i /in cof(kappa).
    Then F[(i,f)] = (delta(xi[i])) /circ f.
    (delta(xi[i])) /circ f is a zffunction.
    Dom((delta(xi[i])) /circ f) = lambda.
    ((delta(xi[i])) /circ f) : lambda /rightarrow xi[i].
    Proof.
      Let j /in lambda.
      f : lambda /rightarrow kappa.
      f[j] /in kappa.
      Then f[j] /in Dom(delta(xi[i])).
      ((delta(xi[i])) /circ f)[j] = (delta(xi[i]))[f[j]].
      Then ((delta(xi[i])) /circ f)[j] /in xi[i].
      Proof.
        Case f[j] /in xi[i]. Then (delta(xi[i]))[f[j]] = f[j]. end.
        Case f[j] /notin xi[i]. Then f[j] /in /VV /setminus xi[i]. Then (delta(xi[i]))[f[j]] = 0. end.
      end.
    end.
    Then ((delta(xi[i])) /circ f) /in ^{lambda}(xi[i]).
  end.
  Then forall f /in ^{lambda}kappa forall i /in cof(kappa) (i /in Dom(G[f]) /\ (G[f])[i] /in ^{lambda}(xi[i])).
  Proof.
    Let f /in ^{lambda}kappa.
    Then G[f] = F{cof(kappa),^{lambda}kappa}(-,f).
    Let i /in cof(kappa).
    Then i /in Dom(G[f]).
    (G[f])[i] = F[(i,f)].
    Then (G[f])[i] /in ^{lambda}(xi[i]).
  end.
  
  G is a zffunction.
  Proof.
    Dom(G) = ^{lambda}kappa.
    Forall f /in ^{lambda}kappa G[f] /in /VV.
    Proof.
      Let f /in ^{lambda}kappa.
      Let g = G[f].
      g = F{cof(kappa),^{lambda}kappa}(-,f).
      g is a zffunction.
      Dom(g) = cof(kappa).
      Dom(g) /in /VV.
      Then g /in /VV.
    end.
  end.
  G is injective.
  Proof.
    Let f1, f2 /in Dom(G). Let f1 /neq f2.
    Then G[f1] /neq G[f2].
    Proof.
      Exists a /in lambda (f1[a] /neq f2[a]).
      Proof by contradiction. Assume the contrary.
        f1,f2 are functions.
        Dom(f1) = Dom(f2).
        Dom(f1) = lambda.
        Forall a /in Dom(f1) f1[a] = f2[a].
        Then f1 = f2.
        Contradiction.
      end.
      Take a zfset a such that a /in lambda /\ f1[a] /neq f2[a].
      f1 : lambda /rightarrow kappa.
      Then f1[a] /in kappa.
      Take a zfset i1 such that i1 /in cof(kappa) /\ f1[a] /in xi[i1].
      f2 : lambda /rightarrow kappa.
      Then f2[a] /in kappa.
      Take a zfset i2 such that i2 /in cof(kappa) /\ f2[a] /in xi[i2].
      Exists i /in cof(kappa) (xi[i1] /subset xi[i] /\ xi[i2] /subset xi[i]).
      Proof.
        i1,i2 /in /Ord.
        Then i1 /in i2 \/ i2 /in i1 \/ i1 = i2.
        Case i1 = i2. end.
        Case i1 /in i2.
          Then xi[i1] /subset xi[i2].
        end.
        Case i2 /in i1.
          Then xi[i2] /subset xi[i1].
        end.
      end.
      Take a zfset i such that i /in cof(kappa) /\ (xi[i1] /subset xi[i] /\ xi[i2] /subset xi[i]).
      Then f1[a] /in xi[i] /\ f2[a] /in xi[i].
      Then (G[f1])[i] /neq (G[f2])[i].
      Proof.
        (G[f1])[i] = F[(i,f1)].
        F[(i,f1)] = (delta(xi[i])) /circ f1.
        f1[a] /in xi[i].
        Then (delta(xi[i]))[f1[a]] = f1[a].
        Then ((delta(xi[i])) /circ f1)[a] = f1[a].
        Then (F[(i,f1)])[a] = f1[a].
  
        (G[f2])[i] = F[(i,f2)].
        F[(i,f2)] = (delta(xi[i])) /circ f2.
        f2[a] /in xi[i].
        Then (delta(xi[i]))[f2[a]] = f2[a].
        Then ((delta(xi[i])) /circ f2)[a] = f2[a].
        Then (F[(i,f2)])[a] = f2[a].
        
        Then F[(i,f1)] /neq F[(i,f2)].
        Then (G[f1])[i] /neq (G[f2])[i].
      end.
      Then G[f1] /neq G[f2].
    end.
  end.
  
  Forall i /in cof(kappa) Card(^{lambda}(xi[i])) /in kappa.
  Proof.
    Let i /in cof(kappa).
    Then xi[i] /in kappa.
    Then xi[i] ^ lambda /in kappa.
    Card(^{lambda}(xi[i])) = xi[i] ^ lambda.
  end.
  Forall i /in cof(kappa) exists f (f : ^{lambda}(xi[i]) /rightarrow kappa /\ (f is injective)).
  Proof.
    Let i /in cof(kappa).
    Then Card(^{lambda}(xi[i])) /subset Card(kappa).
  end.
  Define inj[i] = (Choose a zffunction f such that (f : ^{lambda}(xi[i]) /rightarrow kappa /\ (f is injective)) in f) for i in cof(kappa).
  inj is a zffunction.
  Proof.
    Let i /in cof(kappa).
    Then inj[i] is a zffunction.
    Dom(inj[i]) /in /VV.
    Then inj[i] /in /VV.
  end.
  
  Forall f /in ^{lambda}kappa forall i /in cof(kappa) (G[f])[i] /in Dom(inj[i]).
  Proof.
    Let f /in ^{lambda}kappa.
    Forall i /in cof(kappa) (G[f])[i] /in ^{lambda}xi[i].
  end.
  Forall f /in ^{lambda}kappa exists g (Dom(g) = cof(kappa) /\ (forall i /in cof(kappa) (g[i] = (inj[i])[(G[f])[i]]))).
  Proof.
    Let f /in ^{lambda}kappa.
    Then exists g (Dom(g) = cof(kappa) /\ (forall i /in cof(kappa) (g[i] = (inj[i])[(G[f])[i]]))).
    Proof.
      Define g[i] = (inj[i])[(G[f])[i]] for i in cof(kappa).
      g is a zffunction.
      Proof.
        Let i /in cof(kappa).
        Then g[i] = (inj[i])[(G[f])[i]].
        Then g[i] /in ran(inj[i]).
        Then g[i] /in /VV.
      end.
      Dom(g) = cof(kappa) /\ (forall i /in cof(kappa) (g[i] = (inj[i])[(G[f])[i]])).
    end.
  end.
  
  Card(G^[^{lambda}kappa]) /subset Card(^{cof(kappa)}kappa).
  Proof.
    Let M = G^[^{lambda}kappa].
    Forall g /in M ((g is a zffunction) /\ Dom(g) = cof(kappa) /\ forall i /in cof(kappa) g[i] /in ^{lambda}(xi[i])).
    Proof.
      Let g /in M.
      Then g /in G^[^{lambda}kappa]. 
      Take a zfset f such that f /in ^{lambda}kappa /\ g = G[f].
      g = F{cof(kappa),^{lambda}kappa}(-,f).
      Then Dom(g) = cof(kappa).
      Forall i /in cof(kappa) (F{cof(kappa),^{lambda}kappa}(-,f))[i] = F[(i,f)].
      Proof.
        Let i /in cof(kappa).
        Let A = cof(kappa).
        Let B = ^{lambda}kappa.
        (F{A,B}(-,f))[i] = F[(i,f)].
      end.
      Forall i /in cof(kappa) g[i] = F[(i,f)].
      Forall i /in cof(kappa) g[i] /in ^{lambda}(xi[i]).
      Proof.
        Let i /in cof(kappa).
        Then g[i] = F[(i,f)].
        F[(i,f)] /in ^{lambda}(xi[i]).
      end.
    end.
    Forall g /in M (inj, g are zffunctions).
    Forall g /in M (inj and g are diagcomposable).
    Proof.
      Let g /in M.
      g, inj are zffunctions.
      Dom(g) = Dom(inj).
      Forall i /in Dom(inj) ((inj[i] is a zffunction) /\ g[i] /in Dom(inj[i])).
    end.
    Forall g /in M g /comp inj /in ^{cof(kappa)}kappa.
    Proof.
      Let g /in M.
      g /comp inj is a zffunction.
      Dom(g /comp inj) = cof(kappa).
      g /comp inj : cof(kappa) /rightarrow kappa.
      Proof.
        Let i /in cof(kappa).
        Then (g /comp inj)[i] = (inj[i])[g[i]].
        inj[i] : ^{lambda}(xi[i]) /rightarrow kappa.
        g[i] /in ^{lambda}(xi[i]).
        Then g[i] /in Dom(inj[i]).
        Then (inj[i])[g[i]] /in kappa.
        Then (g /comp inj)[i] /in kappa.
      end.
    end.
    Define H[g] = g /comp inj for g in M.
    H : M /rightarrow ^{cof(kappa)}kappa.
    Proof.
      Let N = ^{cof(kappa)}kappa.
      Forall g /in M H[g] /in N.
      Proof.
        Let g /in M.
        Then H[g] = g /comp inj.
        Then H[g] /in ^{cof(kappa)}kappa.
      end.
      Then H : M /rightarrow N.
    end.
    H is injective.
    Proof.
      Let g1,g2 /in M. Let g1 /neq g2.
      Then H[g1] /neq H[g2].
      Proof.
        Exists i /in cof(kappa) (g1[i] /neq g2[i]).
        Proof by contradiction. Assume the contrary.
          g1,g2 are functions.
          Dom(g1) = Dom(g2).
          Dom(g1) = cof(kappa).
          Forall i /in Dom(g1) g1[i] = g2[i].
          Then g1 = g2.
          Contradiction.
        end.
        Take a zfset i such that i /in cof(kappa) /\ g1[i] /neq g2[i].
        (H[g1])[i] = (g1 /comp inj)[i].
        (g1 /comp inj)[i] = (inj[i])[g1[i]].
        (H[g2])[i] = (g2 /comp inj)[i].
        (g2 /comp inj)[i] = (inj[i])[g2[i]].
        inj[i] is injective.
        g1[i] /neq g2[i].
        Then (inj[i])[g1[i]] /neq (inj[i])[g2[i]].
        Proof.
          Let a = g1[i].
          Let b = g2[i].
          a,b /in Dom(inj[i]).
          a /neq b.
          inj[i] is injective.
          Then (inj[i])[a] /neq (inj[i])[b].
        end.
        Then (H[g1])[i] /neq (H[g2])[i].
        Then H[g1] /neq H[g2].
      end.
    end.
    Then Card(M) /subset Card(^{cof(kappa)}kappa).
    Card(M) = Card(G^[^{lambda}kappa]).
  end.
  
  Card(G^[^{lambda}kappa]) = Card(^{lambda}kappa).
  Proof.
    Let M = ^{lambda}kappa.
    G is a zffunction.
    G is injective.
    Dom(G) = M.
    ran(G) = G^[M].
    Then G : M /leftrightarrow G^[M].
    Then Card(M) = Card(G^[M]).
  end.
  Then Card(G^[^{lambda}kappa]) /subset Card(^{cof(kappa)}kappa).
  Card(^{lambda}kappa) = kappa ^ lambda.
  Card(^{cof(kappa)}kappa) = kappa ^ cof(kappa).
  kappa ^ cof(kappa) = Gimel[kappa].
  Then kappa ^ lambda /subset Gimel[kappa].
  
  Then kappa ^ lambda = Gimel[kappa].  
qed.







