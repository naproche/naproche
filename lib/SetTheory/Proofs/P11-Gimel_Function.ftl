[read Formalizations/Library/L10-Koenigs_Lemma.ftl]

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
Proof.
  Let lambda /in /Lim.
  Beth[lambda] = {zfset x | exists alpha /in lambda x /in Beth[alpha]}.
  Beth[lambda] /subset /bigcup Beth^[lambda].
  Proof.
    Let x /in Beth[lambda].
    Take a zfset alpha such that alpha /in lambda /\ x /in Beth[alpha].
    Then x /in /bigcup Beth^[lambda].
  end.
  /bigcup Beth^[lambda] /subset Beth[lambda].
qed.


Lemma. Forall alpha /in /Ord /NN /subset Beth[alpha].
Proof by induction.
  Let alpha /in /Ord.
  Forall gamma /in alpha /NN /subset Beth[gamma].
  Proof.
    Let gamma /in alpha.
    Then gamma -<- alpha.
  end.
  Then alpha = 0 \/ alpha /in /Lim \/ alpha /in /Succ.
  Case alpha = 0.
  end.
  Case alpha /in /Succ.
    Let gamma = alpha --.
    Then Beth[alpha] = 2 ^ Beth[gamma].
    gamma /in alpha.
    /NN /subset Beth[gamma].
  end.
  Case alpha /in /Lim.
    Then 0 /in alpha.
    Beth[0] /in Beth^[alpha].
    Then Beth[0] /subset /bigcup Beth^[alpha].
  end.
qed.


Lemma. Forall alpha /in /Ord forall beta /in alpha (Beth[beta] /in Beth[alpha]).
Proof by induction.
  Let alpha /in /Ord.
  Forall gamma /in alpha forall beta /in gamma Beth[beta] /in Beth[gamma].
  Proof.
    Let gamma /in alpha.
    Then gamma -<- alpha.
    Then forall beta /in gamma Beth[beta] /in Beth[gamma].
  end.
  Case alpha = 0.
  end.
  Case alpha /in /Succ.
    Let gamma = alpha --.
    gamma /in alpha.
    Beth[alpha] = 2 ^ Beth[gamma].
    Then forall beta /in alpha Beth[beta] /in Beth[alpha].
    Proof.
      Let beta /in alpha.
      Then beta /in gamma \/ beta = gamma.
      Case beta = gamma.
        Beth[gamma] /in Beth[alpha].
      end.
      Case beta /in gamma.
        Then Beth[beta] /in Beth[gamma].
        Beth[gamma] /subset Beth[alpha].
      end.
    end.
  end.
  Case alpha /in /Lim.
    Then Beth[alpha] = /bigcup Beth^[alpha].
    Forall beta /in alpha Beth[beta] /in Beth[alpha].
    Proof.
      Let beta /in alpha.
      Then beta +' 1 /in alpha.
      Beth[beta] /in Beth[beta +' 1].
      Then Beth[beta] /in /bigcup Beth^[alpha].
    end.
  end.
qed.


Lemma. Forall alpha, beta /in /Ord (alpha /in beta iff Beth[alpha] /in Beth[beta]).
Proof.
  Let alpha, beta /in /Ord.
  Let Beth[alpha] /in Beth[beta].
  Then alpha /in beta.
  Proof.
    alpha /in beta \/ beta /in alpha \/ alpha = beta (by TotalOrder).
  end.
qed.


Lemma. Forall alpha, beta /in /Ord (alpha /subset beta iff Beth[alpha] /subset Beth[beta]).


Lemma. Beth is injective.
Proof.
  Let alpha, beta /in /Ord.
  Let alpha /neq beta.
  Then alpha /in beta \/ beta /in alpha (by TotalOrder).
  Then Beth[alpha] /in Beth[beta] \/ Beth[beta] /in Beth[alpha].
  Then Beth[alpha] /neq Beth[beta].
qed.


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
Proof.
  Dom(Gimel) = /Card.
  Let kappa /in /Card.
  Gimel[kappa] /in /VV.
  Gimel[kappa] /in /Card.
qed.


Signature. Let kappa /in /Cd. Let lambda /in /Card. kappa ^< lambda is a set.
Axiom. Let kappa /in /Cd. Let lambda /in /Card. kappa ^< lambda = {zfset x | exists v /in lambda x /in kappa ^ Card(v)}.


Signature. Exp is a function.
Axiom. Dom(Exp) = /Cd /times /Ord.
Lemma. Forall o1,o2 ((o1,o2) /in /Cd /times /Ord => o1 /in /Cd /\ o2 /in /Ord).
Axiom. Let a,b be objects. Let (a,b) /in /Cd /times /Ord. Then Exp[(a,b)] = a ^ Card(b).
Lemma. Exp : /Cd /times /Ord /rightarrow /Cd.
Proof.
  Let pair /in /Cd /times /Ord.
  Take zfsets a,b such that a /in /Cd /\ b /in /Ord /\ pair = (a,b).
  Then Exp[pair] = a ^ Card(b).
  a ^ Card(b) /in /Cd.
  Then Exp[pair] /in /Cd.
qed.


Lemma. Let kappa /in /Cd. Then Exp{/Cd,/Ord}(kappa,-) : /Ord /rightarrow /Cd.
Proof.
  Dom(Exp{/Cd,/Ord}(kappa,-)) = /Ord.
  Let v /in /Ord. 
  Then (kappa,v) /in /Cd /times /Ord.
  (Exp{/Cd,/Ord}(kappa,-))[v] = Exp[(kappa,v)].
  Exp[(kappa,v)] /in /Cd.
  Then (Exp{/Cd,/Ord}(kappa,-))[v] /in /Cd.  
qed.


Signature. Let kappa /in /Cd. Cont(kappa) is a function.
Axiom. Let kappa /in /Cd. Dom(Cont(kappa)) = /Ord.
Axiom. Let kappa /in /Cd. Let alpha /in /Ord. Then (Cont(kappa))[alpha] = kappa ^ Card(alpha).
Lemma. Let kappa /in /Cd. Cont(kappa) : /Ord /rightarrow /Cd.
Proof.
  Dom(Cont(kappa)) = /Ord.
  Let alpha /in /Ord.
  Then Card(alpha) /in /Cd.
  (Cont(kappa))[alpha] = kappa ^ Card(alpha).
  (Cont(kappa))[alpha] /in /VV.
  (Cont(kappa))[alpha] /in /Cd.
qed.


Lemma. Let kappa /in /Cd. Let lambda /in /Card. kappa ^< lambda = /bigcup (Cont(kappa))^[lambda].
Proof.
  kappa ^< lambda /subset /bigcup (Cont(kappa))^[lambda].
  Proof.
    Let x /in kappa ^< lambda.
    Exists v /in lambda x /in kappa ^ Card(v).
    Take a zfset v such that v /in lambda /\ x /in kappa ^ Card(v).
    Then x /in (Cont(kappa))[v].
    (Cont(kappa))[v] /in (Cont(kappa))^[lambda].
    Then x /in /bigcup (Cont(kappa))^[lambda].
  end.
  /bigcup (Cont(kappa))^[lambda] /subset kappa ^< lambda.
  Proof.
    Let x /in /bigcup (Cont(kappa))^[lambda].
    Take a zfset y such that y /in (Cont(kappa))^[lambda] /\ x /in y.
    Take a zfset a such that a /in lambda /\ y = (Cont(kappa))[a].
    Then x /in kappa ^ Card(a).
    Then exists v /in lambda x /in kappa ^ Card(v).
    Then x /in kappa ^< lambda.
  end.
qed.


Lemma. Let kappa /in /Cd. Let lambda /in /Card. Then kappa ^< lambda /in /Cd.
Proof.
  (Cont(kappa))^[lambda] /subset /Cd.
  Proof.
    ran(Cont(kappa)) /subset /Cd.
  end.
  (Cont(kappa))^[lambda] /in /VV.
  Then /bigcup (Cont(kappa))^[lambda] /in /Cd.
qed.


Lemma. Let kappa /in /Card. Then 2 ^< kappa /in /Card.
Proof.
  2 ^< kappa /in /Cd.
  /NN /subset 2 ^< kappa.
  Proof.
    Let n /in /NN.
    2 ^< kappa = {zfset x | exists v /in kappa x /in 2 ^ Card(v)}.
    n /in kappa.
    Card(n) = n.
    Then n /in 2 ^ Card(n).
    Then n /in 2 ^< kappa.
  end.
qed.


Lemma. Forall kappa /in /Card (Gimel[kappa] /in /Card /\ kappa /in Gimel[kappa]).
Proof.
  Let kappa /in /Card.
  cof(kappa) /in cofset2(kappa).
  Take a zfset x such that x /subset kappa /\ x /cof kappa /\ Card(x) = cof(kappa).
  Take a zffunction f such that f : Card(x) /leftrightarrow x.
  Define sum[i] = Card(f[i]) for i in Card(x).
  Then sum is a sequence of cardinals.
  Proof.
    Let i /in Card(x). Then sum[i] /in /Cd.
  end.
  kappa /subset /sum sum.
  Proof. 
    Define bij[i] = (choose a zffunction g such that g : i /leftrightarrow Card(i) in g) for i in kappa.
    Forall i /in kappa exists a /in Card(x) (i /in f[a]).
    Proof.
      Let i /in kappa.
      x /cof kappa.
      Take a zfset y such that y /in x /\ i /in y.
      Take a zfset z such that z /in Card(x) /\ f[z] = y.
    end.
    Forall a /in Card(x) (f[a] /in kappa /\ Dom(bij[f[a]]) = f[a]).
    Define inc[i] = (choose a zfset a such that a /in Card(x) /\ i /in f[a] in ((bij[f[a]])[i],a)) for i in kappa.
    Then inc : kappa /rightarrow /sumset sum.
    Proof.
      Let i /in kappa.
      Take a zfset a such that a /in Card(x) /\ i /in f[a] /\ inc[i] = ((bij[f[a]])[i],a).
      Then (bij[f[a]])[i] /in Card(f[a]).
      Then (bij[f[a]])[i] /in sum[a].
      Then inc[i] /in /sumset sum.
    end.
    inc is injective.
    Proof.
      Let i1, i2 /in kappa. Let i1 /neq i2.
      Then inc[i1] /neq inc[i2].
      Proof.
        Take a zfset a1 such that a1 /in Card(x) /\ i1 /in f[a1] /\ inc[i1] = ((bij[f[a1]])[i1],a1).
        Take a zfset a2 such that a2 /in Card(x) /\ i2 /in f[a2] /\ inc[i2] = ((bij[f[a2]])[i2],a2).
        Case a1 /neq a2. Then ((bij[f[a1]])[i1],a1) /neq ((bij[f[a2]])[i2],a2). end.
        Case a1 = a2. 
          bij[f[a1]] is injective.
          Then (bij[f[a1]])[i1] /neq (bij[f[a1]])[i2].
          Then ((bij[f[a1]])[i1],a1) /neq ((bij[f[a2]])[i2],a2).
        end.
      end.
    end.
    Then Card(kappa) /subset Card(/sumset sum).
    Then kappa /subset /sum sum.
  end.
  Then kappa /in /sum sum \/ kappa = /sum sum.
  Proof.
    kappa, /sum sum /in /Ord.
  end.
  
  Define prod[i] = kappa for i in cof(kappa).
  Then prod is a sequence of cardinals.
  /prod prod = Gimel[kappa].
  Proof.
    /prodset prod /subset ^{cof(kappa)}kappa.
    Proof.
      Let func /in /prodset prod.
      Then func is a zffunction.
      Dom(func) = cof(kappa).
      Forall i /in Dom(func) (func[i] /in prod[i]).
      Forall i /in cof(kappa) prod[i] = kappa.
      Then forall i /in cof(kappa) func[i] /in kappa.
      Then func : cof(kappa) /rightarrow kappa.
    end.
    ^{cof(kappa)}kappa /subset /prodset prod.
    Proof.
      Let func /in ^{cof(kappa)}kappa.
      Then func : cof(kappa) /rightarrow kappa.
      Dom(func) = cof(kappa).
      Forall i /in cof(kappa) func[i] /in kappa.
      Then forall i /in cof(kappa) func[i] /in prod[i].
      Then func /in /prodset prod.
    end.
    Then /prodset prod = ^{cof(kappa)}kappa.
    Then Card(/prodset prod) = Card(^{cof(kappa)}kappa).
  end.
  
  Dom(sum) = Dom(prod).
  Forall i /in Dom(sum) sum[i] /in prod[i].
  Proof.
    Let i /in Dom(sum).
    Then i /in Card(x).
    Then f[i] /in x.
    Then f[i] /in kappa.
    Then Card(f[i]) /in kappa.
    sum[i] = Card(f[i]).
    prod[i] = kappa.
  end.
  Then /sum sum /in /prod prod (by Koenig).
  Then kappa /in /prod prod.
  Proof.
    /prod prod /in /Ord.
    kappa /in /sum sum \/ kappa = /sum sum.
    Case kappa = /sum sum. end.
    Case kappa /in /sum sum. 
      /sum sum /in /prod prod.
      Trans(/prod prod).
    end.
  end.
qed.


Lemma. Let kappa /in /Card. Let cof(kappa) = kappa. Then Gimel[kappa] = 2 ^ kappa.
Proof.
  2 /subset kappa.
  kappa /subset 2 ^ kappa.
  Then kappa ^ kappa = 2 ^ kappa.
  Gimel[kappa] = kappa ^ kappa.
qed.


Lemma. Let kappa /in /Card. Let cof(kappa) /in kappa. Then 2 ^ kappa /subset (2 ^< kappa) ^ cof(kappa).
Proof.
  Take a zfset x such that x /subset kappa /\ x /cof kappa /\ otp(x) = cof(kappa).
  Exists f (f : cof(kappa) /leftrightarrow x /\ (f is an epsiso)).
  Proof.
    x /in /VV. x /subset /Ord. cof(kappa) = otp(x).
  end.
  Take a zffunction kap such that kap : otp(x) /leftrightarrow x /\ (kap is an epsiso).
  Forall i /in cof(kappa) Card(/PP kap[i]) /subset 2 ^< kappa.
  Proof.
    Let i /in cof(kappa).
    kap[i] /in kappa.
    Card(/PP kap[i]) = 2 ^ Card(kap[i]).
    2 ^< kappa = {zfset x | exists v /in kappa x /in 2 ^ Card(v)}.
    Then 2 ^ Card(kap[i]) /subset 2 ^< kappa.
  end.
  Forall i /in cof(kappa) exists f (f : /PP kap[i] /rightarrow 2 ^< kappa /\ (f is injective)).
  Proof.
    Let i /in cof(kappa).
    Card(/PP kap[i]) /subset Card(2 ^< kappa).
    /PP kap[i] <= 2 ^< kappa.
  end.
  Define inj[i] = (Choose a zffunction f such that (f : /PP kap[i] /rightarrow 2 ^< kappa /\ (f is injective)) in f)
  for i in cof(kappa).
  
  Forall o1,o2 ((o1,o2) /in /PP kappa /times cof(kappa) => o1 /in /PP kappa /\ o2 /in cof(kappa)).
  Forall M /in /PP kappa forall i /in cof(kappa) (M /cap kap[i] /in Dom(inj[i])).
  Proof.
    Let M /in /PP kappa.
    Let i /in cof(kappa).
    Dom(inj[i]) = /PP kap[i].
    M /cap kap[i] /subset kap[i].
    M /cap kap[i] /in /PP kap[i].
  end.
  
  Define Fun[(M,i)] = (inj[i])[M /cap kap[i]] for (M,i) in /PP kappa /times cof(kappa).
  
  Fun is a zffunction.
  Proof.
    Let pair /in /PP kappa /times cof(kappa).
    Take zfsets M,i such that M /in /PP kappa /\ i /in cof(kappa) /\ pair = (M,i).
    Then Fun[pair] = (inj[i])[M /cap kap[i]].
    (inj[i])[M /cap kap[i]] /in ran(inj[i]).
    Then (inj[i])[M /cap kap[i]] /in /VV.
    Then Fun[pair] /in /VV.
  end.
  Dom(Fun) = /PP kappa /times cof(kappa).
  /PP kappa, cof(kappa) are sets.
  kappa is a zfset. kappa /in /Lim.
  Forall M /in /PP kappa (Fun{/PP kappa,cof(kappa)}(M,-) is a zffunction).
  Define G[M] = Fun{/PP kappa,cof(kappa)}(M,-) for M in /PP kappa.
  
  G : /PP kappa /rightarrow ^{cof(kappa)}(2 ^< kappa).
  Proof.
    Let alpha = ^{cof(kappa)}(2 ^< kappa).
    Forall M /in Dom(G) G[M] /in alpha.
    Proof.
      Let M /in Dom(G).
      Then M /in /PP kappa.
      Then G[M] = Fun{/PP kappa,cof(kappa)}(M,-).
      Let f = G[M].
      Then f : cof(kappa) /rightarrow 2 ^< kappa.
      Proof.
        Let i /in cof(kappa).
        Then f[i] = Fun[(M,i)].
        Fun[(M,i)] = (inj[i])[M /cap kap[i]].
        inj[i] : /PP kap[i] /rightarrow 2 ^< kappa.
        Then ran(inj[i]) /subset 2 ^< kappa.
        M /cap kap[i] /in Dom(inj[i]).
        Then (inj[i])[M /cap kap[i]] /in 2 ^< kappa.
        Then f[i] /in 2 ^< kappa.
      end.
      Then f /in ^{cof(kappa)}(2 ^< kappa).
      Then G[M] /in alpha.
    end.
    Then G : /PP kappa /rightarrow alpha.
  end.
  
  G is injective.
  Proof.
    Forall M1, M2 /in Dom(G) (M1 /neq M2 => G[M1] /neq G[M2]).
    Proof.
      Let M1, M2 /in /PP kappa.
      Let M1 /neq M2.
      Then exists z (z /in M1 /setminus M2 \/ z /in M2 /setminus M1).
      Proof.
        (not (M1 /subset M2)) \/ (not (M2 /subset M1)).
        Proof by contradiction. Assume the contrary.
          Then M1 /subset M2 /\ M2 /subset M1.
          Then M1 = M2.
          Contradiction.
        end.
      end.
      Take a zfset z such that (z /in M1 /setminus M2 \/ z /in M2 /setminus M1).
      Then z /in kappa.
      Take a zfset i such that i /in cof(kappa) /\ z /in kap[i].
      Then M1 /cap kap[i] /neq M2 /cap kap[i].
      inj[i] is injective.
      Then (inj[i])[M1 /cap kap[i]] /neq (inj[i])[M2 /cap kap[i]].
      Proof.
        M1 /cap kap[i], M2 /cap kap[i] /in /VV.
        Proof.
          M1, M2 /in /VV.
          M1 /cap kap[i] /subset M1.
          M2 /cap kap[i] /subset M2.
        end.
        Take zfsets a1, a2 such that a1 = M1 /cap kap[i] /\ a2 = M2 /cap kap[i].
        Then a1 /neq a2.
        a1,a2 /in Dom(inj[i]).
        Then (inj[i])[a1] /neq (inj[i])[a2].
      end.
      Let pair1 = (M1,i). 
      Then pair1 /in /PP kappa /times cof(kappa).
      Fun[(M1,i)] = (inj[i])[M1 /cap kap[i]].
      Let pair2 = (M2,i). 
      Then pair2 /in /PP kappa /times cof(kappa).
      Fun[(M2,i)] = (inj[i])[M2 /cap kap[i]].
      Then Fun[(M1,i)] /neq Fun[(M2,i)].     
      Then G[M1] /neq G[M2].
      Proof.
        i /in cof(kappa).
        i /in Dom(G[M1]).
        i /in Dom(G[M2]).
        (G[M1])[i] = Fun[(M1,i)].
        (G[M2])[i] = Fun[(M2,i)].
        (G[M1])[i] /neq (G[M2])[i].
      end.
    end.
  end.
  
  /PP kappa, ^{cof(kappa)}(2 ^< kappa) are zfsets.
  Then Card(/PP kappa) /subset Card(^{cof(kappa)}(2 ^< kappa)).
  Card(/PP kappa) = 2 ^ kappa.
  Card(^{cof(kappa)}(2 ^< kappa)) = (2 ^< kappa) ^ cof(kappa).
qed.


Lemma. Let kappa /in /Card. Let cof(kappa) /in kappa. Let (exists kappap /in /Card /cap kappa forall lambda /in /Card
(kappap /subset lambda /\ lambda /in kappa => 2 ^ kappap = 2 ^ lambda)). Then 2 ^ kappa = 2 ^< kappa.
Proof.
  Take a zfset kappap such that kappap /in /Card /cap kappa /\ forall lambda /in /Card
  (kappap /subset lambda /\ lambda /in kappa => 2 ^ kappap = 2 ^ lambda).
  2 ^< kappa = 2 ^ kappap.
  Proof.
    2 ^< kappa = {zfset x | exists v /in kappa x /in 2 ^ Card(v)}.
    Then 2 ^ kappap /subset 2 ^< kappa.
    Proof.
      Let x /in 2 ^ kappap.
      kappap /in kappa.
      Card(kappap) = kappap.
      Then exists v /in kappa x /in 2 ^ Card(v).
      Then x /in 2 ^< kappa.
    end.
    2 ^< kappa /subset 2 ^ kappap.
    Proof.
      Let x /in 2 ^< kappa.
      Take a zfset v such that v /in kappa /\ x /in 2 ^ Card(v).
      Card(v) /in kappa.
      kappap /subset Card(v) \/ Card(v) /in kappap.
      Proof.
        Take ordinals aa,bb such that aa = kappap /\ bb = Card(v).
        Then aa /in bb \/ bb /in aa \/ aa = bb.
        Then aa /subset bb \/ bb /in aa.
      end.
      Case kappap /subset Card(v). 
        Card(v) /in /Card.
        Then 2 ^ Card(v) = 2 ^ kappap.
      end.
      Case Card(v) /in kappap.
        Then 2 ^ Card(v) /subset 2 ^ kappap.
      end.
    end.
  end.
  
  2 ^< kappa /subset 2 ^ kappa.
  Proof.
    2 ^ kappap /subset 2 ^ kappa.
  end.
  
  2 ^ kappa /subset 2 ^< kappa.
  Proof.
    2 ^ kappa /subset (2 ^< kappa) ^ cof(kappa).
    2 ^< kappa = 2 ^ kappap.
    Then 2 ^ kappa /subset (2 ^ kappap) ^ cof(kappa).
    (2 ^ kappap) ^ cof(kappa) = 2 ^ (kappap * cof(kappa)).
    2 ^ (kappap * cof(kappa)) /subset 2 ^ kappap.
    Proof.
      kappap, cof(kappa) /in /Ord.
      Then kappap /in cof(kappa) \/ cof(kappa) /in kappap \/ kappap = cof(kappa) (by TotalOrder).
      Case kappap = cof(kappa).
        Then kappap * cof(kappa) = kappap.
      end.
      Case kappap /in cof(kappa).
        Then kappap /subset cof(kappa).
        Then kappap * cof(kappa) /subset cof(kappa) * cof(kappa).
        Proof.
          kappap /times cof(kappa) /subset cof(kappa) /times cof(kappa).
          Then Card(kappap /times cof(kappa)) /subset Card(cof(kappa) /times cof(kappa)).
        end.
        cof(kappa) * cof(kappa) = cof(kappa).
        Then kappap * cof(kappa) /subset cof(kappa).
        Then 2 ^ (kappap * cof(kappa)) /subset 2 ^ cof(kappa).
        Proof.
          Take cardinals aa, bb such that aa = kappap * cof(kappa) /\ bb = cof(kappa).
          0 /in 2.
          aa /subset bb.
          Then 2 ^ aa /subset 2 ^ bb.
        end.
        2 ^ cof(kappa) = 2 ^ kappap.
      end.
      Case cof(kappa) /in kappap.
        Then cof(kappa) /subset kappap.
        Then kappap * cof(kappa) /subset kappap * kappap.
        Proof.
          kappap /times cof(kappa) /subset kappap /times kappap.
          Then Card(kappap /times cof(kappa)) /subset Card(kappap /times kappap).
        end.
        kappap * kappap = kappap.
        Then kappap * cof(kappa) /subset kappap.
        Then 2 ^ (kappap * cof(kappa)) /subset 2 ^ kappap.
        Proof.
          Take cardinals aa, bb such that aa = kappap * cof(kappa) /\ bb = kappap.
          0 /in 2.
          aa /subset bb.
          Then 2 ^ aa /subset 2 ^ bb.
        end.
      end.
    end.
    Then 2 ^ kappa /subset 2 ^ kappap.
    2 ^ kappap = 2 ^< kappa.
  end.
qed.


Lemma. Let kappa /in /Card. Let cof(kappa) /in kappa. Let (forall kappap /in /Cd /cap kappa exists lambda /in /Cd /cap kappa
(kappap /in lambda /\ 2 ^ kappap /in 2 ^ lambda)). Then 2 ^ kappa = Gimel[2 ^< kappa].
Proof.
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
    Let lambda /in kappa.
    alpha /in /Lim.
    Then Alef[alpha] = /bigcup Alef^[alpha].
    Take a zfset beta such that beta /in alpha /\ lambda /in Alef[beta].
    Take a zfset b such that b /in xa /\ beta /in b.
    Then Alef[beta] /subset Alef[b].
    Then lambda /in Alef[b].
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
  Take a zffunction kap such that kap : cof(kappa) /leftrightarrow x /\ (kap is an epsiso).
  Forall i1,i2 /in cof(kappa) (i1 /in i2 => kap[i1] /in kap[i2]) (by epsiso).
  Forall i /in cof(kappa) kap[i] /in /Card.
  Proof.
    Let i /in cof(kappa).
    Then kap[i] /in x.
    Take a zfset j such that j /in xa /\ kap[i] = Alef[j].
    Alef[j] /in /Cd.
    /NN /subset Alef[j].
    Then Alef[j] /in /Card.
  end.
  Card(x) = cof(kappa).
  cof(kappa) = cof(2 ^< kappa).
  Proof.
    cof(2 ^< kappa) /subset cof(kappa).
    Proof.
      Define f[i] = 2 ^ kap[i] for i in cof(kappa).
      f is a zffunction.
      Proof.
        Let i /in cof(kappa).
        Then f[i] /in /VV.
      end.
      Let M = f^[cof(kappa)].
      Then Card(M) /subset cof(kappa).
      M /subset 2 ^< kappa.
      Proof.
        Let a /in M.
        Take a zfset b such that b /in cof(kappa) /\ a = f[b].
        Then a = 2 ^ kap[b].
        kap[b] /in kappa.
        kap[b] /in /Cd /cap kappa.
        Take a zfset c such that c /in /Cd /cap kappa /\ kap[b] /in c /\ 2 ^ kap[b] /in 2 ^ c.
        Then a /in 2 ^< kappa.
        Proof.
          2 /in /Cd.
          c /in kappa.
          Card(c) = c.
          a /in 2 ^ Card(c).
          Then a /in (Cont(2))[c].
          Then a /in /bigcup (Cont(2))^[kappa].
          2 ^< kappa = /bigcup (Cont(2))^[kappa].
        end.
      end.
      M /cof 2 ^< kappa.
      Proof.
        Forall a1 /in 2 ^< kappa exists a2 /in M a1 /in a2.
        Proof.
          Let a /in 2 ^< kappa.
          2 ^< kappa = /bigcup (Cont(2))^[kappa].
          Take a zfset b such that b /in (Cont(2))^[kappa] /\ a /in b.
          Take a zfset v such that v /in kappa /\ b = (Cont(2))[v].
          Then a /in 2 ^ Card(v).
          Take a zfset c such that c /in x /\ v /in c.
          Take a zfset d such that d /in cof(kappa) /\ kap[d] = c.
          Card(v) /subset kap[d].
          Then 2 ^ Card(v) /subset 2 ^ kap[d].
          Proof.
            2, Card(v), kap[d] /in /Cd.
            0 /in 2.
            Card(v) /subset kap[d].
            Then 2 ^ Card(v) /subset 2 ^ kap[d] (by ExpSubset).
          end.
          2 ^ kap[d] = f[d].
          Then 2 ^ kap[d] /in M.
          a /in 2 ^ kap[d].
        end.
      end.
      Then Card(M) /in cofset2(2 ^< kappa).
      Then min(cofset2(2 ^< kappa)) /subset Card(M).
      cof(2 ^< kappa) = min(cofset2(2 ^< kappa)).
      Then cof(2 ^< kappa) /subset Card(M).
    end.
    
    cof(2 ^< kappa) /notin cof(kappa).
    Proof by contradiction. Assume the contrary.
      Take a cardinal beta such that beta = 2 ^< kappa.
      cof(beta) /in cofset2(beta).
      Take a zfset z such that z /subset beta /\ z /cof beta /\ Card(z) = cof(beta).
  
      Define ind[delta] = {i /in cof(kappa) | delta /subset 2 ^ kap[i]} for delta in z.
      Forall delta /in z ind[delta] /neq /emptyset.
      Proof.
        Let delta /in z.
        Then delta /in 2 ^< kappa.
        Forall aa /in /Cd forall bb /in /Card (aa ^< bb = {zfset y | exists v /in bb y /in aa ^ Card(v)}).
        2 /in /Cd.
        kappa /in /Card.
        Then 2 ^< kappa = {zfset y | exists v /in kappa y /in 2 ^ Card(v)}.
        Take a zfset v such that v /in kappa /\ delta /in 2 ^ Card(v).
        Take a zfset a1 such that a1 /in x /\ v /in a1.
        Take a zfset a2 such that a2 /in cof(kappa) /\ kap[a2] = a1.
        Card(v) /in a1.
        Then 2 ^ Card(v) /subset 2 ^ kap[a2].
        Then delta /subset 2 ^ kap[a2].
        Then a2 /in ind[delta].
      end.
      Forall delta /in z ind[delta] /subset /Ord.
      Forall delta /in z min(ind[delta]) /in cof(kappa).
      Proof.
        Let delta /in z.
        ind[delta] /subset /Ord.
        ind[delta] /neq /emptyset.
        Then min(ind[delta]) /in ind[delta].
      end.
      Define f[delta] = min(ind[delta]) for delta in z.
      f is a zffunction.
      Proof.
        Let delta /in Dom(f). 
        Then f[delta] /in cof(kappa).
        Then f[delta] /in /VV.
      end.
      Let zz = f^[z].
      Then zz /subset cof(kappa).
      Proof.
        Let a1 /in zz.
        Take a zfset a2 such that a2 /in z /\ a1 = f[a2].
        Then a1 = min(ind[a2]).
        min(ind[a2]) /in cof(kappa).
        Then a1 /in cof(kappa).
      end.
      zz /cof cof(kappa).
      Proof.
        Let a /in cof(kappa).
        kap[a] /in kappa.
        Forall kappap /in /Cd /cap kappa exists lambdap /in /Cd /cap kappa (kappap /in lambdap /\ 2 ^ kappap /in 2 ^ lambdap).
        kap[a] /in /Cd /cap kappa.
        Then exists lambdap /in /Cd /cap kappa (kap[a] /in lambdap /\ 2 ^ kap[a] /in 2 ^ lambdap).
        Take a cardinal lambda such that lambda /in /Cd /cap kappa /\ kap[a] /in lambda /\ 2 ^ kap[a] /neq 2 ^ lambda.
        2 ^ kap[a] /in 2 ^ lambda.
        Proof.
          2 ^ kap[a] /subset 2 ^ lambda.
          Take ordinals aa, bb such that aa = 2 ^ kap[a] /\ bb = 2 ^ lambda.
          Then aa /in bb \/ bb /in aa \/ aa = bb.
          aa /subset bb.
          aa /neq bb.
          Then aa /in bb.
        end.
        Then 2 ^ kap[a] /in 2 ^< kappa.
        Proof.
          2 /in /Cd.
          kappa /in /Card.
          lambda /in kappa.
          Card(lambda) = lambda.
          2 ^ kap[a] /in 2 ^ Card(lambda).
          Then 2 ^ kap[a] /in (Cont(2)[lambda]).
          Then 2 ^ kap[a] /in /bigcup (Cont(2))^[kappa].
          2 ^< kappa = /bigcup (Cont(2))^[kappa].
        end.
        Take a zfset b such that b /in z /\ 2 ^ kap[a] /in b.
        Then f[b] /in zz.
        a /notin ind[b].
        Proof.
          not (b /subset 2 ^ kap[a]).
        end.
        min(ind[b]) /in ind[b].
        Then f[b] /in ind[b].
        Forall i /in ind[b] (i /in cof(kappa) /\ (2 ^ kap[i] is a zfset) /\ b /subset 2 ^ kap[i]).
        2 ^ kap[f[b]] is a zfset.
        b /subset 2 ^ kap[f[b]].
        2 ^ kap[a] /in b.
        Then 2 ^ kap[a] /in 2 ^ kap[f[b]].
        Then kap[a] /in kap[f[b]].
        Proof.
          Take cardinals a1,a2 such that a1 = kap[a] /\ a2 = kap[f[b]].
          a1,a2 /in /Ord.
          Then a1 /in a2 \/ a2 /in a1 \/ a1 = a2 (by TotalOrder).
          Case a1 /in a2. end.
          Case a2 /in a1.
            Then 2 ^ a2 /subset 2 ^ a1.
            Contradiction.
          end.
          Case a1 = a2. 
            Then 2 ^ a1 = 2 ^ a2.
            Contradiction.
          end.
        end.
        Then a /in f[b].
        Proof.
          a, f[b] /in /Ord.
          Then a /in f[b] \/ f[b] /in a \/ a = f[b].
          a, f[b] /in Dom(kap).
          Case a = f[b].
            Then kap[a] = kap[f[b]].
            Contradiction.
          end.
          Case a /in f[b]. end.
          Case f[b] /in a.
            Then kap[f[b]] /in kap[a].
            kap[a] /in kap[f[b]].
            Trans(kap[a]).
            Then kap[a] /in kap[a].
            Contradiction.
          end.
        end.
      end.
      
      Card(zz) /in cofset2(cof(kappa)).
      Then min(cofset2(cof(kappa))) /subset Card(zz).
      Then cof(cof(kappa)) /subset Card(zz).
      cof(cof(kappa)) = cof(kappa).
      Then cof(kappa) /subset Card(zz).
      
      Card(zz) /subset Card(z).
      Card(z) = cof(beta).
      cof(beta) /in cof(kappa).
      Then cof(beta) /in Card(z).
      Then Card(z) /in Card(z).
      
      Contradiction.
    end.
    
    Take ordinals a1,a2 such that a1 = cof(2 ^< kappa) /\ a2 = cof(kappa).
    Then a1 /in a2 \/ a2 /in a1 \/ a1 = a2.
    a1 /subset a2.
    a1 /notin a2.
    Then a1 = a2.
    
  end.
  
  2 ^ kappa /subset Gimel[2 ^< kappa].
  Proof.
    2 ^ kappa /subset (2 ^< kappa) ^ cof(kappa).
    cof(kappa) = cof(2 ^< kappa).
    Then (2 ^< kappa) ^ cof(kappa) = (2 ^< kappa) ^ cof(2 ^< kappa).
    (2 ^< kappa) ^ cof(2 ^< kappa) = Gimel[2 ^< kappa].
  end.
  
  Gimel[2 ^< kappa] /subset 2 ^ kappa.
  Proof.
    Gimel[2 ^< kappa] = (2 ^< kappa) ^ cof(2 ^< kappa).
    cof(2 ^< kappa) = cof(kappa).
    Then Gimel[2 ^< kappa] = (2 ^< kappa) ^ cof(kappa).
    2 ^< kappa /subset 2 ^ kappa.
    Proof.
      Let a /in 2 ^< kappa.
      2 ^< kappa = /bigcup (Cont(2))^[kappa].
      Take a zfset b such that b /in (Cont(2))^[kappa] /\ a /in b.
      Take a zfset v such that v /in kappa /\ b = (Cont(2))[v].
      Then a /in 2 ^ Card(v).
      2,Card(v),kappa /in /Cd.
      Card(v) /subset kappa.
      0 /in 2.
      Then 2 ^ Card(v) /subset 2 ^ kappa (by ExpSubset).
      Then a /in 2 ^ kappa.
    end.
    2 ^< kappa, 2 ^ kappa, cof(kappa) /in /Cd.
    Then (2 ^< kappa) ^ cof(kappa) /subset (2 ^ kappa) ^ cof(kappa) (by BaseSubset).
    (2 ^ kappa) ^ cof(kappa) = 2 ^ (kappa * cof(kappa)).
    cof(kappa) /subset kappa.
    Then kappa * cof(kappa) /subset kappa * kappa.
    Proof.
      kappa /times cof(kappa) /subset kappa /times kappa.
      Then Card(kappa /times cof(kappa)) /subset Card(kappa /times kappa).
    end.
    kappa * kappa = kappa.
    Then kappa * cof(kappa) /subset kappa.
    Then 2 ^ (kappa * cof(kappa)) /subset 2 ^ kappa.
    Proof.
      Take cardinals aa, bb such that aa = (kappa * cof(kappa)) /\ bb = kappa.
      2,aa,bb /in /Cd.
      0 /in 2.
      aa /subset bb.
      Then 2 ^ aa /subset 2 ^ bb.
    end.
  end.
qed.





