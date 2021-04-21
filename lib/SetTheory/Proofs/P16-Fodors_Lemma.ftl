[read Formalizations/Library/L15-Stationary_Sets.ftl]


## Pretyped Variables

Let w,x,y,z,W,X,Y,Z stand for zfsets.
Let a,b,c,d,A,B,C,D,M stand for sets.
Let o,o1,o2 stand for objects.
Let alpha, beta, gamma stand for ordinals.
Let f,g,h,F,G,H stand for zffunction.
Let kappa, lambda stand for cardinals.




## Prerequisites

Signature. A successor cardinal is a cardinal.
Signature. A limit cardinal is a cardinal.

Definition. Let kappa be a cardinal. kappa is infinite iff /NN /subset kappa.
Axiom. Let kappa be a cardinal. Then kappa is a successor cardinal iff exists alpha /in /Ord (kappa = Alef[alpha +' 1]).
Axiom. Let kappa be a cardinal. kappa is a limit cardinal iff exists lambda /in /Lim (kappa = Alef[lambda]).

Lemma. Let kappa be a successor cardinal. Then kappa /in /Lim.

Lemma. Let kappa be a limit cardinal. Then kappa /in /Lim.

Lemma. Let kappa be a successor cardinal. Then kappa is regular.
Proof.
  Take an ordinal alpha such that kappa = Alef[alpha+'1].
  Alef[alpha+'1] is regular.
qed.


Lemma. Let f be an epsiso. Let alpha /in /Lim. Let alpha /subset Dom(f). Let ran(f) /subset /Ord. Then /bigcup f^[alpha] /in /Lim /\ cof(/bigcup f^[alpha]) = cof(alpha).
Proof.
  f is a zffunction.
  /bigcup f^[alpha] /in /Ord.
  Proof.
    /bigcup f^[alpha] /in /VV.
    f^[alpha] /subset /Ord.
    Then Trans(/bigcup f^[alpha]).
  end.
  /bigcup f^[alpha] /in /Lim.
  Proof.
    /bigcup f^[alpha] /neq 0.
    Proof.
      0,1 /in Dom(f).
      0 /in 1.
      Then f[0] /in f[1] (by epsiso).
      f[1] /in f^[alpha].
      Then f[0] /in /bigcup f^[alpha].
    end.
    Let a /in /bigcup f^[alpha].
    Take a zfset b such that b /in f^[alpha] /\ a /in b.
    Take a zfset c such that c /in alpha /\ b = f[c].
    c, c+'1 /in Dom(f).
    c /in c+'1.
    Then f[c] /in f[c+'1] (by epsiso).
    Then a+'1 /in f[c+'1].
    Proof.
      f[c] /in /Ord.
      a /in f[c].
      a /subset f[c].
      Then a++ /subset f[c].
      a+'1, f[c] /in /Ord.
      Then a+'1 /in f[c] \/ f[c] /in a+'1 \/ a+'1 = f[c] (by TotalOrder).
      f[c] /notin a+'1.
      Then a+'1 /in f[c] \/ a+'1 = f[c].
      f[c] /in f[c+'1].
      Case a+'1 = f[c]. end.
      Case a+'1 /in f[c]. f[c] /in f[c+'1]. f[c+'1] /in /Ord. end.
    end.
    f[c+'1] /in f^[alpha].
    Then a++ /in /bigcup f^[alpha].
  end.
  
  cof(/bigcup f^[alpha]) /subset cof(alpha).
  Proof.
    Take a zfset x such that x /subset alpha /\ x /cof alpha /\ Card(x) = cof(alpha).
    Let y = f^[x].
    Then y /subset /bigcup f^[alpha].
    Proof.
      Let a /in y.
      Take a zfset b such that b /in x /\ a = f[b].
      Then b,b+'1 /in Dom(f).
      b /in b+'1.
      Then f[b] /in f[b+'1] (by epsiso).
      f[b+'1] /in f^[alpha].
      Then a /in /bigcup f^[alpha].
    end.
    y /cof /bigcup f^[alpha].
    Proof.
      y /subset /bigcup f^[alpha].
      Let a /in /bigcup f^[alpha].
      Take a zfset b such that b /in f^[alpha] /\ a /in b.
      Take a zfset c such that c /in alpha /\ b = f[c].
      Take a zfset d such that d /in x /\ c /in d.
      c,d /in Dom(f).
      Then f[c] /in f[d] (by epsiso).
      Then f[d] /in y.
      f[d] /in /Ord.
      Then a /in f[d].
    end.
    Card(y) = Card(x).
    Proof.
      f /upharpoonright x : x /leftrightarrow y.
      Proof.
        Dom(f /upharpoonright x) = x.  
        ran(f /upharpoonright x) = (f /upharpoonright x)^[x].
        Forall i /in x (f /upharpoonright x)[i] = f[i].
        Then (f /upharpoonright x)^[x] = f^[x].
        Then ran(f /upharpoonright x) = y.
        f /upharpoonright x is injective.
        Proof.
          Let a1,a2 /in x.
          Let a1 /neq a2.
          Then f[a1] /neq f[a2].
          Proof.
            a1,a2 /in /Ord.
            a1 /in a2 \/ a2 /in a1 \/ a1 = a2 (by TotalOrder).
            Then a1 /in a2 \/ a2 /in a1.
            Case a1 /in a2. 
              a1,a2 /in Dom(f). 
              Then f[a1] /in f[a2] (by epsiso). 
            end.
            Case a2 /in a1. 
              a1,a2 /in Dom(f).
              Then f[a2] /in f[a1] (by epsiso). 
            end.
          end.
        end.
      end.
    end.
    Then Card(y) /in cofset2(/bigcup f^[alpha]).
    cofset2(/bigcup f^[alpha]) /subset /Ord.
    Then min(cofset2(/bigcup f^[alpha])) /subset Card(y).
  end.
  
  cof(alpha) /subset cof(/bigcup f^[alpha]).
  Proof.
    Take a limit ordinal lambda such that lambda = /bigcup f^[alpha].
    Take a zfset x such that x /subset lambda /\ x /cof lambda /\ 
    Card(x) = cof(lambda).
    Forall y /in x exists beta /in alpha y /in f[beta].
    Define g[n] = (choose zfset beta such that beta /in alpha /\ n /in f[beta] in beta) for n in x.
    g is a zffunction.
    Proof.
      Let n /in x.
      Then g[n] /in /VV.
    end.
    Let y = g^[x].
    Then y /subset alpha.
    Proof.
      ran(g) /subset alpha.
      Then g^[x] /subset alpha.
    end.
    y /cof alpha.
    Proof.
      Let beta /in alpha.
      Then f[beta] /in /bigcup f^[alpha].
      Proof.
        beta, beta +' 1 /in Dom(f).
        beta /in beta +' 1.
        Then f[beta] /in f[beta +' 1] (by epsiso).
        f[beta +' 1] /in f^[alpha].
      end.
      Take a zfset z such that z /in x /\ f[beta] /in z.
      Then g[z] /in y.
      z /in f[g[z]].
      Then f[beta] /in f[g[z]].
      Then beta /in g[z].
      Proof.
        beta, g[z] /in /Ord.
        Then beta /in g[z] \/ g[z] /in beta \/ g[z] = beta.
        Case beta /in g[z]. end.
        Case g[z] /in beta.
          g[z],beta /in Dom(f).
          Then f[g[z]] /in f[beta] (by epsiso).
          Take ordinals a1,a2 such that a1 = f[beta] /\ a2 = f[g[z]].
          Then a1 /in a2 /\ a2 /in a1.
          Contradiction. 
        end.
        Case g[z] = beta. 
          Then f[beta] = f[g[z]]. 
          Contradiction. 
        end.
      end.
    end.
    Card(y) /subset Card(x).
    Proof.
      g is a zffunction.
      x /subset Dom(g).
      Then Card(g^[x]) /subset Card(x).
    end.
    Card(y) /in cofset2(alpha).
    Then min(cofset2(alpha)) /subset Card(y).
    Then min(cofset2(alpha)) /subset Card(x).
  end.
qed.



## Fodors Lemma


Definition. Let kappa /in /BigCard. The set of stationary subsets of kappa is
{C /subset kappa | C is stationary in kappa}.
Let stat(k) stand for the set of stationary subsets of k.

Definition. The set of regular uncountable cardinals is {kappa /in /BigCard | kappa is regular}.
Let /BigRegCard stand for the set of regular uncountable cardinals.

Definition. Let f be a zffunction. f is constant iff exists c /in /VV forall x /in Dom(f) f[x] = c.

Definition. Let f be a zffunction. Let Dom(f) /subset /Ord. f is regressive iff forall alpha /in Dom(f) /setminus <0> f[alpha] /in alpha.


Theorem Fodor. Let kappa /in /BigRegCard. Let f be a zffunction. Let Dom(f) /in stat(kappa). Let f be regressive.
Then exists i /in /Ord f^{-1}[[i]] /in stat(kappa).
Proof by contradiction. Assume the contrary.
  Then forall i /in /Ord f^{-1}[[i]] /in NS(kappa).
  Proof.
    Let i /in /Ord.
    Then f^{-1}[[i]] is not stationary in kappa.
    f^{-1}[[i]] /subset kappa.
    Then f^{-1}[[i]] /in NS(kappa).
  end.
  Forall i /in /Ord kappa /setminus f^{-1}[[i]] /in Club(kappa).
  Define X[i] = kappa /setminus f^{-1}[[i]] for i in kappa.
  X is a zffunction.
  Proof.
    Let i /in kappa.
    Then X[i] /subset kappa.
    Then X[i] /in /VV.
  end.
  kappa /in /Ord.
  Forall i /in kappa (X[i] /subset kappa /\ X[i] /in Club(kappa)).
  Then X is a sequence of length kappa in Club(kappa) (by sequence).
  kappa /in /BigCard.
  kappa is regular.
  Then /triangle(X,kappa) /in Club(kappa).
  Then exists C /subset /triangle(X,kappa) (C /club kappa).
  Take a zfset C such that C /subset /triangle(X,kappa) /\ C /club kappa.
  Let CC = C /setminus <0>.
  Then CC /club kappa.
  Proof.
    CC /subset kappa.
    CC /cof kappa.
    Proof.
      Let alpha /in kappa.
      Take an zfset beta such that beta /in C /\ alpha /in beta.
      Then beta /in CC.
    end.
    CC /closed kappa.
    Proof.
      Let lambda /in kappa /cap /Lim.
      Let CC /cap lambda /cof lambda.
      Then C /cap lambda /cof lambda.
      Then lambda /in C.
      Then lambda /in CC.
    end.
  end.
  Then CC /cap Dom(f) /neq /emptyset.
  Proof.
    kappa /in /BigCard.
    Dom(f) /subset kappa.
    Dom(f) is stationary in kappa.
    CC /subset kappa.
    CC /club kappa.
    Then CC /cap Dom(f) /neq /emptyset (by stationary).
  end.
  Take a zfset alpha such that alpha /in CC /cap Dom(f).
  Then alpha /in /triangle(X,kappa) /\ alpha /neq 0.
  Then forall i /in alpha alpha /in X[i].
  Then forall i /in alpha alpha /notin f^{-1}[[i]].
  Proof.
    Let i /in alpha.
    alpha /in X[i].
    X[i] = kappa /setminus f^{-1}[[i]].
    Then alpha /notin f^{-1}[[i]].
  end.
  Then forall i /in alpha f[alpha] /neq i.
  Then f[alpha] /notin alpha.
  f is regressive.
  alpha /in Dom(f) /setminus <0>.
  Dom(f) /subset /Ord.
  Then f[alpha] /in alpha.
  Contradiction.
qed.


Corollary Fodor2. Let kappa /in /BigRegCard. Let f be a zffunction. Let Dom(f) /in stat(kappa). Let f be regressive. Then exists T /subset Dom(f) (T /in stat(kappa) /\ (f /upharpoonright T is constant)).
Proof.
  Take an ordinal i such that f^{-1}[[i]] /in stat(kappa).
  Let T = f^{-1}[[i]].
  T /subset Dom(f).
  T /in stat(kappa).
  f /upharpoonright T is constant.
qed.


Definition. Let kappa /in /BigCard. Let C /in Cl(kappa). The derivation of C in kappa is
{alpha /in kappa /cap /Lim | C /cap alpha /cof alpha}.
Let der(C,k) stand for the derivation of C in k.


Lemma. Let kappa /in /BigCard. Let C /in Cl(kappa). Then der(C,kappa) /subset C.
Proof.
  Let alpha /in der(C,kappa).
  Then C /cap alpha /cof alpha.
  C /subset kappa.
  C /closed kappa.
  Then alpha /in C.
qed.


Lemma. Let kappa /in /BigCard. Let C /in Cl(kappa). Then der(C,kappa) /in Cl(kappa).
Proof.
  der(C,kappa) /subset kappa.
  der(C,kappa) /closed kappa.
  Proof.
    Let lambda /in kappa /cap /Lim.
    Let der(C,kappa) /cap lambda /cof lambda.
    der(C,kappa) /subset C.
    Then der(C,kappa) /cap lambda /subset C /cap lambda.
    Then C /cap lambda /cof lambda.
    Proof.
      Let alpha /in lambda.
      Take a zfset beta such that beta /in der(C,kappa) /cap lambda /\ alpha /in beta.
      Then beta /in C /cap lambda.
    end.
  end.
  der(C,kappa) /cof kappa.
  Proof.
    Let alpha /in kappa.
    C /club kappa.
    Forall a /in kappa exists b /in C a /in b.
    Define sup[a] = (Choose a zfset b such that b /in C /\ a /in b in b) for a in kappa.
    sup : kappa /rightarrow kappa.
    Proof.
      Let i /in kappa.
      Then sup[i] /in C.
      C /subset kappa.
      Then sup[i] /in kappa.
    end.
    Forall beta /in kappa beta /in sup[beta].
    Proof.
      Let beta /in kappa.
      Take ordinals a,b such that a = beta /\ b = sup[beta].
      Then a,b /in /Ord.
      Then a /in b \/ b /in a \/ a = b (by TotalOrder).
      sup[beta] /notin beta +' 1.
      Then b /notin a+'1.
      Then b /notin a /\ b /neq a.
      Then a /in b.
    end.
    ran(sup) /subset Dom(sup).
    Proof.
      Let a /in ran(sup).
      Take a zfset b such that b /in kappa /\ a = sup[b].
      Then a /in kappa.
      Then a /in Dom(sup).
    end.    
  
    Define f[n] = (sup ^^ (n+'1))[alpha] for n in /NN.
  
    Forall n /in /NN f[n] /in kappa.
    Proof.
      Let n /in /NN.
      f[n] = (sup ^^ (n+'1))[alpha].
      Then f[n] /in ran(sup ^^ (n+'1)).
      ran(sup ^^ (n+'1)) /subset Dom(sup).
    end.
    f is a zffunction.
    Proof.
      Let n /in /NN.
      Then f[n] /in kappa.
      Then f[n] /in /VV.
    end.
    f[0] = sup[alpha].
    Forall n /in /NN (n /neq 0 => (n-- /in /NN /\ f[n] = sup[f[n--]])).
    Proof by induction.
      Let n /in /NN.
      Case n = 0. end.
      Case n /neq 0.
        Let m = n--.
        m /in /NN.
        f[n] = (sup ^^ (n+'1))[alpha].
        (sup ^^ (n++))[alpha] = sup[(sup ^^ n)[alpha]].
        Then f[n] = sup[(sup ^^ n)[alpha]].
        f[m] = (sup ^^ n)[alpha].
        Then f[n] = sup[f[m]].
      end.
    end.
    Forall a,b /in /NN (a /in b => f[a] /in f[b]).
    Proof.
      Let a /in /NN.
      Forall b /in /NN (a /in b => f[a] /in f[b]).
      Proof by induction.
        Let b /in /NN.
        Case b = 0. end.
        Case b /neq 0.
          Let c = b--.
          Then c -<- b.
          Then a /notin c \/ f[a] /in f[c].
          Case f[a] /in f[c].
            f[b] = sup[f[c]].
            Then f[c] /in f[b].
            Trans(f[b]).
            Then f[a] /in f[b].
          end.
          Case a /notin c.
            Then a /notin b \/ a = c.
          end.
        end.
      end.
    end.
    Forall a,b /in /NN (a /subset b => f[a] /subset f[b]).
    Proof.
      Let a,b /in /NN. Let a /subset b.
      a,b /in /Ord.
      Then a /in b \/ b /in a \/ a = b (by TotalOrder).
      Then a /in b \/ a = b.
    end.
        
    Let x = /bigcup f^[/NN].
    x /in /Ord.
    Proof.
      f^[/NN] /subset /Ord.
      Then Trans(/bigcup f^[/NN]).
      Then /bigcup f^[/NN] /in /Ord.
    end.
    x /subset kappa.
    Proof.
      Let a /in x.
      Take a zfset b such that b /in f^[/NN] /\ a /in b.
      Take a zfset n such that n /in /NN /\ b = f[n].
      Then b /in kappa.
      Then a /in kappa.
    end.
    Then x /in kappa \/ x = kappa.
    x /in kappa.
    Proof by contradiction. Assume the contrary.
      Then x = kappa.
      f^[/NN] /cof kappa.
      Proof.
        Let a /in kappa.
        Then a /in /bigcup f^[/NN].
      end.
      Card(f^[/NN]) /subset /NN.
      f^[/NN] /subset kappa.
      Card(f^[/NN]) /in cofset2(kappa).
      Then min(cofset2(kappa)) /subset Card(f^[/NN]).
      Then cof(kappa) /subset /NN.
      Alef[1] /subset cof(kappa).
      Contradiction.
    end.
      
    alpha /in x.
    Proof.
      f[0] = sup[alpha].
      Then alpha /in f[0].
      Then alpha /in /bigcup f^[/NN].
    end.
      
    x /in /Lim.
    Proof by contradiction. Assume the contrary.
      alpha /in x.
      Then x /neq 0.
      Then x /in /Succ.
      Take an ordinal a such that x = a+'1.
      Then a /in x.
      Take a zfset b such that b /in f^[/NN] /\ a /in b.
      f^[/NN] /subset kappa.
      Then b /in /Ord.
      Then a+'1 /subset b.
      Then a+'1 = b \/ a+'1 /in b.
      Proof.
        a+'1,b /in /Ord.
        a+'1 /in b \/ b /in a+'1 \/ a+'1 = b (by TotalOrder).
        b /notin a+'1.
      end.
      Take a zfset n such that n /in /NN /\ b = f[n].
      Then b /in f[n+'1].
      Then b /in /bigcup f^[/NN].
      Then b /in x.
      Then a+'1 /in x.
      Contradiction.
    end.
  
    x /in der(C,kappa).
    Proof.
      C /cap x /cof x.
      Proof.
        Let j /in x.
        Take a zfset n such that n /in /NN /\ j /in f[n].
        f[n] /in C.
        Proof.
          Case n = 0.
            Then f[n] = sup[alpha].
          end.
          Case n /neq 0.
            Let m = n--.
            f[n] = sup[f[m]].
            sup[f[m]] /in C.
          end.
        end.
        f[n] /in x.
        Proof.
          f[n] /in f[n+'1].
          f[n+'1] /in f^[/NN].
          Then f[n] /in /bigcup f^[/NN].
        end.
        f[n] /in C /cap x.
        j /in f[n].
      end.
      x /in kappa /cap /Lim.
    end.
    alpha /in x.
  end.
qed.


Lemma. Let kappa /in /BigCard. Let S /subset kappa. Let S be stationary in kappa. Then S /cap /Lim is stationary in kappa.
Proof.
  Let X = S /cap /Lim.
  X /subset kappa.
  Forall C /subset kappa (C /club kappa => X /cap C /neq /emptyset).
  Proof.
    Let C /subset kappa.
    Let C /club kappa.
    Then C /in Cl(kappa).
    Then der(C,kappa) /in Cl(kappa).
    Then S /cap der(C,kappa) /neq /emptyset (by stationary).
    der(C,kappa) /subset C /cap /Lim.
    Take a zfset alpha such that alpha /in der(C,kappa) /cap S.
    Then alpha /in (S /cap /Lim) /cap C.
    Then X /cap C /neq /emptyset.
  end.
  Then X is stationary in kappa (by stationary).
qed.


Lemma. Let kappa /in /BigCard. Let S /in stat(kappa). Then S /cap /Lim /in stat(kappa).


Definition. Let lambda, kappa /in /BigRegCard. Let lambda /in kappa. The subset of cofinality lambda in kappa is
{alpha /in kappa /cap /Lim | cof(alpha) = lambda}.
Let Estat(k,l) stand for the subset of cofinality l in k.


Lemma. Let lambda, kappa /in /BigRegCard. Let lambda /in kappa. Then Estat(kappa,lambda) is stationary in kappa.
Proof.
  Let X = Estat(kappa,lambda).
  kappa /in /BigCard.
  X /subset kappa.
  Forall C /subset kappa (C /club kappa => X /cap C /neq /emptyset).
  Proof.
    Let C /subset kappa.
    Let C /club kappa.
    Then C /cof kappa.
    Then kappa /subset otp(C).
    Proof.
      otp(C) /in cofset(kappa).
      cof(kappa) = kappa.
      Then min(cofset(kappa)) = kappa.
      min(cofset(kappa)) /subset otp(kappa).
    end.
    Then lambda /subset cof(kappa).
    C /subset /Ord.
    C /in /VV.
    Take a zffunction f such that (f is an epsiso) /\ f : otp(C) /leftrightarrow C.
    /bigcup f^[lambda] /in /Lim /\ cof(/bigcup f^[lambda]) = cof(lambda).
    Let alpha = /bigcup f^[lambda].
    Then alpha /in /Lim /\ cof(alpha) = lambda.
    alpha /in kappa.
    Proof.
      lambda /in otp(C).
      alpha /subset f[lambda].
      Proof.
        Let a /in alpha.
        Take a zfset b such that b /in f^[lambda] /\ a /in b.
        Take a zfset c such that c /in lambda /\ b = f[c].
        c,lambda /in Dom(f).
        Then f[c] /in f[lambda] (by epsiso).
        f[lambda] /in /Ord.
        Then a /in f[lambda].
      end.
      f[lambda] /in kappa.
      alpha, kappa are ordinals.
      Then alpha /in kappa \/ kappa /in alpha \/ alpha = kappa (by TotalOrder).
      alpha /neq kappa.
      kappa /notin alpha.
      Then alpha /in kappa.
    end.
    Then alpha /in /Lim /cap kappa.
    C /cap alpha /cof alpha.
    Proof.
      Let a /in alpha.
      Take a zfset b such that b /in f^[lambda] /\ a /in b.
      Forall c /in lambda c /in kappa.
      Take a zfset c such that c /in lambda /\ b = f[c].
      c, c+'1 /in Dom(f).
      c /in c+'1.
      Then f[c] /in f[c+'1] (by epsiso).
      c+'1 /in lambda.
      Then f[c+'1] /in f^[lambda].
      Then f[c] /in /bigcup f^[lambda].
      Then f[c] /in C /cap alpha.
      a /in f[c].
    end.
    Then alpha /in C.
  end.
  Then X is stationary in kappa (by stationary).
qed.










