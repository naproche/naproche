[read Formalizations/Library/L08-Cardinal_Arithmetic.ftl]

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
Proof by contradiction. Assume the contrary.
  
  Define M = {ordinal n | n /in /NN /\ exists x (x /subset lambda /\ x /cof lambda /\ Card(x) = n)}.
  M /subset /Ord.
  M /neq /emptyset.
  Let n = min(M).
  Then n /in M.
    
  Take a zfset x such that x /subset lambda /\ x /cof lambda /\ Card(x) = n.
  Take a zffunction f such that f : n /leftrightarrow x.
  Then lambda = /bigcup f^[n].
  n-- /subset Dom(f).
  n-- /in Dom(f).
  /bigcup f^[n] = (/bigcup f^[n--]) /cup f[n--].
  Proof.
    n-- /subset n.
    /bigcup f^[n] /subset (/bigcup f^[n--]) /cup f[n--].
    Proof.
      Let a /in /bigcup f^[n].
      Take a zfset m such that m /in n /\ a /in f[m].
      Then m /in n-- \/ m = n--.
      n-- /subset Dom(f).
      Then a /in (/bigcup f^[n--]) /cup f[n--].
    end.
    (/bigcup f^[n--]) /cup f[n--] /subset /bigcup f^[n].
    Proof.
      Let a /in (/bigcup f^[n--]) /cup f[n--].
      Case a /in f[n--]. (n--) /in n. Then a /in /bigcup f^[n]. end.
      Case a /in /bigcup f^[n--]. Then a /in /bigcup f^[n]. end.
    end.
  end.
  Then lambda = /bigcup f^[n--] /cup f[n--].
  
  /bigcup f^[n--] /in /Ord.
  Proof.
    f^[n--] /subset /Ord.
    Trans(/bigcup f^[n--]).
  end.
  f[n--] /in x.
  Then f[n--] /in /Ord.
  
  Then lambda = /bigcup f^[n--] \/ lambda = f[n--].
  Proof.
    Take ordinals alpha, beta such that alpha = /bigcup f^[n--] /\ beta = f[n--].
    Then alpha /in beta \/ beta /in alpha \/ alpha = beta.
    Then alpha /cup beta = alpha \/ alpha /cup beta = beta.
  end.
  
  Then lambda = /bigcup f^[n--].
  
  Then f^[n--] /cof lambda.
  
  n--,f^[n--] are zfsets.
  Card(f^[n--]) = Card(n--).
  Proof.
    f /upharpoonright (n--) : n-- /leftrightarrow f^[n--].
    Proof.
      Dom(f /upharpoonright (n--)) = n--.
      ran(f /upharpoonright (n--)) = f^[n--].
      Proof.
        ran(f /upharpoonright (n--)) /subset f^[n--].
        Proof.
          Let a /in ran(f /upharpoonright (n--)).
          Take a zfset m such that m /in (n--) /\ a = (f /upharpoonright (n--))[m].
          Then m /in n.
          Then a = f[m].
          Then a /in f^[n--].
        end.
        f^[n--] /subset ran(f /upharpoonright (n--)).
        Proof.
          Let a /in f^[n--].
          Forall m /in (n--) m /in Dom(f).
          Take a zfset m such that m /in (n--) /cap Dom(f) /\ a = f[m].
          Then a = (f /upharpoonright (n--))[m].
          Then a /in ran(f /upharpoonright (n--)).
        end.
      end.
      f /upharpoonright (n--) is injective.
      Proof.
        f is injective.
        Let a1,a2 /in (n--). Let a1 /neq a2.
        Then a1,a2 /in n.
        Then f[a1] /neq f[a2].
        Then (f /upharpoonright (n--))[a1] /neq (f /upharpoonright (n--))[a2].
      end.
    end.
  end.
  
  n-- /in /NN.
  Then Card(n--) = n--.
  Then n-- /in M.
  Proof.
    f^[n--] /subset lambda.
    f^[n--] /cof lambda.
    Card(f^[n--]) = n--.
  end.  
  Contradiction.
qed.


Signature. Let lambda /in /Lim. The cofinality of lambda is a notion.
Let cof(x) stand for the cofinality of x.


Definition. Let lambda /in /Lim. The cofset of lambda is {otp(x) | x /subset lambda /\ x /cof lambda}.
Let cofset(x) stand for the cofset of x.


Lemma. Let lambda /in /Lim. Then cofset(lambda) /subset /Ord.
Proof.
  Let x /subset lambda /\ x /cof lambda.
  Then x /in /VV.
  x /subset /Ord.
  Then otp(x) /in /Ord.
qed.


Lemma. Let lambda /in /Lim. cofset(lambda) /neq /emptyset.
Proof.
  lambda /cof lambda.
qed.


Axiom. Let lambda /in /Lim. Then cof(lambda) = min(cofset(lambda)).


Lemma. Let lambda /in /Lim. Then cof(lambda) /in /Ord.
Proof.
  cofset(lambda) /subset /Ord.
qed.


Lemma. Let lambda /in /Lim. cof(lambda) /in cofset(lambda).
Proof.
  cof(lambda) = min(cofset(lambda)).
qed.


Lemma. Let lambda /in /Lim. Then cof(lambda) /subset lambda.
Proof.
  lambda /in cofset(lambda).
  Proof.
    lambda /cof lambda.
    lambda = otp(lambda).
  end.
  Then /bigcap cofset(lambda) /subset lambda.
qed.


Definition. Let lambda /in /Lim. lambda is regular iff cof(lambda) = lambda.


Definition. Let lambda /in /Lim. lambda is singular iff cof(lambda) /neq lambda.


Lemma. Let lambda /in /Lim. Let lambda be singular. Then cof(lambda) /in lambda.
Proof.
  cof(lambda) /subset lambda.
  cof(lambda) /neq lambda.
qed.


Definition. Let lambda /in /Lim. The alternativecofset of lambda is {Card(x) | (x is a zfset) /\ x /subset lambda /\ x /cof lambda}.
Let cofset2(x) stand for the alternativecofset of x.


Lemma. Let lambda /in /Lim. Then cofset2(lambda) /neq /emptyset.
Proof.
  lambda /cof lambda.
  Then Card(lambda) /in cofset2(lambda).
qed.


Lemma. Let lambda /in /Lim. Then cof(lambda) = min(cofset2(lambda)).
Proof.
  min(cofset2(lambda)) /subset cof(lambda).
  Proof.
    Let y /in min(cofset2(lambda)).
    Then forall z /in cofset2(lambda) y /in z.
    Then forall z /in cofset(lambda) y /in z.
    Proof.
      Let z /in cofset(lambda).
      Take a zfset x such that x /subset lambda /\ x /cof lambda /\ z = otp(x).
      x /subset /Ord.
      Then Card(x) /subset otp(x).
      y /in Card(x).
    end.
    Then y /in cof(lambda).
  end.
  cofset2(lambda) /subset /Ord.
  min(cofset2(lambda)) /in cofset2(lambda).
 
  cof(lambda) /subset min(cofset2(lambda)).
  Proof.
    Take a zfset x such that x /subset lambda /\ x /cof lambda /\ Card(x) = min(cofset2(lambda)).
    Take a zffunction f such that f : Card(x) /leftrightarrow x.
    Define g[n] = /bigcup f^[n] for n in Card(x).
    Then g : Card(x) /rightarrow lambda.
    Proof.
      Forall n /in Card(x) g[n] /in /Ord.
      Proof.
        Let n /in Card(x). Then f^[n] /subset /Ord.
        Then Trans(/bigcup f^[n]).
      end.
      Forall n /in Card(x) g[n] /in lambda.
      Proof by Contradiction. Assume the contrary.
        Take a zfset n such that n /in Card(x) /\ g[n] /notin lambda.
        g[n] /subset lambda.
        Proof.
          f^[n] /subset lambda.
          Then /bigcup f^[n] /subset lambda.
        end.
        Then g[n] = lambda.
        f^[n] /subset lambda.
        f^[n] /cof lambda.
        Then Card(f^[n]) /in cofset2(lambda).
        Card(f^[n]) = Card(n).
        Proof.
          f /upharpoonright n : n /leftrightarrow f^[n].
          Proof.
            Dom(f /upharpoonright n) = n.
            ran(f /upharpoonright n) = f^[n].
            f /upharpoonright n is injective.
          end.
        end.
        Card(n) /in Card(x).
        Card(n) /in cofset2(lambda).
        Contradiction.
      end.
      g is a zffunction.
    end.
  
    g^[Card(x)] /cof lambda.
    Proof.
      Let alpha /in lambda.
      Take a zfset y such that y /in x /\ alpha /in y.
      Take a zfset beta such that beta /in Card(x) /\ f[beta] = y.
      Then beta +' 1 /in Card(x).
      Proof.
        Card(x) /notin /NN.
        Card(x) /in /Lim.
      end.
      beta /in beta +' 1.
      Then y /in f^[beta +' 1].
      Then alpha /in g[beta +' 1].
    end.    
    Forall a1,a2 /in Card(x) (a1 /in a2 => g[a1] /subset g[a2]).
    Proof.
      Let a1,a2 /in Card(x). Let a1 /in a2.
      Then f^[a1] /subset f^[a2].
      Then /bigcup f^[a1] /subset /bigcup f^[a2].
    end.
  
    Define M = {ordinal i | i /in Card(x) /\ forall j /in i (g[j] /in g[i])}.
    Let h = g /upharpoonright M.
    Forall i /in M h[i] = g[i].
    Proof.
      Let i /in M.
      Then g[i] = (g /upharpoonright M)[i].
    end.    
    Then h is an epsiso.
    Proof.
      Forall i /in M (h[i] is a zfset).
      h is a zffunction.
      Forall i,j /in M (i /in j => h[i] /in h[j]).
      Proof.
        Let i,j /in M.
        Let i /in j.
        h[i] = g[i].
        h[j] = g[j].
        g[i] /in g[j].
      end.
      Forall i,j /in M (h[i] /in h[j] => i /in j).
      Proof.
        Let i,j /in M.
        Let h[i] /in h[j].
        Take an ordinal a such that a = i.
        Take an ordinal b such that b = j.
        a,b /in /Ord.
        Then a /in b \/ b /in a \/ a = b (by TotalOrder).
        Then i /in j \/ j /in i \/ i = j.
        i /neq j.
        Proof by contradiction. Assume the contrary.
          Then h[i] = h[j].
          Contradiction.
        end.
        j /notin i.
        Proof by contradiction. Assume the contrary.
          Then h[j] /in h[i].
          h[i] /in h[j].
          Contradiction.
        end.
        Then i /in j.
      end.
      h is injective.
      Proof.
        Let i,j /in Dom(h).
        Let i /neq j.
        i,j /in /Ord.
        Then i /in j \/ j /in i \/ i = j (by TotalOrder).
        Then i /in j \/ j /in i.
        Then h[i] /in h[j] \/ h[j] /in h[i].
        Then h[i] /neq h[j].
      end.
      Forall i,j /in Dom(h) (i /in j iff h[i] /in h[j]).
    end.
    
    h^[M] /subset lambda.
    Proof.
      Let i /in M. Then h[i] = g[i].
      g[i] /in lambda.
    end.  
    h^[M] /cof lambda.
    Proof.
      Let alpha /in lambda.
      Take a zfset y such that y /in Card(x) /\ alpha /in g[y].
      Case y /in M. Then alpha /in h[y]. end.
      Case y /notin M.
        Define N = {ordinal z | z /in y /\ g[z] /notin g[y]}.
        Forall z /in N g[z] = g[y].
        Proof.
          Let z /in N.
          Then z /in y.
          z,y /in Card(x).
          z /in y.
          Then g[z] /subset g[y] /\ g[z] /notin g[y].
          g[z], g[y] /in /Ord.
          Proof.
            g : Card(x) /rightarrow lambda.
            Forall a /in Card(x) g[a] /in lambda.
            Then forall a /in Card(x) g[a] /in /Ord.
          end.
          Take ordinals alpha1, beta1 such that alpha1 = g[z] /\ beta1 = g[y].
          Then alpha1 /in beta1 \/ beta1 /in alpha1 \/ alpha1 = beta1.
          alpha1 /notin beta1 /\ alpha1 /subset beta1.
          Then alpha1 = beta1.
        end.
        N /neq /emptyset.
        N /subset /Ord.
        Let yy = min(N).
        min(N) /in N.
        Then yy /in N.
        g[yy] = g[y].
        yy /in M.
        Proof.
          Forall j /in yy (j /in Card(x) /\ g[j] /in g[yy]).
          Proof.
            Let j /in yy.
            j,yy /in Card(x).
            Proof.
              yy /in Card(x).
              Trans(Card(x)).
              Then j /in Card(x).
            end.
            Then g[j] /subset g[yy].
            ran(g) /subset /Ord.
            g[j], g[yy] /in /Ord.
            g[j] /in g[yy] \/ g[j] = g[yy].
            Case g[j] = g[yy]. Then j /in N. Contradiction. end.
            Case g[j] /in g[yy]. end.
          end.
          yy /in Card(x).
        end.
        Then alpha /in h[yy].
      end.
    end.
    
    h : M /leftrightarrow h^[M].
    h^{-1} : h^[M] /leftrightarrow M.    
    M /subset Card(x).
    Then otp(M) /subset Card(x).    
    M /subset /Ord.
    otpfunc(M) : M /leftrightarrow otp(M).
    otpfunc(M) /circ h^{-1} : h^[M] /leftrightarrow otp(M).
    Proof.
      Dom(otpfunc(M) /circ h^{-1}) = h^[M].
      ran(otpfunc(M) /circ h^{-1}) = otp(M).
      otpfunc(M) /circ h^{-1} is injective.
    end.
    otpfunc(M) is an epsiso.
    h^{-1} is an epsiso.
    Then otpfunc(M) /circ h^{-1} is an epsiso.   
    Then otp(h^[M]) = otp(M).
    Proof.
      h^[M] /subset /Ord.
      Let y = otp(M).
      y /in /Ord.
      Exists F ((F is an epsiso) /\ F : h^[M] /leftrightarrow y).
      Then otp(h^[M]) = y.
    end.
       
    Then otp(M) /in cofset(lambda).
    Then /bigcap cofset(lambda) /subset otp(M).
    Then cof(lambda) /subset otp(M).
    otp(M) /subset Card(x).
    Then cof(lambda) /subset Card(x).    
  end.
qed.


Lemma. Let lambda /in /Lim. Then cof(lambda) = min(cofset2(lambda)).


Lemma. Let lambda /in /Lim. Then cof(lambda) /in cofset2(lambda).
Proof.
  cofset2(lambda) /subset /Ord.
  cofset2(lambda) /neq /emptyset.
  min(cofset2(lambda)) /in cofset2(lambda).
qed.


Lemma. Forall lambda /in /Lim cof(lambda) /subset Card(lambda).
Proof.
  Let lambda /in /Lim.
  Card(lambda) /in cofset2(lambda).
  Proof.
    lambda /subset lambda. lambda /cof lambda.
  end.
  Then /bigcap cofset2(lambda) /subset Card(lambda).  
qed.


Lemma. Forall lambda /in /Lim /NN /subset cof(lambda).
Proof.
  Let lambda /in /Lim.
  Forall x /in cofset2(lambda) /NN /subset x.
  Proof.
    Let x /in cofset2(lambda).
    Take a zfset y such that y /subset lambda /\ y /cof lambda /\ Card(y) = x.
    Then Card(y) /notin /NN.
    Card(y) /in /Ord.
    Then Card(y) /in /NN \/ /NN /in Card(y) \/ /NN = Card(y).
    Then /NN /subset Card(y).
  end.
  Then /NN /subset /bigcap cofset2(lambda).
qed.


Lemma. cof(/NN) = /NN.
Proof.
  cof(/NN) /subset /NN.
  /NN /subset cof(/NN).
qed.


Lemma. Forall lambda /in /Lim cof(lambda) /in /Card.
Proof.
  Let lambda /in /Lim.
  cof(lambda) /in cofset2(lambda).
  cofset2(lambda) /subset /Cd.
  Then cof(lambda) /in /Cd.
  /NN /subset cof(lambda).
qed.


Lemma. Let lambda /in /Lim. Exists x (x /subset lambda /\ x /cof lambda /\ otp(x) = cof(lambda)).
Proof.
  cof(lambda) /in cofset(lambda).
qed.

Lemma. Let lambda /in /Lim. Exists x (x /subset lambda /\ x /cof lambda /\ Card(x) = cof(lambda)).
Proof.
  cof(lambda) /in cofset2(lambda).
qed.


Lemma. Forall lambda /in /Lim (cof(lambda) is regular).
Proof.
  Let lambda /in /Lim.
  cof(cof(lambda)) /subset cof(lambda).

  cof(lambda) /subset cof(cof(lambda)).
  Proof.
    Take an ordinal gamma such that gamma = cof(lambda).
    gamma /in cofset(lambda).
    Take a zfset x such that x /subset lambda /\ x /cof lambda /\ otp(x) = gamma.
    x /subset /Ord.
    Then otpfunc(x) : x /leftrightarrow gamma.
    Let f = (otpfunc(x))^{-1}. 
    Then f : gamma /leftrightarrow x.
    f is an epsiso.
    cof(gamma) /in cofset(gamma).
    Take a zfset y such that y /subset gamma /\ y /cof gamma /\ otp(y) = cof(gamma).
    y /subset /Ord.
    Then otpfunc(y) : y /leftrightarrow cof(gamma).
    Let g = (otpfunc(y))^{-1}. 
    Then g : cof(gamma) /leftrightarrow y.
    g is an epsiso.
    Let h = f /circ g.
    Then h : cof(gamma) /rightarrow x.
    Proof.
      Let a /in cof(gamma). 
      Then g[a] /in y.
      Then f[g[a]] /in x.
      Then h[a] /in x.
    end.
    h is an epsiso.
    Let z = h^[cof(gamma)].
    h^{-1} : z /leftrightarrow cof(gamma).
    h^{-1} is an epsiso.
    cof(gamma) /in /Ord.
    z /subset /Ord.
    Then otp(z) = cof(gamma).
    z /cof lambda.
    Proof. 
      Let alpha /in lambda.
      x /cof lambda.
      Take a zfset xa such that xa /in x /\ alpha /in xa.
      f : gamma /leftrightarrow x.
      Take a zfset beta such that beta /in gamma /\ f[beta] = xa.
      y /cof gamma.
      Take a zfset yb such that yb /in y /\ beta /in yb.
      g : cof(gamma) /leftrightarrow y.
      Take a zfset delta such that delta /in cof(gamma) /\ g[delta] = yb.
      Then h[delta] = f[yb].
      f is an epsiso.
      Forall a,b /in Dom(f) (a /in b iff f[a] /in f[b]) (by epsiso).
      beta, yb /in Dom(f).
      beta /in yb iff f[beta] /in f[yb].
      beta /in yb.
      Then f[beta] /in f[yb].
      alpha /in f[beta].
      f[yb] /in /Ord.
      Then alpha /in f[yb].
    end.
    Then otp(z) /in cofset(lambda).
    Then /bigcap cofset(lambda) /subset otp(z).
    Then cof(lambda) /subset cof(gamma).
  end.  
qed.


Lemma. Forall alpha /in /Ord Alef[alpha] /in /Lim.
Proof.
  Let alpha /in /Ord.
  Then Alef[alpha] /in /Card.
qed.


Lemma. Let alpha /in /Lim. Then cof(Alef[alpha]) = cof(alpha).
Proof.
  cof(Alef[alpha]) /subset cof(alpha).
  Proof.
    Take a zfset x such that x /subset alpha /\ x /cof alpha /\ Card(x) = cof(alpha).
    Let y = Alef^[x].
    Then y /subset Alef[alpha].
    Proof.
      Let a /in y.
      Take a zfset b such that b /in x /\ a = Alef[b].
      Then b /in alpha.
      Then Alef[b] /in Alef[alpha].
    end.
    y /cof Alef[alpha].
    Proof.
      Let a /in Alef[alpha].
      Alef[alpha] = /bigcup Alef^[alpha].
      Take a zfset beta such that beta /in alpha /\ a /in Alef[beta].
      x /cof alpha.
      Take a zfset z such that z /in x /\ beta /in z.
      Then Alef[z] /in y.
      Alef[beta] /subset Alef[z].
      a /in Alef[z].
    end.
    Card(y) = Card(x).
    Proof.
      Alef /upharpoonright x : x /leftrightarrow y.
      Proof.
        Dom(Alef /upharpoonright x) = x.
        Alef is a zffunction.
        x /subset Dom(Alef).
        ran(Alef /upharpoonright x) = Alef^[x].
        ran(Alef /upharpoonright x) = y.
        Alef /upharpoonright x is injective.
        Proof.
          Let a1,a2 /in x.
          Let a1 /neq a2.
          Then Alef[a1] /neq Alef[a2].
          Proof.
            Forall b1, b2 /in /Ord (b1 /in b2 \/ b2 /in b1 \/ b1 = b2).
            a1,a2 /in /Ord.
            Then a1 /in a2 \/ a2 /in a1 \/ a1 = a2.
            a1 /in a2 \/ a2 /in a1.
            Case a1 /in a2. Then Alef[a1] /in Alef[a2]. end.
            Case a2 /in a1. Then Alef[a2] /in Alef[a1]. end.
          end.
        end.
      end.
    end.
    Then Card(y) /in cofset2(Alef[alpha]).
    Then min(cofset2(Alef[alpha])) /subset Card(y).
  end.
  
  cof(alpha) /subset cof(Alef[alpha]).
  Proof.
    Take a zfset x such that x /subset Alef[alpha] /\ x /cof Alef[alpha] /\ 
    Card(x) = cof(Alef[alpha]).
    Forall y /in x exists beta /in alpha y /in Alef[beta].
    Proof.
      Alef[alpha] = /bigcup Alef^[alpha].
    end.
    Define f[n] = (choose zfset beta such that beta /in alpha /\ n /in Alef[beta] in beta) 
    for n in x.
    f is a zffunction.
    Proof.
      Let n /in x.
      Then f[n] /in /VV.
    end.
    ran(f) /subset alpha.
    Proof.
      Let n /in Dom(f).
      Then f[n] /in alpha.
    end.
    Let y = f^[x].
    Then y /subset alpha.
    y /cof alpha.
    Proof.
      Let beta /in alpha.
      Then Alef[beta] /in Alef[alpha].
      Take a zfset z such that z /in x /\ Alef[beta] /in z.
      Then f[z] /in y.
      z /in Alef[f[z]].
      Then Alef[beta] /in Alef[f[z]].
      Then beta /in f[z].
      Proof.
        beta, f[z] /in /Ord.
        Then beta /in f[z] \/ f[z] /in beta \/ f[z] = beta.
        Case beta /in f[z]. end.
        Case f[z] /in beta. 
          Then Alef[f[z]] /in Alef[beta].
          Take ordinals a1,a2 such that a1 = Alef[beta] /\ a2 = Alef[f[z]].
          Then a1 /in a2 /\ a2 /in a1.
          Contradiction. 
        end.
        Case f[z] = beta. 
          Then Alef[beta] = Alef[f[z]]. 
          Contradiction. 
        end.
      end.
    end.
    Card(y) /subset Card(x).
    Proof.
      f is a zffunction.
      x /subset Dom(f).
      Then Card(f^[x]) /subset Card(x).
    end.
    Card(y) /in cofset2(alpha).
    Then min(cofset2(alpha)) /subset Card(y).
    Then min(cofset2(alpha)) /subset Card(x).
  end.  
qed.


Lemma. cof(Alef[/NN]) = /NN.


Lemma exsurj. Let x be a zfset. Let x /neq /emptyset. Let alpha /in /Ord. Let Card(x) /subset alpha. Then exists f (f : alpha /rightarrow x /\ ran(f) = x).
Proof.
  Take a zffunction g such that g : Card(x) /leftrightarrow x.
  Take a zfset b such that b /in x.
  Define f[n] =
    Case n /in Card(x) -> g[n],
    Case n /notin Card(x) -> b
  for n in alpha.
  Then f : alpha /rightarrow x.
  Proof.
    Dom(f) = alpha.
    Let beta /in alpha. Then f[beta] /in x.
  end.
  ran(f) = x.
  Proof.
    Let y /in x.
    Take a zfset beta such that beta /in Card(x) /\ g[beta] = y.
    Then f[beta] = y.
  end.
qed.


Lemma. Forall alpha /in /Ord cof(Alef[alpha +' 1]) = Alef[alpha +' 1].
Proof by contradiction. Assume the contrary.
  Take an ordinal alpha such that alpha /in /Ord /\ cof(Alef[alpha +' 1]) /neq Alef[alpha +' 1].
  Take a zfset x such that x /subset Alef[alpha +' 1] /\ x /cof Alef[alpha +' 1] /\ Card(x) = cof(Alef[alpha +' 1]).
  Then Card(x) /subset Alef[alpha].
  Proof.
    Card(x) /subset Alef[alpha +' 1].
    Card(x) /neq Alef[alpha +' 1].
    /NN /subset Card(x).
    Take an ordinal beta such that Card(x) = Alef[beta].
    Then beta /in alpha +' 1.
    Then beta /in alpha \/ beta = alpha.
    Then beta /subset alpha.
    Then Card(x) /subset Alef[alpha].
  end.
  Forall i /in Alef[alpha +' 1] Card(i) /subset Alef[alpha].
  Proof.
    Let i /in Alef[alpha +' 1].
    Then i /in /Ord.
    i /subset Alef[alpha +' 1].
    Card(i) /subset i.
    Then Card(i) /subset Alef[alpha +' 1].
    Card(i) /neq Alef[alpha +' 1].
    Card(i) /in /NN \/ /NN /subset Card(i).
    Proof.
      Card(i), /NN /in /Ord.
      Then Card(i) /in /NN \/ /NN /in Card(i) \/ /NN = Card(i) (by TotalOrder).
    end.
    Case Card(i) /in /NN. 
      /NN /subset Alef[alpha].
      Card(i) /subset /NN.
      Then Card(i) /subset Alef[alpha].
    end.
    Case /NN /subset Card(i).
      Take an ordinal beta such that Card(i) = Alef[beta].
      Then beta /in alpha +' 1.
      Then beta /in alpha \/ beta = alpha.
      Then beta /subset alpha.
      Then Card(i) /subset Alef[alpha].
    end.
  end.
  
  Take a zffunction f such that f : Alef[alpha] /rightarrow x /\ ran(f) = x.
  
  Forall i /in Alef[alpha +' 1] (exists h (h : Alef[alpha] /rightarrow i+'1 /\ ran(h) = i+'1)).
  Proof.
    Let i /in Alef[alpha +' 1].
    Then i+'1 /in Alef[alpha +' 1].
    Card(i+'1) /subset i+'1.
    Card(i+'1) /in /Ord.
    Then Card(i+'1) = i+'1 \/ Card(i+'1) /in i+'1.
    Alef[alpha +' 1] /in /Ord.
    Then Card(i+'1) /in Alef[alpha +' 1].
    Then Card(i+'1) /subset Alef[alpha].
    i+'1 /neq /emptyset.
    i+'1 is a zfset.
    Alef[alpha] /in /Ord.
    Then exists h (h : Alef[alpha] /rightarrow i+'1 /\ ran(h) = i+'1) (by exsurj).
  end.
  Define g[i] = (choose a zffunction phi such that (phi : Alef[alpha] /rightarrow (i+'1) /\ ran(phi) = (i+'1)) in phi)
  for i in Alef[alpha +' 1].
  
  Forall a /in Alef[alpha] f[a] /in Alef[alpha +' 1].
  Forall a,b /in Alef[alpha] (f[a] /in Dom(g) /\ b /in Dom(g[f[a]])).
  Forall o1,o2 ((o1,o2) /in Alef[alpha] /times Alef[alpha] => o1,o2 /in Alef[alpha]).
  
  Define h[(a,b)] = (g[f[a]])[b] for (a,b) in Alef[alpha] /times Alef[alpha].
  
  h is a zffunction.
  Proof.
    Let pair /in Alef[alpha] /times Alef[alpha].
    Take zfsets a,b such that a,b /in Alef[alpha] /\ pair = (a,b).
    Then f[a] /in x.
    Then g[f[a]] is a zffunction.
    Dom(g[f[a]]) = Alef[alpha].
    Then (g[f[a]])[b] /in /VV.
    (g[f[a]])[b] = h[pair].
    Then h[pair] /in /VV.
  end.
  
  Alef[alpha +' 1] /subset h^[Alef[alpha] /times Alef[alpha]].
  Proof.
    Let a /in Alef[alpha +' 1].
    Take a zfset b such that b /in x /\ a /in b.
    Take a zfset c such that c /in Alef[alpha] /\ f[c] = b.
    a /in ran(g[b]).
    Take a zfset d such that d /in Alef[alpha] /\ (g[b])[d] = a.
    Then (g[f[c]])[d] = a.
    Let pair = (c,d).
    Then pair /in Alef[alpha] /times Alef[alpha].
    h[pair] = (g[f[c]])[d].
    Then h[pair] = a.
    Then a /in h^[Alef[alpha] /times Alef[alpha]].
  end.
  
  Then Card(Alef[alpha +' 1]) /subset Card(h^[Alef[alpha] /times Alef[alpha]]).
  Card(h^[Alef[alpha] /times Alef[alpha]]) /subset Card(Alef[alpha] /times Alef[alpha]).
  Card(Alef[alpha +' 1]) = Alef[alpha +' 1].
  Card(Alef[alpha] /times Alef[alpha]) = Alef[alpha].
  Then Alef[alpha +' 1] /subset Alef[alpha].
  Proof.
    Take a zfset a such that a = Card(Alef[alpha +' 1]).
    h^[Alef[alpha] /times Alef[alpha]] is a zfset.
    Take a zfset b such that b = Card(h^[Alef[alpha] /times Alef[alpha]]).
    Alef[alpha] /times Alef[alpha] is a zfset.
    Take a zfset c such that c = Card(Alef[alpha] /times Alef[alpha]).
    a /subset b.
    b /subset c.
    Then a /subset c.
    a = Alef[alpha +' 1].
    c = Alef[alpha].
  end.
  Alef[alpha] /in Alef[alpha +' 1].
  
  Contradiction.  
qed.


Lemma. Forall alpha /in /Succ (Alef[alpha] is regular).
Proof.
  Let alpha /in /Succ.
  Take an ordinal beta such that alpha = beta +' 1.
  Then Alef[alpha] = Alef[beta +' 1].
  Alef[beta +' 1] is regular.
qed.



