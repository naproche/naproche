[read Formalizations/Library/L17-Disjoint_Stationary_Subsets.ftl]


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
Proof.
  F /subset ^{lambda}/VV.
qed.

Axiom adfam. Let lambda /in /Lim. Let F be an almost disjoint family of functions on lambda. Then forall f,g /in F (f /neq g => (f and g are almost disjoint on lambda)).

Signature. An adfampair is a notion.
Axiom adfampair. Let a,b be objects. (a,b) is an adfampair iff b /in /Lim /\ a /subset ^{b}/VV.
Lemma. Let lambda /in /Lim. Let F be an almost disjoint family of functions on lambda. Then (F,lambda) is an adfampair.
Lemma. Let lambda, F be objects. Let (F,lambda) be an adfampair. Then forall f /in F (f is a zffunctions and f /in ^{lambda}/VV).
Proof.
  F /subset ^{lambda}/VV.
qed.

Axiom adfam2. Let lambda, F be objects. Let (F,lambda) be an adfampair. Let forall f,g /in F (f /neq g => (f and g are almost disjoint on lambda)).
Then F is an almost disjoint family of functions on lambda.

Lemma. Let lambda /in /Ord. Let A be a zffunction. Let Dom(A) = lambda. Let F /subset /prodset A. Then F /subset ^{lambda}/VV.

Definition. The class of singular cardinals of uncountable cofinality is
{kappa /in /BigCard | kappa is singular}.
Let /BigSingCard stand for the class of singular cardinals of uncountable cofinality.

Lemma. Let kappa /in /BigSingCard. Then exists alpha /in /Lim (kappa = Alef[alpha]).
Proof.
  Take an ordinal alpha such that kappa = Alef[alpha].
  Then alpha /in /Lim.
  Proof.
    Case alpha = 0. Contradiction. end.
    Case alpha /in /Succ. Then Alef[alpha] is regular. Contradiction. end.
    Case alpha /in /Lim. end.
  qed.
qed.



## New notions to store information


Lemma. Let kappa /in /Lim. Then exists x /subset kappa (otp(x) = cof(kappa) /\ x /club  kappa).
Proof.
  Take a zfset x such that x /subset kappa /\ otp(x) = cof(kappa) /\ x /cof kappa.
  Let lambda = cof(kappa).
  lambda /in /Ord.
  x /subset /Ord.
  Take a zffunction f such that f : lambda /leftrightarrow x /\ (f is an epsiso).
  Forall a,b /in lambda (a /in b => f[a] /in f[b]) (by epsiso).
  Define g[i] =
    Case i /in /Lim -> /bigcup f^[i],
    Case i /notin /Lim -> f[i]
  for i in lambda.
  g is a zffunction.
  Proof.
    Forall i /in lambda g[i] /in /VV.
    Proof.
      Let i /in lambda.
      Case i /notin /Lim.
        Then g[i] = f[i].
      end.
      Case i /in /Lim.
        Then g[i] = /bigcup f^[i].
      end.
    end.
  end.
  Forall a /in lambda g[a] /subset f[a].
  Proof.
    Let a /in lambda.
    Then g[a] /subset f[a].
    Proof.
      Case a /notin /Lim.
        Then f[a] = g[a].
      end.
      Case a /in /Lim.
        Forall b /in g[a] b /in f[a].
        Proof.
          Let b /in g[a].
          g[a] = /bigcup f^[a].
          Take a zfset y such that y /in f^[a] /\ b /in y.
          Forall c /in a c /in Dom(f).
          Take a zfset c such that c /in a /\ y = f[c].
          Then b /in f[c].
          c /in a.
          c,a /in Dom(f).
          Then f[c] /in f[a] (by epsiso).
          f[a] /in /Ord.
          Then b /in f[a].
        end.
        Then g[a] /subset f[a].
      end.
    end.
  end.
  g : lambda /rightarrow kappa.
  Proof.
    Let i /in lambda.
    Then g[i] /in kappa.
    Proof.
      Case i /notin /Lim.
        Then g[i] = f[i].
      end.
      Case i /in /Lim.
        Then g[i] = /bigcup f^[i].
        f^[i] /subset /Ord.
        f^[i] /neq /emptyset.
        Then /bigcup f^[i] /in /Ord.
        Then g[i],f[i] /in /Ord.
        g[i] /subset f[i].
        Then g[i] /in f[i] \/ g[i] = f[i].
        f[i] /in kappa.
        Then g[i] /in kappa.
      end.
    end.
  end.
  Forall a,b /in Dom(g) (a /in b iff g[a] /in g[b]).
  Proof.
    Forall a,b /in Dom(g) (a /in b => g[a] /in g[b]).
    Proof.
      Let a,b /in lambda.
      Let a /in b.
      Then g[a] /in g[b].
      Proof.
        a,b /in Dom(f).
        Then f[a] /in f[b] (by epsiso).
        Case b /notin /Lim.
          Then g[b] = f[b].
          g[a] /subset f[a].
          g[a] /in /Ord.
          Proof.
            a /in lambda.
            Then g[a] /in kappa.
          end.
          f[a] /in /Ord.
          Then g[a] /in f[a] \/ g[a] = f[a].
          Then g[a] /in g[b].
        end.
        Case b /in /Lim.
          Then g[b] = /bigcup f^[b].
          g[a] /subset f[a].
          g[a] /in /Ord.
          Proof.
            a /in lambda.
            Then g[a] /in kappa.
          end.
          f[a] /in /Ord.
          Then g[a] /in f[a] \/ g[a] = f[a].
          a /in a++.
          a,a++ /in Dom(f).
          Then f[a] /in f[a++] (by epsiso).
          f[a++] /in /Ord.
          Then g[a] /in f[a++].
          f[a++] /in f^[b].
          Then g[a] /in /bigcup f^[b].          
        end.
      end.
    end.
    Forall a,b /in Dom(g) (g[a] /in g[b] => a /in b).
    Proof by contradiction. Assume the contrary.
      Take zfsets a,b such that a,b /in Dom(g) /\ g[a] /in g[b] /\ a /notin b.
      a,b /in /Ord.
      Then b /in a \/ a = b.
      Case a = b.
        Then g[a] = g[b].
        Contradiction.
      end.
      Case b /in a.
        Then g[b] /in g[a].
        Contradiction.
      end.
    end.
  end.
  g is injective.
  Proof.
    Let a,b /in Dom(g).
    Let a /neq b.
    Then g[a] /neq g[b].
    Proof.
      a /in b \/ b /in a.
      Then g[a] /in g[b] \/ g[b] /in g[a].
    end.
  end.
  Then g is an epsiso (by epsiso).

  Forall i /in lambda /cap /Lim g[i] = /bigcup g^[i].
  Proof.
    Let i /in lambda /cap /Lim.
    Then g[i] = /bigcup f^[i].
    g[i] /subset /bigcup g^[i].
    Proof.
      Let a /in g[i].
      Then a /in /bigcup f^[i].
      Take a zfset z such that z /in f^[i] /\ a /in z.
      Forall b /in i b /in Dom(f).
      Take a zfset b such that b /in i /\ z = f[b].
      Then a /in f[b].
      b, b++ /in Dom(f).
      b /in b++.
      Then f[b] /in f[b++] (by epsiso).
      f[b++] /in /Ord.
      Then a /in f[b++].
      b++ /notin /Lim.
      Then g[b++] = f[b++].
      Then a /in g[b++].
      b++ /in i.
      Then g[b++] /in g^[i].
      Then a /in /bigcup g^[i].
    end.
    /bigcup g^[i] /subset g[i].
    Proof.
      Let a /in /bigcup g^[i].
      Take a zfset z such that z /in g^[i] /\ a /in z.
      Forall b /in i b /in Dom(g).
      Take a zfset b such that b /in i /\ z = g[b].
      Then a /in g[b].
      b, b++ /in Dom(g).
      b /in b++.
      Then g[b] /in g[b++] (by epsiso).
      g[b++] /in kappa.
      g[b++] /in /Ord.
      Then a /in g[b++].
      b++ /notin /Lim.
      Then g[b++] = f[b++].
      Then a /in f[b++].
      b++ /in i.
      Then f[b++] /in f^[i].
      Then a /in /bigcup f^[i].
      Then a /in g[i].
    end.
  end.

  Let y = ran(g).
  Then g : lambda /leftrightarrow y.
  lambda /in /Ord.
  y /subset /Ord.
  Then otp(y) = lambda.
  y /subset kappa.
  y /club kappa.
  Proof.
    y /cof kappa.
    Proof.
      Let alpha /in kappa.
      Take a zfset z such that z /in x /\alpha /in z.
      Take a zfset beta such that beta /in lambda /\ f[beta] = z.
      Then alpha /in f[beta].
      beta ++ /in lambda.
      beta ++ /notin /Lim.
      Then g[beta ++] = f[beta ++].
      beta, beta ++ /in Dom(f).
      beta /in beta ++.
      Then f[beta] /in f[beta ++] (by epsiso).
      f[beta ++] /in /Ord.
      Then f[beta] /subset f[beta ++].
      Then alpha /in f[beta ++].
      Then alpha /in g[beta ++].
      g[beta ++] /in y.
    end.
    y /closed kappa.
    Proof.
      Let lam /in /Lim /cap kappa.
      Let y /cap lam /cof lam.
      Then lam /in y.
      Proof.
        Define z = {alpha /in lambda | g[alpha] /in y /cap lam}.
        z is a zfset.
        Proof.
          z /subset lambda.
        end.
        g^[z] = y /cap lam.
        z /in /Ord.
        Proof.
          z /subset /Ord.
          z /in /VV.
          Trans(z).
          Proof.
            Let a /in z.
            Let b /in a.
            Then b /in z.
            Proof.
              a,b /in Dom(g).
              b /in a.
              Then g[b] /in g[a] (by epsiso).
              g[a] /in y /cap lam.
              Then g[b] /in y /cap lam.
              Then b /in z.
            end.
          end.
        end.
        z /in /Lim.
        Proof by contradiction. Assume the contrary.
          Then z = 0 \/ z /in /Succ.
          Case z = 0.
            Then g^[z] = /emptyset.
            Contradiction.
          end.
          Case z /in /Succ.
            Take a zfset zz such that z = zz ++.
            Then g[zz] /in y /cap lam.
            y /cap lam /cof lam.
            Take a zfset a such that a /in y /cap lam /\ g[zz] /in a.
            Then a /in g^[z].
            Take a zfset b such that b /in z /\ a = g[b].
            Then g[zz] /in g[b].
            zz,b /in Dom(g).
            Then zz /in b (by epsiso).
            b /in z.
            z = zz ++.
            Then b /in zz \/ b = zz.
            Contradiction.
          end.
        end.
        z /in lambda.
        Proof by contradiction. Assume the contrary.
          z /subset lambda.
          Then z = lambda.
          Contradiction.
        end.
        Then g[z] = /bigcup g^[z].
        Then g[z] = /bigcup (y /cap lam).
        y /cap lam /cof lam.
        Then /bigcup (y /cap lam) = lam.
        Then g[z] = lam.
        Then lam /in y.
      end.
    end.
  end.
qed.


Signature. A cofpair is a notion.

Axiom. Let kappa, x be objects. (kappa,x) is a cofpair iff kappa /in /BigSingCard /\ x /subset kappa /cap /Card /\ otp(x) = cof(kappa) /\ x /club kappa.

Lemma. Let kappa /in /BigSingCard. Then exists x ((kappa,x) is a cofpair).
Proof.
  Let lambda = cof(kappa).
  Take an ordinal alpha such that kappa = Alef[alpha].
  alpha /in /Lim.
  cof(kappa) = cof(alpha).
  Take a zfset x such that x /subset alpha /\ otp(x) = lambda /\ x /club alpha.
  lambda /in /Ord.
  x /subset /Ord.
  Take a zffunction f such that f : lambda /leftrightarrow x /\ (f is an epsiso).
  ran(f) /subset /Ord.
  Let g = Alef /circ f.
  g is an epsiso.
  ran(g) /subset /Card.
  Proof.
    ran(g) = g^[lambda].
    Let i /in lambda.
    f[i] /in /Ord.
    g[i] = Alef[f[i]].
    Then g[i] /in /Card.
  end.
  ran(g) /subset kappa.
  Proof.
    ran(g) = g^[lambda].
    Let i /in lambda.
    f[i] /in /Ord.
    g[i] = Alef[f[i]].
    f[i] /in alpha.
    Then g[i] /in Alef[alpha].
  end.
  Then ran(g) /subset kappa /cap /Card.

  ran(g) /cof kappa.
  Proof.
    Let beta /in kappa.
    kappa = Alef[alpha].
    alpha /in /Lim.
    Then Alef[alpha] = /bigcup Alef^[alpha].
    Take a zfset y such that y /in Alef^[alpha] /\ beta /in y.
    Take an ordinal gamma such that gamma /in alpha /\ y = Alef[gamma].
    Take a zfset z such that z /in x /\ gamma /in z.
    Take a zfset w such that w /in lambda /\ f[w] = z.
    gamma /in f[w].
    gamma, f[w] /in /Ord.
    Then Alef[gamma] /in Alef[f[w]] (by AlefIn).
    Alef[f[w]] /in /Ord.
    Then Alef[gamma] /subset Alef[f[w]].
    beta /in Alef[gamma].
    Then beta /in Alef[f[w]].
    Alef[f[w]] = g[w].
    g[w] /in ran(g).
  end.

  ran(g) /closed kappa.
  Proof.
    Let lam /in /Lim /cap kappa.
    Let ran(g) /cap lam /cof lam.
    Then lam /in ran(g).
    Proof.
      Define z = {y /in x | Alef[y] /in ran(g) /cap lam}.
      z is a zfset.
      Proof.
        z /subset x.
      end.
      ran(g) = Alef^[x].
      ran(g) /cap lam = Alef^[z].
      Proof.
        ran(g) /cap lam /subset Alef^[z].
        Proof.
          Let a /in ran(g) /cap lam.
          Then a /in ran(g).
          Then a /in Alef^[x].
          Take a zfset b such that b /in x /\ a = Alef[b].
          Then b /in z.
          Alef[b] /in Alef^[z].
          Then a /in Alef^[z].
        end.
        Alef^[z] /subset ran(g) /cap lam.
      end.
      /bigcup z /in /Ord.
      Proof.
        z /subset /Ord.
        z /neq /emptyset.
        z /in /VV.
      end.
      /bigcup z /in /Lim.
      Proof by contradiction. Assume the contrary.
        /bigcup z /in /Ord.
        /bigcup z /notin /Lim.
        Then /bigcup z = 0 \/ /bigcup z /in /Succ.
        Case /bigcup z = 0.
          Then z /subset 1.
          Proof by contradiction. Assume the contrary.
            Take a zfset a such that a /in z /\ a /notin 1.
            Then a /neq /emptyset.  
            Take a zfset b such that b /in a.
            Then b /in /bigcup z.
            Contradiction.
          end.
          Then z = 0 \/ z = 1.
          Then Alef^[z] = /emptyset \/ Alef^[z] = </NN>.
          Contradiction.
        end.
        Case /bigcup z /in /Succ.
          Take a zfset zz such that /bigcup z = zz ++.
          Then zz ++ /in z.
          Proof.
            Take a zfset a such that a /in z /\ zz /in a.
            a /in /Ord.
            Then zz /subset a.
            Then zz ++ /subset a.
            Then zz ++ /in a \/ zz ++ = a.
            Case zz ++ = a.
            end.
            Case zz ++ /in a.
              Then zz ++ /in /bigcup z.
              Contradiction.
            end.
          end.
          Forall a /in z a /subset zz ++.
          Proof by contradiction. Assume the contrary.
            Take a zfset a such that a /in z /\ not (a /subset zz ++).
            a, zz ++ /in /Ord.
            Then zz ++ /in a.
            Then zz ++ /in /bigcup z.
            Contradiction.            
          end.
          Then forall b /in Alef^[z] b /subset Alef[zz ++].
          Alef[zz ++] /in Alef^[z].
          Alef^[z] /cof lam.
          Alef[zz ++] /in lam.
          Take a zfset b such that b /in Alef^[z] /\ Alef[zz ++] /in b.
          b /subset Alef[zz ++].
          Contradiction.
        end.
      end.
      Let gamma = /bigcup z.
      z = x /cap gamma.
      Proof.
        z /subset x /cap gamma.
        Proof.
          Let a /in z.
          Then a /in x.
          Alef[a] /in ran(g) /cap lam.
          Take a zfset b such that b /in ran(g) /cap lam /\ Alef[a] /in b.
          Take a zfset c such that c /in lambda /\ b = g[c].
          Then f[c] /in z.
          Alef[f[c]] = b.
          Then Alef[a] /in Alef[f[c]].
          a, f[c] /in /Ord.
          Then a /in f[c] (by AlefIn).
          Then a /in /bigcup z.
        end.
        x /cap gamma /subset z.
        Proof.
          Let a /in x /cap gamma.
          Then a /in /bigcup z.
          Take a zfset b such that b /in z /\ a /in b.
          a,b /in /Ord.
          Then Alef[a] /in Alef[b].
          Alef[b] /in lam.
          Then Alef[a] /in lam.
          Then Alef[a] /in ran(g) /cap lam. 
          Then a /in z.
        end.
      end.
      gamma /in alpha.
      Proof by contradiction. Assume the contrary.
        gamma /subset alpha.
        Proof.
          Let a /in gamma.
          Then a /in /bigcup z.
          Take a zfset b such that b /in z /\ a /in b.
          b /in alpha.
          Then a /in alpha.
        end.
        Then gamma = alpha.
        x /subset alpha.
        Then x /cap gamma = x.
        Then z = x.
        ran(g) = Alef^[x].
        ran(g) /cap lam = Alef^[z].
        Then ran(g) /subset lam.
        ran(g) /cof kappa.
        lam /in kappa.
        Take a zfset a such that a /in ran(g) /\ lam /in a.
        Contradiction.
      end.
      z /cof gamma.
      Then gamma /in x.
      Alef[gamma] /in ran(g).
      Alef[gamma] = /bigcup Alef^[gamma].
      /bigcup Alef^[gamma] = /bigcup Alef^[z].
      Proof.
        /bigcup Alef^[gamma] /subset /bigcup Alef^[z].
        Proof.
          Let a /in /bigcup Alef^[gamma].
          Take a zfset b such that b /in Alef^[gamma] /\ a /in b.
          Take a zfset c such that c /in gamma /\ b = Alef[c].
          Take a zfset d such that d /in z /\ c /in d.
          c,d /in /Ord.
          Then Alef[c] /in Alef[d] (by AlefIn).
          Then b /in Alef[d].
          Then a /in Alef[d].
          Alef[d] /in Alef^[z].
          Then a /in /bigcup Alef^[z].
        end.
        /bigcup Alef^[z] /subset /bigcup Alef^[gamma].
      end.
      Alef^[z] /cof lam.
      Then /bigcup Alef^[z] = lam.
      Then Alef[gamma] = lam.
    end.
  end.

  otp(ran(g)) = lambda.
  Proof.
    g : lambda /leftrightarrow ran(g).
    lambda /in /Ord.
    ran(g) /subset /Ord.
    g is an epsiso.
  end.
  Then (kappa,ran(g)) is a cofpair.
qed.

Definition. Let f be an epsiso. Let Dom(f) /in /Ord \/ Dom(f) = /Ord. f is continuous iff forall lambda /in Dom(f) /cap /Lim (f[lambda] = /bigcup f^[lambda]).

Lemma clubcont. Let kappa /in /Lim. Let x /subset kappa. Let x /club kappa. Let f be an epsiso. Let f : otp(x) /leftrightarrow x. Then Dom(f) /in /Ord and f is continuous.
Proof.
  x is a zfset.
  Proof.
    x /subset kappa.
  end.
  x /subset /Ord.
  otp(x) /in /Ord.
  Dom(f) /in /Ord.
  Let lambda /in Dom(f) /cap /Lim.
  Then f[lambda] = /bigcup f^[lambda].
  Proof.
    f^[lambda /cap Dom(f)] = f[lambda] /cap ran(f).
    lambda /subset Dom(f).
    Then lambda /cap Dom(f) = lambda.
    Then f^[lambda] = f[lambda] /cap ran(f).
    f^[lambda] /subset x.
    Let gamma = /bigcup f^[lambda].
    gamma /in /Ord.
    gamma /in /Lim.
    gamma /subset f[lambda].
    Proof.
      Let a /in gamma.
      Then a /in /bigcup f^[lambda].
      Take a zfset b such that b /in f^[lambda] /\ a /in b.
      Take a zfset c such that c /in lambda /\ b = f[c].
      Then a /in f[c].
      c,lambda /in Dom(f).
      c /in lambda.
      Then f[c] /in f[lambda] (by epsiso).
      f[lambda] /in /Ord.
      Then a /in f[lambda].
    end.
    gamma, f[lambda] /in /Ord.
    Then gamma /in f[lambda] \/ gamma = f[lambda].
    f[lambda] /in kappa.
    Then gamma /in kappa.
    Then gamma /in /Lim /cap kappa.
    f^[lambda] /subset gamma.
    Proof.
      Let a /in f^[lambda].
      Take a zfset b such that b /in lambda /\ a = f[b].
      b++ /in lambda.
      b /in b++.
      b, b++ /in Dom(f).
      f is a zffunction.
      Then f[b] /in f[b++] (by epsiso).
      f[b++] /in f^[lambda].
      Then a /in /bigcup f^[lambda].
      Then a /in gamma.
    end.
    f^[lambda] /cof gamma.
    f^[lambda] = x /cap gamma.
    x /closed kappa.
    Then gamma /in x.
  end.
qed.

Signature. A coftriple is a notion.

Axiom. Let kappa, x, f be objects. (kappa,x,f) is a coftriple iff ((kappa,x) is a cofpair) /\ (f is an epsiso) /\ f : cof(kappa) /leftrightarrow x.

Lemma. Let kappa,x be objects. Let (kappa,x) be a cofpair. Then exists f ((kappa,x,f) is a coftriple).
Proof.
  kappa /in /BigSingCard.
  x /subset kappa /cap /Card.
  Then x /subset /Ord.
  Let lambda = otp(x).
  Then lambda /in /Ord.
  Take a zffunction f such that f : lambda /leftrightarrow x /\ (f is an epsiso).
qed.

Lemma. Let kappa,x,f be objects. Let (kappa,x,f) be a coftriple. Then f is a sequence of cardinals and Dom(f) = cof(kappa).
Proof.
  x /subset kappa /cap /Card.
  Then x /subset /Card.
  Dom(f) = cof(kappa).
  cof(kappa) /in /Ord.
  Then Dom(f) /in /Ord.
  f is a zffunction.
  Forall i /in Dom(f) (f[i] /in /Cd).
  Then f is a sequence of cardinals.
qed.

Lemma. Let kappa,x,f be objects. Let (kappa,x,f) be a coftriple. Then Dom(f) /in /Ord and f is continuous.
Proof.
  (kappa,x) is a cofpair.
  kappa /in /Lim.
  x /subset kappa /cap /Card.
  x /subset /Ord.
  Dom(f) = otp(x).
  Then Dom(f) /in /Ord.
  (kappa,x) is a cofpair.
  x /subset kappa /cap /Card.
  Then x /subset kappa.
  x /club kappa.
  f is an epsiso.
  f : otp(x) /leftrightarrow x.
  Then f is continuous (by clubcont).
qed.

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
Proof.
  Let lambda /in kappa /cap /Cd.
  Then lambda ^ cof(kappa) /in kappa.
  Proof.
    lambda, 2 ^ cof(kappa) /in /Ord.
    lambda /subset 2 ^ cof(kappa) \/ 2 ^ cof(kappa) /in lambda.
    Case lambda /subset 2 ^ cof(kappa).
      lambda /in 2 \/ 2 /subset lambda.
      lambda /in 2 iff lambda = 0 \/ lambda = 1.
      Case lambda = 0. end.
      Case lambda = 1. end.
      Case 2 /subset lambda.
        cof(kappa) /in /Card.
        lambda /subset 2 ^ cof(kappa).
        Then lambda ^ cof(kappa) = 2 ^ cof(kappa) (by ExpEq).
        kappa is singular.
        Then cof(kappa) /in kappa.
        cof(kappa) /in kappa /cap /Card.
        Then 2 ^ cof(kappa) = Plus[cof(kappa)].
        cof(kappa) /in kappa.
        Then Plus[cof(kappa)] /subset kappa.
        Then Plus[cof(kappa)] /in kappa.
      end.
    end.
    Case 2 ^ cof(kappa) /in lambda.
      Then cof(kappa) /in lambda.
      lambda ^ lambda is a zfset.
      lambda ^ cof(kappa) /subset lambda ^ lambda.
      Then lambda ^ cof(kappa) /in lambda ^ lambda \/ lambda ^ cof(kappa) = lambda ^ lambda.
      lambda /in /Card.
      2 /subset lambda.
      lambda /in 2 ^ lambda.
      lambda /subset 2 ^ lambda.
      Then lambda ^ lambda = 2 ^ lambda (by ExpEq).
      lambda /in kappa /cap /Card.
      Then 2 ^ lambda = Plus[lambda].
      lambda /in kappa.
      Then Plus[lambda] /subset kappa.
      Then Plus[lambda] /in kappa.
    end.
  end.
qed.



## The First Helping Lemma


Lemma Silver1. Let kappa, x, kap, F be objects. Let (kappa,x,kap) be a coftriple. Let Silver below kappa. Let A be a zffunction. Let A be compatible with kap relative to kappa and x.
Let F be almost disjoint relative to A. Then Card(F) /subset kappa.
Proof.

  # Getting Started

  (kappa,x) is a cofpair.
  x /subset kappa /cap /Card.
  Then x /subset kappa.
  x /cof kappa.
  Let S = CofSupp(kappa,x,kap){A}.
  Take an ordinal lambda such that lambda = cof(kappa).
  lambda /in /BigRegCard.
  otp(x) = lambda.
  S /in stat(lambda).
  Dom(kap) = lambda.
  Dom(A) = lambda.
  Forall i /in lambda A[i], kap[i] /in /VV.
  Forall i /in lambda exists f (f : A[i] /leftrightarrow Card(A[i])).
  Define bij[i] = (Choose a zffunction f such that f : A[i] /leftrightarrow Card(A[i]) in f) for i in lambda.
  bij is a zffunction.
  Proof.
    Let i /in lambda.
    Then bij[i] is a zffunction.
    Dom(bij[i]) /in /VV.
    Then bij[i] /in /VV.
  end.
  Forall i /in S Card(A[i]) /subset kap[i].
  Then forall i /in S (bij[i] : A[i] /rightarrow kap[i] /\ (bij[i] is injective)).

  F /subset /prodset A.
  Forall f /in F (f is a zffunction and Dom(f) = lambda).
  Forall f /in F forall i /in lambda f[i] /in A[i].
  Proof.
    Let f /in F.
    Then f /in /prodset A.
    Then forall i /in Dom(f) f[i] /in A[i].
  end.
  Then forall f /in F forall i /in Dom(f) f[i] /in Dom(bij[i]).
  Then forall f /in F (bij and f are diagcomposable).

  Define Incl[f] = f /comp bij for f in F.
  Forall f /in F ((Incl[f] is a zffunction) /\ Dom(Incl[f]) = lambda).
  Incl is a zffunction.
  Proof.
    Let f /in F.
    Then Incl[f] is a zffunction.
    Dom(Incl[f]) /in /VV.
    Then Incl[f] /in /VV.
  end.
  Incl is injective.
  Proof.
    Let f, g /in F.
    Let f /neq g.
    Then Incl[f] /neq Incl[g].
    Proof.
      Dom(f) = Dom(g).
      Then exists i /in lambda f[i] /neq g[i].
      Proof by contradiction. Assume the contrary.
        f,g are functions.
        Dom(f) = Dom(g).
        Forall i /in Dom(f) f[i] = g[i].
        Then f = g.
        Contradiction.
      end.
      Take a zfset i such that i /in lambda /\ f[i] /neq g[i].
      Then (Incl[f])[i] /neq (Incl[g])[i].
      Proof.
        (Incl[f])[i] = (bij[i])[f[i]].
        (Incl[g])[i] = (bij[i])[g[i]].
        bij[i] is injective.
        Then (bij[i])[f[i]] /neq (bij[i])[g[i]].
      end.
    end.
  end.
  Take a zfset G such that G = ran(Incl).
  Then Card(F) = Card(G).
  Proof.
    Incl : F /leftrightarrow G.
  end.
  Forall f /in G (f is a zffunction and Dom(f) = lambda).
  Proof.
    Let f /in G.
    Take a zfset ff such that ff /in F /\ f = Incl[ff].
  end.
  G is an almost disjoint family of functions on lambda.
  Proof.
    lambda /in /Lim.
    G /subset ^{lambda}/VV.
    (G,lambda) is an adfampair.
    Forall f,g /in G (f /neq g => (f and g are almost disjoint on lambda)).
    Proof.
      Let f,g /in G.
      Let f /neq g.
      Take a zfset ff such that ff /in F /\ f = Incl[ff].
      Take a zfset gg such that gg /in F /\ g = Incl[gg].
      lambda /in /Lim.
      F /subset ^{lambda}/VV.
      F is an almost disjoint family of functions on lambda.
      ff,gg /in F.
      ff /neq gg.
      Then ff and gg are almost disjoint on lambda (by adfam).
      Take an ordinal alpha such that alpha /in lambda /\ forall beta /in lambda (alpha /in beta => ff[beta] /neq gg[beta]).
      Then forall beta /in lambda (alpha /in beta => f[beta] /neq g[beta]).
      Proof.
        Let beta /in lambda.
        Let alpha /in beta.
        Then f[beta] /neq g[beta].
        Proof.
          ff[beta] /neq gg[beta].
          f = Incl[ff].
          g = Incl[gg].
          (Incl[ff])[beta] /neq (Incl[gg])[beta].
          Proof.
            (Incl[ff])[beta] = (bij[beta])[ff[beta]].
            (Incl[gg])[beta] = (bij[beta])[gg[beta]].
            bij[beta] is injective.
            Then (bij[beta])[ff[beta]] /neq (bij[beta])[gg[beta]].
          end.
        end.
      end.
      Then f and g are almost disjoint on lambda.
    end.
    Then G is an almost disjoint family of functions on lambda (by adfam2).
  end.
  Forall f /in G forall i /in S f[i] /in kap[i].
  Proof.
    Let f /in G.
    Let i /in S.
    Take a zfset ff such that ff /in F /\ f = Incl[ff].
    f = ff /comp bij.
    i /in lambda.
    f[i] = (bij[i])[ff[i]].
    ff[i] /in A[i].
    Card(A[i]) /subset kap[i].
    Then (bij[i])[ff[i]] /in kap[i].
    Then f[i] /in kap[i].
  end.
  
  # functions are bounded on stationary subsets

  Define minset[i] = {beta /in lambda | i /in kap[beta]} for i in kappa.  
  Forall i /in kappa minset[i] /neq /emptyset.
  Proof.
    Let i /in kappa.
    x /cof kappa.
    Take a zfset y such that y /in x /\ i /in y.
    Take a zfset beta such that beta /in lambda /\ kap[beta] = y.
    Then beta /in minset[i].
  end.
  Forall i /in kappa minset[i] /subset /Ord.

  Define h[i] = min(minset[i]) for i in kappa.
  h : kappa /rightarrow lambda.
  Proof.
    Let i /in kappa.
    Then h[i] /in lambda.
  end.
  Forall i /in kappa h[i] /in Dom(kap).
  Proof.
    Let i /in kappa.
    Then h[i] /in lambda.
  end.
  Forall i /in kappa i /in kap[h[i]].
  Proof.
    Let i /in kappa.
    h[i] /in minset[i].
    minset[i] = {beta /in lambda | i /in kap[beta]}.
    Then i /in kap[h[i]].
  end.
  
  Forall f /in G exists Sf /in stat(lambda,S) exists alpha /in lambda (f^[Sf] /subset kap[alpha]).
  Proof.
    Let f /in G.
    Forall i /in S f[i] /in kappa.
    Proof.
      Let i /in S.
      Then f[i] /in kap[i].
      kap[i] /in kappa.
    end.
    Let SS = S /cap /Lim.
    SS /in stat(lambda).
    Define hf[i] = h[f[i]] for i in SS.
    hf is a zffunction.
    Proof.
      Let i /in SS.
      Then hf[i] /in /VV.
    end.
    Dom(hf) /subset /Ord.
    lambda /in /BigRegCard.
    hf is regressive.
    Proof.
      Let i /in Dom(hf) /setminus <0>.
      Then i /in S /cap /Lim.
      f[i] /in kap[i].
      i /in Dom(kap) /cap /Lim.
      kap is continuous.
      kap[i] = /bigcup kap^[i].
      Then f[i] /in /bigcup kap^[i].
      Take a zfset y such that y /in kap^[i] /\ f[i] /in y.
      Forall j /in i j /in Dom(kap).
      Take a zfset j such that j /in i /\ y = kap[j].
      Then f[i] /in kap[j].
      Then j /in minset[f[i]].
      Then hf[i] /subset j.
      Then hf[i] /in j \/ hf[i] = j.
      Then hf[i] /in i.
    end.
    Dom(hf) /in stat(lambda).
    Then exists T /subset Dom(hf) (T /in stat(lambda) /\ (hf /upharpoonright T is constant)) (by Fodor2).
    Take T /subset Dom(hf) such that T /in stat(lambda) /\ (hf /upharpoonright T is constant).
    Take a zfset alpha such that forall i /in T (hf /upharpoonright T)[i] = alpha.
    Forall i /in T hf[i] = alpha.
    Proof.
      Let i /in T.
      (hf /upharpoonright T)[i] = hf[i].
    end.
    T /neq /emptyset.
    Proof.
      T /in stat(lambda).
      /emptyset is nonstationary in lambda.
    end.
    Take a zfset z such that z /in T.
    hf[z] = alpha.
    hf[z] = h[f[z]].
    h[f[z]] /in lambda.
    Then alpha /in lambda.
    Forall i /in T f[i] /in kap[alpha].
    Proof.
      Let i /in T.
      hf[i] = alpha.
      Then h[f[i]] = alpha.
      Then alpha /in minset[f[i]].
      Then f[i] /in kap[alpha].
    end.
    Then f^[T] /subset kap[alpha].
    T /in stat(lambda,S).
  end.

  Define StatS[f] = (Choose a zfset Sf such that Sf /in stat(lambda,S) /\ exists alpha /in lambda (f^[Sf] /subset kap[alpha]) in Sf) for f in G.
  Forall f /in G StatS[f] /subset Dom(f).
  Forall f /in G exists alpha /in lambda f^[StatS[f]] /subset kap[alpha].

  # f <-> f /upharpoonright Sf

  Define Inj[f] = (f /upharpoonright StatS[f], StatS[f]) for f in G.
  Inj is a zffunction.
  Proof.
    Let f /in G.
    Then f /upharpoonright StatS[f] is a zffunction.
    ran(f /upharpoonright StatS[f]) /in /VV.
    Then f /upharpoonright StatS[f] /in /VV.
    StatS[f] /in /VV.
    Then (f /upharpoonright StatS[f], StatS[f]) /in /VV.
    Then Inj[f] /in /VV.
  end.
  Inj is injective.
  Proof.
    Let f,g /in G.
    Let f /neq g.
    Then Inj[f] /neq Inj[g].
    Proof.
      Case StatS[f] /neq StatS[g].
        Then (f /upharpoonright StatS[f], StatS[f]) /neq (g /upharpoonright StatS[g], StatS[g]).
      end.
      Case StatS[f] = StatS[g].
        lambda /in /Lim.
        G is an almost disjoint family of functions on lambda.
        f,g /in G.
        f /neq g.
        Then f and g are almost disjoint on lambda (by adfam).
        Take a zfset alpha such that alpha /in lambda /\ forall beta /in lambda (alpha /in beta => f[beta] /neq g[beta]).
        Define C = { beta /in lambda | alpha /in beta}.
        C /subset lambda.
        C /cof lambda.
        Proof.
          Let beta /in lambda.
          Then exists gamma /in C (beta /in gamma).
          Proof.
            Case alpha /in beta.
              Then alpha /in beta +' 1.
              beta +' 1 /in lambda.
              Then beta +' 1 /in C.
              beta /in beta +' 1.
            end.
            Case beta /subset alpha.
              Then beta /in alpha +' 1.
              alpha +' 1 /in lambda.
              Then alpha +' 1 /in C.
            end.
          end.
        end.
        C /closed lambda.
        Proof.
          Let lam /in /Lim /cap lambda.
          Let C /cap lam /cof lam.
          Then C /cap lam /neq /emptyset.
          Take a zfset z such that z /in C /cap lam.
          Then alpha /in z.
          Then alpha /in lam.
          lam /in lambda.
          Then lam /in C.
        end.
        Then C /club lambda.
        lambda /in /BigCard.
        StatS[f] is stationary in lambda.
        Then StatS[f] /cap C /neq /emptyset (by stationary).
        Take a zfset z such that z /in StatS[f] /cap C.
        Then f[z] /neq g[z].
        Then (f /upharpoonright StatS[f])[z] /neq (g /upharpoonright StatS[g])[z].
        Then f /upharpoonright StatS[f] /neq g /upharpoonright StatS[g].
        Then (f /upharpoonright StatS[f], StatS[f]) /neq (g /upharpoonright StatS[g], StatS[g]).
      end.
    end.
  end.
  
  Take a zfset H such that H = ran(Inj).
  Then Inj : G /leftrightarrow H.
  Then Card(G) = Card(H).

  Forall pair /in H exists a,b /in /VV (pair = (a,b)).
  Proof.
    Let pair /in H.
    Take a zfset f such that f /in G /\ pair = Inj[f].
    Then pair = (f /upharpoonright StatS[f], StatS[f]).
    f /upharpoonright StatS[f], StatS[f] /in /VV.
  end.
  Forall o1,o2 ((o1,o2) /in H => o1,o2 /in /VV).
  Proof.
    Let a,b be objects.
    Let (a,b) /in H.
    Take zfsets aa,bb such that (a,b) = (aa,bb).
    Then a = aa /\ b = bb.
  end.
  Forall a,b /in /VV ((a,b) /in H => (b /subset lambda /\ (a is a zffunction) /\ Dom(a) = b /\ (exists alpha /in lambda ran(a) /subset kap[alpha]))).
  Proof.
    Let a,b /in /VV.
    Let (a,b) /in H.
    Take a zfset f such that f /in G /\ (a,b) = Inj[f].
    Then (a,b) = (f /upharpoonright StatS[f], StatS[f]).
    Then a = f /upharpoonright StatS[f] /\ b = StatS[f].
    b /subset lambda.
    a is a zffunction.
    Dom(a) = b.
    Exists alpha /in lambda ran(a) /subset kap[alpha].
    Proof.
      Take a zfset alpha such that alpha /in lambda /\ f^[StatS[f]] /subset kap[alpha].
      f^[StatS[f]] = a^[b].
    end.
  end.

  # for max kappa f Sf = b
  
  Define Image[b] = {a /in /VV | (a,b) /in H} for b in /PP(lambda).  
  Image is a zffunction.
  Proof.
    Let b /in /PP(lambda).
    Define Proj[(a,c)] = a for (a,c) in H.
    Proj is a zffunction.
    Proof.
      Let pair /in H.
      Take zfsets a,c such that pair = (a,c).
      Then a,c /in /VV.
      Then Proj[pair] /in /VV.
    end.
    Image[b] /subset Proj^[H].
    Then Image[b] /in /VV.
  end.
  Forall b /in /PP(lambda) Card(Image[b]) /subset kappa.
  Proof.
    Let b /in /PP(lambda).
    Forall a /in Image[b] ((a is a zffunction) /\ Dom(a) = b /\ (exists alpha /in lambda ran(a) /subset kap[alpha])).
    Proof.
      Let a /in Image[b].
      Image[b] = {a /in /VV | (a,b) /in H}.
      Then (a,b) /in H.
      Then (a is a zffunction) /\ Dom(a) = b /\ (exists alpha /in lambda ran(a) /subset kap[alpha]).
    end.

    Define Func = {a /in ^{b}/VV | (exists alpha /in lambda ran(a) /subset kap[alpha])}.
    Func is a zfset.
    Proof.
      Func /subset ^{b}kappa.
      Proof.
        Let a /in Func.
        Then a : b /rightarrow /VV.
        Take a zfset alpha such that alpha /in lambda /\ ran(a) /subset kap[alpha].
        Then a : b /rightarrow kap[alpha].
        kap[alpha] /in kappa.
        kap[alpha] /subset kappa.
        Then a : b /rightarrow kappa.
        Then a /in ^{b}kappa.
      end.
    end.
    Image[b] /subset Func.
    Then Card(Image[b]) /subset Card(Func).

    Define FuncPart[alpha] = {a /in Func | ran(a) /subset kap[alpha]} for alpha in lambda.
    FuncPart is a zffunction.
    Proof.
      Let alpha /in lambda.
      FuncPart[alpha] /subset Func.
      Then FuncPart[alpha] /in /VV.
    end.
    Forall alpha /in lambda Card(FuncPart[alpha]) /subset kappa.
    Proof.
      Let alpha /in lambda.
      FuncPart[alpha] /subset ^{b}kap[alpha].
      ^{b}kap[alpha] /tilde ^{Card(b)}kap[alpha].
      Card(b) /in /Cd.
      kap[alpha] /in /Card.
      Proof.
        kap[alpha] /in x. 
        x /subset kappa /cap /Card.
        Then x /subset /Card.
      end.
      Card(^{b}kap[alpha]) = kap[alpha] ^ Card(b).
      Card(b) /subset lambda.
      0 /in kap[alpha].
      Then kap[alpha] ^ Card(b) /subset kap[alpha] ^ lambda (by ExpSubset).
      kap[alpha] /in kappa.
      Then kap[alpha] ^ lambda /in kappa.
      Card(FuncPart[alpha]) /subset Card(^{b}kap[alpha]).
      Card(^{b}kap[alpha]) /subset kap[alpha] ^ lambda.
      kap[alpha] ^ lambda /subset kappa.
      Then Card(FuncPart[alpha]) /subset kappa.
      Proof.
        Let aa = Card(FuncPart[alpha]).
        Let bb = Card(^{b}kap[alpha]).
        Let cc = kap[alpha] ^ lambda.
        Then aa /subset bb.
        bb /subset cc.
        cc /subset kappa.
        Then aa /subset kappa.
      end.
    end.
    Forall a /in Func exists alpha /in lambda (a /in FuncPart[alpha]).
    Define FuncIncl[a] = (Choose a zfset alpha such that alpha /in lambda /\ a /in FuncPart[alpha] in (a,alpha)) for a in Func.
    FuncIncl is a zffunction.
    Proof.
      Let a /in Func.
      Take a zfset alpha such that FuncIncl[a] = (a,alpha).
      Then (a,alpha) /in /VV.
      Then FuncIncl[a] /in /VV.
    end.
    FuncIncl is injective.
    Proof.
      Let a,b /in Func.
      Let a /neq b.
      Then FuncIncl[a] /neq FuncIncl[b].
    end.
    ran(FuncIncl) /subset /sumset FuncPart.
    Then FuncIncl : Func /rightarrow /sumset FuncPart.
    Then Func <= /sumset FuncPart.
    Then Card(Func) /subset Card(/sumset FuncPart).
    Card(/sumset FuncPart) = Card(/sumset cardseq(FuncPart)).
    /sumset cardseq(FuncPart) /subset kappa /times kappa.
    Then Card(/sumset cardseq(FuncPart)) /subset Card(kappa /times kappa).
    kappa /in /Card.
    kappa * kappa = Card(kappa /times kappa).
    kappa * kappa = kappa.
    Then Card(kappa /times kappa) = kappa.
    Then Card(Func) /subset kappa.
    Then Card(Image[b]) /subset kappa.
  end.

  # Finish
  
  Card(/PP lambda) /tilde /PP lambda.
  Take a zffunction Pre such that Pre : Card(/PP lambda) /leftrightarrow /PP lambda.
  ran(Pre) /subset Dom(Image).
  Take a zffunction PreImage such that PreImage = Image /circ Pre.
  Then Dom(PreImage) = Card(/PP lambda).
  
  H /subset /sumset Image.
  Proof.
    Let pair /in H.
    Take zfsets a,b such that pair = (a,b).
    Then (a,b) /in H.
    b /subset lambda.
    Then b /in /PP(lambda).
    Then a /in Image[b].
    Then (a,b) /in /sumset Image.
    Then pair /in /sumset Image.
  end.
  /sumset Image /tilde /sumset PreImage.
  Proof.
    Forall o1,o2 ((o1,o2) /in /sumset PreImage => o2 /in Dom(Pre)).
    Forall pair /in /sumset PreImage exists a,c /in /VV (a,c) = pair.
    Forall pair /in /sumset Image exists a,b /in /VV (a,b) = pair.
    Define Tilde[(a,c)] = (a,Pre[c]) for (a,c) in /sumset PreImage.
    Tilde : /sumset PreImage /rightarrow /sumset Image.
    Proof.
      Let pair /in /sumset PreImage.
      Take zfsets a,c such that pair = (a,c).
      Then Pre[c] /in /VV.
      Then (a,Pre[c]) /in /VV.
      Tilde[pair] = (a,Pre[c]).
      (a,Pre[c]) /in /sumset Image.
      Then Tilde[pair] /in /sumset Image.
    end.
    Tilde is injective.
    Proof.
      Let pair1,pair2 /in /sumset PreImage.
      Let pair1 /neq pair2.
      Then Tilde[pair1] /neq Tilde[pair2].
      Proof.
        Take zfsets a1,c1 such that pair1 = (a1,c1).
        Take zfsets a2,c2 such that pair2 = (a2,c2).
        Then (a1,c1) /neq (a2,c2).  
        Then a1 /neq a2 \/ c1 /neq c2.
        Case a1 /neq a2.
        end.
        Case c1 /neq c2.
          Then Pre[c1] /neq Pre[c2].
        end.
      end.
    end.
    ran(Tilde) = /sumset Image.
    Proof.
      Let pair /in /sumset Image.
      Take zfsets a,b such that pair = (a,b).
      Then b /in /PP lambda.
      Take a zfset c such that c /in Card(/PP lambda) /\ Pre[c] = b.
      Then (a,c) /in /sumset PreImage.
      Tilde[(a,c)] = (a,b).
      Then pair /in ran(Tilde).
    end.
    Then Tilde : /sumset PreImage /leftrightarrow /sumset Image.
  end.
  Then Card(H) /subset Card(/sumset PreImage).
  Card(/sumset PreImage) = Card(/sumset cardseq(PreImage)).
  cardseq(PreImage) is a sequence of cardinals.
  Forall pair /in /sumset cardseq(PreImage) exists a,b /in /VV pair = (a,b).
  /sumset cardseq(PreImage) /subset kappa /times kappa.
  Proof.
    Let pair /in /sumset cardseq(PreImage).
    Take zfsets a,b such that pair = (a,b).
    Then b /in Dom(cardseq(PreImage)) /\ a /in (cardseq(PreImage))[b].
    b /in Card(/PP lambda).
    Card(/PP lambda) = 2 ^ lambda.
    2 ^ lambda /in kappa.
    Then b /in kappa.
    (cardseq(PreImage))[b] = Card(PreImage[b]).
    PreImage[b] = Image[Pre[b]].
    Card(Image[Pre[b]]) /subset kappa.
    Then a /in kappa.
    Then (a,b) /in kappa /times kappa.
    Then pair /in kappa /times kappa.
  end.
  Then Card(/sumset cardseq(PreImage)) /subset Card(kappa /times kappa).
  kappa /in /Card.
  kappa * kappa = Card(kappa /times kappa).
  kappa * kappa = kappa.
  Then Card(kappa /times kappa) = kappa.
  Then Card(H) /subset kappa.  
  
  Card(F) = Card(H).
  Then Card(F) /subset kappa.
qed.




