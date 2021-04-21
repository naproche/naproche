[read Formalizations/Library/L18-Almost_Disjoint_Functions.ftl]


## Pretyped Variables

Let w,x,y,z,W,X,Y,Z stand for zfsets.
Let a,b,c,d,A,B,C,D,M stand for sets.
Let o,o1,o2 stand for objects.
Let alpha, beta, gamma stand for ordinals.
Let f,g,h,F,G,H stand for zffunction.
Let kappa, lambda stand for cardinals.



## General Lemmas

Lemma. Let f be a function. Let x be a zfset. Then f /caret [x] is a zfset.
Proof.
  Define domain = {i /in Dom(f) | f[i] /in /VV}.
  Define g[i] = f[i] for i in domain.
  g is a zffunction.
  Proof.
    Let i /in domain.
    Then f[i] /in /VV.
    Then g[i] /in /VV.
  end.
  f /caret [x] = g^[x].
  Then f /caret [x] /in /VV.
end.

Lemma. Let x be a zfset. Let x /neq /emptyset. Then x /in Dom(Choice).



## Prerequisites

Lemma. Let A be a zffunction. Forall i /in Dom(A) (A[i] is a zfset).

Lemma. Let kappa,x,kap be objects. Let (kappa,x,kap) be a coftriple. Then forall i /in cof(kappa) (Plus[kap[i]] is a zfset).

Definition. Let kappa,x,kap be objects. Let (kappa,x,kap) be a coftriple. Let A be a zffunction. A is silvercompatible with kap relative to kappa and x iff
Dom(A) = cof(kappa) /\ forall i /in cof(kappa) Card(A[i]) /subset Plus[kap[i]].

Definition. Let f,g be zffunctions. Let Dom(f) = Dom(g). Let X /subset Dom(f). g is smaller than f on X iff forall i /in X g[i] /subset f[i].
Let g <{X} f stand for g is smaller than f on X.

Definition. Let lambda be a zfset. Let S /subset lambda. Let F /subset ^{lambda}/VV. Let f /in ^{lambda}/VV. The set of bounded functions by f on S in F relative to lambda is
{g /in F | g <{S} f}.
Let F<{f,S,l} stand for the set of bounded functions by f on S in F relative to l.

Lemma. Let lambda /in /Lim. Let F be an almost disjoint family of functions on lambda. Let G /subset F. Then G is an almost disjoint family of functions on lambda.
Proof.
  F /subset ^{lambda}/VV.
  Then G /subset ^{lambda}/VV.
  Then (G,lambda) is an adfampair.
  Forall f,g /in G (f /neq g => (f and g are almost disjoint on lambda)).
  Proof.
    Let f,g /in G.
    Let f /neq g.
    f,g /in F.
    Then f and g are almost disjoint on lambda (by adfam).
  end.
  Then G is an almost disjoint family of functions on lambda (by adfam2).
qed.



## The last Lemma before Silver's Theorem


Lemma Silver2. Let kappa, x, kap, F be objects. Let (kappa,x,kap) be a coftriple. Let Silver below kappa. Let A be a zffunction. Let A be silvercompatible with kap relative to kappa and x.
Let F be almost disjoint relative to A. Then Card(F) /subset Plus[kappa].
Proof. 
  
  # Getting Started

  (kappa,x) is a cofpair.
  x /subset kappa /cap /Card.
  Then x /subset kappa.
  x /club kappa.
  Take an ordinal lambda such that lambda = cof(kappa).
  lambda /in /BigRegCard.
  stat(lambda) /subset /PP lambda.
  stat(lambda) /in /VV.
  Card(stat(lambda)) /subset kappa.
  Proof.
    stat(lambda) /subset /PP lambda.
    Then Card(stat(lambda)) /subset Card(/PP lambda).
    Card(/PP lambda) = 2 ^ lambda.
    2 ^ lambda /in kappa.
    Then Card(stat(lambda)) /subset kappa.
  end.
  otp(x) = lambda.
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
  Forall i /in lambda Card(A[i]) /subset Plus[kap[i]].
  Then forall i /in lambda (bij[i] : A[i] /rightarrow Plus[kap[i]] /\ (bij[i] is injective)).

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
  Forall i /in lambda (Plus[kap[i]] is a zfset).
  Forall f /in G forall i /in lambda f[i] /in Plus[kap[i]].
  Proof.
    Let f /in G.
    Let i /in lambda.
    Take a zfset ff such that ff /in F /\ f = Incl[ff].
    f = ff /comp bij.
    i /in lambda.
    f[i] = (bij[i])[ff[i]].
    ff[i] /in A[i].
    Card(A[i]) /subset Plus[kap[i]].
    Then (bij[i])[ff[i]] /in Plus[kap[i]].
    Then f[i] /in Plus[kap[i]].
  end.
  
  # Defining FfS
  
  Forall o1,o2 ((o1,o2) /in G /times stat(lambda) => o1 /in G /\ o2 /in stat(lambda)).
  Define FfSset[(f,S)] = G<{f,S,lambda} for (f,S) in G /times stat(lambda).
  FfSset is a zffunction.
  Proof.
    Let pair /in G /times stat(lambda).
    Take zfsets f,S such that f /in G /\ S /in stat(lambda) /\ pair = (f,S).
    G<{f,S,lambda} /subset G.
    Then G<{f,S,lambda} /in /VV.
    FfSset[pair] = G<{f,S,lambda}.
    Then FfSset[pair] /in /VV.
  end.
  Forall f /in G forall S /in stat(lambda) (f,S) /in Dom(FfSset).

  Forall f /in G forall S /in stat(lambda) Card(FfSset[(f,S)]) /subset kappa.
  Proof.
    Let f /in G.
    Let S /in stat(lambda).
    Then Card(FfSset[(f,S)]) /subset kappa.
    Proof.
      f is a zffunction.
      Dom(f) = lambda.
      Forall i /in lambda Plus[kap[i]] /in /Card.
      Proof.
        Let i /in lambda.
        kap[i] /in x.
        x /subset kappa /cap /Card.
        Then x /subset /Card.
        Then kap[i] /in /Card.
        Then PlusCard(kap[i]) /subset /Card.
        Plus[kap[i]] /in PlusCard(kap[i]).
        Then Plus[kap[i]] /in /Card.
      end.
      Forall i /in lambda f[i] /in Plus[kap[i]].
      Then forall i /in lambda f[i] /in /Ord.
      Proof.
        Let i /in lambda.
        f[i] /in Plus[kap[i]].
        Plus[kap[i]] /in /Ord.
        Then f[i] /in /Ord.
      end.
      
      FfSset[(f,S)] is a zfset.
      Forall g /in FfSset[(f,S)] ((g is a zffunction) /\ Dom(g) = lambda).
      Define Sup[i] = {g[i] | g /in FfSset[(f,S)]} for i in lambda.
      Sup is a zffunction.
      Proof.
        Let i /in lambda.
        Define Supfunc[g] = g[i] for g in FfSset[(f,S)].
        Supfunc is a zffunction.
        Proof.
          Let g /in FfSset[(f,S)].
          Then g[i] /in /VV.  
          Then Supfunc[g] /in /VV.
        end.
        Sup[i] /subset Supfunc^[FfSset[(f,S)]].
        Then Sup[i] /in /VV.
      end.
      
      Define AfS[i] = 
        Case i /in S -> f[i] +' 1,
        Case i /notin S -> Sup[i]
      for i in lambda.
      AfS is a zffunction.
      Proof.
        Let i /in lambda.
        Then AfS[i] /in /VV.
        Proof.
          Case i /in S. 
            Then AfS[i] = f[i] +' 1.
          end.
          Case i /notin S.
            Then AfS[i] = Sup[i].
          end.
        end.
      end.
      S /subset CofSupp(kappa,x,kap){AfS}.
      Proof.
        Let i /in S.
        Then i /in lambda.
        Then kap[i] /in /VV.
        f[i] /in Plus[kap[i]].
        Plus[kap[i]] /in /Lim.
        Then f[i] ++ /in Plus[kap[i]].
        Then f[i] +' 1 /in Plus[kap[i]].
        Then Card(f[i]+'1) /in Plus[kap[i]].
        Proof.
          Card(f[i]+'1) /subset f[i]+'1.
        end.
        Then Card(f[i]+'1) /subset kap[i].
        Proof by contradiction. Assume the contrary.
          Take a cardinal value such that value = Card(f[i]+'1).
          kap[i] /in value.
          value /in /Card.
          Then value /in PlusCard(kap[i]).
          Then Plus[kap[i]] /subset value.
          Then Card(f[i]+'1) /in Card(f[i]+'1).
          Contradiction.
        end.
        Then Card(AfS[i]) /subset kap[i].
      end.
      S /in stat(lambda).
      Then CofSupp(kappa,x,kap){AfS} /in stat(lambda).
      Then AfS is compatible with kap relative to kappa and x.

      FfSset[(f,S)] /subset G.
      Then FfSset[(f,S)] is an almost disjoint family of functions on lambda.
      FfSset[(f,S)] /subset /prodset AfS.
      Proof.
        Let g /in FfSset[(f,S)].
        S /subset lambda.
        FfSset[(f,S)] = G<{f,S,lambda}.
        Then g /in G<{f,S,lambda}.
        g <{S} f.
        Then forall i /in S g[i] /subset f[i].
        Then g is a zffunction.
        Dom(g) = lambda.
        Forall i /in lambda g[i] /in AfS[i].
        Proof.
          Let i /in lambda.
          Then g[i] /in AfS[i].
          Proof.
            Case i /in S.
              Then g[i] /subset f[i].
              g[i] /in Plus[kap[i]].
              Plus[kap[i]] /in /Ord.
              g[i] /in /Ord.
              Then g[i] /in f[i] \/ g[i] = f[i].
              AfS[i] = f[i] ++.
              Then g[i] /in AfS[i].
            end.
            Case i /notin S.
              Then g[i] /in Sup[i].
              AfS[i] = Sup[i].
            end.
          end.
        end.
        Then g /in /prodset AfS.
      end.
      Then FfSset[(f,S)] is almost disjoint relative to AfS.
      Then Card(FfSset[(f,S)]) /subset kappa (by Silver1).
    end.
  end.

  # Defining Ff

  Define Ffhelp[f] = {FfSset[(f,S)] | S /in stat(lambda)} for f in G.
  Ffhelp is a zffunction.
  Proof.
    Let f /in G.
    Define Ffhelpfunc[S] = FfSset[(f,S)] for S in stat(lambda).
    Ffhelpfunc is a zffunction.
    Proof.
      Let S /in stat(lambda).
      Then FfSset[(f,S)] /in /VV.
      Then Ffhelpfunc[S] /in /VV.
    end.
    Ffhelp[f] /subset Ffhelpfunc^[stat(lambda)].
    Then Ffhelp[f] /in /VV.
  end.
  Define Ff[f] = /bigcup Ffhelp[f] for f in G.
  Ff is a zffunction.
  Proof.
    Let f /in G.
    Then Ffhelp[f] /in /VV.
    Then Ff[f] /in /VV.
  end.
  
  Forall f /in G Card(Ff[f]) /subset kappa.
  Proof.
    Let f /in G.
    Then Card(Ff[f]) /subset kappa.
    Proof.
      Forall g /in Ff[f] exists S /in stat(lambda) g /in FfSset[(f,S)].
      Proof.
        Let g /in Ff[f].
        Then g /in /bigcup Ffhelp[f].
        Take a zfset a such that a /in Ffhelp[f] /\ g /in a.
        Ffhelp[f] = {FfSset[(f,S)] | S /in stat(lambda)}.
        Take a zfset S such that S /in stat(lambda) /\ a = FfSset[(f,S)].
        Then g /in FfSset[(f,S)].
      end.
      Forall S /in stat(lambda) (FfSset[(f,S)] is a zfset).
      Define Ffinj[g] = (Choose a zfset S such that S /in stat(lambda) /\ g /in FfSset[(f,S)] in (g,S)) for g in Ff[f].
      Ffinj is a zffunction.
      Proof.
        Let g /in Ff[f].
        Take a zfset S such that S /in stat(lambda) /\ g /in FfSset[(f,S)] /\ Ffinj[g] = (g,S).
        Then (g,S) /in /VV.
        Then Ffinj[g] /in /VV.
      end.
      Ffinj is injective.
      Let H = ran(Ffinj).
      H is a zfset.
      Proof.
        H = Ffinj^[Ff[f]].
        Ff[f] is a zfset.
      end.
      Then Ffinj : Ff[f] /leftrightarrow H.
      Then Card(Ff[f]) = Card(H).
      
      Forall S /in stat(lambda) Card(FfSset[(f,S)]) /subset kappa.
      Then forall S /in stat(lambda) exists g (g : FfSset[(f,S)] /rightarrow kappa /\ (g is injective)).
      Define FfSinj[S] = (Choose an injective zffunction g such that g : FfSset[(f,S)] /rightarrow kappa in g) for S in stat(lambda).
      
      Forall pair /in H exists b /in stat(lambda) exists a /in FfSset[(f,b)] (pair = (a,b)).
      Proof.
        Let pair /in H.
        Then pair /in ran(Ffinj).
        Take a zfset g such that g /in Ff[f] /\ pair = Ffinj[g].
        Then exists S /in stat(lambda) (g /in FfSset[(f,S)] /\ Ffinj[g] = (g,S)).
        Take a zfset S such that S /in stat(lambda) /\ g /in FfSset[(f,S)] /\ Ffinj[g] = (g,S).
        Then pair = (g,S).
      end.
      Forall o1,o2 ((o1,o2) /in H => o2 /in stat(lambda) /\ o1 /in FfSset[(f,o2)]).
      Proof.
        Let a,b be objects.
        Let (a,b) /in H.
        Then (a,b) /in ran(Ffinj).
        Take a zfset g such that g /in Ff[f] /\ (a,b) = Ffinj[g].
        Take a zfset S such that S /in stat(lambda) /\ g /in FfSset[(f,S)] /\ Ffinj[g] = (g,S).
        Then (a,b) = (g,S).
        Then a = g /\ b = S.
      end.
      Forall o1,o2 ((o1,o2) /in H => o2 /in Dom(FfSinj) /\ (FfSinj[o2] is a zffunction) /\ o1 /in Dom(FfSinj[o2])).
      Define Ffincl[(g,S)] = ((FfSinj[S])[g],S) for (g,S) in H.
      Ffincl is a zffunction.
      Proof.
        Let pair /in H.
        Then exists b /in stat(lambda) exists a /in FfSset[(f,b)] (pair = (a,b)).
        Take zfsets g,S such that S /in stat(lambda) /\ g /in FfSset[(f,S)] /\ pair = (g,S).
        (FfSinj[S])[g] is a zfset.
        Then ((FfSinj[S])[g],S) is a zfset.
        Ffincl[pair] = ((FfSinj[S])[g],S).
        Then Ffincl[pair] is a zfset.
      end.
      Ffincl is injective.
      Proof.
        Let pair1,pair2 /in H.
        Let pair1 /neq pair2.
        Then Ffincl[pair1] /neq Ffincl[pair2].
        Proof.
          pair1 /in H.
          Then exists b /in stat(lambda) exists a /in FfSset[(f,b)] (pair1 = (a,b)).
          Take zfsets g1,S1 such that S1 /in stat(lambda) /\ g1 /in FfSset[(f,S1)] /\ pair1 = (g1,S1).
          pair2 /in H.
          Then exists b /in stat(lambda) exists a /in FfSset[(f,b)] (pair2 = (a,b)).
          Take zfsets g2,S2 such that S2 /in stat(lambda) /\ g2 /in FfSset[(f,S2)] /\ pair2 = (g2,S2).
          Ffincl[(g1,S1)] = ((FfSinj[S1])[g1],S1).
          Ffincl[(g2,S2)] = ((FfSinj[S2])[g2],S2).
          (g1,S1) /neq (g2,S2).
          Then g1 /neq g2 \/ S1 /neq S2.
          Case S1 /neq S2.
            Then ((FfSinj[S1])[g1],S1) /neq ((FfSinj[S2])[g2],S2).
            Then Ffincl[(g1,S1)] /neq Ffincl[(g2,S2)].
          end.
          Case S1 = S2 /\ g1 /neq g2.
            FfSinj[S1] is injective.
            g1,g2 /in Dom(FfSinj[S1]).
            g1 /neq g2.
            Then (FfSinj[S1])[g1] /neq (FfSinj[S1])[g2].
            Then ((FfSinj[S1])[g1],S1) /neq ((FfSinj[S2])[g2],S2).
            Then Ffincl[(g1,S1)] /neq Ffincl[(g2,S2)].
          end.
        end.
      end.
      Let I = ran(Ffincl).
      I is a zfset.
      Proof.
        I = Ffincl^[H].
        Ffincl is a zffunction.
        H is a zfset.
      end.
      Then Ffincl : H /leftrightarrow I.
      Then Card(Ff[f]) = Card(I).
      I /subset kappa /times stat(lambda).
      Proof.
        Let pair /in I.
        Then pair /in ran(Ffincl).
        Take a zfset prepair such that prepair /in H /\ pair = Ffincl[prepair].
        prepair /in H.
        Then exists b /in stat(lambda) exists a /in FfSset[(f,b)] (prepair = (a,b)).
        Take zfsets g,S such that S /in stat(lambda) /\ g /in FfSset[(f,S)] /\ prepair = (g,S).
        Ffincl[prepair] = ((FfSinj[S])[g],S).
        Then pair = ((FfSinj[S])[g],S).
        S /in stat(lambda).
        Let FfSinjS = FfSinj[S].
        (FfSinj[S]) : FfSset[(f,S)] /rightarrow kappa.
        FfSinjS : FfSset[(f,S)] /rightarrow kappa.
        g /in Dom(FfSinjS).
        Then FfSinjS[g] /in kappa.
        (FfSinj[S])[g] = FfSinjS[g].
        Then (FfSinj[S])[g] /in kappa.
        Then pair /in kappa /times stat(lambda).
      end.
      Then Card(I) /subset Card(kappa /times stat(lambda)).
      kappa /times stat(lambda) /tilde kappa /times Card(stat(lambda)).
      kappa /times Card(stat(lambda)) /subset kappa /times kappa.
      Then Card(kappa /times Card(stat(lambda))) /subset Card(kappa /times kappa).
      kappa /in /Card.
      kappa * kappa = kappa.
      kappa * kappa = Card(kappa /times kappa).
      Then Card(kappa /times Card(stat(lambda))) /subset kappa.
      Card(kappa /times stat(lambda)) = Card(kappa /times Card(stat(lambda))).
      Then Card(kappa /times stat(lambda)) /subset kappa.
      Then Card(I) /subset kappa.

      Then Card(Ff[f]) /subset kappa.
    end.
  end.

  # Defining the sequence f xi

  Forall set /in /VV (set /neq /emptyset => set /in Dom(Choice)).
  Forall a (G /setminus a is a zfset).
  Proof.
    Let a be a set.
    G /setminus a /subset G.
  end.
  Define fxi[xi] =
    Case G /setminus (/bigcup Ff^[fxi /caret [xi]]) /in /VV /setminus </emptyset> -> Choice[G /setminus (/bigcup Ff^[fxi /caret [xi]])],
    Case G /setminus (/bigcup Ff^[fxi /caret [xi]]) = /emptyset -> G
  for xi in /Ord.
  Forall xi /in /Ord G /setminus (/bigcup Ff^[fxi /caret [xi]]) /in /VV.
  fxi is a zffunction.
  Proof.
    Let xi /in /Ord.
    Then fxi[xi] /in /VV.
    Proof.
      Case G /setminus (/bigcup Ff^[fxi /caret [xi]]) /neq /emptyset.
        Then fxi[xi] = Choice[G /setminus (/bigcup Ff^[fxi /caret [xi]])].
        Choice[G /setminus (/bigcup Ff^[fxi /caret [xi]])] /in G /setminus (/bigcup Ff^[fxi /caret [xi]]).
        Then Choice[G /setminus (/bigcup Ff^[fxi /caret [xi]])] /in /VV.
        Then fxi[xi] /in /VV.
      end.
      Case G /setminus (/bigcup Ff^[fxi /caret [xi]]) = /emptyset.
        Then fxi[xi] = G.
      end.
    end.
  end.
 
  Forall xi /in /Ord (fxi[xi] = G \/ fxi[xi] /in G).
  Proof.
    Let xi /in /Ord.
    Case G /setminus (/bigcup Ff^[fxi /caret [xi]]) = /emptyset.
    end.
    Case G /setminus (/bigcup Ff^[fxi /caret [xi]]) /neq /emptyset.
      Then fxi[xi] = Choice[G /setminus (/bigcup Ff^[fxi /caret [xi]])].
      Choice[G /setminus (/bigcup Ff^[fxi /caret [xi]])] /in G /setminus (/bigcup Ff^[fxi /caret [xi]]).
      G /setminus (/bigcup Ff^[fxi /caret [xi]]) /subset G.
      Then Choice[G /setminus (/bigcup Ff^[fxi /caret [xi]])] /in G.
      Then fxi[xi] /in G.
    end.
  end.
  
  Exists xi /in /Ord fxi[xi] = G.
  Proof by contradiction. Assume the contrary.
    Then forall xi /in /Ord fxi[xi] /in G.
    Then fxi : /Ord /rightarrow G.
    fxi is injective.
    Proof.
      Let a,b /in /Ord.
      Let a /neq b.
      Then fxi[a] /neq fxi[b].
      Proof by contradiction. Assume the contrary.
        Then fxi[a] = fxi[b].
        a /in b \/ b /in a (by TotalOrder).
        Case a /in b.
          G /setminus (/bigcup Ff^[fxi /caret [b]]) /neq /emptyset.
          Then fxi[b] = Choice[G /setminus (/bigcup Ff^[fxi /caret [b]])].
          Choice[G /setminus (/bigcup Ff^[fxi /caret [b]])] /in G /setminus (/bigcup Ff^[fxi /caret [b]]).
          Then fxi[a] /in G /setminus (/bigcup Ff^[fxi /caret [b]]).
          Then fxi[a] /notin /bigcup Ff^[fxi /caret [b]].
          fxi[a] /in Ff[fxi[a]].
          Proof.
            Ff[fxi[a]] = /bigcup Ffhelp[fxi[a]].
            Ffhelp[fxi[a]] = {FfSset[(fxi[a],S)] | S /in stat(lambda)}.
            Take a zfset S such that S /in stat(lambda).
            fxi[a] /in FfSset[(fxi[a],S)].
            Proof.
              fxi[a] /in G.
              S /subset Dom(fxi[a]).
              Forall i /in S ((fxi[a])[i] is a zfset).
              Forall i /in S (fxi[a])[i] /subset (fxi[a])[i].
              Then fxi[a] <{S} fxi[a].
            end.
            FfSset[(fxi[a],S)] /in Ffhelp[fxi[a]].
            Then fxi[a] /in /bigcup Ffhelp[fxi[a]].
          end.
          fxi[a] /in fxi /caret [b].
          Then Ff[fxi[a]] /in Ff^[fxi /caret [b]].
          Let Set1 = Ff[fxi[a]].
          Let Set2 = Ff^[fxi /caret [b]].
          Set1 /in Set2.
          fxi[a] /in Set1.
          Then fxi[a] /in /bigcup Set2.
          Then fxi[a] /in /bigcup Ff^[fxi /caret [b]].
          Contradiction.
        end.
        Case b /in a.
          G /setminus (/bigcup Ff^[fxi /caret [a]]) /neq /emptyset.
          Then fxi[b] = Choice[G /setminus (/bigcup Ff^[fxi /caret [a]])].
          Choice[G /setminus (/bigcup Ff^[fxi /caret [a]])] /in G /setminus (/bigcup Ff^[fxi /caret [a]]).
          Then fxi[b] /in G /setminus (/bigcup Ff^[fxi /caret [a]]).
          Then fxi[b] /notin /bigcup Ff^[fxi /caret [a]].
          fxi[b] /in Ff[fxi[b]].
          Proof.
            Ff[fxi[b]] = /bigcup Ffhelp[fxi[b]].
            Ffhelp[fxi[b]] = {FfSset[(fxi[b],S)] | S /in stat(lambda)}.
            Take a zfset S such that S /in stat(lambda).
            fxi[b] /in FfSset[(fxi[b],S)].
            Proof.
              fxi[b] /in G.
              S /subset Dom(fxi[b]).
              Forall i /in S ((fxi[b])[i] is a zfset).
              Forall i /in S (fxi[b])[i] /subset (fxi[b])[i].
              Then fxi[b] <{S} fxi[b].
            end.
            FfSset[(fxi[b],S)] /in Ffhelp[fxi[b]].
            Then fxi[b] /in /bigcup Ffhelp[fxi[b]].
          end.
          fxi[b] /in fxi /caret [a].
          Then Ff[fxi[b]] /in Ff^[fxi /caret [a]].
          Let Set1 = Ff[fxi[b]].
          Let Set2 = Ff^[fxi /caret [a]].
          Set1 /in Set2.
          fxi[b] /in Set1.
          Then fxi[b] /in /bigcup Set2.
          Then fxi[b] /in /bigcup Ff^[fxi /caret [a]].
          Contradiction.
        end.
      end.
    end.
    Let H = ran(fxi).
    Then fxi : /Ord /leftrightarrow H.
    H /subset G.
    Then H is a zfset.
    fxi^{-1} : H /leftrightarrow /Ord.
    /Ord = (fxi^{-1})^[H].
    Then /Ord /in /VV.
    Contradiction.
  end.
  
  Define vanish = {ordinal alpha | fxi[alpha] = G}.
  vanish /subset /Ord.
  vanish /neq /emptyset.
  Take a zfset alpha such that alpha = min(vanish).
  alpha /in vanish.
  Then fxi[alpha] = G.
  /bigcup Ff^[fxi^[alpha]] = G.
  Proof.
    G /setminus (/bigcup Ff^[fxi /caret [alpha]]) = /emptyset.
    Proof by contradiction. Assume the contrary.
      Then G /setminus (/bigcup Ff^[fxi /caret [alpha]]) /in /VV /setminus </emptyset>.
      Then fxi[alpha] = Choice[G /setminus (/bigcup Ff^[fxi /caret [alpha]])].
      Choice[G /setminus (/bigcup Ff^[fxi /caret [alpha]])] /in G /setminus (/bigcup Ff^[fxi /caret [alpha]]).
      G /setminus (/bigcup Ff^[fxi /caret [alpha]]) /subset G.
      Then Choice[G /setminus (/bigcup Ff^[fxi /caret [alpha]])] /in G.
      Then fxi[alpha] /in G.
      G /notin G.
      Then fxi[alpha] /neq G.
      Contradiction.
    end.
    Then G /subset /bigcup Ff^[fxi /caret [alpha]].
    fxi /caret [alpha] = fxi^[alpha].
    /bigcup Ff^[fxi /caret [alpha]] = /bigcup Ff^[fxi^[alpha]].
    /bigcup Ff^[fxi^[alpha]] /subset G.
    Proof.
      Let a /in /bigcup Ff^[fxi^[alpha]].
      Let Set1 = Ff^[fxi^[alpha]].
      a /in /bigcup Set1.
      Take a zfset b such that b /in Set1 /\ a /in b.
      b /in Ff^[fxi^[alpha]].
      Let Set2 = fxi^[alpha].
      b /in Ff^[Set2].
      Take a zfset c such that c /in Dom(Ff) /cap Set2 /\ b = Ff[c].
      Ff[c] = /bigcup Ffhelp[c].
      a /in /bigcup Ffhelp[c].
      Take a zfset d such that d /in Ffhelp[c] /\ a /in d.
      Ffhelp[c] = {FfSset[(c,S)] | S /in stat(lambda)}.
      Take a zfset S such that S /in stat(lambda) /\ d = FfSset[(c,S)].
      FfSset[(c,S)] /subset G.
      a /in FfSset[(c,S)].
      Then a /in G.
    end.
    Then /bigcup Ff^[fxi^[alpha]] = G.
  end.
    
  Let fxirest = fxi /upharpoonright alpha.
  fxirest : alpha /rightarrow G.
  Proof.
    Let i /in alpha.
    Then fxirest[i] = fxi[i].
    fxi[i] /in G.
    Then fxirest[i] /in G.
  end.
  fxirest is injective.
  Proof.
    Let a,b /in alpha.
    Let a /neq b.
    Then fxirest[a] /neq fxirest[b].
    Proof.
      fxirest[a] = fxi[a].
      fxirest[b] = fxi[b].
      fxi[a] /neq fxi[b].
      Proof by contradiction. Assume the contrary.
        Then fxi[a] = fxi[b].
        a,b are ordinals.
        a /in b \/ b /in a (by TotalOrder).
        Case a /in b.
          G /setminus (/bigcup Ff^[fxi /caret [b]]) /neq /emptyset.
          Then fxi[b] = Choice[G /setminus (/bigcup Ff^[fxi /caret [b]])].
          Choice[G /setminus (/bigcup Ff^[fxi /caret [b]])] /in G /setminus (/bigcup Ff^[fxi /caret [b]]).
          Then fxi[a] /in G /setminus (/bigcup Ff^[fxi /caret [b]]).
          Then fxi[a] /notin /bigcup Ff^[fxi /caret [b]].
          fxi[a] /in G.
          fxi[a] /in Ff[fxi[a]].
          Proof.
            Ff[fxi[a]] = /bigcup Ffhelp[fxi[a]].
            Ffhelp[fxi[a]] = {FfSset[(fxi[a],S)] | S /in stat(lambda)}.
            Take a zfset S such that S /in stat(lambda).
            fxi[a] /in FfSset[(fxi[a],S)].
            Proof.
              fxi[a] /in G.
              S /subset Dom(fxi[a]).
              Forall i /in S ((fxi[a])[i] is a zfset).
              Forall i /in S (fxi[a])[i] /subset (fxi[a])[i].
              Then fxi[a] <{S} fxi[a].
            end.
            FfSset[(fxi[a],S)] /in Ffhelp[fxi[a]].
            Then fxi[a] /in /bigcup Ffhelp[fxi[a]].
          end.
          fxi[a] /in fxi /caret [b].
          Then Ff[fxi[a]] /in Ff^[fxi /caret [b]].
          Let Set1 = Ff[fxi[a]].
          Let Set2 = Ff^[fxi /caret [b]].
          Set1 /in Set2.
          fxi[a] /in Set1.
          Then fxi[a] /in /bigcup Set2.
          Then fxi[a] /in /bigcup Ff^[fxi /caret [b]].
          Contradiction.
        end.
        Case b /in a.
          G /setminus (/bigcup Ff^[fxi /caret [a]]) /neq /emptyset.
          Then fxi[b] = Choice[G /setminus (/bigcup Ff^[fxi /caret [a]])].
          Choice[G /setminus (/bigcup Ff^[fxi /caret [a]])] /in G /setminus (/bigcup Ff^[fxi /caret [a]]).
          Then fxi[b] /in G /setminus (/bigcup Ff^[fxi /caret [a]]).
          Then fxi[b] /notin /bigcup Ff^[fxi /caret [a]].
          fxi[b] /in G.
          fxi[b] /in Ff[fxi[b]].
          Proof.
            Ff[fxi[b]] = /bigcup Ffhelp[fxi[b]].
            Ffhelp[fxi[b]] = {FfSset[(fxi[b],S)] | S /in stat(lambda)}.
            Take a zfset S such that S /in stat(lambda).
            fxi[b] /in FfSset[(fxi[b],S)].
            Proof.
              fxi[b] /in G.
              S /subset Dom(fxi[b]).
              Forall i /in S ((fxi[b])[i] is a zfset).
              Forall i /in S (fxi[b])[i] /subset (fxi[b])[i].
              Then fxi[b] <{S} fxi[b].
            end.
            FfSset[(fxi[b],S)] /in Ffhelp[fxi[b]].
            Then fxi[b] /in /bigcup Ffhelp[fxi[b]].
          end.
          fxi[b] /in fxi /caret [a].
          Then Ff[fxi[b]] /in Ff^[fxi /caret [a]].
          Let Set1 = Ff[fxi[b]].
          Let Set2 = Ff^[fxi /caret [a]].
          Set1 /in Set2.
          fxi[b] /in Set1.
          Then fxi[b] /in /bigcup Set2.
          Then fxi[b] /in /bigcup Ff^[fxi /caret [a]].
          Contradiction.
        end.
      end.
    end.
  end.

  /bigcup Ff^[fxirest^[alpha]] = G.
  Proof.
    Forall i /in alpha fxirest[i] = fxi[i].
    Proof.
      Let i /in alpha.
      fxi[i] = (fxi /upharpoonright alpha)[i].
      (fxi /upharpoonright alpha)[i] = fxirest[i].
      Then fxirest[i] = fxi[i].
    end.
    fxirest^[alpha] = fxi^[alpha].
  end.

  # alpha /subset Plus[kappa]

  alpha /subset Plus[kappa].
  Proof by contradiction. Assume the contrary.
    Then Plus[kappa] /in alpha.
    fxi[Plus[kappa]] /in G.
    Let f = fxi[Plus[kappa]].
    Forall v /in Plus[kappa] fxi[v] /in Dom(Ff).
    Forall v /in Plus[kappa] f /notin Ff[fxi[v]].
    Proof by contradiction. Assume the contrary.
      Take a zfset v such that v /in Plus[kappa] /\ f /in Ff[fxi[v]].
      fxi[v] /in G.
      Let kappaplus = Plus[kappa].
      f = fxi[kappaplus].
      G /setminus (/bigcup Ff^[fxi /caret [kappaplus]]) /neq /emptyset.
      fxi[kappaplus] = Choice[G /setminus (/bigcup Ff^[fxi /caret [kappaplus]])].
      Choice[G /setminus (/bigcup Ff^[fxi /caret [kappaplus]])] /in G /setminus (/bigcup Ff^[fxi /caret [kappaplus]]).
      Then f /in G /setminus (/bigcup Ff^[fxi /caret [kappaplus]]).
      Then f /notin /bigcup Ff^[fxi /caret [kappaplus]].
      v /in kappaplus.
      Then fxi[v] /in fxi /caret [kappaplus].
      Then Ff[fxi[v]] /in Ff^[fxi /caret [kappaplus]].
      Let Set1 = Ff^[fxi /caret [kappaplus]].
      Let Set2 = Ff[fxi[v]].
      f /in Ff[fxi[v]].
      Then f /in Set2.
      Set2 /in Set1.
      Then f /in /bigcup Set1.
      Then f /in /bigcup Ff^[fxi /caret [kappaplus]].
      Contradiction.
    end.
    Forall v /in Plus[kappa] fxi[v] /in Ff[f].
    Proof.
      Let v /in Plus[kappa].
      f /notin Ff[fxi[v]].
      Then fxi[v] /in Ff[f].
      Proof.
        f, fxi[v] /in G.
        Then f,fxi[v] are zffunctions.
        Dom(f) = lambda.
        Dom(fxi[v]) = lambda.
        Forall i /in lambda ((fxi[v])[i] is a zfset).
        Define sset = {i /in lambda | f[i] /subset (fxi[v])[i]}.
        sset is nonstationary in lambda.
        Proof by contradiction. Assume the contrary.
          Then sset is stationary in lambda.
          Then sset /in stat(lambda).
          f <{sset} fxi[v].
          Then f /in FfSset[(fxi[v],sset)].
          FfSset[(fxi[v],sset)] /in Ffhelp[fxi[v]].
          Then f /in /bigcup Ffhelp[fxi[v]].
          Ff[fxi[v]] = /bigcup Ffhelp[fxi[v]].
          Then f /in Ff[fxi[v]].
          Contradiction.
        end.
        Then lambda /setminus sset /in Club(lambda).
        Then lambda /setminus sset is stationary in lambda.
        Let lset = lambda /setminus sset.
        lset /in stat(lambda).
        Forall i /in lambda f[i], (fxi[v])[i] /in /Ord.
        Proof.
          f, fxi[v] /in G.
          Let i /in lambda.
          Plus[kap[i]] /in /Ord.
          f[i], (fxi[v])[i] /in Plus[kap[i]].
          Then f[i], (fxi[v])[i] /in /Ord.
        end.
        Then forall i /in lambda (f[i] /subset (fxi[v])[i] \/ (fxi[v])[i] /in f[i]).
        Forall i /in lset (fxi[v])[i] /subset f[i].
        Proof.
          Let i /in lset.
          Then i /in lambda.
          i /notin sset.
          Then not (f[i] /subset (fxi[v])[i]).
          Then (fxi[v])[i] /in f[i].
          Then (fxi[v])[i] /subset f[i].
        end.
        Then fxi[v] <{lset} f.
        Then fxi[v] /in FfSset[(f,lset)].
        FfSset[(f,lset)] /in Ffhelp[f].
        Let Set1 = FfSset[(f,lset)].
        Let Set2 = Ffhelp[f].
        fxi[v] /in Set1.
        Set1 /in Set2.
        Then fxi[v] /in /bigcup Set2.
        Ff[f] = /bigcup Set2.
        Then fxi[v] /in Ff[f].
      end.
    end.
    Then fxi^[Plus[kappa]] /subset Ff[f].
    Forall i /in Plus[kappa] i /in alpha.
    Forall i /in Plus[kappa] fxi[i] = fxirest[i].
    Proof.
      Let i /in Plus[kappa].
      i /in alpha.
      Then (fxi /upharpoonright alpha)[i] = fxi[i].
      fxirest[i] = (fxi /upharpoonright alpha)[i].
    end.
    fxi^[Plus[kappa]] = fxirest^[Plus[kappa]].
    Then fxirest^[Plus[kappa]] /subset Ff[f].
    Let fxipk = fxirest /upharpoonright Plus[kappa].
    fxipk : Plus[kappa] /rightarrow Ff[f].
    fxipk is injective.
    Then Plus[kappa] <= Ff[f].
    Then Plus[kappa] /subset Card(Ff[f]).
    Then kappa /in Card(Ff[f]).
    Card(Ff[f]) /subset kappa.
    Contradiction.
  end.

  # Finish

  G = /bigcup Ff^[fxi^[alpha]].
  Forall i /in alpha fxi[i] /in Dom(Ff).
  Forall f /in G exists i /in alpha f /in Ff[fxi[i]].
  Proof.
    Let f /in G.
    Then f /in /bigcup Ff^[fxi^[alpha]].
    Let Set1 = Ff^[fxi^[alpha]].
    f /in /bigcup Set1.
    Take a zfset a such that a /in Set1 /\ f /in a.
    Let Set2 = fxi^[alpha].
    a /in Ff^[Set2].
    Take a zfset b such that b /in Dom(Ff) /cap Set2 /\ a = Ff[b].
    b /in fxi^[alpha].
    Dom(fxi) /cap alpha = alpha.
    Take a zfset i such that i /in alpha /\ b = fxi[i].
    Then f /in Ff[fxi[i]].
  end.
  
  Define Gincl[f] = (Choose a zfset i such that i /in alpha /\ f /in Ff[fxi[i]] in (f,i)) for f in G.
  Gincl is a zffunction.
  Proof.
    Let f /in G.
    Take a zfset i such that i /in alpha /\ f /in Ff[fxi[i]] /\ Gincl[f] = (f,i).
    Then (f,i) /in /VV.
    Then Gincl[f] /in /VV.
  end.
  Gincl is injective.
  
  Define Ginclfunc[i] = Ff[fxi[i]] for i in alpha.
  Ginclfunc is a zffunction.
  Proof.
    Let i /in alpha.
    Ff[fxi[i]] /in /VV.
    Then Ginclfunc[i] /in /VV.
  end.
  ran(Gincl) /subset /sumset Ginclfunc.
  Then Gincl : G /rightarrow /sumset Ginclfunc.
  Card(G) /subset Card(/sumset Ginclfunc).
  Card(/sumset Ginclfunc) = /sum cardseq(Ginclfunc).
  /sumset cardseq(Ginclfunc) /subset Plus[kappa] /times Plus[kappa].
  Proof.
    Forall pair /in /sumset cardseq(Ginclfunc) pair /in Plus[kappa] /times Plus[kappa].
    Proof.
      Let pair /in /sumset cardseq(Ginclfunc).
      Let f = cardseq(Ginclfunc).
      Then pair /in /sumset f.
      Dom(f) = alpha.
      Then exists b /in alpha exists a /in f[b] (pair = (a,b)).
      Take zfsets a,b such that b /in alpha /\ a /in f[b] /\ pair = (a,b).
      Then b /in Plus[kappa].
      f[b] = cardseq(Ginclfunc)[b].
      cardseq(Ginclfunc)[b] = Card(Ginclfunc[b]).
      Ginclfunc[b] = Ff[fxi[b]].
      Let g = fxi[b].
      g /in G.
      Then Card(Ff[g]) /subset kappa.
      Then f[b] /subset kappa.
      Then a /in kappa.
      kappa /in Plus[kappa].
      Then kappa /subset Plus[kappa].
      Then a /in Plus[kappa].
      Then pair /in Plus[kappa] /times Plus[kappa].
    end.
  end.
  Plus[kappa] /times Plus[kappa] is a zfset.
  Then Card(/sumset cardseq(Ginclfunc)) /subset Card(Plus[kappa] /times Plus[kappa]).
  Card(Plus[kappa] /times Plus[kappa]) = Plus[kappa] * Plus[kappa].
  Plus[kappa] /in /Card.
  Proof.
    kappa /in /Card.
    Then /NN /subset kappa.
    kappa /in Plus[kappa].
    kappa /subset Plus[kappa].
    Then /NN /subset Plus[kappa].
  end.
  Then Plus[kappa] * Plus[kappa] = Plus[kappa].
  Then Card(Plus[kappa] /times Plus[kappa]) = Plus[kappa].
  Then Card(G) /subset Plus[kappa].
  
  Then Card(F) /subset Plus[kappa].
qed.




