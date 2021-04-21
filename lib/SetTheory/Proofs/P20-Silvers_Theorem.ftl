[read Formalizations/Library/L19-The_Last_Lemma.ftl]


## Pretyped Variables

Let w,x,y,z,W,X,Y,Z stand for zfsets.
Let a,b,c,d,A,B,C,D,M stand for sets.
Let o,o1,o2 stand for objects.
Let alpha, beta, gamma stand for ordinals.
Let f,g,h,F,G,H stand for zffunction.
Let kappa, lambda stand for cardinals.



## Prerequisites

Lemma. Let X be a set. Let f be a zffunction. Then exists g (Dom(f) = Dom(g) and forall i /in Dom(f) g[i] = f[i] /cap X).
Proof.
  Define g[i] = f[i] /cap X for i in Dom(f).
  g is a zffunction.
  Proof.
    Let i /in Dom(f).
    Then f[i] /in /VV.
    f[i] /cap X /subset f[i].
    Then f[i] /cap X /in /VV.
    Then g[i] /in /VV.
  end.
qed.

Definition. Let X be a set. Let f be a zffunction. The functionintersection of f and X is a zffunction g such that
Dom(f) = Dom(g) and forall i /in Dom(f) g[i] = f[i] /cap X.
Let f /intersect X stand for the functionintersection of f and X.



## The Theorem


Theorem Silver. Let kappa /in /BigSingCard. Let GCH below kappa. Then 2 ^ kappa = Plus[kappa].
Proof.
  Take a zfset x such that (kappa,x) is a cofpair.
  Take a zffunction kap such that (kappa,x,kap) is a coftriple.
  Dom(kap) = cof(kappa).
  Take an ordinal lambda such that lambda = cof(kappa).
  x /subset kappa /cap /Card.
  x /subset kappa.
  x /subset /Card.
  Forall i /in lambda kap[i] /in /Card.
  Forall i /in lambda kap[i] /in kappa.
  Define A[i] = /PP kap[i] for i in lambda.
  Then A is a zffunction.
  Proof.
    Let i /in lambda.
    kap[i] /in /VV.
    Then /PP kap[i] /in /VV.
    Then A[i] /in /VV.
  end.
  Forall i /in lambda (Plus[kap[i]] is a zfset).
  Forall i /in lambda Card(A[i]) /subset Plus[kap[i]].
  Proof.
    Let i /in lambda.
    A[i] = /PP kap[i].
    Card(/PP kap[i]) = 2 ^ kap[i].
    kap[i] /in kappa /cap /Card.
    Then 2 ^ kap[i] = Plus[kap[i]].
    Then Card(A[i]) = Plus[kap[i]].
  end.
  Then A is silvercompatible with kap relative to kappa and x.

  Define f[X] = kap /intersect X for X in /PP kappa.
  f is a zffunction.
  Proof.
    Let X /in /PP kappa.
    f[X] is a zffunction.
    Dom(f[X]) /in /VV.
    Then f[X] /in /VV.
  end.
  Let F = ran(f).
  F = f^[/PP kappa].
  
  f is injective.
  Proof.
    Let X,Y /in Dom(f).
    Let X /neq Y.
    X,Y /in /PP kappa.
    Then exists alpha /in /VV ((alpha /in X /\ alpha /notin Y) \/ (alpha /in Y /\ alpha /notin X)).
    Proof.
      not (X /subset Y) \/ not (Y /subset X).
      Proof by contradiction. Assume the contrary.
        Then X /subset Y /\ Y /subset X.
        Then X = Y.
        Contradiction.
      end.
    end.
    Take a zfset alpha such that (alpha /in X /\ alpha /notin Y) \/ (alpha /in Y /\ alpha /notin X).
    Then alpha /in kappa.
    x /club kappa.
    Take a zfset y such that y /in x /\ alpha /in y.
    Take a zfset beta such that beta /in lambda /\ kap[beta] = y.
    X /cap kap[beta] /neq Y /cap kap[beta].
    (f[X])[beta] = X /cap kap[beta].
    (f[Y])[beta] = Y /cap kap[beta].
    Then (f[X])[beta] /neq (f[Y])[beta].
    Then f[X] /neq f[Y].
  end.
  Then f : /PP kappa /leftrightarrow F.
  Then Card(F) = Card(/PP kappa).
  Card(/PP kappa) = 2 ^ kappa.
  Then Card(F) = 2 ^ kappa.
  Then Plus[kappa] /subset Card(F).

  F /subset /prodset A.
  Proof.
    Let g /in F.
    Take a zfset X such that X /in /PP kappa /\ f[X] = g.
    Then g = kap /intersect X.
    Then Dom(g) = lambda.
    Forall i /in lambda g[i] = kap[i] /cap X.
    Then forall i /in lambda g[i] /in /PP kap[i].
    Forall i /in lambda A[i] = /PP kap[i].
    Then forall i /in lambda g[i] /in A[i].
    Then g /in /prodset A.
  end.

  F is an almost disjoint family of functions on lambda.
  Proof.
    (F,lambda) is an adfampair.
    Forall g,h /in F (g /neq h => (g and h are almost disjoint on lambda)).
    Proof.
      Let g,h /in F.
      Let g /neq h.
      Then g and h are almost disjoint on lambda.
      Proof.
        Take a zfset X such that X /in /PP kappa /\ g = f[X].
        Take a zfset Y such that Y /in /PP kappa /\ h = f[Y].
        g = kap /intersect X.
        h = kap /intersect Y.
        X /neq Y.
        Then exists alpha /in /VV ((alpha /in X /\ alpha /notin Y) \/ (alpha /in Y /\ alpha /notin X)).
        Proof.
          not (X /subset Y) \/ not (Y /subset X).
          Proof by contradiction. Assume the contrary.
            Then X /subset Y /\ Y /subset X.
            Then X = Y.
            Contradiction.
          end.
        end.
        Take a zfset alpha such that (alpha /in X /\ alpha /notin Y) \/ (alpha /in Y /\ alpha /notin X).
        Then alpha /in kappa.
        x /club kappa.
        Take a zfset y such that y /in x /\ alpha /in y.
        Take a zfset beta such that beta /in lambda /\ kap[beta] = y.
        Then forall gamma /in lambda (beta /in gamma => g[gamma] /neq h[gamma]).
        Proof.
          Let gamma /in lambda.
          Let beta /in gamma.
          Then g[gamma] /neq h[gamma].
          Proof.
            beta, gamma /in Dom(kap).
            beta /in gamma.
            kap is an epsiso.
            Then kap[beta] /in kap[gamma] (by epsiso).
            Then alpha /in kap[gamma].
            Then X /cap kap[gamma] /neq Y /cap kap[gamma].
            (f[X])[gamma] = X /cap kap[gamma].
            (f[Y])[gamma] = Y /cap kap[gamma].
            Then (f[X])[gamma] /neq (f[Y])[gamma].
            Then g[gamma] /neq h[gamma].
          end.
        end.
      end.
    end.
    Then F is an almost disjoint family of functions on lambda (by adfam2).
  end.
  Then F is almost disjoint relative to A.
  Silver below kappa.
  Then Card(F) /subset Plus[kappa] (by Silver2).
  Then Card(F) = Plus[kappa].
  
  Then 2 ^ kappa = Plus[kappa].
qed.




