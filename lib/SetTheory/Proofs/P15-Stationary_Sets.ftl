[read Formalizations/Library/L14-Clubs.ftl]


## Pretyped Variables

Let w,x,y,z,W,X,Y,Z stand for zfsets.
Let a,b,c,d,A,B,C,D,M stand for sets.
Let o,o1,o2 stand for objects.
Let alpha, beta, gamma stand for ordinals.
Let f,g,h,F,G,H stand for zffunction.
Let kappa, lambda stand for cardinals.



## Stationary Sets

Definition. Let kappa /in /BigCard. Let X /subset kappa. X is nonstationary in kappa iff kappa /setminus X /in Club(kappa).

Definition. Let kappa /in /BigCard. The nonstationary ideal of kappa is {X /subset kappa | X is nonstationary in kappa}.
Let NS(k) stand for the nonstationary ideal of k.

Definition. Let kappa /in /BigCard. Let X /subset kappa. X is stationary in kappa iff X /notin NS(kappa).

Lemma stationary. Let kappa /in /BigCard. Let X /subset kappa. X is stationary in kappa iff (forall C /subset kappa (C /club kappa => X /cap C /neq /emptyset)).
Proof.
  (X is stationary in kappa) => (forall C /subset kappa (C /club kappa => X /cap C /neq /emptyset)).
  Proof.
    Let X be stationary in kappa. Let C /subset kappa. Let C /club kappa.
    Then X /cap C /neq /emptyset.
    Proof by contradiction. Assume the contrary.
      Then X /cap C = /emptyset.
      Then C /subset kappa /setminus X.
      Then kappa /setminus X /in Club(kappa).
      Contradiction.
    end.
  end.
  (Forall C /subset kappa (C /club kappa => X /cap C /neq /emptyset)) => (X is stationary in kappa).
  Proof by contradiction. Assume the contrary.
    Then kappa /setminus X /in Club(kappa).
    Take a zfset C such that C /subset kappa /setminus X /\ C /club kappa.
    Then C /cap X = /emptyset.
    C /subset kappa /\ C /club kappa.
    Contradiction.
  end.
qed.


Lemma. Let kappa /in /BigCard. Let X /in Club(kappa). Then X is stationary in kappa.
Proof.
  Take a zfset C such that C /subset X /\ C /club kappa.
  Forall D /subset kappa (D /club kappa => C /cap D /club kappa).
  Proof.
    Let D /subset kappa. Let D /club kappa.
    C,D /subset kappa. C,D /club kappa. Then C /cap D /club kappa.
  end.
  Forall E /subset kappa (E /club kappa => E /neq /emptyset).
  Forall D /subset kappa (D /club kappa => C /cap D /neq /emptyset).
  Then forall D /subset kappa (D /club kappa => X /cap D /neq /emptyset).
  Then X is stationary in kappa (by stationary).
qed.


Lemma. Let kappa /in /BigCard. /emptyset /neq NS(kappa) /\ NS(kappa) /subset /PP kappa.
Proof.
  /emptyset is nonstationary in kappa.
  Proof.
    kappa /setminus /emptyset /in Club(kappa).
  end.
qed.


Lemma. Let kappa /in /BigCard. kappa /notin NS(kappa).
Proof.
  /emptyset /notin Club(kappa).
  Then kappa is not nonstationary in kappa.
qed.


Lemma NSsubset. Let kappa /in /BigCard. Let X /in NS(kappa). Let Y /subset X. Then Y /in NS(kappa).
Proof.
  kappa /setminus X /in Club(kappa).
  kappa /setminus X /subset kappa /setminus Y.
  kappa /setminus Y /subset kappa.
  Then kappa /setminus Y /in Club(kappa).
  Proof.
    Let XX = kappa /setminus X.
    Let YY = kappa /setminus Y.
    XX /in Club(kappa).
    XX /subset YY.
    YY /subset kappa.
    Then YY /in Club(kappa) (by ClubSubset).
  end.
qed.


Lemma. Let kappa /in /BigCard. Let X,Y /in NS(kappa). Then X /cup Y /in NS(kappa).
Proof.
  kappa /setminus X, kappa /setminus Y /in Club(kappa).
  Then (kappa /setminus X) /cap (kappa /setminus Y) /in Club(kappa).
  (kappa /setminus X) /cap (kappa /setminus Y) = kappa /setminus (X /cup Y).
  Then kappa /setminus (X /cup Y) /in Club(kappa).
  Then X /cup Y is nonstationary in kappa.
qed.


Lemma. Let kappa /in /BigCard. Let lambda /in cof(kappa). Let lambda /neq /emptyset. Let X be a sequence of length lambda in NS(kappa). Then /bigcup X^[lambda] /in NS(kappa).
Proof.
  Define Y[i] = kappa /setminus X[i] for i in lambda.
  Y is a zffunction.
  Proof.
    Let i /in lambda.
    Then Y[i] /subset kappa.
    Then Y[i] /in /VV.
  end.
  Then Y is a sequence of length lambda in Club(kappa).
  Proof.
    kappa /in /BigCard.
    lambda /in /Ord.
    Dom(Y) = lambda.
    Forall i /in lambda Y[i] /in Club(kappa).
    Then Y is a sequence of length lambda in Club(kappa) (by sequence).
  end.
  Then /bigcap Y^[lambda] /in Club(kappa).
  kappa /setminus /bigcap Y^[lambda] /in NS(kappa).
  Proof.
    kappa /setminus (kappa /setminus /bigcap Y^[lambda]) = /bigcap Y^[lambda].
  end.
  /bigcup X^[lambda] /subset kappa /setminus /bigcap Y^[lambda].
  Proof.
    Let a /in /bigcup X^[lambda].
    Take a zfset b such that b /in X^[lambda] /\ a /in b.
    Take a zfset i such that i /in lambda /\ b = X[i].
    X[i] /in NS(kappa).
    Then X[i] /subset kappa.
    Then a /in kappa.
    Then a /notin Y[i].
    Then a /notin /bigcap Y^[lambda].
    Then a /in kappa /setminus /bigcap Y^[lambda].
  end.
  Then /bigcup X^[lambda] /in NS(kappa) (by NSsubset).
qed.


Lemma. Let kappa /in /BigCard. Let cof(kappa) = kappa. Let X be a sequence of length kappa in /PP kappa. Then forall i /in kappa X[i] /in /VV.


Definition. Let kappa /in /BigCard. Let cof(kappa) = kappa. Let X be a sequence of length kappa in /PP kappa.
The diagonal intersection of X of length kappa is {beta /in kappa | forall i /in beta (i /in kappa /\ X[i] /subset kappa /\ beta /in X[i])}.
Let /triangle(X,k) stand for the diagonal intersection of X of length k.


Definition. Let kappa /in /BigCard. Let cof(kappa) = kappa. Let X be a sequence of length kappa in /PP kappa.
The diagonal union of X of length kappa is {beta /in kappa | exists i /in beta (i /in kappa /\ X[i] /subset kappa /\ beta /in X[i])}.
Let /vartriangle(X,k) stand for the diagonal union of X of length k.


Lemma. Let kappa /in /BigCard. Let X be a sequence of length kappa in Club(kappa). Then X is a sequence of length kappa in /PP kappa.
Proof.
  X is a zffunction.
  Dom(X) = kappa /\ forall i /in kappa X[i] /in /PP kappa.
  Proof.
    Let i /in kappa.
    Then X[i] /in Club(kappa).
  end.
  kappa /in /Ord.
  Then X is a sequence of length kappa in /PP kappa (by sequence).
qed.


Lemma. Let kappa /in /BigCard. Let X be a sequence of length kappa in Cl(kappa). Then X is a sequence of length kappa in /PP kappa.
Proof.
  X is a zffunction.
  Dom(X) = kappa /\ forall i /in kappa X[i] /in /PP kappa.
  Proof.
    Let i /in kappa.
    Then X[i] /in Cl(kappa).
  end.
  kappa /in /Ord.
  Then X is a sequence of length kappa in /PP kappa (by sequence).
qed.


Lemma. Let kappa /in /BigCard. Let X be a sequence of length kappa in NS(kappa). Then X is a sequence of length kappa in /PP kappa.
Proof.
  X is a zffunction.
  Dom(X) = kappa /\ forall i /in kappa X[i] /in /PP kappa.
  Proof.
    Let i /in kappa.
    Then X[i] /in NS(kappa).
  end.
  kappa /in /Ord.
  Then X is a sequence of length kappa in /PP kappa (by sequence).
qed.


Lemma. Let kappa /in /BigCard. Let kappa be regular. Let X be a sequence of length kappa in Club(kappa). Then /triangle(X,kappa) /in Club(kappa).
Proof.
  Forall i /in kappa (X[i] is a zfset).
  Forall i /in kappa exists Ci /subset X[i] (Ci /in Cl(kappa)).
  Proof.
    Let i /in kappa.
    Then X[i] /in Club(kappa).
    Forall Ci /subset X[i] Ci /subset kappa.
    Take a zfset Ci such that Ci /subset X[i] /\ Ci /club kappa.
    Then Ci /in Cl(kappa).
  end.
  Define C[i] = (Choose a zfset Ci such that Ci /subset X[i] /\ Ci /in Cl(kappa) in Ci) for i in kappa.
  C is a zffunction.
  Proof.
    Let i /in kappa.
    Then C[i] /subset kappa.
    Then C[i] /in /VV.
  end.
  C is a sequence of length kappa in Cl(kappa).
  Proof.
    C is a zffunction.
    kappa /in /Ord.
    Dom(C) = kappa /\ forall i /in kappa C[i] /in Cl(kappa).
    Then C is a sequence of length kappa in Cl(kappa) (by sequence).
  end.
  /triangle(C,kappa) /subset /triangle(X,kappa).
  Proof.
    Let beta /in /triangle(C,kappa).
    Then forall i /in beta (beta /in C[i]).
    Then forall i /in beta (i /in kappa /\ X[i] /subset kappa /\ beta /in X[i]).
    Proof.
      Let i /in beta.
      Then i /in kappa.
      Then X[i] /subset kappa.
      beta /in C[i].
      C[i] /subset X[i].
      Then beta /in X[i].
    end.
    Then beta /in /triangle(X,kappa).
  end.
  
  Let M = /triangle(C,kappa).
  M /subset kappa.
  M /closed kappa.
  Proof.
    Let lambda /in /Lim /cap kappa.
    Let lambda /cap M /cof lambda.
    Then lambda /in M.
    Proof.
      Forall j /in lambda j /in kappa.
      Forall j /in lambda lambda /in C[j].
      Proof.
        Let j /in lambda.
        M /setminus (j+'1) /subset C[j].
        Proof.
          Let beta /in M /setminus (j+'1).
          Forall i /in beta (i /in kappa /\ beta /in C[i]).
          j /in beta.
          Proof.
            j, beta /in /Ord.
            j /in beta \/ beta /in j \/ j = beta (by TotalOrder).
            beta /notin j+'1.
            Then beta /neq j /\ beta /notin j.
          end.
        end.
        lambda /cap (M /setminus (j+'1)) /cof lambda.
        Proof.
          Let alpha /in lambda.
          lambda /cap M /cof lambda.
          Exists z /in lambda /cap M (alpha /in z /\ j /in z).
          Proof.
            alpha, j /in lambda.
            Take a zfset z1 such that z1 /in lambda /cap M /\ alpha /in z1.
            Take a zfset z2 such that z2 /in lambda /cap M /\ j /in z2.
            Let z = z1 /cup z2.
            Then z1 /subset z /\ z2 /subset z.
            z = z1 \/ z = z2.
            Proof.
              z1, z2 /in /Ord.
              z1 /in z2 \/ z2 /in z1 \/ z1 = z2 (by TotalOrder).
              Then z1 /subset z2 \/ z2 /subset z1.
              Then z1 /cup z2 = z1 \/ z1 /cup z2 = z2.
            end.
            Then z /in lambda /cap M.
            alpha /in z /\ j /in z.
          end.
          Take a zfset z such that z /in lambda /cap M /\ alpha /in z /\ j /in z.
          Then z /notin (j+'1).
          Then z /in lambda /cap (M /setminus (j+'1)).
        end.
        lambda /cap (M /setminus (j+'1)) /subset (lambda /cap C[j]).
        Then C[j] /cap lambda /cof lambda.
        Proof.
          Let alpha /in lambda.
          Take a zfset z such that z /in lambda /cap (M /setminus (j+'1)) /\ alpha /in z.
          Then z /in C[j] /cap lambda.
        end.
        Then lambda /in C[j].
      end.
      lambda /in kappa.
      Then lambda /in /triangle(C,kappa).
    end.
  end.
  
  M /cof kappa.
  Proof.
    Let alpha /in kappa.
    Forall beta /in kappa (/bigcap C^[beta] /setminus (beta+'1)) /cap kappa /neq /emptyset.
    Proof.
      Let beta /in kappa.
      Then (/bigcap C^[beta] /setminus (beta+'1)) /cap kappa /neq /emptyset.
      Proof.
        Case beta /neq 0.
          Forall i /in beta i /in kappa.
          Define D[i] = C[i] for i in beta.
          Then D is a zffunction.
          Proof.
            Let i /in beta.
            Then D[i] = C[i].
            C[i] /in /VV.
          end.
          beta /in /Ord.
          Dom(D) = beta /\ forall i /in beta D[i] /in Cl(kappa).
          Then D is a sequence of length beta in Cl(kappa) (by sequence).
          beta /in cof(kappa).
          Then /bigcap D^[beta] /club kappa.
          beta /in kappa.
          Take a zfset z such that z /in /bigcap D^[beta] /\ beta /in z.
          /bigcap D^[beta] /subset /bigcap C^[beta].
          Then z /in /bigcap C^[beta] /setminus (beta+'1).
          Proof.
            z /in /bigcap C^[beta].
            beta /in z.
            Then z /notin beta.
            z /neq beta.
            Then z /notin beta +' 1.
          end.
          Take a zfset i such that i /in beta.
          C[i] /in C^[beta].
          Then /bigcap C^[beta] /subset C[i].
          Then z /in C[i].
          C[i] /subset kappa.
          Then z /in kappa.
          Then z /in (/bigcap C^[beta] /setminus (beta+'1)) /cap kappa.
        end.
        Case beta = 0.
          Then C^[beta] = /emptyset.
          Then /bigcap C^[beta] = /VV.
        end.
      end.
    end.
    Define sup[beta] = (Choose a zfset j such that (j /in (/bigcap C^[beta] /setminus (beta+'1)) /cap kappa) in j) for i in kappa.
    sup : kappa /rightarrow kappa.
    Proof.
      Let i /in kappa.
      Then sup[i] /in kappa.
    end.
    Forall beta /in kappa beta /in sup[beta].
    Proof.
      Let beta /in kappa.
      Take ordinals a,b such that a = beta /\ b = sup[beta].
      Then a,b /in /Ord.
      Then a /in b \/ b /in a \/ a = b (by TotalOrder).
      sup[beta] /notin beta +' 1.
      Then b /notin a++.
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
    x, kappa /in /Ord.
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
  
    Then x /in /triangle(C,kappa).
    Proof.
      Let j /in x.
      Take a zfset n such that n /in /NN /\ j /in f[n].
      f^[/NN /setminus (n+'1)] /subset C[j].
      Proof.
        Let a /in f^[/NN /setminus (n+'1)].
        f^[/NN /setminus (n+'1)] = {f[m] | m /in /NN /setminus (n+'1)}.
        Take a zfset m such that m /in (/NN /setminus (n+'1)) /\ a = f[m].
        Then n /in m.
        m /neq 0.
        f[m] = sup[f[m--]].
        sup[f[m--]] /in /bigcap C^[f[m--]].
        Then a /in /bigcap C^[f[m--]].
        n /subset m--.
        Proof.
          m = (m--)++.
        end.
        Then f[n] /subset f[m--].
        Then j /in f[m--].
        Then C[j] /in C^[f[m--]].
        Then /bigcap C^[f[m--]] /subset C[j].
        Then a /in C[j].
      end.
      x /in /Lim /cap kappa.
      C[j] /cap x /cof x.
      Proof.
        Let a /in x.
        Take a zfset b such that b /in f^[/NN] /\ a /in b.
        Take a zfset m such that m /in /NN /\ b = f[m].
        Let k = m /cup (n+'1).
        k = m \/ k = n+'1.
        Proof.
          m, n+'1 /in /Ord.
          m /in n+'1 \/ n+'1 /in m \/ m = n+'1 (by TotalOrder).
          Then m /subset n+'1 \/ n+'1 /subset m.
          Then m /cup (n+'1) = m \/ m /cup (n+'1) = n+'1.
        end.
        m /subset k.
        Then f[m] /subset f[k].
        Proof.
          Forall aa,bb /in /NN (aa /subset bb => f[aa] /subset f[bb]).
          m,k /in /NN => (m /subset k => f[m] /subset f[k]).
          Then m /subset k => f[m] /subset f[k].
        end.
        Then a /in f[k].
        k /notin n+'1.
        Then k /in /NN /setminus (n+'1).
        Then f[k] /in f^[/NN /setminus (n+'1)].
        Then f[k] /in C[j].
        f[k] /in f[k+'1].
        f[k+'1] /in f^[/NN].
        Then f[k] /in x.
        Then f[k] /in C[j] /cap x.
      end.
    end.  
  end.  
qed.


Lemma. Let kappa /in /BigCard. Let kappa be regular. Let X be a sequence of length kappa in NS(kappa). Then /vartriangle(X,kappa) /in NS(kappa).
Proof.
  Define Y[i] = kappa /setminus X[i] for i in kappa.
  Then Y is a zffunction.
  Proof.
    Let i /in kappa.
    Then Y[i] /subset kappa.
    Then Y[i] /in /VV.
  end.
  kappa /in /Ord.
  Dom(Y) = kappa /\ forall i /in kappa Y[i] /in Club(kappa).
  Proof.
    Let i /in kappa.
    Then X[i] is nonstationary in kappa.
    Then kappa /setminus X[i] /in Club(kappa).
    Then Y[i] /in Club(kappa).
  end.
  Then Y is a sequence of length kappa in Club(kappa) (by sequence).
  Then /triangle(Y,kappa) /in Club(kappa).
  Then kappa /setminus /triangle(Y,kappa) /in NS(kappa).
  Proof.
    kappa /setminus (kappa /setminus /triangle(Y,kappa)) = /triangle(Y,kappa).
    Then kappa /setminus (kappa /setminus /triangle(Y,kappa)) /in Club(kappa).
    Then kappa /setminus /triangle(Y,kappa) is nonstationary in kappa.
  end.
  /vartriangle(X,kappa) /subset kappa /setminus /triangle(Y,kappa).
  Proof.
    Let beta /in /vartriangle(X,kappa).
    Then beta /in kappa.
    Take a zfset i such that i /in beta /\ X[i] /subset kappa /\ beta /in X[i].
    Then beta /notin Y[i].
    Then beta /notin /triangle(Y,kappa).
    Then beta /in kappa /setminus /triangle(Y,kappa).
  end.
qed.





