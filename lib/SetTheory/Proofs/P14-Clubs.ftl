[read Formalizations/Library/L12-Cardinal_Exponentiation.ftl]


## Pretyped Variables

Let w,x,y,z,W,X,Y,Z stand for zfsets.
Let a,b,c,d,A,B,C,D,M stand for sets.
Let o,o1,o2 stand for objects.
Let alpha, beta, gamma stand for ordinals.
Let f,g,h,F,G,H stand for zffunction.
Let kappa, lambda stand for cardinals.





## Closed unbounded sets


Definition. The class of cardinals of uncountable cofinality is
{kappa /in /Card | Alef[1] /subset cof(kappa)}.
Let /BigCard stand for the class of cardinals of uncountable cofinality.


Lemma. Let kappa /in /BigCard. Then kappa /in /Card and Alef[1] /subset cof(kappa).


Definition. Let kappa /in /Lim. Let C /subset kappa. C is closed in kappa iff
(forall lambda /in /Lim /cap kappa (C /cap lambda /cof lambda => lambda /in C)).
Let C /closed k stand for C is closed in k.


Definition. Let kappa /in /Lim. Let C /subset kappa. C is closed unbounded in kappa iff
(C /cof kappa /\ (C is closed in kappa)).
Let C /club k stand for C is closed unbounded in k.


Definition. Let kappa /in /Lim. The set of clubs in kappa is
{X /subset kappa | X /club kappa}.
Let Cl(k) stand for the set of clubs in k.


Lemma. Let kappa /in /Lim. Let alpha /in kappa. Let X /in Cl(kappa). Then X /setminus alpha /in Cl(kappa).
Proof.
  X /setminus alpha /subset kappa.
  X /setminus alpha /cof kappa.
  Proof.
    Let a /in kappa.
    Then a /cup alpha /in kappa.
    X /club kappa.
    Take a zfset b such that b /in X /\ a /cup alpha /in b.
    Then b /in X /setminus alpha.
    a, a /cup alpha are ordinals.
    a /subset a /cup alpha.
    Then a = a /cup alpha \/ a /in a /cup alpha.
    a /in b.
  end.
  Forall lambda /in /Lim /cap kappa ((X /setminus alpha) /cap lambda /cof lambda => lambda /in X /setminus alpha).
  Proof.
    Let lambda /in /Lim /cap kappa.
    Let (X /setminus alpha) /cap lambda /cof lambda.
    Then X /cap lambda /cof lambda.
    Then lambda /in X.
    lambda /notin alpha.
    Proof by contradiction. Assume the contrary.
      Then lambda /in alpha.
      Then (X /setminus alpha) /cap lambda = /emptyset.
      Contradiction.
    end.
    Then lambda /in X /setminus alpha.
  end.
  Then X /setminus alpha is closed in kappa.
  Then X /setminus alpha /in Cl(kappa).
qed.


Signature. Let M be a set. Let lambda /in /Ord. A sequence of length lambda in M is a zffunction.
Axiom sequence. Let M be a set. Let lambda /in /Ord. Let C be a zffunction. C is a sequence of length lambda in M iff Dom(C) = lambda /\ forall i /in lambda C[i] /in M.
Axiom. Let M be a set. Let lambda /in /Ord. Let C be a sequence of length lambda in M. Then (C is a zffunction) /\ Dom(C) = lambda /\ forall i /in lambda C[i] /in M.


Lemma clubintersection. Let kappa /in /BigCard. Let lambda /in cof(kappa). Let lambda /neq /emptyset. Let C be a sequence of length lambda in Cl(kappa).
Then (C is a zffunction) /\ /bigcap C^[lambda] /subset kappa /\ /bigcap C^[lambda] /club kappa.
Proof.
  C is a zffunction.
  Dom(C) = lambda /\ forall i /in lambda (C[i] /in Cl(kappa)).
  Let M = /bigcap C^[lambda].
  M /subset kappa.
  Proof.
    Let x /in M.
    Take a zfset i such that i /in lambda.
    C[i] /in C^[lambda].
    Then x /in C[i].
    C[i] /subset kappa.
    Then x /in kappa.
  end.
  
  M /closed kappa.
  Proof.
    Let gamma /in /Lim /cap kappa.
    Let M /cap gamma /cof gamma.
    Then gamma /in M.
    Proof.
      Let y /in C^[lambda].
      Then gamma /in y.
      Proof.
        Take a zfset i such that i /in lambda /\ y = C[i].
        M /subset C[i].
        Then C[i] /cap gamma /cof gamma.
        Then C[i] /club kappa.
        Then gamma /in C[i].
      end.
    end.
  end.
  
  M /cof kappa.
  Proof.
    Let alpha /in kappa.
    Then exists x /in M (alpha /in x).
    Proof.
      Define supset[beta] = {gamma /in kappa | (forall i /in lambda exists j /in C[i] /cap gamma (beta /in j))} for beta in kappa.
      Forall beta /in kappa forall gamma /in supset[beta] beta /in gamma.
      Proof.
        Let beta /in kappa.
        Let gamma /in supset[beta].
        Then gamma /in kappa /\ forall ii /in lambda exists j /in C[ii] /cap gamma (beta /in j).
        Take a zfset i such that i /in lambda.
        Take a zfset j such that j /in C[i] /cap gamma /\ beta /in j.
        Then j /in gamma.
        Then beta /in gamma.
      end.
      Forall beta /in kappa supset[beta] /neq /emptyset.
      Proof.
        Let beta /in kappa.
        beta is an ordinal.
        Forall i /in lambda exists j /in C[i] (j /notin (beta +' 1)).
        Proof.
          Let i /in lambda.
          C[i] /club kappa.
          beta /in kappa.
          Take a zfset j such that (j /in C[i] /\ beta /in j).
          Then j /notin (beta +' 1).
        end.
        Define f[i] = (Choose a zfset j such that (j /in C[i] /setminus (beta +' 1)) in j) for i in lambda.
        f : lambda /rightarrow kappa.
        Proof.
          Let i /in lambda.
          Then f[i] /in C[i].
          Then f[i] /in kappa.
        end.
        Forall i /in lambda beta /in f[i].
        Proof.
          Let i /in lambda.
          f[i] /in C[i] /setminus (beta +' 1).
          f[i], beta /in /Ord.
          f[i] /in beta \/ beta /in f[i] \/ f[i] = beta (by TotalOrder).
          f[i] /notin beta /\ f[i] /neq beta.
          Then beta /in f[i].
        end.
        /bigcup f^[lambda] /in kappa.
        Proof by contradiction. Assume the contrary.
          f^[lambda] /subset kappa.
          /bigcup f^[lambda] /in /Ord.
          Proof.
            f^[lambda] /subset /Ord.
            Then Trans(/bigcup f^[lambda]).
          end.
          Then /bigcup f^[lambda] = kappa.
          Proof.
            Take an ordinal a such that a = /bigcup f^[lambda].
            kappa, a /in /Ord.
            Then a /in kappa \/ kappa /in a \/ a = kappa (by TotalOrder).
            a /notin kappa.
            kappa /notin a.
            Proof by contradiction. Assume the contrary.
              Then kappa /in a.
              Take a zfset b such that b /in f^[lambda] /\ kappa /in b.
              ran(f) /subset kappa.
              Then f^[beta] /subset kappa.
              Contradiction.
            end.
          end.
          Then f^[lambda] /cof kappa.
          Proof.
            Let a /in kappa.
            Then a /in /bigcup f^[lambda].
          end.
          Card(f^[lambda]) /subset Card(lambda).
          Card(lambda) /subset lambda.
          Then Card(f^[lambda]) /subset lambda.
          Card(f^[lambda]) /in cofset2(kappa).
          Then min(cofset2(kappa)) /subset Card(f^[lambda]).
          Then cof(kappa) /subset lambda.
          Contradiction.
        end.
        Let gamma = /bigcup f^[lambda] +' 1.
        Then gamma /in supset[beta].
        Proof.
          gamma /in supset[beta] iff (gamma /in kappa /\ forall i /in lambda exists j /in C[i] /cap gamma (beta /in j)).
          gamma /in kappa.
          Proof.
            kappa /in /Lim.
            Then forall x /in kappa x++ /in kappa (by limit).
            /bigcup f^[lambda] /in kappa.
            Let x = /bigcup f^[lambda].
            Then x ++ /in kappa.
          end.
          Forall i /in lambda exists j /in C[i] /cap gamma (beta /in j).
          Proof.
            Let i /in lambda.
            Then f[i] /in C[i].
            f[i] /in gamma.
            Proof.
              f[i] /in f^[lambda].
              Then f[i] /subset /bigcup f^[lambda].
              Then f[i] /in /bigcup f^[lambda] \/ f[i] = /bigcup f^[lambda].
              Proof.
                Take ordinals a,b such that a = f[i] /\ b = /bigcup f^[lambda].
                Then a /in b \/ b /in a \/ a = b (by TotalOrder).
                a /subset b.
                Then a /in b \/ a = b.
              end.
              Then f[i] /in (/bigcup f^[lambda]) ++.
            end.
            beta /in f[i].
          end.
        end.
      end.
      Define sup[beta] = (Choose a zfset gamma such that gamma /in supset[beta] in gamma) for beta in kappa.
      Forall beta /in kappa beta /in sup[beta].
      Forall beta /in kappa sup[beta] /in kappa.
      Forall beta /in kappa forall i /in lambda exists j /in C[i] /cap sup[beta] (beta /in j).
      sup is a zffunction.
      Proof.
        Let a /in kappa.
        Then sup[a] /in kappa.
        Then sup[a] /in /VV.
      end.
      ran(sup) /subset Dom(sup).
      Proof.
        Let a /in ran(sup).
        Take a zfset b such that b /in kappa /\ a = sup[b].
        Then a /in kappa.
        Then a /in Dom(sup).
      end.    
  
      Define f[n] = (sup ^^ (n+'1)) [alpha] for n in /NN.        
      
      Forall n /in /NN f[n] /in kappa.
      Proof.
        Let n /in /NN.
        f[n] = (sup ^^ (n+'1)) [alpha].
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
          Then m -<- n.
          Then m /neq 0 => (m-- /in /NN /\ f[m] = sup[f[m--]]).
          Then m = 0 \/ f[m] = sup[f[m--]].
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
      Proof.
        x, kappa are ordinals.
        Then x /in kappa \/ kappa /in x \/ x = kappa (by TotalOrder).
        kappa /notin x.
      end.
      x /in kappa.
      Proof by contradiction. Assume the contrary.
        Then x = kappa.
        f^[/NN] /subset kappa.
        f^[/NN] /cof kappa.
        Proof.
          Let a /in kappa.
          Then a /in /bigcup f^[/NN].
        end.
        Card(f^[/NN]) /subset /NN.
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
        f^[/NN] /subset /Ord.
        Then b /in /Ord.
        Then a+'1 /subset b.
        Then a+'1 = b \/ a+'1 /in b.
        Proof.
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
      
      Forall i /in lambda x /in C[i].
      Proof.
        Let i /in lambda.
        C[i] is a zfset.
        Forall n /in /NN exists j /in C[i] (f[n] /in j /\ j /in f[n+'1]).
        Proof.
          Let n /in /NN.
          f[n+'1] = sup[f[n]].
          Then exists j /in C[i] /cap f[n+'1] (f[n] /in j).
        end.
        Define val[n] = (Choose a zfset j such that j /in C[i] /\ (f[n] /in j /\ j /in f[n+'1]) in j) for n in /NN.
        val is a zffunction.
        Proof.
          Let n /in /NN.
          Then val[n] /in /VV.
        end.
        ran(val) /subset /Ord.
        /bigcup val^[/NN] /in /Ord.
        Proof.
          val^[/NN] /subset /Ord.
          Proof.
            Let n /in /NN.
            Then val[n] /in C[i].
            Then val[n] /in /Ord.
          end.
          Then Trans(/bigcup val^[/NN]).
        end.
        /bigcup val^[/NN] /subset x.
        Proof.
          Let a /in /bigcup val^[/NN].
          Take a zfset b such that b /in val^[/NN] /\ a /in b.
          Take a zfset c such that c /in /NN /\ b = val[c].
          val[c] /in f[c+'1].
          Then val[c] /in /bigcup f^[/NN].
          Then val[c] /in x.
          Trans(x).
          Then a /in x.
        end.
        x /subset /bigcup val^[/NN].
        Proof.
          Let a /in x.
          Take a zfset b such that b /in f^[/NN] /\ a /in b.
          Take a zfset c such that c /in /NN /\ b = f[c].
          Then b /in val[c].
          val[c] /in val^[/NN].
          Then b /in /bigcup val^[/NN].
          Trans(/bigcup val^[/NN]).
          Then a /in /bigcup val^[/NN].
        end.
        Then x = /bigcup val^[/NN].
        
        x /in /Lim /cap kappa.
        C[i] /cap x /cof x.
        Proof.
          Let a /in x.
          Take a zfset b such that b /in val^[/NN] /\ a /in b.
          Take a zfset c such that c /in /NN /\ b = val[c].
          Then b /in f[c+'1].
          Then b /in /bigcup f^[/NN].
          Then b /in x.
          b /in C[i].
          Then b /in C[i] /cap x.
        end.
        Then x /in C[i].
      end.
      Then x /in M.
      Proof.
        Forall a /in C^[lambda] x /in a.
        Then x /in /bigcap C^[lambda].
      end.  
    end.  
  end.
qed.


Lemma. Let kappa /in /BigCard. Let C,D /subset kappa. Let C,D /club kappa. Then C /cap D /club kappa.
Proof.
  C,D /in Cl(kappa).
  Define f[i] =
    Case i = 0 -> C,
    Case i = 1 -> D
  for i in 2.
  Then f is a zffunction.
  Proof.
    Let i /in 2.
    Then f[i] /subset kappa.
    Proof.
      i = 0 \/ i = 1.
    end.
    Then f[i] /in /VV.
  end.
  kappa /in /BigCard.
  2 /neq /emptyset.
  2 /in cof(kappa).
  Proof.
    cof(kappa) /in /Lim.
  end.
  f is a sequence of length 2 in Cl(kappa).
  Proof.
    f is a zffunction.
    Dom(f) = 2.
    2 /in /Ord.
    Forall i /in 2 f[i] /in Cl(kappa).
    Proof.
      Let i /in 2.
      Then i = 0 \/ i = 1.
    end.
    Then f is a sequence of length 2 in Cl(kappa) (by sequence).
  end.
  Then /bigcap f^[2] /club kappa (by clubintersection).
  f^[2] = <C,D>.
  Proof.
    Let i /in 2.
    Then i = 0 \/ i = 1.
    Then f[i] /in <C,D>.
  end.
  Then /bigcap f^[2] = C /cap D.
qed.


Definition. Let kappa /in /BigCard. The closed unbounded filter on kappa is
{X /subset kappa | exists C /subset X (C /club kappa)}.
Let Club(k) stand for the closed unbounded filter on k.


Lemma. Let kappa /in /BigCard. Let C /subset kappa. Let C /club kappa. Then C /in Club(kappa).


Lemma. Let kappa /in /BigCard. Then kappa /club kappa.


Lemma. Let kappa /in /BigCard. Then Club(kappa) /in /VV.
Proof.
  Club(kappa) /subset /PP kappa.
qed.


Lemma. Let kappa /in /BigCard. Then Club(kappa) /neq /emptyset /\ Club(kappa) /subset /PP kappa.
Proof.
  kappa /club kappa.
qed.


Lemma. Let kappa /in /BigCard. Then /emptyset /notin Club(kappa).


Lemma ClubSubset. Let kappa /in /BigCard. Let X /in Club(kappa). Let Y /subset kappa. Let X /subset Y. Then Y /in Club(kappa).
Proof.
  Take a zfset C such that C /subset X /\ C /club kappa.
  Then C /subset Y /\ C /club kappa.
  Then Y /in Club(kappa).
qed.


Lemma. Let kappa /in /BigCard. Let X,Y /in Club(kappa). Then X /cap Y /in Club(kappa).
Proof.
  Take a zfset C such that C /subset X /\ C /club kappa.
  Take a zfset D such that D /subset Y /\ D /club kappa.
  C,D /subset kappa.
  Then C /cap D /club kappa.
  C /cap D /subset X /cap Y.
qed.


Lemma. Let kappa /in /BigCard. Let lambda /in cof(kappa). Let lambda /neq /emptyset. Let X be a sequence of length lambda in Club(kappa). Then /bigcap X^[lambda] /in Club(kappa). 
Proof.
  Forall i /in lambda (X[i] is a set).
  Forall i /in lambda exists Ci /subset X[i] (Ci /in Cl(kappa)).
  Proof.
    Let i /in lambda.
    Then X[i] /in Club(kappa).
    Forall Ci /subset X[i] (Ci /subset kappa).
    Take a zfset Ci such that Ci /subset X[i] /\ Ci /club kappa.
    Then Ci /in Cl(kappa).
  end.
  Define C[i] = (Choose a zfset Ci such that Ci /subset X[i] /\ Ci /in Cl(kappa) in Ci) for i in lambda.
  C is a zffunction.
  Proof.
    Let i /in lambda.
    Then C[i] /subset X[i].
    Then C[i] /in /VV.
  end.
  C is a sequence of length lambda in Cl(kappa).
  Proof.
    C is a zffunction.
    lambda /in /Ord.
    Dom(C) = lambda.
    Forall i /in lambda C[i] /in Cl(kappa).
    Then C is a sequence of length lambda in Cl(kappa) (by sequence).
  end.
  (C is a zffunction) /\ /bigcap C^[lambda] /subset kappa /\ /bigcap C^[lambda] /club kappa (by clubintersection).
  /bigcap C^[lambda] /subset /bigcap X^[lambda].
  /bigcap X^[lambda] /subset kappa.
  Proof.
    Take a zfset i such that i /in lambda.
    Then /bigcap X^[lambda] /subset X[i].
    X[i] /in Club(kappa).
    Then X[i] /subset kappa.
  end.
  Then /bigcap X^[lambda] /in Club(kappa). 
qed.




