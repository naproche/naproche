[read Formalizations/Library/L02-Cardinals_Part_1.ftl]

## Pretyped Variables

Let w,x,y,z,W,X,Y,Z stand for zfsets.
Let a,b,c,d,A,B,C,D,M stand for sets.
Let o,o1,o2 stand for objects.
Let alpha, beta, gamma, delta stand for ordinals.
Let k,l,m,n stand for natural numbers.
Let f,g,h,F,G,H stand for zffunction.


## Von Neumann Hierarchy

Signature. V is a function.
Axiom. Dom(V) = /Ord.
Axiom. V[0] = /emptyset.
Axiom. Forall alpha /in /Ord (V[alpha] is a set).

Axiom. Let alpha /in /Ord. Then V[alpha ++] = {zfset x | x /subset V[alpha]}.
Axiom. Let lambda be an ordinal. Let lambda /in /Lim. Then V[lambda] = /bigcup V /caret [lambda].

Lemma. V is a zffunction.
Proof.
  Forall alpha /in /Ord V[alpha] /in /VV.
  Proof by induction.
    Let alpha /in /Ord.
    Then V[alpha] /in /VV.
    Proof.
      Case alpha /in /Succ.
        Let beta = alpha --.
        Then V[alpha] = /PP V[beta].
      end.
      Case alpha /in /Lim.
        Define VV[beta] = V[beta] for beta in alpha.
        Then VV is a zffunction.
        V[alpha] /subset /bigcup VV^[alpha].
        Proof.
          V[alpha] = /bigcup V /caret [alpha].
          Let x /in V[alpha].
          Take an ordinal beta such that beta /in alpha /\ x /in V[beta].
          Then x /in VV[beta].
          Then x /in /bigcup VV^[alpha].
        end.
        Then V[alpha] /in /VV.
      end.
      Case alpha = 0.
      end.
    end.
  end. 
qed.

Lemma. Let alpha /in /Ord. Then V[alpha] is a zfset and V[alpha ++] = /PP V[alpha].

Lemma. Let lambda /in /Lim. Then V[lambda] = /bigcup V^[lambda].
Proof.
  V /caret [lambda] = V^[lambda].
  V[lambda] = /bigcup V /caret [lambda].
qed.

Lemma. Forall alpha (forall beta /in alpha (V[beta] /in V[alpha] /\ V[beta] /subset V[alpha] /\ Trans(V[alpha]))).
Proof by induction.
  Let alpha be an ordinal.
  Forall gamma /in alpha (forall beta /in gamma (V[beta] /in V[gamma] /\ V[beta] /subset V[gamma] /\ Trans(V[gamma]))).

  Then forall beta /in alpha (V[beta] /in V[alpha]).
  Proof.
    Case alpha /in /Succ. Let gamma = alpha--.
      Let beta /in alpha. Then beta = gamma \/ beta /in gamma.
      Then V[beta] = V[gamma] \/ V[beta] /subset V[gamma].
      V[alpha] = /PP V[gamma].
      Then V[beta] /in V[alpha].
    end.
    Case alpha /in /Lim. Let beta /in alpha.
      V[alpha] = /bigcup V^[alpha].
      V[beta] /in V[beta++].
      beta++ /in alpha.
      Proof. 
        beta++ /subset alpha. 
        beta++ /neq alpha. 
        beta++ is an ordinal. 
        alpha is an ordinal. 
      end.
      Then V[beta ++] /in V^[alpha].
      Then V[beta ++] /subset V[alpha].
      Then V[beta] /in V[alpha].
    end.
    Case alpha = /emptyset.
    end.
  end.
 
  Forall beta /in alpha (V[beta] /subset V[alpha]).
  Proof.
    Case alpha /in /Succ. Let gamma = alpha--.
      Let beta /in alpha. Then beta = gamma \/ beta /in gamma.
      Then V[beta] /subset V[gamma].
      Then V[beta] /subset V[alpha].
      Proof.
        Let w /in V[beta]. Then w /in V[gamma]. Then w /subset V[gamma].
        Then w /in V[alpha].
      end.
    end.
    Case alpha /in /Lim. 
      Let beta /in alpha. 
      Then V[beta] /in V^[alpha].
      V[alpha] = /bigcup V^[alpha].
      Then V[beta] /subset V[alpha].
    end.
    Case alpha = /emptyset.
    end.
  end.

  Forall w /in V[alpha] (w /subset V[alpha]).
  Proof.
    Case alpha = /emptyset.
    end.
    Case alpha /in /Lim. V[alpha] = /bigcup V^[alpha].
      Let w /in V[alpha]. 
      Take a zfset x such that x /in V^[alpha] /\ w /in x.
      Take an ordinal gamma such that gamma /in alpha /\ x = V[gamma].
      Then w /in V[gamma].
      V[gamma] is transitive.
      Then w /subset V[gamma].
      V[gamma] /subset V[alpha].
      Then w /subset V[alpha].
    end.
    Case alpha /in /Succ. Let gamma = alpha--.
      Let w /in V[alpha]. 
      Then w /subset V[gamma].
      V[gamma] /subset V[alpha].
      Then w /subset V[alpha].
    end.
  end.
  Then Trans(V[alpha]).
qed.


Lemma. Forall alpha /in /Ord V[alpha] /cap /Ord = alpha.
Proof by induction.
  Let alpha /in /Ord.
  Trans(V[alpha]).
  Then Trans(V[alpha] /cap /Ord).
  V[alpha] /in /VV.
  Then V[alpha] /cap /Ord /in /VV.
  Proof.
    V[alpha] /cap /Ord /subset V[alpha].
  end.
  Then (V[alpha] /cap /Ord) /in /Ord.
  Let delta = V[alpha] /cap /Ord.
  Then alpha = delta.
  Proof.
    Case alpha /in /Succ.
      Let beta = alpha --.
      Then V[beta] /cap /Ord = beta.
      beta /in V[alpha].
      Then beta /in delta.
      Then beta ++ /subset delta.
      Then alpha = delta.
      Proof by contradiction.
        Assume the contrary. Then alpha /neq delta.
        Then alpha /in delta.
        Then alpha /subset V[beta].
        Contradiction.
      end.
    end.
    Case alpha /in /Lim.
      V[alpha] = /bigcup V^[alpha].
      Forall beta /in alpha (beta = V[beta] /cap /Ord).
      Forall beta /in alpha (beta ++ /in alpha).
      Forall beta /in alpha (beta /in V[beta++]).
      Then alpha /subset V[alpha].
      Proof.
        Let beta /in alpha.
        Then beta /in V[beta ++].
        V[beta ++] /in V^[alpha].
        Then beta /in V[alpha].
      end.
      Then alpha /subset delta.
      Then alpha = delta.
      Proof by contradiction. Assume the contrary.
        Then alpha /neq delta.
        Then alpha /in delta.
        Then exists gamma /in alpha (alpha /in V[gamma]).
        Contradiction.
      end.      
    end.
    Case alpha = 0.
    end.
  end.
qed.


Lemma. Forall x /in /VV (x /subset /bigcup ran(V) => exists beta x /subset V[beta]).
Proof.
  Let x /subset /bigcup ran(V). Let x /in /VV.
  Define f[y] = choose an ordinal gamma such that y /in V[gamma] in gamma for y in x.
  Define g[y] = f[y] ++ for y in x.
  Then f,g are zffunctions.
  Let a = /bigcup g^[x].
  Then a is an ordinal.
  Proof.
    g^[x] /subset /Ord.
    g^[x] is a zfset.
    Then /bigcup g^[x] is an ordinal.
  end.
  x /subset V[a].
  Proof.
    Let y /in x. 
    Then y /in V[f[y]]. 
    f[y] /in g[y]. 
    Then f[y] /in /bigcup g^[x]. 
    Then f[y] /in a.
    Then V[f[y]] /subset V[a].
    Then y /in V[a].
  end.
qed.


Lemma. /VV = /bigcup ran(V).
Proof by contradiction. Assume the contrary.
  Let A = /bigcup ran(V). Let B = /VV /setminus A.
  Then B /neq /emptyset.
  Take a zfset x such that (x /in B /\ forall y /in x y /notin B).
  Then x /subset /bigcup ran(V).
  Take an ordinal beta such that x /subset V[beta].
  Then x /in V[beta ++].  
  V[beta ++] /in ran(V).
  Then x /in /bigcup ran(V).
  Then x /in A.
  Contradiction.
qed.


## Rank Function

Lemma. Forall x exists alpha (x /in V[alpha ++] /setminus V[alpha]).
Proof.
  Let x /in /VV.
  Define M = {ordinal beta | x /in V[beta]}.
  M /subset /Ord.
  M /neq /emptyset.
  Proof.
    /VV = /bigcup ran(V).
    x /in /VV.
    Take a zfset y such that y /in ran(V) /\ x /in y.
    Take an ordinal beta such that y = V[beta].
    Then beta /in M.
  end.
  Let beta = min(M).
  Then beta /in /Succ.
  Proof by contradiction. Assume the contrary.
    beta /neq 0.
    Then beta /in /Lim.
    beta /in M. 
    Then x /in V[beta].
    V[beta] = /bigcup V^[beta].
    Take a zfset y such that y /in V^[beta] /\ x /in y.
    Take an ordinal gamma such that gamma /in beta /\ y = V[gamma].
    Then x /in V[gamma].
    Then gamma /in M.
    Contradiction.
  end.
  Let alpha = beta --.
  alpha is an ordinal.
  Then x /in V[alpha ++].
  x /notin V[alpha].
  Then x /in V[alpha ++] /setminus V[alpha].
qed.

Lemma. Exists f (Dom(f) = /VV and forall x /in /VV (f[x] /in /Ord /\ x /in V[f[x]++] /setminus V[f[x]])).
Proof.
  Define f[x] = (Choose an ordinal alpha such that x /in V[alpha ++] /setminus V[alpha] in alpha) for x in /VV.
  f is a zffunction.
  Forall x /in /VV (f[x] /in /Ord /\ x /in V[f[x]++] /setminus V[f[x]]).
qed.


Signature. rk is a function.
Signature. rk+ is a function.

Axiom. rk : /VV /rightarrow /Ord.
Axiom. rk+ : /VV /rightarrow /Ord.

Lemma. rk, rk+ are zffunctions.
Lemma. Let x /in /VV. Then rk[x] /in /Ord.
Axiom. Let x /in /VV. Then x /in V[rk[x]++] /setminus V[rk[x]].

Lemma rank. Let x /in /VV. Let alpha /in /Ord. Let x /in V[alpha ++] /setminus V[alpha]. Then rk[x] = alpha.
Proof.
  x /in V[rk[x]++] /setminus V[rk[x]].
  Then x /notin V[rk[x]].
  alpha, rk[x] /in /Ord.
  Then alpha /in rk[x] \/ rk[x] /in alpha \/ rk[x] = alpha (by TotalOrder).
  Case rk[x] = alpha.
  end.
  Case alpha /in rk[x].
    Then alpha ++ /subset rk[x].
    Then V[alpha ++] /subset V[rk[x]].
    x /in V[alpha ++].
    Then x /in V[rk[x]].
    Contradiction.
  end.
  Case rk[x] /in alpha.
    Then rk[x]++ /subset alpha.
    Then V[rk[x]++] /subset V[alpha].
    x /in V[rk[x]++].
    Then x /in V[alpha].
    Contradiction.
  end.
qed.

Lemma. Exists f (Dom(f) = /VV and forall x /in /VV (f[x] /in /Ord /\ f[x] = rk[x] ++)).
Proof.
  Define f[x] = rk[x] ++ for x in /VV.
qed.
Axiom. Forall x /in /VV rk+[x] = rk[x] ++.

Lemma. Let x /in /VV. Let rk[x] = alpha. Then x /notin V[alpha]. 

Lemma. Let x /in y. Then rk[x] /in rk[y].
Proof. Take ordinals alpha, beta such that alpha = rk[x] /\ beta = rk[y].
  Then y /in V[beta ++].
  Then y /subset V[beta].
  Then x /in V[beta].
  Then rk[x] /neq beta.
  Then alpha /neq beta.
  Then alpha /in beta \/ beta /in alpha.
  Case beta /in alpha. 
    Then V[beta] /subset V[alpha]. 
    Contradiction.
  end.
  Then alpha /in beta.
qed.


Lemma. Forall x /in /VV (rk[x] = /bigcup rk+^[x]).
Proof.
  Forall alpha /in /Ord forall x /in V[alpha] (rk[x] = /bigcup rk+^[x]).
  Proof by induction.
    Let alpha /in /Ord.
    Then forall x /in V[alpha] (rk[x] = /bigcup rk+^[x]).
    Proof.
      Case alpha /in /Succ.
        Let beta = alpha --.
        Let x /in V[alpha].
        Case x /in V[beta].
        end.
        Case x /notin V[beta].
          x /in V[beta ++] /setminus V[beta].
          Then rk[x] = beta.
          Proof.
            Forall a /in /VV forall b /in /Ord (rk[a] = b iff a /in V[b ++] /setminus V[b]).
            x /in /VV.
            beta /in /Ord.
            x /in V[beta ++] /setminus V[beta]. 
            Then rk[x] = beta (by rank).
          end.
          Then /bigcup rk+^[x] /subset beta.
          Proof.
            Let z /in /bigcup rk+^[x]. 
            Take a zfset y such that (y /in x /\ z /in rk+[y]).
            Take an ordinal gamma such that gamma = rk[y].
            Then rk[y] /in rk[x].
            Then gamma /in beta.
            Then z /in beta.
          end.
          Let delta = /bigcup rk+^[x].
          Then Trans(delta).
          Proof.
            rk+^[x] /subset /Ord.
            Then Trans(/bigcup rk+^[x]).
          end.
          Then delta /in /Ord.
          Then delta /in beta \/ delta = beta.
          Assume delta /in beta.
            x /subset V[delta].
            Proof.
              Let y /in x. 
              Then rk+[y] /subset delta.
              Proof. rk+[y] /subset /bigcup rk+^[x].
              end.
              y /in V[rk+[y]].
              Proof. y /in /VV. 
                Take an ordinal gamma such that gamma = rk[y].
                Then y /in V[gamma ++].
              end.
              Then y /in V[delta].
              Proof. rk+[y] /in delta \/ rk+[y] = delta.
                Case rk+[y] /in delta.
                  Then V[rk+[y]] /subset V[delta].
                end.
              end.
            end.
          Then x /in V[delta ++].
          Then x /in V[beta].
          Proof. delta /in beta. Then delta ++ /subset beta.
            Take an ordinal delta1 such that delta1 = delta ++.
            Forall m,n /in /Ord (m /in n \/ n /in m \/ n = m).
            delta1, beta /in /Ord.
            Then delta1 = beta \/ delta1 /in beta \/ beta /in delta1.
            beta /notin delta1.
            Then delta ++ = beta \/ delta ++ /in beta.
            Case delta ++ = beta. 
            end.
            Case delta ++ /in beta. 
              Then V[delta ++] /subset V[beta]. 
            end.
          qed.
          Contradiction.
          Then delta = beta.
        end.
      end.
      Case alpha /in /Lim.
        V[alpha] = /bigcup V^[alpha].
        Let x /in V[alpha]. 
        Take a zfset y such that y /in V^[alpha] /\ x /in y.
        Take an ordinal beta such that beta /in alpha /\ y = V[beta].
        Then (rk[x] = /bigcup rk+^[x]).
      end.
      Case alpha = 0.
      end.
    end.
  end.
  Let x /in /VV.
  /VV = /bigcup ran(V).
  Take a zfset y such that y /in ran(V) /\ x /in y.
  Take an ordinal alpha such that y = V[alpha].
  Then x /in V[alpha].
  Then rk[x] = /bigcup rk+^[x].
qed.





