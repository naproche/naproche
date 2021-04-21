[read Formalizations/Library/L16-Fodors_Lemma.ftl]

## Pretyped Variables

Let w,x,y,z,W,X,Y,Z stand for zfsets.
Let a,b,c,d,A,B,C,D,M stand for sets.
Let o,o1,o2 stand for objects.
Let alpha, beta, gamma stand for ordinals.
Let f,g,h,F,G,H stand for zffunction.
Let kappa, lambda stand for cardinals.





## Prerequisites

Lemma. Let kappa be a successor cardinal. Then kappa /in /BigCard.
Proof.
  cof(kappa) = kappa.
  Take an ordinal alpha such that kappa = Alef[alpha +' 1].
  1 /subset alpha +' 1.
  Then Alef[1] /subset Alef[alpha +' 1].
  Then Alef[1] /subset kappa.
qed.

Definition. Let kappa /in /BigCard. Let S be a set. The set of stationary subsets of kappa in S is
{x /in stat(kappa) | x /subset S}.
Let stat(k,S) stand for the set of stationary subsets of k in S.

Lemma. Let M be a set. Let lambda /in /Ord. Let f be a sequence of length lambda in M. Forall a /in lambda (f[a] is a zfset).

Definition. Let M be a set. Let lambda /in /Ord. Let f be a sequence of length lambda in M. f is pairwise disjoint on lambda in M iff
forall a,b /in lambda (a /neq b => f[a] /cap f[b] = /emptyset).

Signature. Let a,b,c be objects. (a,b,c) is an object.
Axiom. Let a1,a2,b1,b2,c1,c2 be objects. (a1,b1,c1) = (a2,b2,c2) => a1 = a2 /\ b1 = b2 /\ c1 = c2.

Definition. Let lambda be an ordinal. Let M be a set. A sequence of functions on M of length lambda is a zffunction f such that 
Dom(f) = lambda /\ forall i /in lambda ((f[i] is a zffunction) /\ Dom(f[i]) = M).

Signature. A functiontriple is a notion.

Axiom. Let f,lambda,M be objects. (f,lambda,M) is a functiontriple iff M is a set and lambda is an ordinal and f is a sequence of functions on M of length lambda.

Lemma. Let (f,lambda,M) be a functiontriple. Forall v /in lambda ((f is a zffunction) /\ v /in Dom(f) /\ (f[v] is a zffunction)).

Definition. Let (f,lambda,M) be a functiontriple. Let i /in M. Let alpha be a zfset.
The support of f in lambda on M at i over alpha is {v /in lambda | i /in Dom(f[v]) /\ alpha /subset (f[v])[i]}.
Let Supp(f,l,M){i,a} stand for the support of f in l on M at i over a.

Definition. Let (f,lambda,M) be a functiontriple. Let i /in M. Let alpha be a zfset.
The eqsupport of f in lambda on M at i at alpha is {v /in lambda | i /in Dom(f[v]) /\ alpha = (f[v])[i]}.
Let EqSupp(f,l,M){i,a} stand for the eqsupport of f in l on M at i at a.

Lemma. Let x be a zfset. Let M be a set. Then exists f (Dom(f) = M /\ forall i /in M f[i] = x).
Proof.
  Define f[i] = x for i in M.
qed.

Definition. Let x be a zfset. Let M be a set. const(x,M) is a zffunction f such that Dom(f) = M /\ forall i /in M f[i] = x.



## The Theorem


Theorem DisjStat. Let kappa be a successor cardinal. Let S /in stat(kappa). Then exists f (f is a sequence of length kappa in stat(kappa,S) and f is pairwise disjoint on kappa in stat(kappa,S)).
Proof.
  
  # Introduction
  
  Take an ordinal lam such that kappa = Alef[lam +' 1].
  Let lambda = Alef[lam].
  Then kappa = Plus[lambda].
  Proof.
    Alef[lam +' 1] = Plus[Alef[lam]].
  end.
  Forall v /in kappa /setminus <0> exists f (f : lambda /rightarrow v /\ ran(f) = v).
  Proof.
    Let v /in kappa /setminus <0>.
    Then Card(v) /in kappa.
    Then Card(v) /in lambda \/ Card(v) = lambda.
    Proof by contradiction. Assume the contrary.
      Card(v), lambda /in /Ord.
      Then lambda /in Card(v).
      Card(v) /in /Cd.
      Then Card(v) /in PlusCard(lambda).
      Plus[lambda] = min(PlusCard(lambda)).
      Then Plus[lambda] /subset Card(v).
      Contradiction.
    end.
    Then Card(v) /subset lambda.
    Then exists f (f : lambda /rightarrow v /\ ran(f) = v).
  end.
  Define surj[v] = (Choose a zffunction fv such that fv : lambda /rightarrow v /\ ran(fv) = v in fv) for v in kappa /setminus <0>.
  Forall v /in kappa (v /neq 0 => v /in Dom(surj)).
  Define f[v] = 
    Case v /neq 0 -> surj[v],
    Case v = 0 -> const(0,lambda)
  for v in kappa.
  f is a zffunction.
  Proof.
    Let v /in kappa.
    Then f[v] /in /VV.
    Proof.
      Case v = 0. end.
      Case v /neq 0. 
        f[v] = surj[v].
        surj[v] is a zffunction.
        Dom(surj[v]) /in /VV.
        Then surj[v] /in /VV.
      end.
    end.
  end.
  Forall v /in kappa (f[v] is a zffunction and Dom(f[v]) = lambda).
  Proof.
    Let v /in kappa.
    Then f[v] is a zffunction.
    Dom(f[v]) = lambda.
  end.
  Then f is a sequence of functions on lambda of length kappa.
  (f,kappa,lambda) is a functiontriple.
  Forall alpha /in kappa forall i /in lambda (Supp(f,kappa,lambda){i,alpha} /subset kappa).

  # Part 1

  Forall alpha /in kappa exists i /in lambda (Supp(f,kappa,lambda){i,alpha} /cap S /in stat(kappa)).
  Proof by contradiction. Assume the contrary.
    Take an ordinal alpha such that alpha /in kappa /\ forall i /in lambda (Supp(f,kappa,lambda){i,alpha} /cap S /notin stat(kappa)).
    Define NS[i] = Supp(f,kappa,lambda){i,alpha} /cap S for i in lambda.
    Forall i /in lambda exists C /in Cl(kappa) (NS[i] /cap C = /emptyset).
    Proof.
      Let i /in lambda.
      Then NS[i] is nonstationary in kappa.
      Then kappa /setminus NS[i] /in Club(kappa).
      Then exists C /subset (kappa /setminus NS[i]) (C /club kappa).
      Take a zfset C such that C /subset (kappa /setminus NS[i]) /\ C /club kappa.
      Then NS[i] /cap C = /emptyset.
      C /subset kappa.
      Then C /in Cl(kappa).
    end.
    Define C[i] = (Choose a zfset Ci such that Ci /in Cl(kappa) /\ NS[i] /cap Ci = /emptyset in Ci) for i in lambda.
    C is a zffunction.
    Proof.
      Let i /in lambda.
      Then C[i] /in Cl(kappa).
      Then C[i] /in /VV.
    end.
    C is a sequence of length lambda in Cl(kappa).
    Proof.
      Let i /in lambda.
      Then C[i] /in Cl(kappa).
      lambda /in /Ord.
      Then C is a sequence of length lambda in Cl(kappa) (by sequence).
    end.
    kappa /in /BigCard.
    lambda /in cof(kappa).
    lambda /neq /emptyset.
    Then /bigcap C^[lambda] /subset kappa /\ /bigcap C^[lambda] /club kappa (by clubintersection).
    alpha ++ /in kappa.
    Then /bigcap C^[lambda] /setminus (alpha +' 1) /in Cl(kappa).
    Then /bigcap C^[lambda] /setminus (alpha +' 1) /club kappa.
    
    S /subset kappa.
    S is stationary in kappa.
    Then S /cap (/bigcap C^[lambda] /setminus (alpha +' 1)) /neq /emptyset.
    Proof.
      kappa /in /BigCard. 
      S /subset kappa. 
      S is stationary in kappa iff (forall Cl /subset kappa (Cl /club kappa => S /cap Cl /neq /emptyset)) (by stationary).
      S is stationary in kappa.
      /bigcap C^[lambda] /setminus (alpha +' 1) /subset kappa.
      /bigcap C^[lambda] /setminus (alpha +' 1) /club kappa.
      Then S /cap (/bigcap C^[lambda] /setminus (alpha +' 1)) /neq /emptyset.
    end.
    
    Take a zfset v such that v /in S /cap (/bigcap C^[lambda] /setminus (alpha +' 1)).
    Then alpha /in v.
    
    Forall i /in lambda v /notin NS[i].
    Proof.
      Let i /in lambda.
      Then C[i] /in C^[lambda].
      Then /bigcap C^[lambda] /subset C[i].
      v /in /bigcap C^[lambda].
      Then v /in C[i].
      C[i] /cap NS[i] = /emptyset.
      Then v /notin NS[i].
    end.
    Then forall i /in lambda (f[v])[i] /in alpha.
    Proof.
      Let i /in lambda.
      Then v /notin NS[i].
      Then v /notin Supp(f,kappa,lambda){i,alpha} /cap S.
      v /in S.
      Then v /notin Supp(f,kappa,lambda){i,alpha}.
      Then (f[v])[i] /in alpha.
      Proof by contradiction. Assume the contrary.
        (f[v])[i], alpha /in /Ord.
        Proof.
          v /neq 0.
          Then f[v] = surj[v].
          ran(surj[v]) = v.
          Then (f[v])[i] /in v.
        end.
        Then alpha /subset (f[v])[i].
        Then v /in Supp(f,kappa,lambda){i,alpha}.
        Contradiction.
      end.
    end.
    ran(f[v]) = v.
    Proof.
      v /neq 0.
      Then f[v] = surj[v].
      ran(surj[v]) = v.
    end.
    alpha /notin ran(f[v]).
    Proof.
      Dom(f[v]) = lambda.
      Forall i /in lambda (f[v])[i] /in alpha.
      Then forall i /in lambda (f[v])[i] /neq alpha.
    end.
    Contradiction.
  end.
  
  # Part 2
  
  Exists i /in lambda forall alpha /in kappa (Supp(f,kappa,lambda){i,alpha} /cap S /in stat(kappa)).
  Proof.
    Define i[alpha] = (Choose a zfset ia such that ia /in lambda /\ Supp(f,kappa,lambda){ia,alpha} /cap S /in stat(kappa) in ia) for alpha in kappa.
    i : kappa /rightarrow lambda.
    Proof.
      Let alpha /in kappa.
      Then i[alpha] /in lambda.
    end.
    Forall j /in lambda i^{-1}[[j]] /subset kappa.
    Exists j /in lambda Card(i^{-1}[[j]]) = kappa.
    Proof by contradiction. Assume the contrary.
      Then forall j /in lambda Card(i^{-1}[[j]]) /in kappa.
      Proof.
        Let j /in lambda.
        i^{-1}[[j]] /subset kappa.
        Then Card(i^{-1}[[j]]) /subset kappa.
        Card(i^{-1}[[j]]) /neq kappa.
      end.
      Then forall j /in lambda Card(i^{-1}[[j]]) /subset lambda.
      Proof.
        Let j /in lambda.
        Card(i^{-1}[[j]]) /in kappa.
        Then Card(i^{-1}[[j]]) /in lambda \/ Card(i^{-1}[[j]]) = lambda.
        Proof by contradiction. Assume the contrary.
          Card(i^{-1}[[j]]), lambda are ordinals.
          Then Card(i^{-1}[[j]]) /in lambda \/ Card(i^{-1}[[j]]) = lambda \/ lambda /in Card(i^{-1}[[j]]) (by TotalOrder).
          Then lambda /in Card(i^{-1}[[j]]).
          Card(i^{-1}[[j]]) /in /Cd.
          Then Card(i^{-1}[[j]]) /in PlusCard(lambda).
          Plus[lambda] = min(PlusCard(lambda)).
          Then Plus[lambda] /subset Card(i^{-1}[[j]]).
          Contradiction.
        end.
      end.
      Forall j /in lambda (i^{-1}[[j]] is a zfset).
      Define pre[j] = i^{-1}[[j]] for j in lambda.
      pre is a zffunction.
      Proof.
        Let j /in lambda. 
        pre[j] is a zfset.
      end.
      Let seq = cardseq(pre).
      Forall j /in lambda seq[j] /subset lambda.
      /sumset seq /subset lambda /times lambda.
      lambda /times lambda /tilde lambda.
      Then /sumset seq <= lambda.
      Card(/sumset pre) = kappa.
      Proof.
        Define F[alpha] = (alpha,i[alpha]) for alpha in kappa.
        F : kappa /rightarrow /sumset pre.
        Proof.
          Let alpha /in kappa.
          i[alpha] /in lambda.
          Take a zfset j such that j /in lambda /\ j = i[alpha].
          Then alpha /in pre[j].
          Then (alpha,j) /in /sumset pre.
          Then F[alpha] /in /sumset pre.
        end.
        F is injective.
        ran(F) = /sumset pre.
        Proof.
          Let pair /in /sumset pre.
          Take objects a,b such that b /in Dom(pre) /\ a /in pre[b] /\ pair = (a,b).
          pre[b] is a zfset.
          a,b are zfsets.
          a /in i^{-1}[[b]].
          Then i[a] = b.
          Then F[a] = (a,b).
          Then pair /in ran(F).
        end.
        Then F : kappa /leftrightarrow /sumset pre.
      end.
      Contradiction.
    end.
    Take a zfset j such that j /in lambda /\ Card(i^{-1}[[j]]) = kappa.
    Let Z = i^{-1}[[j]].
    Forall alpha /in Z i[alpha] = j.
    Forall alpha /in Z Supp(f,kappa,lambda){j,alpha} /cap S /in stat(kappa).
    Proof.
      Let alpha /in Z.
      i[alpha] = j.
      Supp(f,kappa,lambda){i[alpha],alpha} /cap S /in stat(kappa).
    end.
    Then forall alpha /in kappa Supp(f,kappa,lambda){j,alpha} /cap S /in stat(kappa).
    Proof.
      Let alpha /in kappa.
      Then exists beta /in Z (alpha /in beta).
      Proof by contradiction. Assume the contrary.
        Then forall beta /in Z (beta /in alpha \/ beta = alpha).
        Then Z /subset alpha ++.
        alpha ++ /in kappa.
        Card(alpha ++) /in kappa.
        Card(Z) /subset Card(alpha ++).
        Then Card(Z) /in kappa.
        Contradiction.
      end.
      Take a zfset beta such that beta /in Z /\ alpha /in beta.
      Supp(f,kappa,lambda){j,beta} /subset Supp(f,kappa,lambda){j,alpha}.
      Then Supp(f,kappa,lambda){j,beta} /cap S /subset Supp(f,kappa,lambda){j,alpha} /cap S.
      Supp(f,kappa,lambda){j,beta} /cap S /in stat(kappa).
      Then Supp(f,kappa,lambda){j,alpha} /cap S /in stat(kappa).
    end.
  end.
  Take a zfset i such that i /in lambda /\ forall alpha /in kappa (Supp(f,kappa,lambda){i,alpha} /cap S /in stat(kappa)).
  
  # Part 3
 
  Define SubS[beta] = EqSupp(f,kappa,lambda){i,beta} /cap S for beta in kappa.
  
  Forall alpha /in kappa exists beta /in kappa (alpha /subset beta /\ SubS[beta] /in stat(kappa)).
  Proof by contradiction. Assume the contrary.
    Take an ordinal alpha such that alpha /in kappa /\ forall beta /in kappa (SubS[beta] /in stat(kappa) => not (alpha /subset beta)).
    Then forall beta /in kappa (SubS[beta] /in stat(kappa) => beta /in alpha).
    Supp(f,kappa,lambda){i,alpha} /cap S /in stat(kappa).
    Let T = Supp(f,kappa,lambda){i,alpha} /cap S.
    Forall v /in S v /in kappa.
    Define reg[v] = (f[v])[i] for v in T.
    reg is a zffunction.
    Proof.
      Let v /in T.
      Then reg[v] /in /VV.
    end.
    Dom(reg) /subset /Ord.
    reg is regressive.
    Proof.
      Let beta /in Dom(reg) /setminus <0>.
      f[beta] = surj[beta].
      surj[beta] : lambda /rightarrow beta.
      Then (f[beta])[i] /in beta.
      Then reg[beta] /in beta.
    end.
    kappa /in /BigCard.
    Dom(reg) /in stat(kappa).
    Then exists j /in /Ord reg^{-1}[[j]] /in stat(kappa).
    Take a zfset beta such that beta /in /Ord /\ reg^{-1}[[beta]] /in stat(kappa).
    Let U = reg^{-1}[[beta]].
    U /in stat(kappa).
    /emptyset is nonstationary in kappa.
    Then U /neq /emptyset.
    Take a zfset v such that v /in U.
    Then reg[v] = beta.
    beta /in kappa.
    Proof.
      beta = reg[v].
      beta = (f[v])[i].
      Case v = 0.
        Then f[v] = const(0,lambda).
        Then beta = 0.
      end.
      Case v /neq 0.
        Then f[v] = surj[v].
        Then (f[v])[i] /in v.
        Then beta /in v.
      end.
    end.
    Forall vv /in U (f[vv])[i] = beta.
    Then U /subset EqSupp(f,kappa,lambda){i,beta}.
    U /subset S.
    Then U /subset EqSupp(f,kappa,lambda){i,beta} /cap S.
    U /in stat(kappa).
    Then EqSupp(f,kappa,lambda){i,beta} /cap S /in stat(kappa).
    SubS[beta] = EqSupp(f,kappa,lambda){i,beta} /cap S.
    Then SubS[beta] /in stat(kappa).
    alpha /subset beta.
    Proof.
      beta = (f[v])[i].
      v /in T.
      Then v /in Supp(f,kappa,lambda){i,alpha}.
      Then alpha /subset (f[v])[i].
    end.
    Contradiction.
  end.

  # Ending
  
  Define Z = {beta /in kappa | SubS[beta] /in stat(kappa)}.
  Then Z /subset kappa.
  Z /cof kappa.
  Then Card(Z) /in cofset2(kappa).
  Then min(cofset2(kappa)) /subset Card(Z).
  Then cof(kappa) /subset Card(Z).
  Then Card(Z) = kappa.

  Take a zffunction bij such that bij : kappa /leftrightarrow Z.
  
  Define StatSubS[beta] = SubS[bij[beta]] for beta in kappa.
  StatSubS is a zffunction.
  Proof.
    Let beta /in kappa.
    Then SubS[bij[beta]] /in /VV.
    Then StatSubS[beta] /in /VV.
  end.
  StatSubS is a sequence of length kappa in stat(kappa,S).
  Proof.
    stat(kappa,S) is a set.
    kappa /in /Ord.
    StatSubS is a zffunction.
    Dom(StatSubS) = kappa /\ forall beta /in kappa StatSubS[beta] /in stat(kappa,S).
    Proof.
      Let beta /in kappa.
      Then StatSubS[beta] /in stat(kappa).
      StatSubS[beta] /subset S.
      Then StatSubS[beta] /in stat(kappa,S).
    end.
    Then StatSubS is a sequence of length kappa in stat(kappa,S) (by sequence).
  end.
  
  StatSubS is pairwise disjoint on kappa in stat(kappa,S).
  Proof.
    Let a, b /in kappa.
    Let a /neq b.
    Then StatSubS[a] /cap StatSubS[b] = /emptyset.
    Proof.
      Let aa = bij[a].
      Let bb = bij[b].
      Then aa /neq bb.
      Then SubS[aa] /cap SubS[bb] = /emptyset.
    end.
  end.    
qed.





