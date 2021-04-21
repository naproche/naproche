[read Formalizations/Library/L03-Von_Neumann_Hierarchy.ftl]

## Pretyped Variables

Let w,x,y,z,W,X,Y,Z stand for zfsets.
Let a,b,c,d,A,B,C,D,M stand for sets.
Let o,o1,o2 stand for objects.
Let alpha, beta, gamma, delta stand for ordinals.
Let k,l,m,n stand for natural numbers.
Let f,g,h,F,G,H stand for zffunction.
Let kappa, lambda stand for cardinals.


## Ordinal Arithmetic

Signature. alpha +' beta is an ordinal.
Signature. alpha *' beta is an ordinal.
Signature. alpha ^' beta is an ordinal.


## Addition

Axiom. Let alpha be an ordinal. Then alpha +' 0 = alpha.
Axiom. Let alpha, beta be ordinals. Let beta /in /Succ. Then alpha +'beta = (alpha +' beta--) ++.
Lemma. Let alpha, beta be ordinals. Then alpha +' (beta ++) = (alpha +' beta) +' 1.
Proof.
  (beta ++) -- = beta.
qed.
Axiom AddLim. Let alpha, beta be ordinals. Let beta /in /Lim. Then alpha +' beta = {zfset x | exists gamma /in beta (x /in (alpha +' gamma))}.

Lemma. Forall alpha (alpha +' 1 = alpha ++).

Lemma. Forall alpha ((alpha +' 1) -- = alpha).

Lemma. Forall alpha /in /Ord (0 +' alpha = alpha).
Proof by induction.
  Let alpha /in /Ord.
  Then 0 +' alpha = alpha.
  Proof.
    Case alpha /in /Succ.
      Let beta = alpha --.
      Then 0 +' alpha = (0 +' beta) +' 1.
      beta /in /Ord.
      beta -<- alpha.
      Then 0 +' beta = beta.
      Then 0 +' alpha = beta +' 1.
    end.
    Case alpha /in /Lim.
      0 is an ordinal.
      Then 0 +' alpha = {zfset x | exists beta /in alpha (x /in (0 +' beta))} (by AddLim).
      alpha /subset 0 +' alpha.
      Proof.
        Let x /in alpha.
        Then x +' 1 /in alpha.
        Then 0 +' (x+'1) = x+'1.
        Then x /in 0 +' (x+'1).
        Then x /in 0 +' alpha.
      end.
      0 +' alpha /subset alpha.
      Proof.
        Let x /in 0 +' alpha.
        Take an ordinal beta such that beta /in alpha /\ x /in (0 +' beta).
        Then x /in beta.
        Then x /in alpha.
      end.
      Case alpha = 0.
      end.      
    end.
  end.
qed.

Lemma Add1. Forall alpha, beta, gamma /in /Ord (beta /in gamma => alpha +' beta /in alpha +' gamma).
Proof.
  Let alpha /in /Ord.
  Forall gamma /in /Ord (forall beta /in gamma (alpha +' beta /in alpha +' gamma)).
  Proof by induction.
    Let gamma /in /Ord.
    Then forall beta /in gamma (alpha +' beta /in alpha +' gamma).
    Proof.
      Case gamma /in /Succ.
        Take an ordinal delta such that gamma = delta +' 1.
        Then alpha +' gamma = (alpha +' delta) +' 1.
        Let beta /in delta.
        Then beta = delta \/ beta /in delta.
        Case beta = delta. Then alpha +' beta /in alpha +' gamma. end.
        Case beta /in delta.
          delta /in gamma.
          Then alpha +' beta /in alpha +' delta. 
          Then alpha +' beta /in alpha +' gamma. 
        end.
      end.
      Case gamma /in /Lim.
        Then alpha +' gamma = {zfset x | exists delta /in gamma (x /in alpha +' delta)} (by AddLim).
        Let beta /in gamma.
        gamma is a limit ordinal.
        Then forall x /in gamma (x++ /in gamma) (by limit).
        Then beta +' 1 /in gamma.
        alpha +' (beta +' 1) = (alpha +' beta) +' 1.
        Then alpha +' beta /in alpha +' (beta +' 1).
        Then alpha +' beta /in alpha +' gamma.
      end.
      Case gamma = 0.
      end.
    end.
  end.
qed.


Lemma. Forall alpha, beta /in /Ord (alpha /subset alpha+'beta).
Proof.
  Let alpha /in /Ord.
  Then forall beta /in /Ord alpha /subset alpha +' beta.
  Proof by induction.
    Let beta /in /Ord.
    Case beta = 0. end.
    Case beta /in /Succ.
      Let gamma = beta--.
      alpha /subset alpha +' gamma.
      alpha +' beta = (alpha +' gamma)++.
    end.
    Case beta /in /Lim.
      alpha /in alpha +' beta.
      Proof.
        alpha +' 0 /in alpha +' 1.
      end.
    end.
  end.
qed.


Lemma. Forall alpha, beta /in /Ord (beta /subset alpha +' beta).
Proof.
  Let alpha /in /Ord.
  Then forall beta /in /Ord (beta /subset alpha +' beta).
  Proof by induction.
    Let beta /in /Ord.
    Then beta /subset alpha +' beta.
    Proof.
      Case beta /in /Succ.
        Take an ordinal gamma such that beta = gamma +' 1.
        Then alpha +' beta = (alpha +' gamma) +' 1.
        gamma /subset alpha +' gamma.
        Then gamma = alpha +' gamma \/ gamma /in alpha +' gamma.
        Then gamma /in (alpha +' gamma) ++.
        Then gamma /in alpha +' beta.
        Then beta /subset alpha +' beta.
      end.
      Case beta /in /Lim.
        Then alpha +' beta = {zfset x | exists gamma /in beta (x /in (alpha +' gamma))} (by AddLim).
        Let x /in beta.
        Then x /subset alpha +' x.
        x +' 1 /in beta.
        x /in (alpha +' x) +' 1.
        Then alpha +' (x+'1) = (alpha +' x) +' 1.
        Then x /in alpha +' (x+'1).
        Then x /in alpha +' beta.
      end.
      Case beta = 0.
      end.
    end.
  end.
qed.


Lemma. Let alpha, beta be ordinals. Let beta /in /Lim. Then alpha +' beta /in /Lim.
Proof by contradiction. Assume the contrary.  Then alpha +' beta = /emptyset \/ alpha +' beta /in /Succ.
  alpha +' beta /neq /emptyset.
  Proof. alpha /in alpha +' 1. 1 /in beta. end.
  Then alpha +' beta /in /Succ.
  beta /in /Lim.
  Then forall x /in beta (x+'1 /in beta).
  Let gamma = (alpha +' beta) --.
  Then gamma /in alpha +' beta.
  alpha +' beta = {zfset x | exists n /in beta (x /in alpha +' n)}.
  Take an ordinal n such that n /in beta /\ gamma /in alpha +' n.
  Then gamma +' 1 /in alpha +' (n +' 1).
  Proof. alpha +' (n+'1) = (alpha +' n) +' 1.
    gamma /in alpha +' n.
    gamma /subset alpha +' n.
    Then gamma ++ /subset alpha +' n.
    Then gamma +' 1 /in (alpha +' n) +' 1.    
  end.
  alpha +' beta = {zfset x | exists i /in beta (x /in (alpha +' i))}.
  n /in beta.
  Then n +' 1 /in beta.
  Then gamma +' 1 /in alpha +' beta.
  Contradiction.
qed.



## Multiplication

Axiom. Let alpha be an ordinal. Then alpha *' 0 = 0.
Axiom. Let alpha, beta be ordinals. Let beta /in /Succ. Then alpha *' beta = (alpha *' beta--) +' alpha.
Lemma. Let alpha, beta be ordinals. Then alpha *' (beta +' 1) = (alpha *' beta) +' alpha.
Proof.
  beta +' 1 /in /Succ.
  (beta +' 1) -- = beta.
qed.
Axiom MultLim. Let alpha, beta be ordinals. Let beta /in /Lim. Then alpha *' beta = {zfset x | exists gamma /in beta (x /in alpha *' gamma)}.

Lemma. Forall alpha /in /Ord (alpha *' 1 = alpha).
Proof.
  Let alpha /in /Ord.
  1 = 0+'1.
  Then alpha *' 1 = (alpha *' 0) +' alpha.
  Then alpha *' 1 = alpha.
qed.


Lemma. Forall alpha /in /Ord (0 *' alpha = 0).
Proof by induction.
  Let alpha /in /Ord.
  Then 0 *' alpha = 0.
  Proof.
    Case alpha /in /Succ.
      Let beta = alpha --.
      Then 0 *' alpha = (0 *' beta) +' 0.
    end.
    Case alpha /in /Lim.
      alpha, 0 are ordinals.
      0 *' alpha = {zfset x | exists beta /in alpha (x /in (0 *' beta))} (by MultLim).
    end.
    Case alpha = 0.
    end.
  end.
qed.


Lemma. Forall alpha /in /Ord (1 *' alpha = alpha).
Proof by induction.
  Let alpha /in /Ord.
  Then 1 *' alpha = alpha.
  Proof.
    Case alpha /in /Succ.
      Let beta = alpha --.
      Then 1 *' alpha = (1 *' beta) +' 1.
    end.
    Case alpha /in /Lim.
      1,alpha are ordinals.
      1 *' alpha = {zfset x | exists gamma /in alpha (x /in 1 *' gamma)} (by MultLim).
      alpha /subset 1 *' alpha.
      Proof.
        Let x /in alpha.
        Then x +' 1 /in alpha.
        Then 1 *' (x+'1) = x+'1.
        Then x /in 1 *' (x+'1).
        Then x /in 1 *' alpha.
      end.
      1 *' alpha /subset alpha.
      Proof.
        Let x /in 1 *' alpha.
        Take an ordinal gamma such that gamma /in alpha /\ x /in 1 *' gamma.
        Then x /in gamma.
        Then x /in alpha.
      end.
    end.
    Case alpha = 0.
    end.
  end.
qed.


Lemma. Forall alpha, beta /in /Ord (beta /neq /emptyset => alpha /subset alpha *' beta).
Proof.
  Let alpha /in /Ord.
  Forall beta /in /Ord (beta /neq /emptyset => alpha /subset alpha *' beta).
  Proof by induction.
    Let beta /in /Ord.
    beta /neq /emptyset => alpha /subset alpha *' beta.
    Proof.
    Case beta /in /Succ.
      Take an ordinal gamma such that beta = gamma +' 1.
      Then alpha *' beta = (alpha *' gamma) +' alpha.
      Case gamma /neq 0.
        Then gamma /in beta /setminus <0>.
        alpha /subset alpha *' gamma.
        Then alpha /subset (alpha *' gamma) +' alpha.
      end.
      Case gamma = 0. end.
      end.
      Case beta /in /Lim.
        Then alpha *' beta = {zfset x | exists gamma /in beta (x /in (alpha *' gamma))} (by MultLim).
        1 /in beta.
        alpha = alpha *' 1.
        Then alpha /subset alpha *' beta.
      end.
      Case beta = 0.
      end.      
    end.
  end.
qed.



Lemma. Forall alpha, beta /in /Ord (beta /neq 0 => alpha +' 1 /subset alpha +' beta).
Proof.
  Let alpha /in /Ord.
  Forall beta /in /Ord (beta /neq 0 => alpha +' 1 /subset alpha +' beta).
qed.


Lemma. Forall alpha, beta /in /Ord (alpha /neq 0 => beta /subset alpha *' beta).
Proof.
  Let alpha /in /Ord. 
  Let alpha /neq 0.
  Forall beta /in /Ord (beta /subset alpha *' beta).
  Proof by induction.
    Let beta /in /Ord.
    Then beta /subset alpha *' beta.
    Proof.
      Case beta /in /Succ.
        Let gamma = beta --.
        gamma /subset alpha *' gamma.
        alpha *' beta = (alpha *' gamma) +' alpha.
        Then gamma /in alpha *' beta.
      end.
      case beta /in /Lim.
        Let x /in beta.
        Then x /subset alpha *' x.
        Then x /in (alpha *' x) +' 1.
        1 /subset alpha.
        Then (alpha *' x) +' 1 /subset (alpha *' x) +' alpha.
        Then x /in (alpha *' x) +' alpha.
        alpha *' (x+'1) = (alpha *' x) +' alpha.
        x /in alpha *' (x +' 1).
        x +' 1 /in beta.
        alpha *' beta = {zfset x | exists gamma /in beta (x /in alpha *' gamma)} (by MultLim).
        Then x /in alpha *' beta.
      end.
      Case beta = 0.
      end.
    end.
  end.  
qed.



## Exponentiation

Axiom. Let alpha be an ordinal. Then alpha ^' 0 = 1.
Axiom. Let alpha, beta be ordinals. Let beta /in /Succ.
  Then alpha ^' beta = (alpha ^' beta--) *' alpha.
Lemma. Let alpha, beta be ordinals. Then alpha ^' (beta +' 1) = (alpha ^' beta) *' alpha.
Proof.
  beta +' 1 /in /Succ.
  (beta +' 1) -- = beta.
qed.
Axiom ExpLim. Let alpha, beta be ordinals. Let beta /in /Lim. Then alpha +' beta = {zfset x | exists gamma /in beta (x /in alpha ^' gamma)}.


Lemma. Forall alpha /in /Ord alpha ^' 1 = alpha.
Proof.
Let alpha /in /Ord.
1 = 0+'1.
Then alpha ^' 1 = (alpha ^' 0) *' alpha.
Then alpha ^' 1 = alpha.
qed.



## Finite Arithmetic

Lemma. Forall m,n /in /NN forall x /in (m +' n) (x /in m \/ exists i /in n x = m +' i).
Proof.
  Let m /in /NN.
  m is an ordinal.
  Define M = {k /in /NN | (forall x /in (m +' k) (x /in m \/ exists i /in k (i is an ordinal and x = m +' i)))}.
  Forall k /in M (forall x /in (m +' k) (x /in m \/ exists i /in k (i is an ordinal and x = m +' i))).
  Then 0 /in M.
  Forall n /in M (n +' 1) /in M.
  Proof.
    Forall k /in M (forall x /in (m +' k) (x /in m \/ exists i /in k (i is an ordinal and x = m +' i))).
    Let n be an object.
    n /in M => (forall x /in (m +' n) (x /in m \/ exists i /in n (i is an ordinal and x = m +' i))).
    Let n /in M.
    Then forall x /in (m +' n) (x /in m \/ exists i /in n (i is an ordinal and x = m +' i)).
    n is an ordinal.
    Then forall x /in (m +' (n+'1)) (x /in m \/ exists i /in (n+'1) (i is an ordinal and x = m +' i)).
    Proof.
      m +' (n+'1) = (m +' n) +' 1.
      Let x /in m +' (n+'1). 
      Then x /in m +' n \/ x = m +' n.
      Then x /in m \/ exists i /in (n+'1) (i is an ordinal and x = m +' i).
      Proof.
        Case x /in m +' n. 
          n /in M.
          Then forall X /in (m +' n) (X /in m \/ exists i /in n (i is an ordinal and X = m +' i)).
          x /in m +' n.
          Then x /in m \/ exists i /in n (i is an ordinal and x = m +' i).
        end.
        Case x = m +' n. end.
      end.
    end.
    n+'1 /in /NN.
    Then n+'1 /in M.
  end.
  M /subset /NN.
  M /in /VV.
  Then M /in /Ind.
  Then M = /NN.
qed.


Lemma. Forall m,n /in /NN m+'n /in /NN.
Proof.
  Let m /in /NN. 
  Then forall n /in /NN m+'n /in /NN.
  Proof by induction.
    Let n /in /NN.
    Case n = 0.
    end.
    Case n /neq 0.
      Let k = n --.
      Then m +' k /in /NN.
      m +' n = (m +' k) +' 1.
      Then m +' n /in /NN.
    end.
  end.
qed.


Lemma. Forall m,n /in /NN m*'n /in /NN.
Proof.
  Let m /in /NN. 
  Then forall n /in /NN m*'n /in /NN.
  Proof by induction.
    Let n /in /NN.
    Case n = 0.
    end.
    Case n /neq 0. 
      Let k = n --.
      Then m *' k /in /NN.
      m *' n = (m *' k) +' m.
      Then m *' n /in /NN.
    end.
  end.
qed.


Lemma. Forall m,n /in /NN m^'n /in /NN.
Proof.
  Let m /in /NN. 
  Then forall n /in /NN m^'n /in /NN.
  Proof by induction.
    Let n /in /NN.
    Case n = 0.
    end.
    Case n /neq 0. 
      Let k = n --.
      Then m ^' k /in /NN.
      m ^' n = (m ^' k) *' m.
      Then m ^' n /in /NN.
    end.
  end.
qed.



## Finite Sets

Definition. Let x be a zfset. x is finite iff Card(x) /in /NN.

Lemma. Let x,y be zfsets. Let x be finite. Let y /subset x. Then y is finite.
Proof.
  Card(x) /in /NN.
  Card(y) /subset Card(x).
  Then Card(y) /in /NN.
qed.


Lemma. Let x,y be zfsets. Let x,y be finite. Then x /cup y is finite.
Proof.
  Let y1 = y /setminus x.
  Then x /cup y = x /cup y1.
  y1 /subset y.
  Then y1 is finite.
  Take ordinals m,n such that Card(x) = m /\ Card(y1) = n.
  Then Card(x /cup y) /subset m+'n.
  Proof.
    Take a zffunction f such that f : x /leftrightarrow m.
    Take a zffunction g such that g : y1 /leftrightarrow n.
    Define h[z] =
      Case z /in x -> f[z],
      Case z /in y1 -> m +' g[z]
    for z in x /cup y1.
    Then h is a zffunction.
    Proof.
      Let z /in Dom(h). 
      Then z /in x \/ z /in y1.
      Then h[z] /in /VV.
      Proof.
        Case z /in x. end.
        Case z /in y1. 
          Then h[z] = m +' g[z].
          m +' g[z] /in /Ord.
        end.
      end.
    end.
    h : x /cup y1 /rightarrow m+'n.
    Proof.
      Let z /in x /cup y1. Then z /in x \/ z /in y1.
      Then h[z] /in m+'n.
      Proof.
        Case z /in x. Then h[z] /in m. m /subset m+'n. Then h[z] /in m+'n. end.
        Case z /in y1. 
          Take an ordinal i such that i /in n /\ i = g[z].
          Then h[z] = m+'i.
          m,i,n /in /Ord.
          i /in n.
          Then i /in n => m +' i /in m +' n (by Add1).
        end.
      end.
    end.
    h is injective.
    Proof.
      Let a,b /in x /cup y1.
      Let a /neq b.
      Then h[a] /neq h[b].
      Proof.
        a,b /in x \/ a,b /in y1 \/ (a /in x /\ b /in y1) \/ (a /in y1 /\ b /in x).
        Case a,b /in x. 
          Then f[a] /neq f[b].
          h[a] = f[a] /\ h[b] = f[b].
        end.
        Case a,b /in y1. 
          g[a], g[b] /in /Ord.
          Then g[a] /in g[b] \/ g[b] /in g[a] \/ g[a] = g[b] (by TotalOrder).
          g[a] /neq g[b].
          Then g[a] /in g[b] \/ g[b] /in g[a].
          Then m +' g[a] /in m +' g[b] \/ m +' g[b] /in m +' g[a].
          Then h[a] /in h[b] \/ h[b] /in h[a].
        end.
        Case a /in x /\ b /in y1.
          Then h[a] /in m /\ h[b] /notin m.
        end.
        Case a /in y1 /\ b /in x.
          Then h[b] /in m /\ h[a] /notin m.
        end.
      end.
    end.
    ran(h) = m+'n.
    Proof.
      Let a /in m+'n. 
      Then a /in ran(h).
      Proof.
        Then a /in m \/ a /notin m.
        Case a /in m. Take a zfset b such that b /in x /\ f[b] = a.
          Then h[b] = a.
        end.
        Case a /notin m.
          Exists b /in n a = m+'b.
          Take an ordinal b such that b /in n /\ a = m+'b.
          Take a zfset c such that c /in y1 /\ g[c] = b.
          Then h[c] = a.
        end.
      end.
    end.  
    Then h : x /cup y1 /leftrightarrow m+'n.
    Then m+'n /in Cardset(x /cup y).
    Card(x /cup y) = /bigcap Cardset(x /cup y).
    Then Card(x /cup y) /subset m+'n.
  end.
  m+'n /in /NN.
  Then Card(x /cup y) /in /NN.
qed.


Lemma. Let a,b be zfsets. Let a,b be finite. Then (a /cap b is a zfset) and (a /cap b is finite).
Proof.
  a /cap b /subset a.
qed.



## Alefs


Lemma. Let kappa be a cardinal. Let /NN /subset kappa. Then kappa /in /Lim.
Proof by contradiction. Assume the contrary. 
  Then kappa /notin /Lim.
  Then kappa /in /Succ \/ kappa = /emptyset.
  kappa /neq /emptyset. Then kappa /in /Succ.
  Take an ordinal alpha such that kappa = alpha +' 1.
  Then /NN /subset alpha.
  Take a zfset x such that kappa = Card(x).
  Take a zffunction f such that f : kappa /leftrightarrow x.

  Define g[beta] =
    Case beta /in /NN /\ beta /neq /emptyset -> beta--,
    Case beta = /emptyset -> alpha,
    Case beta /notin /NN -> beta
  for beta in alpha.

  Then g is a zffunction.
  Proof.
    Let beta /in Dom(g).
    Then g[beta] /in /VV.
  end.
  Dom(g) = alpha.
  Forall a,b /in alpha ( g[a] = g[b] => a = b).
  Proof.
    Let a,b /in alpha. Then g[a] = g[b] => a = b.
    Proof.
      Case g[a] = alpha. Then a = /emptyset. end.
      Case g[a] /in /NN. Then a /in /NN /\ a /neq /emptyset. Then a = g[a] +' 1. end.
      Case g[a] /notin /NN /\ g[a] /neq alpha. Then g[a] = a. end.
    end.
  end.
  Then g is injective.
  ran(g) /subset alpha +' 1.
  Proof.
    Let n /in ran(g).
    Take a zfset m such that m /in Dom(g) /\ g[m] = n.
    Then n /in alpha +' 1.
  end.
  alpha +' 1 /subset ran(g).
  Proof.
    Let n /in alpha +' 1.
    Then n /in ran(g).
    Proof.
      Case n = alpha.
      end.
      Case n /in /NN.
        g[n++] = n.
      end.
      Case n /notin /NN /\ n /neq alpha.
        Then g[n] = n.
      end.
    end.
  end.
  Then ran(g) = alpha +' 1.
  Then g : alpha /leftrightarrow alpha +' 1.
  Then f /circ g : alpha /leftrightarrow x.
  Proof. f /circ g : alpha /rightarrow x.
    f /circ g is injective.
    ran(f /circ g) = x.
  end.
  Then alpha /in Cardset(x).
  Then kappa /in alpha.
  Then alpha /in alpha.
  Contradiction.
qed.


Lemma. Forall kappa /in /Card kappa /in /Lim.

Signature. PlusCard(alpha) is a set.
Axiom. Let alpha /in /Ord. PlusCard(alpha) = {cardinal kappa | alpha /in kappa}.

Lemma. Forall alpha PlusCard(alpha) /neq /emptyset.
Proof.
  Let alpha /in /Ord.
  alpha < /PP alpha.
  Then Card(alpha) /in Card(/PP alpha).
  Then alpha /in Card(/PP alpha).
qed.

Signature. Plus is a function.
Axiom. Dom(Plus) = /Ord.
Axiom. Let alpha /in /Ord. Plus[alpha] = min(PlusCard(alpha)).

Lemma. Forall alpha /in /Ord Plus[alpha] /in PlusCard(alpha).
Proof.
  Let alpha /in /Ord.
  PlusCard(alpha) /neq /emptyset.
  PlusCard(alpha) /subset /Ord.
  min(PlusCard(alpha)) /in PlusCard(alpha).  
qed.

Lemma. Forall alpha /in /Ord Plus[alpha] /in /Cd.
Proof.
  Let alpha /in /Ord.
  PlusCard(alpha) /subset /Cd.
  Plus[alpha] /in PlusCard(alpha).
qed.


Lemma. Forall alpha /in /Ord alpha /in Plus[alpha].
Proof.
  Let alpha /in /Ord.
  Plus[alpha] /in PlusCard(alpha).
qed.

Lemma. Forall alpha forall kappa /in /Cd (alpha /in kappa => Plus[alpha] /subset kappa).
Proof.
  Let alpha /in /Ord.
  Let kappa /in /Cd.
  Let alpha /in kappa.
  Then kappa /in PlusCard(alpha).
  Then min(PlusCard(alpha)) /subset kappa.
qed.

Lemma. Plus : /Ord /rightarrow /Cd.
Proof.
  Let alpha /in /Ord.
  Then Plus[alpha] /in /Cd.
qed.

Lemma. Let n /in /NN. Then Plus[n] = n+'1.
Proof. n /in Plus[n]. 
  n+'1 /subset Plus[n].
  Proof. 
    n /subset Plus[n].
    Proof.
      Let m /in n.
      Forall kappa /in /Cd (n /in kappa => n /subset kappa).
      Then forall kappa /in /Cd(n /in kappa => m /in kappa).
      Then m /in Plus[n].
    end.
    n /in Plus[n].
  end.
  n+'1 /in /Cd.
  Plus[n] /subset n+'1.
qed.


Signature. Alef is a function.
Axiom. Dom(Alef) = /Ord.
Axiom. Forall alpha /in /Ord Alef[alpha] /in /Ord.
Lemma. Alef is a zffunction.
Axiom. Alef[/emptyset] = /NN.
Axiom. Let alpha /in /Succ. Let beta /in /Ord. Let alpha = beta +' 1. Then Alef[beta] /in /Ord /\ Alef[alpha] = Plus[Alef[beta]].
Axiom. Let alpha /in /Lim. Then Alef[alpha] = /bigcup Alef^[alpha].

Lemma. Let x /in /VV. Let x /subset /Cd. Then Card(/bigcup x) = /bigcup x.
Proof.
  Trans(/bigcup x).
  /bigcup x, Card(/bigcup x) /in /Ord.
  Take ordinals alpha, beta such that alpha = Card(/bigcup x) /\ beta = /bigcup x.
  Then alpha /in beta \/ beta /in alpha \/ alpha = beta.
  alpha /subset beta.
  Proof. Id /upharpoonright beta : beta /leftrightarrow beta.
  end.
  beta /notin alpha.
  Then alpha /in beta \/ alpha = beta.
  Case alpha = beta. end.
  Case alpha /in beta.
    Take a cardinal kappa such that (kappa /in x /\ alpha /in kappa).
    Take a zffunction f such that f : alpha /leftrightarrow beta.
    Then kappa /subset beta.
    Then Card(kappa) /subset Card(beta).
    kappa /subset alpha.
    Contradiction.
  end.
qed.

Lemma. Let x /in /VV. Let x /subset /Cd. Then (/bigcup x) /in /Cd.


Lemma. Forall alpha /in /Ord Alef[alpha] /in /Cd.
Proof by induction.
  Let alpha /in /Ord.
  Case alpha /in /Succ.
    Let beta = alpha --.
    Then Alef[beta] /in /Cd.
    Alef[alpha] = Plus[Alef[beta]].
  end.
  Case alpha /in /Lim.
    Then Alef[alpha] = /bigcup Alef^[alpha].
    Alef^[alpha] /subset /Cd.
    Then Alef[alpha] /in /Cd.
  end.
  Case alpha = 0.
  end.
qed.


Lemma. Forall alpha /in /Ord forall beta /in alpha (Alef[beta] /in Alef[alpha]).
Proof by induction.
  Let alpha /in /Ord.
  Forall gamma /in alpha forall beta /in gamma (Alef[beta] /in Alef[gamma]).
  Then forall beta /in alpha (Alef[beta] /in Alef[alpha]).
  Proof.
    Case alpha /in /Succ.
      Let gamma = alpha --.
      Let beta /in alpha.
      Then beta /in gamma \/ beta = gamma.
      Then Alef[beta] /in Alef[alpha].
      Proof.
        Alef[alpha] = Plus[Alef[gamma]].
        Case beta = gamma.
        end.
        Case beta /in gamma.
          gamma /in alpha.
          Then Alef[beta] /in Alef[gamma].
          Alef[gamma] /subset Alef[alpha].
        end.
      end.
    end.
    Case alpha /in /Lim.
      Let beta /in alpha.
      Then beta +' 1 /in alpha.
      Then Alef[beta] /in Alef[beta +' 1].
      Then Alef[beta] /in /bigcup Alef^[alpha].
      Then Alef[beta] /in Alef[alpha].
    end.
    Case alpha = 0.
    end.
  end.
qed.


Lemma AlefIn. Forall alpha, beta /in /Ord (alpha /in beta iff Alef[alpha] /in Alef[beta]).


Lemma AlefSubset. Forall alpha, beta /in /Ord (beta /subset alpha iff Alef[beta] /subset Alef[alpha]).


Lemma. Alef is injective.
Proof.
  Let alpha, beta /in /Ord.
  Let alpha /neq beta.
  Then alpha /in beta \/ beta /in alpha.
  Then Alef[alpha] /in Alef[beta] \/ Alef[beta] /in Alef[alpha].
  Then Alef[alpha] /neq Alef[beta].
qed.


Lemma. Alef : /Ord /rightarrow /Card.
Proof.
  Let alpha /in /Ord.
  Then Alef[alpha] /in /Cd.
  Alef[0] /subset Alef[alpha].
  Then Alef[alpha] /in /Card.
qed.


Lemma. Forall alpha /in /Ord (alpha /subset Alef[alpha]).
Proof by induction.
qed.


Lemma. Let kappa /in /Card. Then exists alpha (kappa = Alef[alpha]).
Proof. kappa /subset Alef[kappa]. Then kappa = Alef[kappa] \/ kappa /in Alef[kappa].
  Case kappa = Alef[kappa]. end.
  Case kappa /in Alef[kappa].
    kappa /in /Lim.
    Then Alef[kappa] = /bigcup Alef^[kappa].
    Define A = {ordinal alpha | kappa /in Alef[alpha]}.
    A /neq /emptyset.
    Let beta = min(A).
    A /subset /Ord.
    Then beta /in A.
    Then kappa /in Alef[beta] /\ forall gamma /in beta kappa /notin Alef[gamma].
    beta /notin /Lim.
    Proof by contradiction. Assume the contrary.
      Then Alef[beta] = /bigcup Alef^[beta].
      Then exists gamma /in beta kappa /in Alef[gamma].
      Contradiction.
    end.
    beta /in /Succ. Take an ordinal gamma such that beta = gamma +' 1.
    Then kappa /notin Alef[gamma].
    Alef[gamma], kappa /in /Ord.
    Take ordinals a, b such that a = Alef[gamma] /\ b = kappa.
    Then a /in b \/ a = b \/ b /in a.
    Then kappa /in Alef[gamma] \/ kappa = Alef[gamma] \/ Alef[gamma] /in kappa.
    Case kappa /in Alef[gamma]. Contradiction. end.
    Case kappa = Alef[gamma]. end.
    Case Alef[gamma] /in kappa.
      kappa /in /Cd.
      Then Plus[Alef[gamma]] /subset kappa.
      Proof. Take a cardinal alefgamma such that Alef[gamma] = alefgamma.
        Plus[alefgamma] = min(PlusCard(alefgamma)).
      end.
      Then Alef[beta] /subset kappa.
      Contradiction.
    end.
  end.
qed.

Lemma. ran(Alef) /subset Dom(Alef).

Lemma. Exists kappa (kappa = Alef[kappa]).
Proof.
  Define f[n] = (Alef ^^ n)[/NN] for n in /NN.

  Then f is a zffunction.
  Proof.
    Let n /in /NN. Then f[n] /in /VV.
    Proof.
      Case n = /emptyset. end.
      Case n /neq /emptyset.
        Then f[n] = (Alef ^^ n)[/NN].
        Then f[n] /in /Ord.
      end.
    end.
  end.
  Dom(f) = /NN. 
  ran(f) /subset /Cd.
  Proof. Let n /in /NN.
    Then f[n] /in /Cd.
    Proof.
      Case n = 0. (Alef ^^ 0)[/NN] = /NN. end.
      Case n /neq /emptyset. 
        Then f[n] = (Alef ^^ n)[/NN].
        Then f[n] /in ran(Alef ^^ n).
        ran(Alef ^^ n) /subset ran(Alef).
      end.
    end.
  end.

  Forall n /in /NN f[n +' 1] = Alef[f[n]].
  Proof.
    Let n /in /NN. 
    Then f[n+'1] = (Alef ^^ (n+'1)) [/NN].
    ((Alef^^n)[/NN]) /in /Ord.
    Proof.
      ran(Alef ^^ n) /subset Dom(Alef).
      (Alef^^n)[/NN] /in ran(Alef ^^ n).
    end.
    (Alef ^^ (n+'1)) [/NN] = Alef[((Alef^^n)[/NN])].
    ((Alef^^n)[/NN]) = f[n].
    Proof.
      Case n = /emptyset. end.
      Case n /neq /emptyset. end.
    end.
  end.

  Let alpha = /bigcup ran(f).
  ran(f) = f^[/NN].
  Then alpha /in /Ord.
  Proof. Trans(alpha). 
    alpha /in /VV.
    Proof.
      Forall n /in /NN f[n] /in /VV.
      Then f^[/NN] /in /VV.
      Then ran(f) /in /VV.
      Then /bigcup ran(f) /in /VV.
    end.
  end.
  alpha /in /Cd.
  Proof.
    Forall x /subset /Cd (x /in /VV => /bigcup x /in /Cd).
    ran(f) /subset /Cd.
    ran(f) /in /VV.
    Proof.
      Forall n /in /NN f[n] /in /VV.
      Then f^[/NN] /in /VV.    
    end.
  end.
  /NN /subset alpha.
  Proof.
    /NN = f[0].
    /NN /in ran(f).
  end.
  alpha /in /Lim.
  Then Alef[alpha] = /bigcup Alef^[alpha].

  alpha /subset Alef[alpha].
  alpha, Alef[alpha] /in /Ord.
  Forall a,b /in /Ord (a /in b \/ b /in a \/ a = b).
  Then alpha = Alef[alpha] \/ alpha /in Alef[alpha] \/ Alef[alpha] /in alpha.

  Alef[alpha] /notin alpha.

  alpha /notin Alef[alpha].
  Proof by contradiction. Assume the contrary.
    Then alpha /in Alef[alpha].
    Take an ordinal beta such that beta /in alpha /\ alpha /in Alef[beta].
    Take a natural number n such that beta /in f[n].
    Then Alef[beta] /in Alef[f[n]].
    f[n+'1] = Alef[f[n]].
    Then Alef[beta] /in f[n+'1].
    f[n+'1] /subset alpha.
    Contradiction.
  end.

  Then alpha = Alef[alpha].
qed.




