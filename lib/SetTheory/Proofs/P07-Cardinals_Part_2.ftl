[read Formalizations/Library/L05-Mostowski_Collapse.ftl]

## Pretyped Variables

Let w,x,y,z,W,X,Y,Z stand for zfsets.
Let a,b,c,d,A,B,C,D,M stand for sets.
Let o,o1,o2 stand for objects.
Let alpha, beta, gamma, delta stand for ordinals.
Let f,g,h,F,G,H stand for zffunction.
Let kappa, lambda stand for cardinals.


## Cartesian Product


Lemma. Forall a,b /in /NN ((a /times b is a zfset) and (Card(a /times b) = a *' b)).
Proof.
  Forall a,b /in /NN (a /times b is a zfset).
  Let a /in /NN.
  Forall b /in /NN (Card(a /times b) = a *' b).
  Proof by induction.
    Let b /in /NN.
    Case b = 0.
    end.
    Case b /neq 0.
      Let n = b--.
      n is an ordinal.
      Then Card(a /times n) = a *' n.
      Define A = {(i,n) | i /in a}.     
      (a /times (n+'1)) /subset (a /times n) /cup A.
      Proof.
        Let pair /in a /times (n+'1).
        Take zfsets aa,bb such that aa /in a /\ bb /in (n+'1) /\ pair = (aa,bb).
        Then bb /in n \/ bb = n.
        Case bb /in n. Then (aa,bb) /in a /times n. end.
        Case bb = n. Then (aa,bb) = (aa,n). (aa,n) /in A. end.
      end.
      (a /times n) /cup A /subset (a /times (n+'1)).
      Proof.
        Let pair /in (a /times n) /cup A.
        Then pair /in (a /times n) \/ pair /in A.
        Case pair /in A.
          Take a zfset i such that i /in a \/ pair = (i,n).
          Then i /in a /\ n /in (n+'1).
          Then (i,n) /in a /times (n+'1).
        end.
        Case pair /in a /times n.
          Take zfsets aa,bb such that aa /in a /\ bb /in n /\ pair = (aa,bb).
          Then aa /in a /\ bb /in (n+'1).
          Then (aa,bb) /in (a /times (n+'1)).
        end.
        Then (a /times (n+'1)) = (a /times n) /cup A.
      end.
      Forall pair /in A pair /notin (a /times n).
      Proof.
        Let pair /in A. Take zfsets x,y such that pair = (x,y).
        Take a set i such that i /in a /\ (x,y) = (i,n).
        (x,y) = (i,n).
        Then y = n.
        Then y /notin n.
        Then (x,y) /notin a /times n.
        Proof by contradiction. Assume the contrary.
          Then y /in n.
          Contradiction.      
        end.
      end. 
     
      Take a zffunction f such that f : a /times n /leftrightarrow a *' n.
      Forall x,y /in /VV ((x,y) /in A => x /in /NN).
      Define g[(x,y)] = x for (x,y) in A.
      g is a zffunction.
      Proof.
        Let pair /in A.
        Then g[pair] /in /VV.
      end.
      ran(g) = a.
      Forall x,y /in /VV ((x,y) /in a /times (n+'1) => (x,y) /in A \/ (x,y) /in a /times n).
      Forall x,y /in /VV ((x,y) /in A => (x,y) /in Dom(g) /\ g[(x,y)] /in /Ord).
  
      Forall pair /in A (g[pair] is an ordinal).  

      Define h[(x,y)] =
        Case (x,y) /in a /times n  -> f[(x,y)],
        Case (x,y) /in A -> (a*'n) +' g[(x,y)]
      for (x,y) in a /times (n+'1).

      Then h is a zffunction.
      Proof.
        Let pair /in Dom(h). 
        Take zfsets x,y such that pair = (x,y).
        Then (x,y) /in a /times (n+'1).
        Then h[(x,y)] /in /VV.
        Proof.
          Case (x,y) /in a /times n. end.
          Case (x,y) /in A. end.
        end.
      end.
      ran(h) /subset (a*'n) +' a.
      Proof.
        Let pair /in a /times (n+'1). 
        Take zfsets x,y such that pair = (x,y).
        Then h[(x,y)] /in (a *' n) +' a.
        Proof.
          Case (x,y) /in a /times n. 
            Then h[(x,y)] = f[(x,y)].
            f[(x,y)] /in a *' n. 
            (a*'n) /subset (a*'n) +' a.
            Then f[(x,y)] /in (a*'n) +' a.
          end.
          Case (x,y) /in A. 
            Then h[(x,y)] = (a*'n) +' g[(x,y)].
            a*'n,g[(x,y)],a /in /Ord.
            g[(x,y)] /in a. 
            Then (a*'n) +' g[(x,y)] /in (a*'n) +' a (by Add1).
          end.
        end.
        Then h[pair] /in (a*'n) +' a.
      end.
      h : a /times (n+'1) /rightarrow (a *' n) +' a.

      h is injective.
      Proof.
        Let pair1, pair2 /in a /times (n+'1).
        Let pair1 /neq pair2.
        Then h[pair1] /neq h[pair2].
        Proof.
          pair1, pair2 /in A \/ pair1, pair2 /in a /times n \/ (pair1 /in A /\ pair2 /in a /times n) \/ (pair2 /in A /\ pair1 /in a /times n).
          Case pair1, pair2 /in a /times n.
            a /times n /subset Dom(h).
            Forall pair /in a /times n (f[pair] = h[pair]).
            f[pair1] = h[pair1].
            f[pair2] = h[pair2].
            f[pair1] /neq f[pair2].
          end.
          Case pair1, pair2 /in A.
            Then g[pair1] /neq g[pair2].
            Forall ord1,ord2 /in /Ord (ord1 /in ord2 \/ ord2 /in ord1 \/ ord1 = ord2).
            (a*'n),g[pair1],g[pair2] /in /Ord.
            Then g[pair1] /in g[pair2] \/ g[pair2] /in g[pair1] (by TotalOrder).
            (a*'n) +' g[pair1], (a*'n) +' g[pair2] /in /Ord.
            Then (a*'n) +' g[pair1] /in (a*'n) +' g[pair2] \/ (a*'n) +' g[pair2] /in (a*'n) +' g[pair1] (by Add1).
            Then (a*'n) +' g[pair1] /neq (a*'n) +' g[pair2].
            pair1 /notin a /times n.
            Take zfsets x1,y1 such that pair1 = (x1,y1).
            Then h[(x1,y1)] = (a*'n) +' g[(x1,y1)].
            pair2 /notin a /times n.
            Take zfsets x2,y2 such that pair2 = (x2,y2).
            Then h[(x2,y2)] = (a*'n) +' g[(x2,y2)].
          end.
          Case (pair1 /in A /\ pair2 /in a /times n).
            Take zfsets x2,y2 such that pair2 = (x2,y2).
            h[(x2,y2)] = f[(x2,y2)].
            Then h[pair2] /in a *' n.
            pair1 /notin a /times n.
            Take zfsets x1,y1 such that pair1 = (x1,y1).
            g[(x1,y1)] /in /Ord.
            h[(x1,y1)] = (a*'n) +' g[(x1,y1)].
            h[pair1] /notin a *' n.
          end.
            Case (pair2 /in A /\ pair1 /in a /times n).
            Take zfsets x1,y1 such that pair1 = (x1,y1).
            h[(x1,y1)] = f[(x1,y1)].
            Then h[pair1] /in a *' n.
            pair2 /notin a /times n.
            Take zfsets x2,y2 such that pair2 = (x2,y2).
            g[(x2,y2)] /in /Ord.
            h[(x2,y2)] = (a*'n) +' g[(x2,y2)].
            h[pair2] /notin a *' n.
          end.
        end.
      end.
      
      (a*'n) +' a /subset ran(h).
      Proof.
        Let x /in (a*'n) +' a.
        Then x /in ran(h).
        Proof.
          x /in (a*'n) \/ x /notin (a*'n).
          Case x /in a*'n.
            Take a zfset pair such that pair /in a /times n /\ f[pair] = x.
            Then pair /in Dom(h).
            Take sets x1,y1 such that pair = (x1,y1).
            Then h[(x1,y1)] = x.
          end.
          Case x /notin a*'n.
            Forall mm,nn /in /NN forall xx /in (mm +' nn) (xx /in mm \/ exists i /in nn xx = mm +' i) (by AddFin).
            (a*'n), a /in /NN.
            x /in (a*'n) +' a.
            Then (x /in (a*'n) \/ exists i /in a ((i is an ordinal) /\ x = (a*'n) +' i)) (by AddFin).
            Exists i /in a ((i is an ordinal) /\ x = (a*'n) +' i).
            Take an ordinal i such that i /in a /\ x = (a*'n) +' i.
            Take a zfset pair such that pair /in A /\ i = g[pair].
            Take zfsets x1,y1 such that pair = (x1,y1).
            Then (x1,y1) /notin a /times n.
            Then h[(x1,y1)] = (a *' n) +' g[(x1,y1)].
            Then h[(x1,y1)] = (a *' n) +' i.
          end.
        end.
      end.
      Then ran(h) = (a*'n) +' a.
      Then h : a /times (n+'1) /leftrightarrow (a *' n) +' a.    
      (a *' n) +' a /in /NN.
      n+'1 = b.
      Then Card(a /times b) = (a *' n) +' a.
      a *' b = (a *' n) +' a.
      Then Card(a /times b) = (a *' b).
    end.    
  end.   
qed.


Lemma. Let a1,a2,b1,b2 be zfsets. Let Card(a1) = Card(a2) /\ Card(b1) = Card(b2). Then (a1 /times b1) /tilde (a2 /times b2).
Proof.
  a1 /tilde a2.
  b1 /tilde b2.
  Take a zffunction f such that f : a1 /leftrightarrow a2.
  Take a zffunction g such that g : b1 /leftrightarrow b2.
  
  Define h1[(c,d)] = c for (c,d) in a1 /times b1.
  Define h2[(c,d)] = d for (c,d) in a1 /times b1.
  h1 is a zffunction.
  Proof.
    Let pair /in Dom(h1). Then pair /in a1 /times b1.
    Take zfsets c,d such that pair = (c,d).
    Then h1[pair] /in /VV.
  end.
  ran(h1) /subset a1.
  Proof.
    Let pair /in Dom(h1). Then pair /in a1 /times b1.
    Take zfsets c,d such that pair = (c,d) /\ c /in a1.
    Then h1[pair] /in a1.
  end.
  h2 is a zffunction.
  Proof.
    Let pair /in Dom(h2). Then pair /in a1 /times b1.
    Take zfsets c,d such that pair = (c,d).
    Then h2[pair] /in /VV.
  end.
  ran(h2) /subset b1.
  Proof.
    Let pair /in Dom(h2). Then pair /in a1 /times b1.
    Take zfsets c,d such that pair = (c,d) /\ d /in b1.
    Then h2[pair] /in b1.
  end.    
  Then f /circ h1 : a1 /times b1 /rightarrow a2.
  Then g /circ h2 : a1 /times b1 /rightarrow b2.
  
  Define h[pair] = ((f /circ h1)[pair],(g /circ h2)[pair]) for pair in a1 /times b1.
  
  Then h is a zffunction.
  Proof.
    Let pair /in a1 /times b1.
    Then (f /circ h1)[pair] /in a2.
    Then (g /circ h2)[pair] /in b2.
    Then h[pair] /in /VV.
  end.
  Then h : a1 /times b1 /rightarrow a2 /times b2.
  Proof.
    Dom(h) = a1 /times b1.
    Let pair /in a1 /times b1.
    Then (f /circ h1)[pair] /in a2.
    Then (g /circ h2)[pair] /in b2.
    Then h[pair] /in a2 /times b2.
  end.
  h is injective.
  Proof.
    Let pair1, pair2 /in a1 /times b1. Let pair1 /neq pair2.
    Then h[pair1] /neq h[pair2].
    Proof.
      Take zfsets x1,y1 such that x1 /in a1 /\ y1 /in b1 /\ pair1 = (x1,y1).
      Take zfsets x2,y2 such that x2 /in a1 /\ y2 /in b1 /\ pair2 = (x2,y2).
      Then x1 /neq x2 \/ y1 /neq y2.
      Case x1 /neq x2.
        h1[(x1,y1)] = x1.
        h1[(x2,y2)] = x2.
        Then f[x1] /neq f[x2].
        Then (f /circ h1)[(x1,y1)] /neq (f /circ h1)[(x2,y2)].
        Then forall aa1,aa2 /in /VV ((f /circ h1)[(x1,y1)],aa1) /neq ((f /circ h1)[(x2,y2)],aa2).
        ((f /circ h1)[(x1,y1)],(g /circ h2)[(x1,y1)]) /neq ((f /circ h1)[(x2,y2)],(g /circ h2)[(x2,y2)]).
      end.
      Case y1 /neq y2.
        h2[(x1,y1)] = y1.
        h2[(x2,y2)] = y2.
        Then g[y1] /neq g[y2].
        Then (g /circ h2)[(x1,y1)] /neq (g /circ h2)[(x2,y2)].
        Then forall aa1,aa2 /in /VV (aa1,(g /circ h2)[(x1,y1)]) /neq (aa2,(g /circ h2)[(x2,y2)]).
        Proof by contradiction. Assume the contrary.
          Take aa1,aa2 /in /VV such that (aa1,(g /circ h2)[(x1,y1)]) = (aa2,(g /circ h2)[(x2,y2)]).
          Take zfsets bb1,bb2 such that bb1 = (g /circ h2)[(x1,y1)] /\ bb2 = (g /circ h2)[(x2,y2)].
          Then (aa1,bb1) = (aa2,bb2).
          Then aa1=aa2 /\ bb1 = bb2.
          Then (g /circ h2)[(x1,y1)] = (g /circ h2)[(x2,y2)].
          Contradiction.
        end.
        ((f /circ h1)[(x1,y1)],(g /circ h2)[(x1,y1)]) /neq ((f /circ h1)[(x2,y2)],(g /circ h2)[(x2,y2)]).
      end.
    end.
  end.    
  Then h : a1 /times b1 /leftrightarrow ran(h).    
  a2 /times b2 /subset ran(h).
  Proof.
    Let pair /in a2 /times b2. Take zfsets x2,y2 such that x2 /in a2 /\ y2 /in b2 /\ pair = (x2,y2).
    Take a zfset x1 such that x1 /in a1 /\ f[x1] = x2.
    Take a zfset y1 such that y1 /in b1 /\ g[y1] = y2.
    Then (x1,y1) /in a1 /times b1.
    h1[(x1,y1)] = x1.
    h2[(x1,y1)] = y1.
    Then (f /circ h1)[(x1,y1)] = x2.
    Then (g /circ h2)[(x1,y1)] = y2.
    Then h[(x1,y1)] = (x2,y2).
    Then pair /in ran(h).
  end.
  Then h : a1 /times b1 /leftrightarrow a2 /times b2.
qed.


Lemma. Let a,b be zfsets. Let a, b be finite. Then (a /times b is a zfset) and (a /times b is finite).
Proof.
  Take natural numbers m,n such that Card(a) = m /\ Card(b) = n.
  Then a /times b /tilde m /times n.
  Card(m /times n) = m *' n.
  Then Card(a /times b) = m *' n.
  m *' n /in /NN.
qed.




# Goedel Ordering

Definition. Let a1,a2,b1,b2 /in /Ord. (a1,b1) isgoedelsmallerthan (a2,b2) iff
(a1 /cup b1 /in a2 /cup b2) \/ (a1 /cup b1 = a2 /cup b2 /\ a1 /in a2)
\/ (a1 /cup b1 = a2 /cup b2 /\ a1 = a2 /\ b1 /in b2).
Let (a, b) <3 (c,d) stand for (a,b) isgoedelsmallerthan (c,d).



Signature. goedel is an object.
Axiom. goedel is a relation.
Axiom. relfield(goedel) = /Ord /times /Ord.
Axiom goedel. Forall a,b,c,d /in /Ord ( (a, b) - goedel - (c,d) iff (a, b) <3 (c,d)).

Lemma. goedel is a strict linear order.
Proof.
  goedel is connex.
  Proof.
    Forall pair1, pair2 /in /Ord /times /Ord (pair1 - goedel - pair2 \/ pair2 - goedel - pair1 \/ pair1 = pair2).
    Proof.
      Let pair1, pair2 /in /Ord /times /Ord.
      Take ordinals a,b such that pair1 = (a,b).
      Take ordinals c,d such that pair2 = (c,d).
      Then (pair1 - goedel - pair2 \/ pair2 - goedel - pair1 \/ pair1 = pair2).
      Proof.
        Forall alpha, beta /in /Ord alpha /cup beta /in /Ord.
        Proof.
          Let alpha, beta /in /Ord.
          Trans(alpha /cup beta).
          alpha /cup beta = /bigcup <alpha, beta>.
          alpha /cup beta /in /VV.
        end.
        Then a /cup b, c /cup d /in /Ord.
        Forall alpha, beta /in /Ord (alpha /in beta \/ beta /in alpha \/ alpha = beta).
        Take ordinals alpha, beta such that a /cup b = alpha /\ c /cup d = beta.
        Then (alpha /in beta \/ beta /in alpha \/ alpha = beta).
        Case alpha /in beta. Then (a,b) <3 (c,d). a,b,c,d /in /Ord. Then (a,b) - goedel - (c,d) (by goedel). end.
        Case beta /in alpha. Then (c,d) <3 (a,b). a,b,c,d /in /Ord. Then (c,d) - goedel - (a,b) (by goedel). end.
        Case alpha = beta. Then a /in c \/ c /in a \/ a = c.
          Case a /in c. Then (a,b) <3 (c,d). a,b,c,d /in /Ord. Then (a,b) - goedel - (c,d) (by goedel). end.
          Case c /in a. Then (c,d) <3 (a,b). a,b,c,d /in /Ord. Then (c,d) - goedel - (a,b) (by goedel). end.
          Case a = c. Then b /in d \/ d /in b \/ b = d.
            Case b /in d. Then (a,b) <3 (c,d). a,b,c,d /in /Ord. Then (a,b) - goedel - (c,d) (by goedel). end.
            Case d /in b. Then (c,d) <3 (a,b). a,b,c,d /in /Ord. Then (c,d) - goedel - (a,b) (by goedel). end.
            Case b = d. Then (a,b) = (c,d). end.
          end.        
        end.
      end.
    end.
  end.
  
  goedel is irreflexive.
  Proof.
    Forall pair /in /Ord /times /Ord (not (pair - goedel - pair)).
    Proof.
      Let pair /in /Ord /times /Ord.
      Take ordinals a,b such that pair = (a,b).
      Then not ((a,b) <3 (a,b)).
    end.
  end.
  
  goedel is reltransitive.
  Proof.
    Forall pair1, pair2, pair3 /in /Ord /times /Ord (pair1 - goedel - pair2 /\ pair2 - goedel - pair3 => pair1 - goedel - pair3).
    Proof.
      Let pair1, pair2, pair3 /in /Ord /times /Ord.
      Let (pair1 - goedel - pair2 /\ pair2 - goedel - pair3).
      Take ordinals a1,b1 such that pair1 = (a1,b1).
      Take ordinals a2,b2 such that pair2 = (a2,b2).
      Take ordinals a3,b3 such that pair3 = (a3,b3).
      Then (a1,b1) <3 (a2,b2).
      Then (a1 /cup b1 /in a2 /cup b2) \/ (a1 /cup b1 = a2 /cup b2 /\ a1 /in a2)
      \/ (a1 /cup b1 = a2 /cup b2 /\ a1 = a2 /\ b1 /in b2).
      Then (pair1 - goedel - pair3).
      Proof.
        Case (a1 /cup b1 /in a2 /cup b2).
          (a2,b2) <3 (a3,b3).
          Then (a2 /cup b2 /in a3 /cup b3) \/ (a2 /cup b2 = a3 /cup b3 /\ a2 /in a3)
          \/ (a2 /cup b2 = a3 /cup b3 /\ a2 = a3 /\ b2 /in b3).
          Then (a2 /cup b2 /in a3 /cup b3) \/ (a2 /cup b2 = a3 /cup b3).
          Then a1 /cup b1 /in a3 /cup b3.
          Proof.
            Case a2 /cup b2 = a3 /cup b3. end.
            Case a2 /cup b2 /in a3 /cup b3.
              Then (a1 /cup b1 /in a2 /cup b2) /\ (a2 /cup b2 /in a3 /cup b3).
              Trans(a3 /cup b3). 
              Then (a2 /cup b2 /subset a3 /cup b3).
              Then (a1 /cup b1 /in a3 /cup b3).
            end.
          end.
          Then (a1,b1) <3 (a3,b3).
          (a1,b1), (a3,b3) /in /Ord /times /Ord.
          Then (a1,b1) - goedel - (a3,b3).
        end.
      
        Case (a1 /cup b1 = a2 /cup b2 /\ a1 /in a2).
          (a2,b2) <3 (a3,b3).
          Then (a2 /cup b2 /in a3 /cup b3) \/ (a2 /cup b2 = a3 /cup b3 /\ a2 /in a3)
          \/ (a2 /cup b2 = a3 /cup b3 /\ a2 = a3 /\ b2 /in b3).
          Case (a2 /cup b2 /in a3 /cup b3). Then a1 /cup b1 /in a3 /cup b3.
            Then (a1,b1) <3 (a3,b3). (a1,b1) = pair1 /\ (a3,b3) = pair3.
          end.
          Case (a2 /cup b2 = a3 /cup b3 /\ a2 /in a3). Then a1 /cup b1 = a3 /cup b3.
            a1 /in a3.
            Then (a1,b1) <3 (a3,b3). (a1,b1) = pair1 /\ (a3,b3) = pair3.
            Then (a1,b1) - goedel - (a3,b3).
          end.
          Case (a2 /cup b2 = a3 /cup b3 /\ a2 = a3 /\ b2 /in b3). Then a1 /cup b1 = a3 /cup b3.
            a1 /in a3.
            Then (a1,b1) <3 (a3,b3). (a1,b1) = pair1 /\ (a3,b3) = pair3.
          end.
        end.
  
        Case (a1 /cup b1 = a2 /cup b2 /\ a1 = a2 /\ b1 /in b2).
          (a2,b2) <3 (a3,b3).
          Then (a2 /cup b2 /in a3 /cup b3) \/ (a2 /cup b2 = a3 /cup b3 /\ a2 /in a3)
          \/ (a2 /cup b2 = a3 /cup b3 /\ a2 = a3 /\ b2 /in b3).
          Case (a2 /cup b2 /in a3 /cup b3). Then a1 /cup b1 /in a3 /cup b3.
            Then (a1,b1) <3 (a3,b3). (a1,b1) = pair1 /\ (a3,b3) = pair3.
          end.
          Case (a2 /cup b2 = a3 /cup b3 /\ a2 /in a3). Then a1 /cup b1 = a3 /cup b3.
            a1 /in a3.
            Then (a1,b1) <3 (a3,b3). (a1,b1) = pair1 /\ (a3,b3) = pair3.
          end.
          Case (a2 /cup b2 = a3 /cup b3 /\ a2 = a3 /\ b2 /in b3). Then a1 /cup b1 = a3 /cup b3.
            a1 = a3.
            b1 /in b3.
            Then (a1,b1) <3 (a3,b3). (a1,b1) = pair1 /\ (a3,b3) = pair3.
          end.
        end.
      end.
    end.
  end.
qed.


Lemma. Forall alpha, beta (alpha /cup beta /in /Ord).
Proof.
  Let alpha, beta /in /Ord.
  Then <alpha,beta> /subset /Ord.
  <alpha,beta> /in /VV.
  alpha /cup beta = /bigcup <alpha,beta>.
qed.

Lemma. reldomain(goedel) = /Ord /times /Ord.
Proof.
  reldomain(goedel) /subset /Ord /times /Ord.
  Proof.
    relfield(goedel) = /Ord /times /Ord.
  end.
  /Ord /times /Ord /subset reldomain(goedel).
  Proof.
    Let pair /in /Ord /times /Ord. Take ordinals a,b such that pair = (a,b).
    Then (a,b) <3 (a+'1,b).
    Proof.
      a /cup b /subset (a+'1) /cup b.
      a,b /in /Ord.
      a /cup b /in /Ord.
      (a+'1) /cup b /in /Ord.
      Take ordinals alpha, beta such that alpha = a /cup b /\ beta = (a+'1) /cup b.
      Then alpha /subset beta. Then alpha /in beta \/ alpha = beta.
      Then a /cup b /in (a+'1) /cup b \/ a /cup b = (a+'1) /cup b.
    end.
    Then (a,b) - goedel - (a+'1,b).
    (a+'1,b) /in /VV.
    Proof.
      a+'1,b /in /VV.
      Forall x,y /in /VV (x,y) /in /VV.
    end.
    Then exists z ((a,b) - goedel - z).
    Then (a,b) /in reldomain(goedel).
  end.
qed.


Lemma. goedel is wellfounded.
Proof.
  reldomain(goedel) /subset /Ord /times /Ord.
  Let A be a set. Let A /subset /Ord /times /Ord. Let A /neq /emptyset.
  Define B = {ordinals alpha | exists beta /in /Ord (beta /subset alpha /\ ((alpha,beta) /in A \/ (beta,alpha) /in A))}.
  B /subset /Ord.
  Then B /neq /emptyset.
  Proof.
    Take an object pair such that pair /in A. Take ordinals a,b such that pair = (a,b).
    Then a /subset b \/ b /subset a. Then a /in B \/ b /in B.
  end.
  Let min = min(B).
  min /in B.
  Define C = {ordinals beta | beta = min \/ (beta /in min /\ (beta,min) /in A)}.
  C /subset /Ord.
  Then C /neq /emptyset.
  Proof.
    min /in B. Take an ordinal beta such that beta /subset min /\ ((beta,min) /in A \/ (min,beta) /in A).
    Then beta /in C \/ min /in C.
  end.
  Let min2 = min(C).
  min2 /in C.
  Then min2 /in min \/ min2 = min.
  
  Case min2 /in min. Then (min2, min) /in A. min2 /cup min = min.
    Let pair = (min2,min). Then forall pair2 /in sset(goedel,pair) pair2 /notin A.
    Proof.
      Let pair2 /in sset(goedel,pair). Then pair2 /in /Ord /times /Ord.
      Take ordinals a,b such that pair2 = (a,b).
      Then pair2 /notin A.
      Proof by contradiction. Assume the contrary. Then pair2 /in A.
        Then a /in b \/ b /in a \/ a = b.
        Case a = b. Then a /in B. Then min /in b \/ min = b.
          Case min /in b.
            Then (min2,min) <3 (a,b). Then not ((a,b) <3 (min2,min)). Contradiction.
          end.
          Case min = b.
            Then min2 /in a \/ min2 = a.
            Case min2 = a. Then (a,b) = (min2, min). Contradiction. end.
            Case min2 /in a. Then (min2,min) <3 (a,b). 
              Then not ((a,b) <3 (min2,min)).
              Contradiction. 
            end.
          end.
        end.
        Case a /in b. Then b /in B. Then min /in b \/ min = b.
          Case min = b.
            Then min2 /in a \/ a = min2.
            Case min2 = a. Then (a,b) = (min2, min). Contradiction. end.
            Case min2 /in a. Then (min2,min) <3 (a,b). 
              Then not ((a,b) <3 (min2,min)).
              Contradiction. 
            end.
          end.
          Case min /in b. Then (min2,min) <3 (a,b). 
            Then not ((a,b) <3 (min2,min)).
            Contradiction. 
          end.
        end.
        Case b /in a. Then a /in B. Then min /in a \/ min = a.
          Case min = a. Then min2 /in a. Then (min2,min) <3 (a,b). 
            Then not ((a,b) <3 (min2,min)).
            Contradiction.
          end.
          Case min /in a. Then (min2,min) <3 (a,b). 
            Then not ((a,b) <3 (min2,min)).
            Contradiction.
          end.
        end.
      end.
    end.
  end.
  
  Case min2 = min.
    Define D = {ordinals alpha | (min, alpha) /in A}.
    D /subset /Ord.
    Then D /neq /emptyset.
    Proof.
      Take an ordinal beta such that beta /subset min /\ ((min,beta) /in A \/ (beta,min) /in A).
      Then beta /in min \/ beta = min.
      Case beta /in min. Then (min,beta) /in A. Then beta /in D. end.
      Case beta = min. Then (min,min) /in A. Then min /in D. end.
    end.
    Let min3 = min(D).
    Let pair = (min,min3). 
    Then min /cup min3 = min.
    Proof.
      min /in B. Take an ordinal alpha such that alpha /subset min /\ ((min,alpha) /in A \/ (alpha,min) /in A).
      Case (min, alpha) /in A. Then min3 /subset alpha. end.
      Case (alpha, min) /in A. Then alpha = min \/ alpha /in min.
      end.
    end.
    Then forall pair2 /in sset(goedel,pair) pair2 /notin A.
    Proof.
      Let pair2 /in sset(goedel,pair). Then pair2 /in /Ord /times /Ord.
      Take ordinals a,b such that pair2 = (a,b).
      Then pair2 /notin A.
      Proof by contradiction. Assume the contrary. Then pair2 /in A.
        a /in b \/ b /in a \/ a = b.
        Case a = b. Then a /cup b = a. Then min /in a \/ a = min.
          Case min /in a. Then (min,min3) <3 (a,b). Then not ((a,b) <3 (min,min3)). Contradiction.
          end.
          Case a = min. Then min3 /in b \/ min3 = b.
            Then (min,min3) <3 (a,b). Then not ((a,b) <3 (min,min3)). Contradiction.
          end.
        end.
        Case a /in b. Then a /cup b = b. Then min /in b \/ min = b.
          Case min /in b.
            Then (min,min3) <3 (a,b). Then not ((a,b) <3 (min,min3)). Contradiction.
          end.
          Case min = b. Then a /in min. Contradiction. end.
        end.
        Case b /in a. Then a /cup b = a. Then min /in a \/ min = a.
          Then (min,min3) <3 (a,b). Then not ((a,b) <3 (min,min3)). Contradiction.
        end.      
      end.
    end.
  end.
qed.


Lemma. goedel is a strong wellorder.
Proof.
  goedel is a wellorder.
  Forall x /in relfield(goedel) sset(goedel,x) /in /VV.
  Proof.
    relfield(goedel) /subset /Ord /times /Ord.
    Let pair /in /Ord /times /Ord.
    Take ordinals a,b such that pair = (a,b).
    Then sset(goedel,pair) /in /VV.
    Proof.
      Trans(a /cup b).
      a /cup b /in /Ord.
      Let c = (a /cup b)+'1.
      Then sset(goedel, pair) /subset c /times c.
      Proof.
        Let pair2 /in sset(goedel,pair).
        Take ordinals a2,b2 such that pair2 = (a2,b2).
        Then (a2,b2) <3 (a,b).
        Then (a2 /cup b2 /in a /cup b) \/ (a2 /cup b2 = a /cup b /\ a2 /in a)
        \/ (a2 /cup b2 = a /cup b /\ a2 = a /\ b2 /in b).
        Then a2 /cup b2 /subset a /cup b.
        a2 /cup b2 /in /Ord.
        Then a2 /cup b2 = a /cup b \/ a2 /cup b2 /in a /cup b.
        Then a2 /cup b2 /in c.
        Then a2 /in c /\ b2 /in c.
        Then pair2 /in c /times c.
      end.
    end.
  end.
qed.


Lemma. reldomain(goedel) is a proper class.
Proof by contradiction. Assume the contrary.
  Then reldomain(goedel) /in /VV.
  reldomain(goedel) = /Ord /times /Ord.
  Define f[(a,b)] = a for (a,b) in /Ord /times /Ord.
  Then f is a zffunction.
  Proof.
    Let x /in Dom(f). Take ordinals a,b such that x = (a,b).
    Then f[x] = a.
  end.
  Then /Ord /subset f^[/Ord /times /Ord].
  Proof.
    Let a /in /Ord.
    Then f[(a,0)] = a.
    Then a /in f^[/Ord /times /Ord].
  end.
  Then /Ord /in /VV.
  Contradiction.
qed.


Lemma. MCol goedel : /Ord /times /Ord /leftrightarrow /Ord.


Signature. Goed is a function.
Axiom. Goed = MCol goedel.
Lemma. Goed is a zffunction.
Lemma. Goed : /Ord /times /Ord /leftrightarrow /Ord.
Lemma. Let a1,a2,b1,b2 /in /Ord. Then (a1,b1),(a2,b2) /in /Ord /times /Ord /\ Goed[(a1,b1)], Goed[(a2,b2)] /in /Ord.
Proof.
  (a1,b1),(a2,b2) /in /Ord /times /Ord.
qed.


Lemma. Let a1,a2,b1,b2 /in /Ord. Let (a1,b1) <3 (a2,b2). 
Then (a1,b1),(a2,b2) /in Dom(Goed) /\ Goed[(a1,b1)], Goed[(a2,b2)] /in /Ord /\ Goed[(a1,b1)] /in Goed[(a2,b2)].
Proof.
  Let x = (a1,b1).
  Let y = (a2,b2).
  x,y /in /Ord /times /Ord.
  Then x,y /in relfield(goedel).
  Then x - goedel - y.
  Then x /in sset(goedel,y).
  goedel is a strongly wellfounded relation.
  Then forall z /in relfield(goedel) (MCol goedel)[z] = (MCol goedel)^[sset(goedel,z)] (by MCol).
  (MCol goedel)[y] = (MCol goedel)^[sset(goedel,y)].
  (MCol goedel)[x] /in (MCol goedel)^[sset(goedel,y)].
  Then (MCol goedel)[x] /in (MCol goedel)[y].
qed.


# The Inverse of the Goedel Pairing

Lemma. Goed^{-1} : /Ord /leftrightarrow /Ord /times /Ord.

Signature. pr1 is a function.
Axiom. pr1 : /VV /times /VV /rightarrow /VV.
Lemma. Dom(pr1) = /VV /times /VV.
Lemma. Forall x,y /in /VV (x,y) /in Dom(pr1).
Proof.
  Let x,y /in /VV. Then (x,y) /in /VV /times /VV.
qed.
Axiom. Forall x,y /in /VV pr1[(x,y)] = x.

Signature. pr2 is a function.
Axiom. pr2 : /VV /times /VV /rightarrow /VV.
Lemma. Dom(pr2) = /VV /times /VV.
Lemma. Forall x,y /in /VV (x,y) /in Dom(pr2).
Proof.
  Let x,y /in /VV. Then (x,y) /in /VV /times /VV.
qed.
Axiom. Forall x,y /in /VV pr2[(x,y)] = y.

Signature. Goed1 is a function.
Lemma. /Ord /times /Ord /subset /VV /times /VV.
Proof.
  Let pair /in /Ord /times /Ord.
  Take ordinals a,b such that pair = (a,b).
  Then pair /in /VV /times /VV.
qed.
Axiom. Goed1 = pr1 /circ Goed^{-1}.

Signature. Goed2 is a function.
Axiom. Goed2 = pr2 /circ Goed^{-1}.

Lemma. Goed1 : /Ord /rightarrow /Ord.
Proof.
  Dom(Goed^{-1}) = /Ord.
  Dom(Goed1) = /Ord.
  Let a /in /Ord.
  Then Goed^{-1}[a] /in /Ord /times /Ord.
  Take ordinals b,c such that Goed^{-1}[a] = (b,c).
  Goed1[a] = (pr1 /circ Goed^{-1})[a].
  (pr1 /circ Goed^{-1})[a] = pr1[(b,c)].
  pr1[(b,c)] = b.
qed.

Lemma. Goed2 : /Ord /rightarrow /Ord.
Proof.
  Dom(Goed^{-1}) = /Ord.
  Dom(Goed2) = /Ord.
  Let a /in /Ord.
  Then Goed^{-1}[a] /in /Ord /times /Ord.
  Take ordinals b,c such that Goed^{-1}[a] = (b,c).
  Goed2[a] = (pr2 /circ Goed^{-1})[a].
  (pr2 /circ Goed^{-1})[a] = pr2[(b,c)].
  pr2[(b,c)] = c.
qed.

Lemma. Forall alpha /in /Ord (Goed1[alpha],Goed2[alpha]) /in /Ord /times /Ord.

Lemma. Forall alpha /in /Ord  Goed[(Goed1[alpha],Goed2[alpha])] = alpha.
Proof.
  Let alpha /in /Ord.
  Then Goed[Goed^{-1}[alpha]] = alpha.  
  (Goed1[alpha],Goed2[alpha]) = Goed^{-1}[alpha].
  Proof.
    Goed^{-1}[alpha] /in /Ord /times /Ord.
    Take ordinals a,b such that Goed^{-1}[alpha] = (a,b).
    Goed1[alpha] = (pr1 /circ Goed^{-1})[alpha].
    (pr1 /circ Goed^{-1})[alpha] = pr1[(a,b)].
    Then Goed1[alpha] = a.
    Goed2[alpha] = (pr2 /circ Goed^{-1})[alpha].
    (pr2 /circ Goed^{-1})[alpha] = pr2[(a,b)].
    Then Goed2[alpha] = b.
    Then (Goed1[alpha],Goed2[alpha]) = (a,b).
  end.
qed.


Lemma. Forall alpha /in /Ord (sset(goedel,(0,alpha)) = alpha /times alpha).
Proof.
  Let alpha /in /Ord.
  sset(goedel,(0,alpha)) /subset alpha /times alpha.
  Proof.
    Let pair /in sset(goedel,(0,alpha)).
    Then pair /in /Ord /times /Ord.
    Take ordinals a,b such that pair = (a,b).
    (a,b) - goedel - (0,alpha).
    a,b,0,alpha /in /Ord.
    Then (a,b) <3 (0,alpha) (by goedel).
    Then a /cup b /in alpha \/ a /cup b = alpha.
    Case a /cup b /in alpha.
      Then a /in alpha /\ b /in alpha.
      Then (a,b) /in alpha /times alpha.
    end.
    Case a /cup b = alpha.
      Then a = alpha \/ b = alpha.
      Case a = alpha. Then (0,alpha) <3 (a,b). Contradiction. end.
      Case b = alpha.
        Then a /in 0 \/ a = 0.
        Contradiction.
      end.
    end.
  end.
  alpha /times alpha /subset sset(goedel,(0,alpha)).
  Proof.
    Let pair /in alpha /times alpha.
    Take ordinals a,b such that a,b /in alpha /\ pair = (a,b).
    Then a /cup b /subset alpha.
    a /cup b /neq alpha.
    Then a /cup b /in alpha.
    Proof.
      a /cup b /in /Ord.
      Forall o1,o2 /in /Ord (o1 /in o2 \/ o2 /in o1 \/ o1 = o2).
      Take ordinals o1,o2 such that a /cup b = o1 /\ alpha = o2.
      Then a /cup b /in alpha \/ a /cup b = alpha \/ alpha /in a /cup b.
    end.
    Then (a,b) <3 (0,alpha).
    Then pair /in sset(goedel,(0,alpha)).
  end.
qed.


Lemma. Forall alpha /in /Ord ((0,alpha) /in /Ord /times /Ord /\ sset(goedel,(0,alpha)) /subset Dom(Goed)  /\
Goed /upharpoonright sset(goedel,(0,alpha)) : sset(goedel,(0,alpha)) /leftrightarrow Goed[(0,alpha)]).
Proof.
  Let alpha /in /Ord.
  Then (0,alpha) /in /Ord /times /Ord /\ sset(goedel,(0,alpha)) /subset Dom(Goed).
  Goed[(0,alpha)] = Goed^[sset(goedel,(0,alpha))].
  Then Goed /upharpoonright sset(goedel,(0,alpha)) : sset(goedel,(0,alpha)) /rightarrow Goed[(0,alpha)].
  Proof.
    Dom(Goed /upharpoonright sset(goedel,(0,alpha))) = sset(goedel,(0,alpha)).
    Let pair /in sset(goedel,(0,alpha)).
    Then (Goed /upharpoonright sset(goedel,(0,alpha)))[pair] = Goed[pair].
    Goed[pair] /in Goed^[sset(goedel,(0,alpha))].
    Then (Goed /upharpoonright sset(goedel,(0,alpha)))[pair] /in Goed[(0,alpha)].
  end.
  Goed /upharpoonright sset(goedel,(0,alpha)) is injective.
  ran(Goed /upharpoonright sset(goedel,(0,alpha))) /subset Goed[(0,alpha)].
  Proof.
    Let x /in ran(Goed /upharpoonright sset(goedel,(0,alpha))).
    ran(Goed /upharpoonright sset(goedel,(0,alpha))) = {zfset z | exists zz /in sset(goedel,(0,alpha)) (Goed /upharpoonright sset(goedel,(0,alpha)))[zz] = z}.
    Take a set y such that y /in sset(goedel,(0,alpha)) /\ (Goed /upharpoonright sset(goedel,(0,alpha)))[y] = x.
    Then x /in Goed^[sset(goedel,(0,alpha))].
    Then x /in Goed[(0,alpha)].
  end.
  Goed[(0,alpha)] /subset ran(Goed /upharpoonright sset(goedel,(0,alpha))).
  Proof.
    Let x /in Goed[(0,alpha)]. Then x /in Goed^[sset(goedel,(0,alpha))].
    Take a zfset y such that y /in sset(goedel,(0,alpha)) /\ Goed[y] = x.
    Then (Goed /upharpoonright sset(goedel,(0,alpha)))[y] = x.
    Then x /in ran(Goed /upharpoonright sset(goedel,(0,alpha))).
  end.
qed.


Lemma. Forall alpha /in /Ord (alpha /times alpha, Goed[(0,alpha)] /in /VV /\ alpha /times alpha /tilde Goed[(0,alpha)]).
Proof.
  Let alpha /in /Ord.
  alpha /times alpha = sset(goedel,(0,alpha)).
  Goed /upharpoonright sset(goedel,(0,alpha)) : sset(goedel,(0,alpha)) /leftrightarrow Goed[(0,alpha)].
qed.


Lemma. Goed[(0,/NN)] = /NN.
Proof.
  /NN <= /NN /times /NN.
  Proof.
    Define f[n] = (n,0) for n in /NN.
    Then f is a zffunction.
    Proof.
      Let n /in /NN.
      Then f[n] /in /VV.
    end.
    f : /NN /rightarrow /NN /times /NN.
    f is injective.
  end.
  Then /NN <= Goed[(0,/NN)].
  Proof. 
    /NN /times /NN /tilde Goed[(0,/NN)].
    Take a zffunction f such that f : /NN /times /NN /leftrightarrow Goed[(0,/NN)].
    Take an injective zffunction g such that g : /NN /rightarrow /NN /times /NN.
    Then f /circ g is an injective zffunction.
    f /circ g : /NN /rightarrow Goed[(0,/NN)].
  end.  
  Goed[(0,/NN)] /in /Ord.
  Then Goed[(0,/NN)] = /NN \/ /NN /in Goed[(0,/NN)].

  Case Goed[(0,/NN)] = /NN. end.
  
  Case /NN /in Goed[(0,/NN)].
    Goed[(0,/NN)] = Goed^[sset(goedel,(0,/NN))].
    sset(goedel,(0,/NN)) = /NN /times /NN.
    Then /NN /in Goed^[/NN /times /NN].
    /NN /times /NN /subset Dom(Goed).
    Goed^[/NN /times /NN] = {zfset z | exists x /in /NN /times /NN (z = Goed[x])}.
    Take a zfset pair such that pair /in /NN /times /NN /\ /NN = Goed[pair].
    Take ordinals a,b such that a,b /in /NN /\ pair = (a,b).
    Then (a,b) /in Dom(Goed).
    Goed[(a,b)] = Goed^[sset(goedel,(a,b))].
    Then /NN = Goed^[sset(goedel,(a,b))].   
    a /cup b /in /Ord.
    Let c = (a /cup b) +' 1.
    sset(goedel,(a,b)) /subset c /times c.
    Proof.
      Let pair2 /in sset(goedel,(a,b)). Then pair2 /in /Ord /times /Ord.
      Take ordinals a2,b2 such that pair2 = (a2,b2).
      Then (a2,b2) <3 (a,b).
      Then a2 /cup b2 /in a /cup b \/ a2 /cup b2 = a /cup b.
      Then a2 /subset a /cup b /\ b2 /subset a /cup b.
      a2 /in c.
      b2 /in c.
      Then pair2 /in c /times c.
    end.    
    a /subset b \/ b /subset a.
    Then a /cup b = a \/ a /cup b = b.
    Then a /cup b /in /NN.
    Then c /in /NN and c is a zfset.
    Then c is finite.
    Then c /times c is finite.
    Then c /times c < /NN.
    sset(goedel,(a,b)) is a zfset.
    sset(goedel,(a,b)) /tilde /NN.
    Proof.
      sset(goedel,(a,b)) /subset Dom(Goed).
      Goed /upharpoonright sset(goedel,(a,b)) : sset(goedel,(a,b)) /leftrightarrow Goed^[sset(goedel,(a,b))].
      Proof.
        Dom(Goed /upharpoonright sset(goedel,(a,b))) = sset(goedel,(a,b)).
        ran(Goed /upharpoonright sset(goedel,(a,b))) = { zfset x | exists z /in sset(goedel,(a,b)) x = Goed[z]}.
        Goed^[sset(goedel,(a,b))] = { zfset x | exists z /in sset(goedel,(a,b)) x = Goed[z]}.
        Then ran(Goed /upharpoonright sset(goedel,(a,b))) = Goed^[sset(goedel,(a,b))].
        Proof.
          ran(Goed /upharpoonright sset(goedel,(a,b))) /subset Goed^[sset(goedel,(a,b))].
          Goed^[sset(goedel,(a,b))] /subset ran(Goed /upharpoonright sset(goedel,(a,b))).
        end.
        Goed is injective.
        Then Goed /upharpoonright sset(goedel,(a,b)) is injective.
        Proof.
          Let x,y /in Dom(Goed /upharpoonright sset(goedel,(a,b))).
          Let (Goed /upharpoonright sset(goedel,(a,b)))[x] = (Goed /upharpoonright sset(goedel,(a,b)))[y].
          (Goed /upharpoonright sset(goedel,(a,b)))[x] = Goed[x].
          (Goed /upharpoonright sset(goedel,(a,b)))[y] = Goed[y].
          Then Goed[x] = Goed[y].
          Then x = y.
        end.
      end.
      Goed^[sset(goedel,(a,b))] = /NN.
    end.    
    sset(goedel,(a,b)) <= c /times c.
    Then /NN <= c /times c.
    Then c /times c /tilde /NN.
    Contradiction.
  end.
qed.


Lemma. Forall alpha /in /Ord (Goed[(0,Alef[alpha])] = Alef[alpha]).
Proof by induction.
  Let alpha /in /Ord.
  Case alpha = 0.
    Then Alef[alpha] = /NN.
  end.
  Case alpha /neq 0.
    Goed[(0,Alef[alpha])], (Alef[alpha] /times Alef[alpha]) /in /VV.
    Goed[(0,Alef[alpha])] /tilde (Alef[alpha] /times Alef[alpha]).
  
    Alef[alpha] <= Alef[alpha] /times Alef[alpha].
    Proof.
      Define f[n] = (n,0) for n in Alef[alpha].
      Then f is a zffunction.
      Proof.
        Let n /in Alef[alpha].
        Then f[n] /in /VV.
      end.
      f : Alef[alpha] /rightarrow Alef[alpha] /times Alef[alpha].
      f is injective.
    end.
    Then Alef[alpha] <= Goed[(0,Alef[alpha])].
    Proof. 
      Alef[alpha] /times Alef[alpha] /tilde Goed[(0,Alef[alpha])].
      Take a zffunction f such that f : Alef[alpha] /times Alef[alpha] /leftrightarrow Goed[(0,Alef[alpha])].
      Take an injective zffunction g such that g : Alef[alpha] /rightarrow Alef[alpha] /times Alef[alpha].
      Then f /circ g is an injective zffunction.
      f /circ g : Alef[alpha] /rightarrow Goed[(0,Alef[alpha])].
      Proof.
        Dom(f /circ g) = Alef[alpha].
        ran(f /circ g) /subset Goed[(0,Alef[alpha])].
      end.
    end.
    
    Goed[(0,Alef[alpha])],Alef[alpha]  /in /Ord.
    Then Goed[(0,Alef[alpha])] = Alef[alpha] \/ Alef[alpha] /in Goed[(0,Alef[alpha])].
    Proof.  
      Alef[alpha] <= Goed[(0,Alef[alpha])].
      Then Alef[alpha] /subset Card(Goed[(0,Alef[alpha])]).
      Card(Goed[(0,Alef[alpha])]) /subset Goed[(0,Alef[alpha])].
      Then Alef[alpha] /subset Goed[(0,Alef[alpha])].
      Forall a,b /in /Ord (a /in b \/ b /in a \/ a = b).
      Goed[(0,Alef[alpha])],Alef[alpha]  /in /Ord.
      Take ordinals a,b such that a = Alef[alpha] /\ b = Goed[(0,Alef[alpha])].
      Then a /in b \/ b /in a \/ a = b.
      Goed[(0,Alef[alpha])] /notin Alef[alpha].
    end.
  
    Case Goed[(0,Alef[alpha])] = Alef[alpha]. end.
    
    Case Alef[alpha] /in Goed[(0,Alef[alpha])].
      Goed[(0,Alef[alpha])] = Goed^[sset(goedel,(0,Alef[alpha]))].
      sset(goedel,(0,Alef[alpha])) = Alef[alpha] /times Alef[alpha].
      Then Alef[alpha] /in Goed^[Alef[alpha] /times Alef[alpha]].
      Alef[alpha] /times Alef[alpha] /subset Dom(Goed).
      Goed^[Alef[alpha] /times Alef[alpha]] = {zfset z | exists x /in Alef[alpha] /times Alef[alpha] (z = Goed[x])}.
      Take a zfset pair such that pair /in Alef[alpha] /times Alef[alpha] /\ Alef[alpha] = Goed[pair].
      Take ordinals a,b such that a,b /in Alef[alpha] /\ pair = (a,b).
      Then (a,b) /in Dom(Goed).
      Goed[(a,b)] = Goed^[sset(goedel,(a,b))].
      Then Alef[alpha] = Goed^[sset(goedel,(a,b))].
      a /cup b /in /Ord.
      Let c = (a /cup b) +' 1.
      sset(goedel,(a,b)) /subset c /times c.
      Proof.
        Let pair2 /in sset(goedel,(a,b)). Then pair2 /in /Ord /times /Ord.
        Take ordinals a2,b2 such that pair2 = (a2,b2).
        Then (a2,b2) <3 (a,b).
        Then a2 /cup b2 /in a /cup b \/ a2 /cup b2 = a /cup b.
        Then a2 /subset a /cup b /\ b2 /subset a /cup b.
        Then a2,b2 /in c.
        Then pair2 /in c /times c.
      end.
      
      a /subset b \/ b /subset a.
      Then a /cup b = a \/ a /cup b = b.
      Then a /cup b /in Alef[alpha].
      Alef[alpha] /in /Lim.
      c = (a /cup b) ++.
      Then c /in Alef[alpha].
      Then Card(c) /in Alef[alpha].
      c /times c /tilde Card(c) /times Card(c).
      Card(c) /times Card(c) < Alef[alpha].
      Proof.
        Card(c) /in /Cd.
        /NN, Card(c) /in /Ord.
        Then /NN /in Card(c) \/ Card(c) /in /NN \/ /NN = Card(c) (by TotalOrder).
        Case Card(c) /in /NN.
          Then Card(c) /times Card(c) is finite.
          Then Card(c) /times Card(c) < /NN.
          /NN <= Alef[alpha].
          Then Card(c) /times Card(c) <= Alef[alpha].
          not (Card(c) /times Card(c) /tilde Alef[alpha]).
        end.
        Case Card(c) = /NN.
          Then Card(c) = Alef[0]. 0 /in alpha.
          Then Card(c) /in Alef[alpha].
          Goed[(0,Alef[0])] = Alef[0].
          Goed[(0,Alef[0])] /tilde Alef[0] /times Alef[0].
          Then Card(c) /times Card(c) /tilde /NN.
          Then Card(c) /times Card(c) <= Alef[alpha].
          not (Card(c) /times Card(c) /tilde Alef[alpha]).
        end.
        Case /NN /in Card(c).
          Card(c) /in /Card.
          Take an ordinal beta such that Card(c) = Alef[beta].
          Alef[beta] /in Alef[alpha].
          beta, alpha /in /Ord.
          Then beta /in alpha (by AlefIn).
          Goed[(0,Alef[beta])] = Alef[beta].
          Goed[(0,Alef[beta])] /tilde Alef[beta] /times Alef[beta].
          Then Card(c) /times Card(c) /tilde Alef[beta].
          Then Card(c) /times Card(c) <= Alef[alpha].
          not (Card(c) /times Card(c) /tilde Alef[alpha]).
        end.
      end.
      
      Then Card(Card(c) /times Card(c)) /in Alef[alpha].
      Then Card(c /times c) /in Alef[alpha].
      Then c /times c < Alef[alpha].
      
      sset(goedel,(a,b)) /tilde Alef[alpha].
      Proof.
        sset(goedel,(a,b)) /subset Dom(Goed).
        Goed /upharpoonright sset(goedel,(a,b)) : sset(goedel,(a,b)) /leftrightarrow Goed^[sset(goedel,(a,b))].
        Proof.
          Dom(Goed /upharpoonright sset(goedel,(a,b))) = sset(goedel,(a,b)).
          Goed is injective.
          sset(goedel,(a,b)) /subset Dom(Goed).
          Then Goed /upharpoonright sset(goedel,(a,b)) is an injective zffunction.
          ran(Goed /upharpoonright sset(goedel,(a,b))) = Goed^[sset(goedel,(a,b))].
        end.
        Goed^[sset(goedel,(a,b))] = Alef[alpha].
      end.
  
      sset(goedel,(a,b)) <= c /times c.
      Then Card(sset(goedel,(a,b))) /subset Card(c /times c).
      Then Card(Alef[alpha]) /subset Card(c /times c).
      Then Alef[alpha] <= c /times c.
      Contradiction.
    end.
  end.
qed.


Lemma. Forall alpha /in /Ord (Alef[alpha] /tilde Alef[alpha] /times Alef[alpha]).
Proof.
  Let alpha /in /Ord.
  Goed[(0,Alef[alpha])] = Alef[alpha].
  Goed[(0,Alef[alpha])] /tilde (Alef[alpha] /times Alef[alpha]).
qed.


Lemma. Forall kappa /in /Card (kappa /tilde kappa /times kappa).
Proof.
  Let kappa /in /Card.
  Take an ordinal alpha such that kappa = Alef[alpha].
qed.


Lemma. Forall x /in /VV (Card(x) /notin /NN => x /tilde x /times x).
Proof.
  Let x /in /VV. Let Card(x) /notin /NN.
  Take a cardinal kappa such that kappa = Card(x).
  Then x /tilde kappa.
  x /times x /tilde kappa /times kappa.
  /NN = kappa \/ /NN /in kappa.
  Then exists alpha /in /Ord kappa = Alef[alpha].
  Proof.
    Case kappa = /NN. Then kappa = Alef[0]. end.
    Case /NN /in kappa. end.
  end.
  Take an ordinal alpha such that kappa = Alef[alpha].
  Then Alef[alpha] /tilde Alef[alpha] /times Alef[alpha].
  Then kappa /tilde kappa /times kappa.
  Then x /tilde x /times x.
qed.




