[read Formalizations/Library/L12-Cardinal_Exponentiation.ftl]


## Pretyped Variables

Let w,x,y,z,W,X,Y,Z stand for zfsets.
Let a,b,c,d,A,B,C,D,M stand for sets.
Let o,o1,o2 stand for objects.
Let alpha, beta, gamma stand for ordinals.
Let f,g,h,F,G,H stand for zffunction.
Let kappa, lambda stand for cardinals.




## Generalized Continuum Hypothesis


Signature. GCH is an atom.
Axiom. GCH iff forall kappa /in /Card 2 ^ kappa = Plus[kappa].

Lemma. Assume GCH. Then forall kappa /in /Card Gimel[kappa] = Plus[kappa].
Proof.
  Let kappa /in /Card.
  cof(kappa) /subset kappa.
  kappa /in Gimel[kappa].
  Then Plus[kappa] /subset Gimel[kappa].
  kappa ^ cof(kappa) /subset kappa ^ kappa.
  kappa ^ kappa = 2 ^ kappa.
  Proof.
    2 /subset kappa.
    kappa /subset 2 ^ kappa.
    Then kappa ^ kappa = 2 ^ kappa.
  end.
qed.

Lemma. Assume GCH. Let kappa, lambda /in /Card. Let lambda /in cof(kappa).
Then kappa ^ lambda = kappa.
Proof.
  kappa ^ 1 = kappa.
  1 /in lambda.
  kappa ^ 1 /subset kappa ^ lambda.
  Then kappa /subset kappa ^ lambda.
  
  Forall f /in ^{lambda}kappa /bigcup ran(f) /in kappa.
  Proof by contradiction. Assume the contrary.
    Take a zffunction f such that f /in ^{lambda}kappa /\ /bigcup ran(f) /notin kappa.
    Then f : lambda /rightarrow kappa.
    ran(f) /subset kappa.
    /bigcup ran(f) /subset kappa.
    /bigcup ran(f) /in /Ord.
    Proof.
      Trans(/bigcup ran(f)).
      ran(f) = f^[lambda].
      Then ran(f) /in /VV.
      Then /bigcup ran(f) /in /VV.
    end.
    Then /bigcup ran(f) = kappa.
    Proof.
      Take ordinals aa,bb such that aa = /bigcup ran(f) /\ bb = kappa.
      Then aa /in bb \/ bb /in aa \/ aa = bb.
      aa /notin bb.
      aa /subset bb.
      Then aa = bb.
    end.
    Then ran(f) /cof kappa.
      
    ran(f) = f^[lambda].
    Then Card(ran(f)) /subset Card(lambda).
    Card(ran(f)) /in cofset2(kappa).
    Then min(cofset2(kappa)) /subset lambda.
    Then cof(kappa) /subset lambda.
    Contradiction.
  end.
  
  Define M = {zffunction f | exists v /in kappa (f : lambda /rightarrow v)}.
  Then M = ^{lambda}kappa.
  Proof.
    M /subset ^{lambda}kappa.
    Proof.
      Let f /in M.
      Take a zfset v such that v /in kappa /\ f : lambda /rightarrow v.
      v /subset kappa.
      Then f : lambda /rightarrow kappa.
      Then f /in ^{lambda}kappa.
    end.
    ^{lambda}kappa /subset M.
    Proof.
      Let f /in ^{lambda}kappa.
      Then /bigcup ran(f) /in kappa.
      Take a zfset v such that v /in kappa /\ v = /bigcup ran(f).
      v is an ordinal.
      Then ran(f) /subset v+'1.
      Proof.
        Let x /in ran(f).
        Then x /subset v.
        x,v /in /Ord.
        Then x /in v+'1.
      end.
      Then f : lambda /rightarrow v+'1.
      kappa /in /Lim.
      Then v+'1 /in kappa.
      Then f /in M.      
    end.
  end.
  kappa, lambda are cardinals.
  M, ^{lambda}kappa are zfsets.
  Card(^{lambda}kappa) = kappa ^ lambda.
  Then Card(M) = kappa ^ lambda.
  
  Forall v /in kappa (^{lambda}v is a zfset).
  Define seq[v] = Card(^{lambda}v) for v in kappa.
  Then seq is a sequence of cardinals.
  Proof.
    Let v /in kappa. Then seq[v] /in /Cd.
  end.
  
  /sumset seq is a zfset.
  Card(M) /subset Card(/sumset seq).
  Proof.
    Forall v /in kappa exists f (f : ^{lambda}v /leftrightarrow Card(^{lambda}v)).
    Define bij[v] = (choose a zffunction psi such that psi : ^{lambda}v /leftrightarrow Card(^{lambda}v) in psi)
    for v in kappa.
    Forall v /in kappa forall f (f : lambda /rightarrow v => f /in Dom(bij[v])).
    Define phi[f] = (choose a zfset v such that v /in kappa /\ f : lambda /rightarrow v in ((bij[v])[f],v)) for f in M.
    Then phi : M /rightarrow /sumset seq.
    Proof.
      Let f /in M.
      Take a zfset v such that v /in kappa /\ f : lambda /rightarrow v /\ phi[f] = ((bij[v])[f],v).
      Then (bij[v])[f] /in seq[v].
      Then phi[f] /in /sumset seq.
    end.
    phi is injective.
    Proof.
      Let f1,f2 /in M. Let f1 /neq f2.
      Take a zfset v1 such that v1 /in kappa /\ f1 : lambda /rightarrow v1 /\ phi[f1] = ((bij[v1])[f1],v1).
      Take a zfset v2 such that v2 /in kappa /\ f2 : lambda /rightarrow v2 /\ phi[f2] = ((bij[v2])[f2],v2).
      Then phi[f1] /neq phi[f2].
      Proof.
        Case v1 /neq v2. Then ((bij[v1])[f1],v1) /neq ((bij[v2])[f2],v2). end.
        Case v1 = v2.
          bij[v1] is injective.
          Then (bij[v1])[f1] /neq (bij[v1])[f2].
          Then ((bij[v1])[f1],v1) /neq ((bij[v2])[f2],v2).
        end.
      end.
    end.
  end.
  
  /sumset seq /subset kappa /times kappa.
  Proof.
    Let pair /in /sumset seq.
    Take zfsets a,b such that b /in kappa /\ a /in seq[b] /\ pair = (a,b).
    seq[b] = Card(^{lambda}b).
    Card(^{lambda}b) = Card(b) ^ lambda.
    Card(b) /in kappa.
    Then Card(b) /in /Cd /cap kappa.
    Then Card(b) ^ lambda /subset kappa.
    Proof.
      Take a cardinal xi such that xi /in /Cd /cap kappa /\ xi = Card(b).
      Then xi ^ lambda /subset kappa.
      Proof.
        xi /subset 2 ^ lambda \/ 2 ^ lambda /subset xi.
        Case xi /subset 2 ^ lambda.
          Then xi ^ lambda /subset 2 ^ lambda.
          Proof.
            2 /subset xi \/ xi /subset 2.
            Case 2 /subset xi. 
            end.
            Case xi /subset 2.
              xi,2,lambda /in /Cd.
              Then xi ^ lambda /subset 2 ^ lambda (by BaseSubset).
            end.
          end.
          2 ^ lambda = Plus[lambda].
          lambda /in cof(kappa).
          Then lambda /in kappa.
          Then Plus[lambda] /subset kappa.
          Then xi ^ lambda /subset kappa.
        end.
        Case 2 ^ lambda /subset xi.
          xi,lambda /in /Card.
          lambda /subset xi.
          0 /in xi.
          Then xi ^ lambda /subset xi ^ xi (by ExpSubset).
          xi ^ xi = 2 ^ xi.
          Proof.
            2 /subset xi.
            xi /subset 2 ^ xi.
            Then xi ^ xi = 2 ^ xi.
          end.
          2 ^ xi = Plus[xi].
          Then xi ^ xi = Plus[xi].
          xi /in kappa.
          Then Plus[xi] /subset kappa.
          xi ^ lambda /subset Plus[xi].
        end.
      end. 
    end.
    Then seq[b] /subset kappa.
    Then a /in kappa.
    Then (a,b) /in kappa /times kappa.
  end.
  Then Card(/sumset seq) /subset Card(kappa /times kappa).
  Card(kappa /times kappa) = kappa * kappa.
  kappa * kappa = kappa.
  Then Card(/sumset seq) /subset kappa.
  
  Then Card(M) /subset kappa.
  Then kappa ^ lambda /subset kappa.
  
qed.



Lemma. Assume GCH. Let kappa, lambda /in /Card. Let cof(kappa) /subset lambda /\ lambda /subset kappa.
Then kappa ^ lambda = Plus[kappa].
Proof.
  Gimel[kappa] = Plus[kappa].
  kappa ^ cof(kappa) /subset kappa ^ lambda.
  kappa ^ lambda /subset kappa ^ kappa.
  kappa ^ kappa = 2 ^ kappa.
  Proof.
    2 /subset kappa.
    kappa /subset 2 ^ kappa.
    Then kappa ^ kappa = 2 ^ kappa.
  end.
qed.


Lemma. Assume GCH. Let kappa, lambda /in /Card. Let kappa /in lambda. Then kappa ^ lambda = Plus[lambda].
Proof.
  Plus[lambda] = 2 ^ lambda.
  2 ^ lambda /subset kappa ^ lambda.
  Proof.
    2, kappa, lambda /in /Cd.
    2 /subset kappa.
    Then 2 ^ lambda /subset kappa ^ lambda (by BaseSubset).
  end.
  kappa ^ lambda /subset lambda ^ lambda.
  lambda ^ lambda = 2 ^ lambda.
  Proof.
    2 /subset lambda.
    lambda /subset 2 ^ lambda.
    Then lambda ^ lambda = 2 ^ lambda (by ExpEq).
  end.
qed.



