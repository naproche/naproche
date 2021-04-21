[read Formalizations/Library/L05-Mostowski_Collapse.ftl]

## Pretyped Variables

Let w,x,y,z,W,X,Y,Z stand for zfsets.
Let a,b,c,d,A,B,C,D,M stand for sets.
Let o,o1,o2 stand for objects.
Let alpha, beta, gamma, delta stand for ordinals.
Let f,g,h,F,G,H stand for zffunction.
Let kappa, lambda stand for cardinals.




## Transitive Closure


Definition. Let R be a strongly wellfounded relation. Let x /subset reldomain(R). The class of transclosed sets of x resp R is
{zfset z | z /subset reldomain(R) /\ x /subset z /\ forall u /in z forall v /in sset(R,u) v /in z}.
Let TCsets(R,x) stand for the class of transclosed sets of x resp R.

Definition. Let R be a strongly wellfounded relation. Let x /subset reldomain(R). The transitive closure of x resp R is
/bigcap TCsets(R,x).
Let TC(R,x) stand for the transitive closure of x resp R.

Lemma. Let R be a strongly wellfounded relation. Let x /subset reldomain(R). Let TC(R,x) /in /VV. Then TC(R,x) /subset reldomain(R).
Proof.
  Forall y /in TCsets(R,x) y /subset reldomain(R).
  Then /bigcap TCsets(R,x) /subset reldomain(R).
qed.

Lemma. Let R be a strongly wellfounded relation. Let x /subset reldomain(R). Let TC(R,x) /in /VV. Then TC(R,x) /in TCsets(R,x).
Proof.
  TC(R,x) /subset reldomain(R).
  Forall y /in TCsets(R,x) x /subset y.
  Then x /subset TC(R,x).
  Forall y /in TCsets(R,x) forall u /in y forall v /in sset(R,u) v /in y.
  Then forall u /in TC(R,x) forall v /in sset(R,u) v /in TC(R,x).
  Proof.
    Let u /in TC(R,x).
    Forall v /in sset(R,u) v /in TC(R,x).
    Proof.
     Let v /in sset(R,u). Forall y /in TCsets(R,x) u /in y. Then forall y /in TCsets(R,x) v /in y.
     Then v /in TC(R,x).
    end.
  end.
  Then TC(R,x) /in TCsets(R,x).
qed.


Lemma. Let R be a strongly wellfounded relation. Then forall x /in /VV (x /subset reldomain(R) => TC(R,x) /in /VV).
Proof.
  R is wellfounded.
  Then (forall A ((A /neq /emptyset /\ A /subset relfield(R)) => (exists x /in A (forall y /in A (not (y - R - x)))))) (by wf).
  Then (forall A ((A /neq /emptyset /\ A /subset relfield(R)) => (exists x /in A (forall y /in sset(R,x) (y /notin A))))).
  Proof.
    Let A be a set. Let A /neq /emptyset /\ A /subset relfield(R).
    Then exists x /in A (forall y /in A (not (y - R - x))) (by wellfounded).
    Take a zfset x such that x /in A /\ forall y /in A (not (y - R - x)).
    Then forall y /in sset(R,x) (y /notin A).
  end.

  Forall x /in reldomain(R) TC(R,<x>) /in /VV.
  Proof.
    Forall x /in reldomain(R)  <x> /subset reldomain(R).
    Define phi[m] =
      Case TC(R,<m>) /in /VV -> 0,
      Case TC(R,<m>) /notin /VV -> 1
    for m in reldomain(R).
  
    Forall x /in reldomain(R) (forall y /in sset(R,x) phi[y] = 0 => phi[x] = 0).
    Proof.
      Let x /in reldomain(R). 
      Let forall y /in sset(R,x) phi[y] = 0.
      Forall y /in sset(R,x) <y> /subset reldomain(R).
      Define A = {TC(R,<y>) | y is a zfset and y /in sset(R,x)}.
      x is a zfset.
      Let z = <x> /cup /bigcup A.
      Then z /in TCsets(R,<x>).
      Proof.
        z /subset reldomain(R).
        Proof.
          Let a /in z. 
          Then a = x \/ a /in /bigcup A.
          Then a /in reldomain(R).
          Proof.
            Case a = x. end.
            Case a /in /bigcup A. 
              Take a zfset b such that b /in sset(R,x) /\ a /in TC(R,<b>).
              TC(R,<b>) /subset reldomain(R). 
              Then a /in reldomain(R).
            end.
          end.
        end.

        <x> /subset z.
      
        Forall u /in z forall v /in sset(R,u) v /in z.
        Proof.
          Let u /in z. 
          Let v /in sset(R,u). 
          v is a zfset.
          v /in z.
          Proof.
            Case u = x. 
              Then TC(R,<v>) /in A. 
              Then TC(R,<v>) /subset z.
              <v> /subset TC(R,<v>). 
              Then v /in z.
            end.
            Case u /in /bigcup A. 
              Take a zfset y such that y /in sset(R,x) /\ u /in TC(R,<y>).
              v /in sset(R,u). 
              TC(R,<y>) /in TCsets(R,<y>).
              Then forall vv /in sset(R,u) vv /in TC(R,<y>).
              Then v /in TC(R,<y>).
              TC(R,<y>) /subset /bigcup A. 
              Then v /in /bigcup A. 
              Then v /in z.
            end.
          end.
        end.
      
        z /in /VV.
        Proof.
          A /in /VV.
          Proof.
            Forall m /in sset(R,x) (m is a zfset).
            Define f[m] = TC(R,<m>) for m in sset(R,x).
            Then f is a zffunction.
            Proof.
              Let m /in sset(R,x).
              TC(R,<m>) is a zfset.
            end.
            A /subset f^[sset(R,x)].
            Proof.
              Let a /in A. 
              Take a set b such that b /in sset(R,x) /\ a = TC(R,<b>).
              Then a = f[b].
            end.
            sset(R,x) /in /VV.
            Then f^[sset(R,x)] /in /VV.
          end.

          Then /bigcup A /in /VV.
          x /in /VV.
          <x,x> = <x>.
          <x> /in /VV.
          /bigcup A is a zfset.
          < <x>, /bigcup A> /in /VV.
          z = /bigcup < <x>, /bigcup A>.
          Then z /in /VV.
        end.      
      end.
    
      TC(R,<x>) = /bigcap TCsets(R,<x>).
      Then TC(R,<x>) /subset z.
      Then TC(R,<x>) /in /VV.
    end.

    Define M = {zfset z | z /in reldomain(R) /\ phi[z] = 0}.
    Then M /subset reldomain(R).
    Let N = reldomain(R) /setminus M.
    Then N /neq /emptyset \/ N = /emptyset.
    Case N = /emptyset. 
    Then reldomain(R) /subset M. 
    M /subset reldomain(R). 
    Then reldomain(R) = M. end.
    Case N /neq /emptyset.
      Then exists x /in N (forall y /in sset(R,x) (y /notin N)).
      Proof.
        Forall B ((B /neq /emptyset /\ B /subset relfield(R)) => (exists x /in B (forall y /in sset(R,x) (y /notin B)))).
        Let B be a set. Let B = N. Then B /neq /emptyset /\ B /subset relfield(R).
      end.
      Take a zfset a such that (a /in N /\ (forall y /in sset(R,a) y /notin N)).
      Then forall y /in sset(R,a) phi[y] = 0.
      Then phi[a] = 0.
      Contradiction.
    end.
  end.

  Let x /in /VV. Let x /subset reldomain(R).
  Forall y /in x <y> /subset reldomain(R).
  Define A = {TC(R,<y>) | y /in x}.
  Let z = /bigcup A.
  Then z /in TCsets(R,x).
  Proof.
  
    z /subset reldomain(R).
    Proof.
      Let a /in z. 
      Take a zfset b such that b /in x /\ a /in TC(R,<b>).
      TC(R,<b>) /subset reldomain(R).
      Then a /in reldomain(R).
    end.
  
    x /subset z.
    Proof.
      Let a /in x. a is a zfset. 
      <a> /subset TC(R,<a>). 
      Then a /in TC(R,<a>).
      TC(R,<a>) /in A.
      Then a /in z.
    end.

    Forall u /in z forall v /in sset(R,u) v /in z.
    Proof.
      Let u /in z. 
      Take a zfset b such that b /in x /\ u /in TC(R,<b>).
      Let v /in sset(R,u).
      Then v /in TC(R,<b>).
      Proof.
        TC(R,<b>) /in TCsets(R,<b>).
        Then forall uu /in TC(R,<b>) forall vv /in sset(R,uu) vv /in TC(R,<b>).
      end.
      TC(R,<b>) /in A.
      Then v /in z.
    end.

    z /in /VV.
    Proof.
      A /in /VV.
      Proof.
        Define f[m] = TC(R,<m>) for m in x.
        f is a zffunction.
        Proof.
          Let m /in x.
          m is a zfset.
          TC(R,<m>) /in /VV.
          Then f[m] /in /VV.
        end.
        Then A /subset f^[x].
        Proof.
          Let b /in A. 
          Take a zfset c such that c /in x /\ b = TC(R,<c>).
          Then b = f[c].
        end.
        Then f^[x] /in /VV.
        Then A /in /VV.
      end.
    end.
  end.

  TC(R,x) = /bigcap TCsets(R,x).
  Then TC(R,x) /subset z.
  Then TC(R,x) /in /VV.
qed.


Definition. Let x /in /VV. The transitive closure of x is
TC(eps,x).
Let TC(x) stand for the transitive closure of x.


Lemma. Let x /in /VV. Then TC(x) /in /VV /\ x /subset TC(x) /\ Trans(TC(x)).
Proof.
  TC(x) /in /VV.
  x /subset TC(x).
  Trans(TC(x)).
  Proof.
    TC(x) /in TCsets(eps,x).
    Let a /in TC(x). Then forall b /in sset(eps,a) b /in TC(x).
    Then forall b /in a b /in TC(x).
  end.
qed.


Lemma. Let x /in /VV. Let A be a set. Let A be transitive. Let x /subset A. Then TC(x) /subset A.
Proof. 
  TC(x) /in /VV.
  A /cap TC(x) /subset TC(x).
  A /cap TC(x) /in /VV.
  x /subset TC(x).
  Then x /subset A /cap TC(x).
  Trans(A /cap TC(x)).
  Then A /cap TC(x) /in TCsets(eps,x).
  Then /bigcap TCsets(eps,x) /subset A /cap TC(x).
qed.

