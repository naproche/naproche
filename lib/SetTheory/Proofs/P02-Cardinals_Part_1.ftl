[read Formalizations/Library/L01-ZF-Sets.ftl]

## Pretyped Variables

Let w,x,y,z,W,X,Y,Z stand for zfsets.
Let a,b,c,d,A,B,C,D,M stand for sets.
Let o,o1,o2 stand for objects.
Let alpha, beta, gamma, delta stand for ordinals.
Let k,l,m,n stand for natural numbers.


## Functions

Let the domain of f stand for Dom(f).

# This is already defined
Lemma. Let f be a function. The domain of f is a set.

[synonym zffunction/-s]
Signature. A zffunction is a notion.
Axiom. Let f be a zffunction. Then f is a function.
Axiom. Let f be a function. f is a zffunction iff forall x /in Dom(f) (f[x] is a zfset).

Axiom. Let f be a zffunction. Let Dom(f) be a zfset. Then f is a zfset.

Let f,g,h,F,G,H stand for zffunction.

Definition. Let f be a zffunction. The range of f is
{f[x] | x /in Dom(f)}.
Let ran(f) stand for the range of f.

Definition. Let f be a zffunction. Let M be a set. The image of M under f is
{f[x] | x /in Dom(f) /cap M}.
Let f^[M] stand for the image of M under f.

Lemma. Let f be a zffunction. Then ran(f) = f^[Dom(f)].

Axiom Replacement. Let f be a zffunction. Let x /in /VV. Then f^[x] /in /VV.

Lemma. Let f be a zffunction. Let Dom(f) /in /VV. Then ran(f) /in /VV.

Definition. Let f be a function. Let M be a set. The functionimage of M under f is
{f[x] | x /in Dom(f) /cap M /\ f[x] /in /VV}.
Let f /caret [M] stand for the functionimage of M under f.

# Composition

Lemma. Let f and g be zffunctions. Let ran(f) /subset Dom(g). Then exists h (Dom(h) = Dom(f) and forall x /in Dom(f) h[x] = g[f[x]]).
Proof.
  Define h[x] = g[f[x]] for x in Dom(f).
  Then h is a zffunction.
  Proof.
    Let x /in Dom(f).
    Then h[x] is a zfset.
  end.
qed.

Definition. Let f and g be zffunctions. Let ran(f) /subset Dom(g). The composition of g and f is
a zffunction h such that Dom(h) = Dom(f) and forall x /in Dom(f) h[x] = g[f[x]].
Let g /circ f stand for the composition of g and f.

Lemma. Let f and g be zffunctions. Let ran(f) /subset Dom(g). Then ran(g /circ f) = g^[ran(f)].

Lemma. Let f and g be zffunctions. Let ran(f) /subset Dom(g). Let M be a set. Then (g /circ f)^[M] = g^[f^[M]].

Definition. A map from A to B is a zffunction F such that
Dom(F) = A and ran(F) /subset B.
Let F : A /rightarrow B stand for F is a map from A to B.

Definition. A partial map from A to B is a zffunction F such that
Dom(F) /subset A and ran(F) /subset B.
Let F : A /harpoonright B stand for F is a partial map from A to B.

# Restriction

Lemma. Let f be a zffunction. Let M /subset Dom(f). Then exists g (Dom(g) = M and forall x /in M /cap Dom(f) (g[x] = f[x])).
Proof.
  Define g[x] = f[x] for x in M.
  g is a zffunction.
qed.

Definition. Let f be a zffunction. Let M /subset Dom(f). The restriction of f to M is a zffunction g such that
Dom(g) = M and forall x /in M /cap Dom(f) (g[x] = f[x]).
Let f /upharpoonright M stand for the restriction of f to M.

Lemma. Let f be a zffunction. Let M /subset Dom(f). Then ran(f /upharpoonright M) = f^[M].

Lemma. Let f be a zffunction. Let M /subset Dom(f). Let A be a set. Then (f /upharpoonright M)^[A] = f^[A /cap M].

Signature. Id is a function.
Axiom. Dom(Id) = /VV.
Axiom. Forall x (Id[x] = x).
Lemma. Id is a zffunction.
Lemma. Forall M Id^[M] = M.

Definition. Let F be a zffunction. Assume F : A /rightarrow B. F is surjective from A to B
iff ran(F) = B.

# Injectivity

Definition. Let f be a zffunction. f is injective iff
forall x,y /in Dom(f) (f[x] = f[y] => x = y).

Lemma. Let f be a zffunction. Then f is injective iff forall x,y /in Dom(f) (x /neq y => f[x] /neq f[y]).

Lemma. Let f be an injective zffunction. Let M /subset Dom(f). Then f /upharpoonright M is an injective zffunction.

Lemma. Let f and g be injective zffunctions. Let ran(f) /subset Dom(g). Then g /circ f is an injective zffunction.

# Bijectivity

Definition. Let F be a zffunction. F is bijective from A to B
iff F : A /rightarrow B and Dom(F) = A and ran(F) = B and F is injective.
Let F : A /leftrightarrow B stand for F is bijective from A to B.

Lemma. Let f,g be zffunctions. Let x,y,z be sets. Let f : x /leftrightarrow y. Let g : y /leftrightarrow z. Then g /circ f : x /leftrightarrow z.

Lemma. Forall M (Id /upharpoonright M : M /leftrightarrow M).
Proof.
  Let M be a set.
  Id /upharpoonright M : M /rightarrow M.
  ran(Id /upharpoonright M) = M.
qed.

# Inverse Map

Lemma. Let f be an injective zffunction. Then exists g (Dom(g) = ran(f) and (forall x /in ran(f) forall y /in Dom(f) (g[x] = y iff f[y] = x))).
Proof.
  Forall x /in ran(f) exists y /in Dom(f) x = f[y].
  Define g[x] = (Choose a zfset y such that y /in Dom(f) /\ x = f[y] in y) for x in ran(f).
  g is a zffunction.
end.

Definition. Let f be an injective zffunction. The inverse of f is a zffunction g such that
Dom(g) = ran(f) and (forall x /in ran(f) forall y /in Dom(f) (g[x] = y iff f[y] = x)).
Let f^{-1} stand for the inverse of f.

Lemma. Let f be an injective zffunction. Then f^{-1} is an injective zffunction.

Lemma. Let f be an injective zffunction. Then ran(f^{-1}) = Dom(f).

Lemma. Let f be a zffunction. Let A,B be sets. Let f : A /leftrightarrow B. Then f^{-1} : B /leftrightarrow A.

Definition. Let A be a zfset. Let B be a set. ^{A}B = {zffunction f | f : A /rightarrow B}.

Lemma. Let A be a zfset. ^{A}/VV = {zffunction f | Dom(f) = A}.

Definition. Let f be a zffunction. Let x /in /VV. The preimage of x under f is
{y /in Dom(f) | f[y] = x}.
Let f^{-1}[[x]] denote the preimage of x under f.

# This is already defined for functions
Lemma. Let f and g be functions. f = g iff Dom(f) = Dom(g) and forall x /in Dom(f) (f[x] = g[x]).

Lemma. Let f and g be zffunctions. f = g iff Dom(f) = Dom(g) and forall x /in Dom(f) (f[x] = g[x]).
Proof.
  f,g are functions.
  Then f = g iff Dom(f) = Dom(g) and forall x /in Dom(f) (f[x] = g[x]).
qed.

Lemma. Let f,g be functions. Let Dom(f) = Dom(g). Let f /neq g. Then exists x /in Dom(f) f[x] /neq g[x].

Lemma. Let f,g be zffunctions. Let Dom(f) = Dom(g). Let f /neq g. Then exists x /in Dom(f) f[x] /neq g[x].
Proof.
  f,g are functions.
  f /neq g.
  Then exists x /in Dom(f) f[x] /neq g[x].
qed.


## Function-Iteration

Signature. f ^^ n is an object.
Axiom. Let f be a zffunction and ran(f) /subset Dom(f) and n /in /NN. Then f ^^ n is a function.
Axiom. Let f be a zffunction. Let ran(f) /subset Dom(f). Let n /in /NN. Then Dom(f^^n) = Dom(f).
Axiom. Let f be a zffunction. Let ran(f) /subset Dom(f). Let x /in Dom(f). Then (f^^0)[x] = x.

Lemma. Let f be a zffunction. Let ran(f) /subset Dom(f). Then f^^0 = Id /upharpoonright Dom(f).
Proof.
  Id /upharpoonright Dom(f), f^^0 are functions.
  Dom(Id /upharpoonright Dom(f)) = Dom(f^^0).
  Forall x /in Dom(f^^0) (f^^0)[x] = (Id /upharpoonright Dom(f))[x].
  Then f^^0 = Id /upharpoonright Dom(f).
qed.

Axiom funcit. Let f be a zffunction. Let ran(f) /subset Dom(f). Let n /in /NN. Let x /in Dom(f). Then (f^^n)[x] /in Dom(f) /\ (f^^(n++))[x] = f[((f^^n)[x])].

Lemma. Let f be a zffunction. Let ran(f) /subset Dom(f). Then forall n /in /NN (f^^n is a zffunction).
Proof by induction.
  Let n /in /NN.
  Case n = 0. 
    Then f^^n = Id /upharpoonright Dom(f).
    Then f^^n is a zffunction.
  end.
  Case n /neq 0.
    Then n /in /Succ.
    Take a natural number m such that n = m++.
    Then m /in n.
    Then m -<-n.
    Then f^^m is a zffunction.
    m /in /NN.
    Forall x /in Dom(f) ((f^^m)[x] /in Dom(f) /\ (f^^(m++))[x] = f[((f^^m)[x])]).
    Proof.
      f is a zffunction.
      ran(f) /subset Dom(f).
      m /in /NN.
      Let x /in Dom(f).
      Then ((f^^m)[x] /in Dom(f) /\ (f^^(m++))[x] = f[((f^^m)[x])]) (by funcit).
    end.
    m++ = n.
    Then forall x /in Dom(f) (f^^(n))[x] = f[((f^^m)[x])].
    Forall x /in Dom(f) f[((f^^m)[x])] /in /VV.
    Then forall x /in Dom(f^^n) (f^^(n))[x] /in /VV.
    Then f^^n is a zffunction.
  end.
qed.

Lemma. Let f be a zffunction. Let ran(f) /subset Dom(f). Then forall n /in /NN ((f^^n is a zffunction) /\ (ran(f^^n) /subset Dom(f))).
Proof.
  Forall n /in /NN (f^^n is a zffunction).
  Forall n /in /NN (ran(f^^n) /subset Dom(f)).
  Proof by induction. end.
qed.

Lemma. Let f be a zffunction. Let ran(f) /subset Dom(f). Then (f ^^ 1) = f.
Proof.
  f, (f ^^ 1) are functions.
  Dom(f) = Dom((f^^1)).
  Forall x /in Dom(f) (f[x] = (f ^^ 1)[x]).
  Proof.
    Let x /in Dom(f).
    Then (f^^1)[x] = f[((f^^0)[x])].
    Proof. 1 = 0++.
      Then (f^^1)[x] = (f^^(0++))[x].
      Forall n /in /NN (f^^(n++))[x] = f[((f^^n)[x])].
    end.
    f[(f^^0)[x]] = f[x].
    Then (f^^1)[x] = f[x].
  end.
  Then f = f^^1.
qed.

Lemma. Let f be a zffunction. Let ran(f) /subset Dom(f). Let n /in /NN. Let n /neq /emptyset. Then ran(f ^^ n) /subset ran(f).
Proof.
  Forall k /in /NN forall x /in Dom(f) ((f^^k)[x] /in Dom(f) /\ (f^^(k++))[x] = f[((f^^k)[x])]). 
  Take an ordinal m such that n = m++. Then m /in /NN. Let x /in Dom(f). Then (f^^(m++))[x] = f[((f^^m)[x])].
qed.



## Ordinals

Signature. Let alpha /in /Succ. alpha -- is an ordinal.

Axiom. Let alpha /in /Succ. Let beta be a zfset. alpha -- = beta iff alpha = beta ++.
Lemma. 0 = 1 --.



## Axiom of Choice

# (Global) Choice is already integrated

Lemma. Exists f (Dom(f) = /VV /setminus </emptyset> /\ forall x /in /VV /setminus </emptyset> f[x] /in x).
Proof.
  Define f[x] = (Choose a zfset y such that y /in x in y) for x in /VV /setminus </emptyset>.
  f is a zffunction.
qed.

Signature. Choice is a zffunction.
Axiom. Dom(Choice) = /VV /setminus </emptyset>.
Axiom. Forall x /in /VV /setminus </emptyset> (Choice[x] /in x).

Theorem Wellorder. Let x be a zfset. Then exists alpha exists f (f : alpha /leftrightarrow x).
Proof.
  Forall A x /setminus A /in /VV.
  Define f[beta] =
    Case x /setminus f /caret [beta] = /emptyset -> x,
    Case (x /setminus f /caret [beta]) /in /VV /setminus </emptyset> -> Choice[x /setminus f /caret [beta]]
  for beta in /Ord.
  Forall beta /in /Ord (f[beta] /in x \/ f[beta] = x).
  Proof.
    Forall beta x /setminus f /caret [beta] /in /VV.
    Then forall beta (x /setminus f /caret [beta] = /emptyset \/ (x /setminus f /caret [beta]) /in /VV /setminus </emptyset>).
    Let beta /in /Ord.
    Then f[beta] /in x \/ f[beta] = x.
    Proof.
      Case x /setminus f /caret [beta] = /emptyset. end.
      Case (x /setminus f /caret [beta]) /in /VV /setminus </emptyset>. end.
    end.
  end.
  f is a zffunction.
  Proof.
    Let beta /in /Ord.
    Then f[beta] /in /VV.
  end.
  Exists beta (f[beta] = x).
  Proof by contradiction. Assume the contrary.
    Then forall beta /in /Ord f[beta] /neq x.
    Then f : /Ord /rightarrow x.
    Proof.
      Let beta /in /Ord.
      Then f[beta] /in x.
    end.
    f is injective.
    Proof.
      Let a,b /in /Ord.
      Let a /neq b.
      Then a /in b \/ b /in a.
      Then f[a] /neq f[b].
      Proof.
        Case a /in b.
          (x /setminus f /caret [b]) /in /VV /setminus </emptyset>.
          Then f[b] = Choice[x /setminus f /caret [b]].
          a /in b.
          Then f[a] /in f /caret [b].
          Then f[a] /notin x /setminus f /caret [b].
          Then f[a] /neq f[b].
        end.
        Case b /in a.
          (x /setminus f /caret [a]) /in /VV /setminus </emptyset>.
          Then f[a] = Choice[x /setminus f /caret [a]].
          b /in a.
          Then f[b] /in f /caret [a].
          Then f[b] /notin x /setminus f /caret [a].
          Then f[b] /neq f[a].        
        end.
      end.
    end.
    Let y = ran(f).
    Then f : /Ord /leftrightarrow y.
    Then f^{-1} : y /leftrightarrow /Ord.
    y /subset x.
    Then y /in /VV.
    Then (f^{-1})^[y] /in /VV.
    (f^{-1})^[y] = /Ord.
    Then /Ord /in /VV.
    Contradiction.
  end.
  Define B = {ordinal beta | f[beta] = x}.
  B /neq /emptyset.
  Take an ordinal alpha such that alpha /in B /\ forall beta /in alpha beta /notin B.
  Let g = f /upharpoonright alpha.
  Then g : alpha /rightarrow x.
  Proof.
    Let beta /in alpha.
    Then g[beta] = f[beta].
    beta /notin B.
    Then f[beta] /neq x.
    Then f[beta] /in x.
    Then g[beta] /in x.
  end.
  g is injective.
  Proof.
    Let a,b /in alpha.
    Then a,b /notin B.
    Let a /neq b.
    Then a /in b \/ b /in a.
    f[a] /neq f[b].
    Proof.
      Case a /in b.
        (x /setminus f /caret [b]) /in /VV /setminus </emptyset>.
        Then f[b] = Choice[x /setminus f /caret [b]].
        a /in b.
        Then f[a] /in f /caret [b].
        Then f[a] /notin x /setminus f /caret [b].
        Then f[a] /neq f[b].
      end.
      Case b /in a.
        (x /setminus f /caret [a]) /in /VV /setminus </emptyset>.
        Then f[a] = Choice[x /setminus f /caret [a]].
        b /in a.
        Then f[b] /in f /caret [a].
        Then f[b] /notin x /setminus f /caret [a].
        Then f[b] /neq f[a].        
      end.
    end.
    f[a] = g[a].
    f[b] = g[b].
    Then g[a] /neq g[b].
  end.
  ran(g) = x.
  Proof.
    ran(g) /subset x.
    ran(g) = g^[alpha].
    Forall i /in alpha f[i] = g[i].
    g^[alpha] = f^[alpha].
    f[alpha] = x.
    Then x /setminus f /caret [alpha] = /emptyset.
    Proof by contradiction. Assume the contrary.
      Then (x /setminus f /caret [alpha]) /in /VV /setminus </emptyset>.
      Then f[alpha] = Choice[x /setminus f /caret [alpha]].
      Then f[alpha] /in x.
      Then f[alpha] /neq x.
      Contradiction.
    end.
    Then x /subset f /caret [alpha].
    f /caret [alpha] /subset f^[alpha].
    Then x /subset ran(g).
  end.
  Then g : alpha /leftrightarrow x.
qed.


## Cardinals

Definition. Let x, y be sets. x and y are equipotent iff
exists f (f : x /leftrightarrow y).
Let x /tilde y stand for x and y are equipotent.

Definition. Let x, y be sets. x has cardinality at most that of y iff
exists f (f : x /rightarrow y /\ (f is injective)).
Let x <= y stand for x has cardinality at most that of y.

Definition. Let x, y be sets. x has smaller cardinality than y iff
(x <= y) /\ not (x /tilde y).
Let x < y stand for x has smaller cardinality than y.

Lemma.  Let x,y be sets. Let x and y be equipotent. Then y and x are equipotent.
Proof. Take a zffunction f such that f : x /leftrightarrow y.
  Then f^{-1} : y /leftrightarrow x.
qed.

Lemma. Let x,y be sets. Let x and y be equipotent. Let y and z be equipotent. Then x and z are equipotent.
Proof. Take a zffunction f such that f : x /leftrightarrow y.
  Take a zffunction g such that g : y /leftrightarrow z.
  Then g /circ f : x /leftrightarrow z.
  Proof.  g /circ f is a function.
    g /circ f is injective.
   Dom(g /circ f) = x.
   ran (g /circ f) = z.
  end.
qed.

Lemma. Let x, y be sets. x /tilde y => (x <= y /\ y <= x).
Proof.
  Let x /tilde y. Take a zffunction f such that f : x /leftrightarrow y.
  Then x <= y.
  f^{-1} : y /leftrightarrow x.
  Then y <= x.
qed.

Lemma. Let x, y, z be sets. Let x <= y /\ y <= z. Then x <= z.
Proof.
  Take an injective zffunction f such that f : x /rightarrow y.
  Take an injective zffunction g such that g : y /rightarrow z.
  Then g /circ f : x /rightarrow z.
  g /circ f is injective.
qed.

Lemma. Let x,y be sets. Let x /subset y. Then x <= y.
Proof.
  Define f[n] = n for n in x.
  Then f is a zffunction.
  f : x /rightarrow y. 
  f is injective.
qed.

Definition. Let x be a zfset. The cardset of x is 
{ordinal alpha | exists f (f : alpha /leftrightarrow x) }.
Let Cardset(x) stand for the cardset of x.

Lemma. Let x be a zfset. Then Cardset(x) /neq /emptyset.

Definition. Let x be a zfset. The cardinality of x is min(Cardset(x)).
Let Card(x) stand for the cardinality of x.

Lemma. Let x be a zfset. The cardinality of x is an ordinal.
Proof. 
  Cardset(x) /subset /Ord.
qed.

Lemma. Let x be a zfset. Then Card(x) /in Cardset(x).
Proof. Card(x) is an ordinal.
  Cardset(x) /subset /Ord.
  min(Cardset(x)) /in Cardset(x).
qed.


# Comparison Card(x) with <, <=, /tilde

Lemma. Let x, y be zfsets. Let x /tilde y. Then Card(x) = Card(y).
Proof.
  Take an ordinal alpha such that alpha = Card(x).
  Take an ordinal beta such that beta = Card(y).
  Then alpha /in beta \/ beta /in alpha \/ alpha = beta.

  Take a zffunction f such that f : alpha /leftrightarrow x.
  Take a zffunction g such that g : beta /leftrightarrow y.
  Take a zffunction h such that h : x /leftrightarrow y.

  Then h /circ f : alpha /leftrightarrow y.
  Proof.
    Dom(h /circ f) = alpha.
    ran(h /circ f) = y.
    h /circ f is injective.
  end.
  Then Card(y) /subset alpha.

  Then h^{-1} /circ g : beta /leftrightarrow x.
  Proof.
    Dom(h^{-1} /circ g) = beta.
    ran(h^{-1} /circ g) = x.
    h^{-1} /circ g is injective.
  end.
  Then Card(x) /subset beta.

  Then alpha = beta.
qed.


Lemma. Let x, y be zfsets. Let Card(x) = Card(y). Then x /tilde y.
Proof.
  Take an ordinal kappa such that kappa = Card(x).
  Take a zffunction f such that f : kappa /leftrightarrow x.
  Take a zffunction g such that g : kappa /leftrightarrow y.
  Then f^{-1} : x /leftrightarrow kappa.
  Then g /circ f^{-1} : x /leftrightarrow y.
  Proof.
    g /circ f^{-1} : x /rightarrow y.
    g /circ f^{-1} is injective.
    ran(g /circ f^{-1}) = y.
  end.
qed.


[synonym cardinal/-s]
Signature. A cardinal is a notion.

Axiom. Let kappa be a cardinal. Then kappa is an ordinal.
Axiom. Let kappa be an ordinal. kappa is a cardinal iff exists x (kappa = Card(x)).

Let kappa stand for a cardinal.

Definition. The class of cardinals is
{ordinal alpha | alpha is a cardinal}.
Let /Cd stand for the class of cardinals.

Definition. The class of infinite cardinals is
{ordinal alpha | (alpha is a cardinal) /\ /NN /subset alpha}.
Let /Card stand for the class of infinite cardinals.

Lemma. Card(/emptyset) = /emptyset.

Lemma. Let alpha be an ordinal. Then Card(alpha) /subset alpha.
Proof. 
  Id /upharpoonright alpha : alpha /leftrightarrow alpha.
qed.

Lemma. Let kappa be a cardinal. Then Card(kappa) = kappa.
Proof. Card(kappa) /subset kappa.
  Then Card(kappa) /in kappa \/ Card(kappa) = kappa.
  Take a zfset x such that kappa = Card(x).
  Take a zffunction f such that f : kappa /leftrightarrow x.
  Take a zffunction g such that g : Card(kappa) /leftrightarrow kappa.
  Then f /circ g : Card(kappa) /leftrightarrow x.
  Proof. Dom(f /circ g) = Card(kappa).
    ran(f /circ g) = x.
    f /circ g is injective.
  end.
  Then Card(x) /subset Card(kappa).
qed.


Lemma. Let alpha be a cardinal. Let x /subset alpha. Then Card(x) /subset alpha.
Proof by contradiction. Assume the contrary. Then Card(alpha) /in Card(x).
  Forall n /in /Ord n++ /in /Ord.
  Define gg[n] = gg[n++] for n in /Ord.
  Define f[n] = f /caret [n /cap x] for n in x.
  # This definition is possible due to the integrated recursive function definition
  Then Dom(f) = x.
  Then f is a zffunction.
  Proof.
    Forall n /in x f[n] /in /VV.
    Proof by induction.
      Let n /in x.
      Forall m /in n /cap x f[m] /in /VV.
      Define g[m] = f[m] for m in n /cap x.
      Then g is a zffunction.
      n /cap x /subset x.
      n /cap x /in /VV.
      Then g^[n /cap x] /in /VV.
      f /caret [n /cap x] = g^[n /cap x].
      f[n] = f /caret [n /cap x].
      Then f[n] /in /VV.
    end.
  end.
  Forall n /in x f[n] = f^[n /cap x].
  Proof.
    f is a zffunction.
    Then forall a f /caret [a] = f^[a].
    Let n /in x. Then f[n] = f^[n /cap x].
  end.

  Take a zfset zero such that (zero /in x /\ forall c /in zero (c /notin x)).
  Then f[zero] = /emptyset.

  Forall y /in x f[y] /in /Ord.
  Proof by induction.
    Let y /in x.
    f[y] = f^[y /cap x].
    Forall z /in y /cap x f[z] /in /Ord.
    Then f[y] /subset /Ord.
    f[y] /in /VV.
    Trans(f[y]).
    Proof.
      Let a /in f[y].
      Let b /in a.
      Take a zfset c such that c /in y /cap x /\ a = f[c].
      Then a = f^[c /cap x].
      Take a zfset d such that d /in c /cap x /\ b = f[d].
      Then b /in f[y].
    end.
    Forall z /in f[y] Trans(z).
    Then f[y] /in /Ord.
  end.

  Then ran(f) /subset /Ord.
  ran(f) /in /VV.
  Forall a /in ran(f) forall b /in a (b /in ran(f)).
  Proof.
    Let a /in ran(f). Take a zfset z1 such that z1 /in x /\ a = f[z1].
    Let b /in a. Then b /in f[z1]. f[z1] = f^[z1 /cap x].
    Take a zfset z2 such that z2 /in (z1 /cap x) /\ b = f[z2].
    Then b /in ran(f).
  end.
  Then Trans(ran(f)).
  Forall a /in ran(f) Trans(a).
  Then ran(f) /in /Ord.
  
  Forall y,z /in x (y /neq z => f[y] /neq f[z]).
  Proof. let y, z /in x. Let y /neq z.
    Then y /in z \/ z /in y.
    f[y] /neq f[z].
    Proof by contradiction. Assume the contrary.
      Then f[y] = f[z].
      Forall c (c /notin c).
      Case y /in z. Then f[y] /in f[z]. Then f[y] /in f[y]. Contradiction. end.
      Case z /in y. Then f[z] /in f[y]. Then f[z] /in f[z]. Contradiction. end.
      Contradiction.
    end.
  end.
 
  f : x /leftrightarrow ran(f).

  Forall y /in x f[y] /subset y.
  Proof by induction.
    Let y /in x.
    Then forall z /in y /cap x f[z] /subset z.
    Then forall z /in y /cap x f[z] /in y.
    f[y] = f^[y /cap x].
    Then f[y] /subset y.
  end.

  Then ran(f) /subset alpha.
 
  f^{-1} : ran(f) /leftrightarrow x.

  Then Card(x) /subset ran(f).
  Then Card(x) /subset alpha.
qed.



Lemma. Let x /subset y. Then Card(x) /subset Card(y).
Proof.
  Take cardinals alpha, beta such that alpha = Card(x) /\ beta = Card(y).
  Take a zffunction f such that f : alpha /leftrightarrow x.
  Take a zffunction g such that g : beta /leftrightarrow y.
  Then g^{-1} : y /leftrightarrow beta.
  Then (g^{-1}) /circ f : alpha /rightarrow beta.

  Define h[n] = ((g^{-1}) /circ f)[n] for n in alpha.
  Then h is a zffunction.
  Then h = (g^{-1}) /circ f.
  Proof. Dom(h) = Dom((g^{-1}) /circ f).
    Forall z /in Dom(h) h[z] = ((g^{-1}) /circ f)[z].
  end.

  Then h : alpha /rightarrow beta.
  Then ran(h) /subset beta.
  h : alpha /leftrightarrow ran(h).
  h^{-1} : ran(h) /leftrightarrow alpha.
  Then Card(ran(h)) /subset beta.

  Take a cardinal gamma such that gamma = Card(ran(h)).
  Take a zffunction i such that i : gamma /leftrightarrow ran(h).
  Then (h^{-1}) /circ i : gamma /leftrightarrow alpha.
  Proof.
    Dom((h^{-1}) /circ i) = gamma.
    ran((h^{-1}) /circ i) = alpha.
    (h^{-1}) /circ i is injective.
  end.

  Define j[n] = ((h^{-1}) /circ i)[n] for n in gamma.
  Then j is a zffunction.
  Then j = (h^{-1}) /circ i.
  Proof. Dom(j) = Dom((h^{-1}) /circ i).
    Forall z /in Dom(j) j[z] = ((h^{-1}) /circ i)[z].
  end.

  Then j : gamma /leftrightarrow alpha.
  Then f /circ j : gamma /leftrightarrow x.
  Proof.
    Dom(f /circ j) = gamma.
    ran(f /circ j) = x.
    f /circ j is injective.
  end.
  Then Card(x) /subset gamma.
  Then Card(x) /subset beta.
qed.


Lemma. Let x, y be zfset. Let x <= y. Then Card(x) /subset Card(y).
Proof.
  Take an injective zffunction f such that f : x /rightarrow y.
  Then f : x /leftrightarrow ran(f).
  Then Card(x) = Card(ran(f)).
  ran(f) /subset y.
  Then Card(ran(f)) /subset Card(y).
  Then Card(x) /subset Card(y).
qed.


Lemma. Let x,y be zfsets. Let Card(x) /subset Card(y). Then x <= y.
Proof.
  Take a zffunction f such that f : x /leftrightarrow Card(x).
  Take a zffunction g such that g : Card(y) /leftrightarrow y.
  Then g /circ f : x /rightarrow y.
  g /circ f is injective.
qed.


Lemma. Let x, y be zfsets. Let x <= y. Let y <= x. Then Card(x) = Card(y).
Proof.
  Card(x) /subset Card(y).
  Card(y) /subset Card(x).
qed.


Lemma. Let x, y be zfsets. Let x <= y. Let y <= x. Then x /tilde y.
Proof.
  Take a zffunction f such that f : Card(x) /leftrightarrow x.
  Take a zffunction g such that g : Card(y) /leftrightarrow y.
  Card(x) = Card(y).
  g : Card(x) /leftrightarrow y.
  f^{-1} : x /leftrightarrow Card(x).
  Then g /circ f^{-1} : x /leftrightarrow y.
  Proof.
    g /circ f^{-1} : x /rightarrow y.
    ran(g /circ f^{-1}) = y.
    g /circ f^{-1} is injective.
  end.
qed.


Lemma. Let x,y be zfsets. Let x < y. Then Card(x) /in Card(y).
Proof.
  Card(x) /subset Card(y).
  Then Card(x) /in Card(y) \/ Card(x) = Card(y).
  Card(x) /neq Card(y).
qed.


Lemma. Let x,y be zfsets. Let Card(x) /in Card(y). Then x < y.
Proof.
  Card(x) /subset Card(y).
qed.


Lemma. Let kappa be a cardinal. Let x /in kappa. Then Card(x) /in kappa.


Lemma. Let x be a zfset. Let f be a zffunction. Let x /subset Dom(f). Then Card(f^[x]) /subset Card(x).
Proof.
  Forall n /in f^[x] exists y /in x (f[y] = n).
  Define g[n] = (Choose a zfset y such that y /in x /\ f[y] = n in y) for n in f^[x].
  g is a zffunction.
  Proof.
    Let n /in f^[x].
    Then g[n] /in /VV.
  end.
  Then g : f^[x] /rightarrow x.
  g is injective.
  Then f^[x] <= x.
qed.



Lemma. Forall n /in /NN Card(n) = n.
Proof by induction.
  Let n /in /NN.
  Then Card(n) /subset n.
  Proof.
    Id /upharpoonright n : n /leftrightarrow n.
    Then n /in Cardset(n).
    Then Card(n) /subset n.
  end.
  Then Card(n) /in n \/ Card(n) = n.
  Case Card(n) = n. end.
  Case Card(n) /in n.
    Take an ordinal m such that Card(n) = m.
    Take a zffunction f such that f : m /leftrightarrow n.
    Let n1 = n--.
    Then n1 /in n.
    Take a set i  such that (i /in m /\ f[i] = n1).
    m /neq /emptyset.
    m /in /NN.
    Let m1 = m--.
    Then m1 /in m.
    Case i = m1.
      Let g = f /upharpoonright (m1).
      Then g : (m1) /leftrightarrow n1.
      Proof. 
        g : (m1) /rightarrow n.
        Proof.
          Let a /in m1.
          Then f[a] /in n.
          f[a] = g[a].
          Then g[a] /in n.
        end.
        Forall a /in m1 g[a] = f[a].
        Then ran(g) = f^[m1].
        Forall j /in (m1) f[j] /neq n1.
        Proof by contradiction. Assume the contrary. 
          Take j /in (m1) such that f[j] = n1.
          Then j /neq i. f[i] = f[j] = n1. Contradiction.
        end.
        Then n1 /notin ran(g).
        Then ran(g) /subset n1.
        Proof.
          ran(g) /subset n.
          n = n1 ++.
        end.
        g is injective.
        ran(g) = n1.
        Proof. Let alpha /in n1. Take j /in m such that (f[j] = alpha).
          Then j /neq (m1).
          Then j /in (m1).
          Then alpha /in f^[m1].
          Then alpha /in ran(g).
        end.
      end.
      n1 is a zfset.
      m1 /in Cardset(n1).
      Then Card(n1) /subset (m1).
      Then Card(n1) /in n1.
      Then Card(n1) /neq n1.
      Contradiction.
    end.

    Case i /neq (m1).
      Then i /in (m1).
      Define g[j] =
        Case i /neq j -> f[j],
        Case i = j -> f[m1]
      for j in (m1).
      Then g is a zffunction.
      Then g : (m1) /leftrightarrow n1.
      Proof.
        g : (m1) /rightarrow n.
        Proof.
          Dom(g) = m1.
          Forall j /in (m1) g[j] /in n.
        end.
        ran(g) = {f[j] | j /in m /\ j /neq i}.
        Forall j /in m (j /neq i => f[j] /neq n1).
        Then ran(g) /subset n1.
        Proof.
          ran(g) /subset n.
          n = n1 ++.
          n1 /notin ran(g).
        end.
        ran(g) = n1.
        Forall j,k /in (m1) (g[j] = g[k] => j = k).
        Proof.
          Let j,k /in (m1). Let g[j] = g[k].
          Case j /neq i /\ k /neq i.
            Then g[j] = f[j] /\ g[k] = f[k].
            Then j = k.
          end.
          Case j = i.
            Then g[k] = f[m1].
            Assume the contrary. Let k /neq i.
            Then f[k] = f[m1] /\ k /in (m1).
            Then k /neq (m1).
            f is injective.
            Contradiction.
          end.
          Case k = i.
            Then g[j] = f[m1].
            Assume the contrary. Let j /neq i.
            Then f[j] = f[m1] /\ j /in (m--).
            f is injective.
            j /neq (m1).
            Contradiction.
          end.
        end.
        Then g is injective.
      end.
      n1 is a zfset.
      m1 /in Cardset(n1).
      Then Card(n1) /subset (m1).
      Then Card(n1) /in n1.
      Contradiction.
    end.
  end.
qed.


Lemma. Card (/NN) = /NN.
Proof.
  Card(/NN) /subset /NN.
  Card(/NN) /in /NN \/ Card(/NN) = /NN.
  Case Card(/NN) = /NN. end.
  Case Card(/NN) /in /NN. Take an ordinal n such that Card(/NN) = n.
    Take a zffunction f such that f : n /leftrightarrow /NN.
    n ++ /subset /NN.
    Then Card(n ++) /subset Card(/NN).
    Card(n ++) = n++.
    Contradiction.
  end.
qed.


Lemma. Let x be a zfset. Then x < /PP x.
Proof.
  x <= /PP x.
  Proof.
    Define f[n] = <n> for n in x.
    Then f is a zffunction.
    Proof.
      Let n /in x.
      Then f[n] /in /VV.
    end.
    Then f : x /rightarrow /PP x and f is injective.
  end.
  not (x /tilde /PP x).
  Proof by contradiction. Assume the contrary.
    Then x /tilde /PP x.
    Take a zffunction f such that f : x /leftrightarrow /PP x.
    Define C = {zfset u | u /in x /\ u /notin f[u]}.
    C /subset x.
    Then C /in ran(f).
    Take a zfset u such that u /in x /\ C = f[u].
    Then u /in C iff u /notin C.
    Contradiction.
  end.
qed.

Lemma. /Ord is a proper class.
Proof by contradiction. Assume the contrary. 
  Then /Ord /in /VV.
  Trans(/Ord).
  Then /Ord /in /Ord.
  Forall x /in /VV (x /notin x).
  Contradiction.
qed.

Lemma. /Cd is a proper class.
Proof by contradiction. Assume the contrary. 
  Then /Cd /in /VV.
  Then /bigcup /Cd /in /VV.
  /Ord /subset /bigcup /Cd.
  Proof.
    Let alpha /in /Ord. Then alpha /tilde Card(alpha).
    Then alpha < Card(/PP alpha).
    Proof.
      alpha <= Card(alpha). Card(alpha) <= Card(/PP alpha). Then alpha <= Card(/PP alpha).
    end.
    Then alpha /in Card(/PP alpha).
    Proof.
      Forall a, b /in /Ord (a /in b \/ b /in a \/ a = b).
      alpha, Card(/PP alpha) /in /Ord.
      Then alpha /in Card(/PP alpha) \/ Card(/PP alpha) /in alpha \/ alpha = Card(/PP alpha).
      Then alpha /in Card(/PP alpha).
      Proof.
        Case alpha /in Card(/PP alpha). end.
        Case alpha = Card(/PP alpha). Then alpha /tilde Card(/PP alpha). Contradiction. end.
        Case Card(/PP alpha) /in alpha. Then Card(/PP alpha) /subset alpha. 
          Then Card(/PP alpha) <= alpha. Then Card(/PP alpha) /tilde alpha. Contradiction. 
        end.
      end.
    end.
    Then alpha /in /bigcup /Cd.
  end.
  Then /Ord /in /VV.
  Contradiction.
qed.

Lemma. Let x be a zfset. Let Card(x) = 0. Then x = /emptyset.

Lemma. Let x be a zfset. Let Card(x) = 1. Then exists y (x = <y>).
Proof.
  Take a zffunction f such that f : 1 /leftrightarrow x.
  Then x = <f[0]>.
qed.

