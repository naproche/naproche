[read Formalizations/Library/L01-ZF-Sets.ftl]

[prove off]

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

Lemma. Let f and g be zffunctions. f = g iff Dom(f) = Dom(g) and forall x /in Dom(f) (f[x] = g[x]).

Lemma. Let f,g be functions. Let Dom(f) = Dom(g). Let f /neq g. Then exists x /in Dom(f) f[x] /neq g[x].

Lemma. Let f,g be zffunctions. Let Dom(f) = Dom(g). Let f /neq g. Then exists x /in Dom(f) f[x] /neq g[x].


## Function-Iteration

Signature. f ^^ n is an object.
Axiom. Let f be a zffunction and ran(f) /subset Dom(f) and n /in /NN. Then f ^^ n is a function.
Axiom. Let f be a zffunction. Let ran(f) /subset Dom(f). Let n /in /NN. Then Dom(f^^n) = Dom(f).
Axiom. Let f be a zffunction. Let ran(f) /subset Dom(f). Let x /in Dom(f). Then (f^^0)[x] = x.

Lemma. Let f be a zffunction. Let ran(f) /subset Dom(f). Then f^^0 = Id /upharpoonright Dom(f).

Axiom funcit. Let f be a zffunction. Let ran(f) /subset Dom(f). Let n /in /NN. Let x /in Dom(f). Then (f^^n)[x] /in Dom(f) /\ (f^^(n++))[x] = f[((f^^n)[x])].

Lemma. Let f be a zffunction. Let ran(f) /subset Dom(f). Then forall n /in /NN (f^^n is a zffunction).

Lemma. Let f be a zffunction. Let ran(f) /subset Dom(f). Then forall n /in /NN ((f^^n is a zffunction) /\ (ran(f^^n) /subset Dom(f))).

Lemma. Let f be a zffunction. Let ran(f) /subset Dom(f). Then (f ^^ 1) = f.

Lemma. Let f be a zffunction. Let ran(f) /subset Dom(f). Let n /in /NN. Let n /neq /emptyset. Then ran(f ^^ n) /subset ran(f).


## Ordinals

Signature. Let alpha /in /Succ. alpha -- is an ordinal.

Axiom. Let alpha /in /Succ. Let beta be a zfset. alpha -- = beta iff alpha = beta ++.
Lemma. 0 = 1 --.


## Axiom of Choice

Lemma. Exists f (Dom(f) = /VV /setminus </emptyset> /\ forall x /in /VV /setminus </emptyset> f[x] /in x).

Signature. Choice is a zffunction.

Axiom. Dom(Choice) = /VV /setminus </emptyset>.

Axiom. Forall x /in /VV /setminus </emptyset> (Choice[x] /in x).

Theorem Wellorder. Let x be a zfset. Then exists alpha exists f (f : alpha /leftrightarrow x).


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

Lemma. Let x,y be sets. Let x and y be equipotent. Let y and z be equipotent. Then x and z are equipotent.

Lemma. Let x, y be sets. x /tilde y => (x <= y /\ y <= x).

Lemma. Let x, y, z be sets. Let x <= y /\ y <= z. Then x <= z.

Lemma. Let x,y be sets. Let x /subset y. Then x <= y.

Definition. Let x be a zfset. The cardset of x is 
{ordinal alpha | exists f (f : alpha /leftrightarrow x) }.
Let Cardset(x) stand for the cardset of x.

Lemma. Let x be a zfset. Then Cardset(x) /neq /emptyset.

Definition. Let x be a zfset. The cardinality of x is min(Cardset(x)).
Let Card(x) stand for the cardinality of x.

Lemma. Let x be a zfset. The cardinality of x is an ordinal.

Lemma. Let x be a zfset. Then Card(x) /in Cardset(x).

# Comparison of Card(x) with <, <=, /tilde

Lemma. Let x, y be zfsets. Let x /tilde y. Then Card(x) = Card(y).

Lemma. Let x, y be zfsets. Let Card(x) = Card(y). Then x /tilde y.

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

Lemma. Let kappa be a cardinal. Then Card(kappa) = kappa.

Lemma. Let alpha be a cardinal. Let x /subset alpha. Then Card(x) /subset alpha.

Lemma. Let x /subset y. Then Card(x) /subset Card(y).

Lemma. Let x, y be zfset. Let x <= y. Then Card(x) /subset Card(y).

Lemma. Let x,y be zfsets. Let Card(x) /subset Card(y). Then x <= y.

Lemma. Let x, y be zfsets. Let x <= y. Let y <= x. Then Card(x) = Card(y).

Lemma. Let x, y be zfsets. Let x <= y. Let y <= x. Then x /tilde y.

Lemma. Let x,y be zfsets. Let x < y. Then Card(x) /in Card(y).

Lemma. Let x,y be zfsets. Let Card(x) /in Card(y). Then x < y.

Lemma. Let kappa be a cardinal. Let x /in kappa. Then Card(x) /in kappa.

Lemma. Let x be a zfset. Let f be a zffunction. Let x /subset Dom(f). Then Card(f^[x]) /subset Card(x).

Lemma. Forall n /in /NN Card(n) = n.

Lemma. Card (/NN) = /NN.

Lemma. Let x be a zfset. Then x < /PP x.

Lemma. /Ord is a proper class.

Lemma. /Cd is a proper class.

Lemma. Let x be a zfset. Let Card(x) = 0. Then x = /emptyset.

Lemma. Let x be a zfset. Let Card(x) = 1. Then exists y (x = <y>).




[prove on]
