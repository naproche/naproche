[read Formalizations/Library/L02-Cardinals_Part_1.ftl]

[prove off]

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

Lemma. Let alpha /in /Ord. Then V[alpha] is a zfset and V[alpha ++] = /PP V[alpha].

Lemma. Let lambda /in /Lim. Then V[lambda] = /bigcup V^[lambda].

Lemma. Forall alpha (forall beta /in alpha (V[beta] /in V[alpha] /\ V[beta] /subset V[alpha] /\ Trans(V[alpha]))).

Lemma. Forall alpha /in /Ord V[alpha] /cap /Ord = alpha.

Lemma. Forall x /in /VV (x /subset /bigcup ran(V) => exists beta x /subset V[beta]).

Lemma. /VV = /bigcup ran(V).


## Rank Function

Lemma. Forall x exists alpha (x /in V[alpha ++] /setminus V[alpha]).

Lemma. Exists f (Dom(f) = /VV and forall x /in /VV (f[x] /in /Ord /\ x /in V[f[x]++] /setminus V[f[x]])).

Signature. rk is a function.
Signature. rk+ is a function.

Axiom. rk : /VV /rightarrow /Ord.
Axiom. rk+ : /VV /rightarrow /Ord.

Lemma. rk, rk+ are zffunctions.

Lemma. Let x /in /VV. Then rk[x] /in /Ord.

Axiom. Let x /in /VV. Then x /in V[rk[x]++] /setminus V[rk[x]].

Lemma rank. Let x /in /VV. Let alpha /in /Ord. Let x /in V[alpha ++] /setminus V[alpha]. Then rk[x] = alpha.

Lemma. Exists f (Dom(f) = /VV and forall x /in /VV (f[x] /in /Ord /\ f[x] = rk[x] ++)).

Axiom. Forall x /in /VV rk+[x] = rk[x] ++.

Lemma. Let x /in /VV. Let rk[x] = alpha. Then x /notin V[alpha]. 

Lemma. Let x /in y. Then rk[x] /in rk[y].

Lemma. Forall x /in /VV (rk[x] = /bigcup rk+^[x]).





[prove on]
