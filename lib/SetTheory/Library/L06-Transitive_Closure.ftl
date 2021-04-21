[read Formalizations/Library/L05-Mostowski_Collapse.ftl]

[prove off]

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

Lemma. Let R be a strongly wellfounded relation. Let x /subset reldomain(R). Let TC(R,x) /in /VV. Then TC(R,x) /in TCsets(R,x).

Lemma. Let R be a strongly wellfounded relation. Then forall x /in /VV (x /subset reldomain(R) => TC(R,x) /in /VV).

Definition. Let x /in /VV. The transitive closure of x is
TC(eps,x).
Let TC(x) stand for the transitive closure of x.

Lemma. Let x /in /VV. Then TC(x) /in /VV /\ x /subset TC(x) /\ Trans(TC(x)).

Lemma. Let x /in /VV. Let A be a set. Let A be transitive. Let x /subset A. Then TC(x) /subset A.



[prove on]


