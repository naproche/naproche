[read vocabulary.ftl]
[read macros.ftl]

### Sets and Classes

Let S, T denote classes.
Let X, Y denote sets.
Let x denote objects.

Lemma. Every set is a class.

Axiom. Every element of every class  is an object.

Let x \in S stand for x is an element of S.
Let x \notin S stand for x is not an element of S.

Let M, N denote classes.

Definition DefEmpty. The empty set is the set that has no elements.

Definition DefSub. A subclass of S is a class T such that every x \in T belongs
to S.

Let T \subseteq S stand for T is a subclass of S.

Axiom Extensionality. If M is a subclass of N and N is a subclass of M then
M = N.

Definition Subset. A subset of S is a set X such that X \subseteq S.

Axiom Separation. Assume that X is a set.
Let T be a subclass of X.
Then T is a set.

### Pairs and Products

Axiom. For any objects a, b, c, d if (a,b) = (c,d) then a = c and b = d.


Definition. M \times N = {(x,y) | x is an element of M and y is an element of N}.

Axiom. M \times N is a set.

Lemma. Let x, y be objects.
If (x,y) is an element of M \times N then x is an element of M and y is an
element of N.


### Functions

Lemma. Every function is a map.

Let f stand for a function.

Definition. Assume M is a subclass of the domain of f.
f[M] = { f(x) | x \in M }.

Let the image of f stand for f[Dom(f)].

Axiom Replacement. Assume M is a subset of the domain of f.
Then f[M] is a set.
