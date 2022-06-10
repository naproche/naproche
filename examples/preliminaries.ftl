[read axioms.ftl]
[read vocabulary.ftl]
[read macros.ftl]


### Sets and Classes

Let S, T denote classes.

Let x \neq y stand for x and y are not equal.
Let x \in S stand for x is an element of S.
Let x \notin S stand for x is not an element of S.

Definition DefEmpty. The empty set is the set that has no elements.

Definition DefSub. A subclass of S is a class T such that every x \in T belongs
to S.

Let T \subseteq S stand for T is a subclass of S.

Let a proper subclass of S stand for a subclass T of S such that T \neq S.

Lemma Extensionality. If S is a subclass of T and T is a subclass of S then
S = T.

Definition Subset. A subset of S is a set X such that X \subseteq S.

Let a proper subset of S stand for a subset X of S such that X \neq S.

Axiom Separation. Assume that X is a set.
Let T be a subclass of X.
Then T is a set.

Definition. The intersection of S and T is {x in S | x \in T}.

Let S \cap T stand for the intersection of S and T.

Definition. The union of S and T is {x | x \in S \/ x \in T}.

Let S \cup T stand for the union of S and T.

Definition. The set difference of S and T is {x in S | x \notin T}.

Let S \ T stand for the set difference of S and T.

Definition. S is disjoint from T iff there is no element of S that is an
element of T.

Definition. A family is a set F such that every element of F is a set.

Definition. A disjoint family is a family F such that X is disjoint from Y for
all nonequal elements X, Y of F.


### Pairs and Products

Axiom. For any objects a, b, c, d if (a,b) = (c,d) then a = c and b = d.


Definition. S \times T = {(x,y) | x is an element of S and y is an element of T}.

Axiom. Let X, Y be sets.
X \times Y is a set.

Lemma. Let x, y be objects.
If (x,y) is an element of S \times T then x is an element of S and y is an
element of T.


### Functions and maps

Let f stand for a map.

Axiom. Assume that Dom(f) is a set and f(x) is an object for any element x of
Dom(f).
Then f is a function.

Definition. Assume S is a subclass of the domain of f.
f[S] = {f(x) | x \in S}.

Let the image of f stand for f[Dom(f)].

Definition. f maps elements of S to elements of T iff Dom(f) = S and f[S]
\subseteq T.

Let f : S \rightarrow T stand for f maps elements of S to elements of T.

Axiom Replacement. Assume M is a subset of the domain of f.
Then f[M] is a set.

Let g retracts f stand for g(f(x)) = x for all elements x of Dom(f).
Let h sections f stand for f(h(y)) = y for all elements y of Dom(h).

Definition. f : S \leftrightarrow T iff f : S \rightarrow T and there exists a
map g such that g : T \rightarrow S and g retracts f and g sections f.
