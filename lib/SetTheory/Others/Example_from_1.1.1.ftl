Let x \in y stand for x is an element of y.
Let x \notin y stand for x is not an element of y.
Let x \neq y stand for x != y.

Let v stand for an object.
Let x,A,B stand for sets.

Definition. A subset of A is a set B such that
forall v (v \in B => v \in A).
Let B \subseteq A stand for B is a subset of A.

Definition. Let p be an object. The singleton of p is
{object v | v = p}.
Let <p> stand for the singleton of p.

Definition. The power set of A is
{set x | x \subseteq A}.
Let \PP(A) stand for the power set of A.

[synonym map/-s]
Signature. A map is a notion.
Let f denote a map.

Signature. The domain of f is an object.
Let \dom(f) denote the domain of f.

Axiom. The domain of f is a set.

Signature. Let x \in \dom(f). f(x) is an object.

Definition. f is injective iff
forall x,y \in \dom(f) (f(x) = f(y) => x = y).

Definition. f is from A to B iff
\dom(f) = A and forall x \in \dom(f) f(x) \in B.
Let f : A \rightarrow B stand for f is from A to B.

Definition. The singletonmap of A is a map f such that 
\dom(f) = A and forall x \in A f(x) = <x>.
Let singmap(A) stand for the singletonmap of A.

Theorem. Let A be a set. There exists an injective map from A to \PP(A).
Proof. 
	singmap(A) is an injective map from A to \PP(A).
qed.

Theorem. Let A be a set. There is no injective map from \PP(A) to A.
Proof by contradiction.
	Assume the contrary.
	Take an injective map f such that f is from \PP(A) to A .
	Define C = {u \in A | forall x \in \PP(A) (u \in x => f(x) \neq u)}.
	Then f(C) \in C.
	Contradiction.
qed.
