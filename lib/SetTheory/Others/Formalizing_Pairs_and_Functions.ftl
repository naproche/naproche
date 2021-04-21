Let a, b, c, x, y, z, X, Y, Z stand for sets.
Let x \in y stand for x is an element of y.
Let x \notin y stand for x is not an element of y.
Let x \neq y stand for x != y.


# Set Arithmetic

Axiom. Let x be a set. Let y \in x. Then y is a set.

Definition. The singleton of x is {set z | z = x}.
Let <x> stand for the singleton of x.

Definition. The unordered pair of x and y is {set z | z = x \/ z = y}.
Let <x,y> stand for the unordered pair of x and y.

Definition. The union of x is {set z | exists y \in x (z \in y)}.
Let \bigcup x stand for the union of x.

Definition. The intersection of x is {set z | forall y \in x (z \in y)}.
Let \bigcap x stand for the intersection of x.

Definition. The difference of x and y is {z \in x | z \notin y}.
Let x \setminus y stand for the difference of x and y.

Definition. A subset of x is a set y such that forall z \in y (z \in x).
Let y \subseteq x stand for y is a subset of x.


# Ordered Pairs

Definition. The ordered pair of x and y is
{set z | z = <x> \/ z = <x,y>}.
Let [x,y] stand for the ordered pair of x and y.

Lemma PairProperty1. Let [x,y] = [X,Y]. Then x = X /\ y = Y.
Proof.
	<x> \in [x,y]. Therefore <x> \in [X,Y].
	Then <x> = <X> or <x> = <X,Y>.
	Then x = X.
	<x,y> \in [x,y]. Therefore <x,y> \in [X,Y].
	Then <x,y> = <X> or <x,y> = <X,Y>.
	y \in <x,y>. Then y = X or  y = Y.
	<X,Y> \in [X,Y]. Therefore <X,Y> \in [x,y].
	Then <X,Y> = <x> or <X,Y> = <x,y>.
	Y \in <X,Y>. Then Y = x or Y = y.
	Then x = X /\ y = Y.
qed.

Signature. A pair is a notion.
Axiom. Let p be a pair. Then p is a set.
Axiom. Let p be a set. p is a pair iff exists x,y p = [x,y].
Let p stand for a pair.

Signature. pi1(p) is an object.
Axiom. Let p be a pair. pi1(p) = \bigcap (\bigcap p).

Lemma PairProperty2. pi1([x,y]) = x.

Signature. pi2(p) is an object.
Axiom. Let p be a pair. Let p = <<pi1(p)>>. Then pi2(p) = pi1(p).
Axiom. Let p be a pair. Let p \neq <<pi1(p)>>. Then pi2(p) = \bigcap (\bigcup p \setminus <pi1(p)>).

Lemma PairProperty3. pi2([ x,y ]) = y.
Proof.
	Case [ x,y ] = <<pi1([ x,y ])>>.
	end.
	Case [ x,y ] \neq <<pi1([ x,y ])>>.
		Then x \neq y.
		Proof by contradiction. Assume the contrary.
			Then x = y.
			Then [x,y] = <<pi1([x,y])>>.
			Contradiction.
		end.
		\bigcup [x,y] = <x,y>.
		pi1([x,y]) = x.
		<x,y> \setminus <x> = <y>.
		\bigcap <y> = y.
	end.
qed.

Definition. The cartesian product of X and Y is {[x,y] | x \in X /\ y \in Y}.



# Functions

Definition. A relation is a set R such that
forall p \in R exists a,b (p = [a,b]).
Let a - R - b stand for [a,b] \in R.

Definition func. A setfunction is a relation F such that
forall x,y,z (x - F - y /\ x - F - z => y = z).

Definition. Let F be a setfunction. The domain of F is
{set x | exists y [x,y] \in F}.
Let dom(F) stand for the domain of F.

Definition. Let F be a setfunction. Let x \in dom(F). The value of F at x is
{set u | forall y (x - F - y => u \in y)}.
Let F(x) stand for the value of F at x.

Lemma FunctionProperty. Let F be a setfunction. Forall a,b ([a,b] \in F iff a \in dom(F) /\ b = F(a)).
Proof.
	Let a,b be sets.
	If [a,b] \in F then a \in dom(F) /\ b = F(a).
	Proof.
		Assume [a,b] \in F.
		Then a \in dom(F).
		b \subseteq F(a).
		F(a) \subseteq b.
		Then F(a) = b.
	end.
	If a \in dom(F) and b = F(a) then [a,b] \in F.
	Proof.
		Assume a \in dom(F) and b = F(a).
		Take a set c such that a - F - c.
		c \subseteq b and b \subseteq c.
		Then b = c.
	end.
qed.



