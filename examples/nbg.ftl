# This module implements the von Neumann-Bernays-Gödel set theory,
# a conservative extension of ZFC. Any lemma that can be proven in ZFC
# also can be proven in NBG, but unlike ZFC, NBG is finitely axiomatizable,
# that is, we can describe it without using schemata over arbitrary formulas.
# The axiom schema of class formation has been omitted in this presentation
# because it is built into the compiler.

# NBG is usually stated using two kinds of basic types: classes and sets.
# Since we want to write statements '2 is in Z' we split the concept of sets
# into two types: sets and setobjects where a set is a collection (of setobjects)
# and a setobject is an object which lives in a set. Thus every set is a setobject
# and one can exhibit a coercion from any type to setobject by assuming as an
# axiom that the class of all inhabitants of this type is a set.

[synonym class/-es]
[synonym set/-s]
[synonym relation/-s]
[synonym function/-s]
[synonym object/-s]
[synonym setobject/-s]
[synonym element/-s]

Signature. A class is a notion.
Signature. A set is a class.
Signature. An object is a notion.
Signature. A setobject is an object.

Let B, C, D, E denote classes.
Let b, c, d, e denote sets.
Let w, x, y, z denote setobjects.

# aElementOf is the variant of isIn which is not type-safe.
# It can be used for deriving setobject-ness and to circum-
# vent the type system.
Signature. An element of B is a notion.
Definition. Let x be a setobject. 
  x is in B iff x is an element of B.

Axiom SetToSetObject. Let b be a set. b is a setobject.
Axiom SetObjectIntro. Let o be an object 
  and s be a set such that o is an element of s.
  Then o is a setobject.

# This axiom is implicitly used in the compiler.
Axiom Ext. If x is an element of C iff x is an element of B then C = B.

Signature. The empty set is a set.
Axiom Empty. x is not an element of the empty set.
Lemma. The empty set is { setobject u | u != u }.

Definition. B is nonempty iff there is a x such that x is in B.
Lemma. If B is nonempty then B is not the empty set.
Definition. B is empty iff B is not nonempty.
Lemma. B is empty iff B is { setobject u | u != u }.

Signature. The pair of x and y is a set.
Axiom Pair. x is in the pair of y and z iff x = y or x = z.
Lemma. The pair of x and y is { setobject u | u = x or u = y }.
Definition. The singleton of x is the pair of x and x.

Definition. The ordered pair of x and y is the pair of x and the pair of x and y.
Definition. (x, y) is the ordered pair of x and y.
Lemma OrdPair. If the ordered pair of x and y is equal to the ordered pair of z and w
  then x = z and y = w.

Signature. The union of b is a set.
Axiom Union. b is the union of d iff (x is in b iff there is a c 
  such that c is in d and x is in c).
Signature. The union of c and b is a notion.
Axiom UnionIntro. c is the union of d and b iff c is the union of the pair of d and b.

Signature. A subclass of B is a class.
Axiom SubclassIntro. C is a subclass of B iff 
  every element of C is an element of B.

Signature. The powerset of b is a set.
Axiom PowerSet. b is the powerset of d iff (c is in b iff c is a subclass of d).

Definition. The successor of b is the pair of b and the singleton of b.
Axiom Inf. There is a set n such that the empty set is in n and for every b
  such that b is in n the successor of b is in n.

Definition. The product of C and B is { (u, v) | u is a setobject and v is a setobject and u is in C and v is in B }.
Signature. A relation is a class.
Axiom RelationIntro. C is a relation iff for every x such that x is in C
  there is a y such that there is a z such that x is the ordered pair of y and z.

Let R, S denote relations.
Definition. The domain of R is { setobject u | there is a setobject v such that (u, v) is in R }.
Definition. The Range  of R is { setobject v | there is a setobject u such that (u, v) is in R }.
# Definition. The field  of R is the union of the domain of R and the Range of R.
Definition. The restriction of R to B is { (u, v) | u is a setobject and v is a setobject and (u, v) is in R and u is in B }.
Definition. The    image of B under R is { setobject v | there is a setobject u such that u is in B and (u, v) is in R }.
Definition. The preimage of B under R is { setobject u | there is a setobject v such that v is in B and (u, v) is in R }.
Definition. The composition of S and R is { (x, z) | x is a setobject and z is a set and there is a setobject y such that (x, y) is in R and (y, z) is in S }.
Definition. The inverse of R is { (y, x) | x is a setobject and y is a setobject and (x, y) is in R }.
Definition. Dom(R) is the domain of R.
Definition. Ran(R) is the range of R.
# Definition. field(R) is the field of R.
Definition. R[B] is the image of B under R.
Definition. R^{-1} is the inverse of R.

# Definition. R is reflexive iff for all x such that x is in the field of R (x, x) is in R.
# Definition. R is irreflexive iff for all x such that x is in the field of R (x, x) is not in R.
Definition. R is symmetric iff for all x, y such that (x, y) is in R (y, x) is in R.
Definition. R is antisymmetric iff for all x, y such that (x, y) is in R and (y, x) is in R x = y.
Definition. R is transitive iff for all x, y, z such that (x, y) is in R and (y, z) is in R (x, z) is in R.
Definition. R is connex iff for all x, y such that x,y are in R
  (x, y) is in R or (y, x) is in R or x = y.

Signature. A function is a relation.
Axiom FunctionIntro. R is a function iff for all x, y, z such that (x, y) is in R and (x, z) is in R y = z.

Let F, G denote functions.
Definition. F at x is a setobject y such that (x, y) is in F.
Definition. F[x] is F at x.

Axiom Choice. Let c be a set such that for all b such that b is in c b is nonempty.
  There exists a function F such that Dom(F) = c
  and for all x such that x is in c there is a set d such that x is in d and d is F at x.

Axiom Replacement. The restriction of F to c is a set.

Definition. The intersection of B is { setobject v | for every set u such that u is in B v is in u }.
Definition. The intersection of c and b is the intersection of the pair of c and b.
Axiom Restriction. If c is nonempty then there is a b such that b is in c and
  (the intersection of c and b) is empty.