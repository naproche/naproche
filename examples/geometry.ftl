[synonym point/-s]


# This is a formalization of the beginnings of Tarskian geometry,
# mainly following the outline of 'Metamathematische Methoden in
# der Geometrie' by Schwabhäuser, Szmielew and Tarski. We refer to
# this book as 'SST' in later comments.


Signature. A point is a notion.
Let x,y,z,u,v,w,p,q,r,g,h denote points.


Signature. Cong(x,y,v,w) is an atom.
Let x and y are congruent to v and w stand for Cong(x,y,v,w).
Let x-y : v-w stand for x and y are congruent to v and w.

Signature. Betw(x,u,y) is an atom.
Let u is between x and y stand for Betw(x,u,y).
Let x-u-y stand for u is between x and y.
Let !x-u-y stand for u is not between x and y.


Definition. Col(x,y,z) iff x-y-z or y-z-x or z-x-y.
Let p is colinear with x and y stand for Col(p,x,y).


# Reflexivity of congruence.
Axiom A1. x-y : y-x.

# Transitivity of congruence.
Axiom A2. If x-y : z-u and x-y : v-w then z-u : v-w.

# Identity of congruence.
Axiom A3. If x-y : z-z then x = y.

# Segment construction.
Axiom A4. There exists a point z such that x-y-z and y-z : p-q.

# Five segments.
Axiom A5. If x != y and x-y-z and p-q-r and
      x-y : p-q and y-z : q-r and x-u : p-v and y-u : q-v then
      z-u : r-v.

# Identity of betweenness.
Axiom A6. If y is between x and x then x = y.

# Inner Pasch.
Axiom A7. If x-u-z and y-v-z then there exists a point w
      such that u-w-y and v-w-x.

# Lower dimension.
Axiom A8. There exist points a,b,c such that !a-b-c and !b-c-a and !c-a-b.

# Upper dimension.
Axiom A9. If x-u : x-v and y-u : y-v and  z-u : z-v and u != v then
x-y-z and y-z-x and z-x-y.

# Euclid.
Axiom A10. If x-r-v and y-r-z and x != r then there exist points s,t such that x-y-s and x-z-t and s-v-t.

# Circle continuity axiom.
#
# This axiom is equivalent to the the following statement: A line that has a point
# within a circle intersects that circle (i.e. shares a point with that circle.).
#
Axiom CA. Assume z-p-q and z-p-r and z-x : z-p and z-y : z-r.
Then there exists w such that z-w : z-q and x-w-y.


# This is definition 2.10 in SST. We say that the points x,y,z,r,u,v,w,p are in an
# outer five-segment-configuration whenever OFS(x,y,z,r,u,v,w,p). Using this predicate
# we can restate axiom A5 in the following manner:
#
# A5'. If OFS(x,y,z,r,u,v,w,p) and x != y then z-r : w-p.
#
Definition OFS. OFS(x,y,z,r,u,v,w,p) iff x-y-z and u-v-w and x-y : u-v and y-z : v-w and x-r : u-p and y-r : v-p.

# Reflexivity of congruence.
Lemma L2_1. x-y : x-y.

# Symmetry of congruence.
Lemma L2_2. Assume x-y : v-w. Then v-w : x-y.

# Transitivity of congruence.
Lemma L2_3. Assume x-y : v-w and v-w : p-q. Then x-y : p-q.

# Cong is independent of the order of the pairs.
Lemma L2_4. Assume x-y : v-w. Then y-x : v-w.
Lemma L2_5. Assume x-y : v-w. Then x-y : w-v.

# Zero-length segments are congruent.
Lemma L2_8. x-x : y-y.

# Concatenation of segments.
Lemma L2_11. Assume x-y-z and r-v-w and x-y : r-v and y-z : v-w. Then x-z : r-w.
#
# The following proof follows the proof from SST and works, but can be omitted entirely.
#
Proof.
  OFS(x,y,z,x,r,v,w,r).     # By previous results and assumption.
  Assume x = y. Then r = v. # Axiom A3 gives this implication.
  Assume x != y.            # Axiom A5 completes the proof.
qed.

# Uniqueness for Axiom A4.
Lemma L2_12. Assume q != x.
Suppose q-x-y and x-y : v-w
and     q-x-r and x-r : v-w.
Then y = r.

# Right-betweenness.
Lemma L3_1. x-y-y.

# Symmetry of betweenness.
Lemma L3_2. Assume x-y-z. Then z-y-x.

# Left-betweenness.
Lemma L3_3. x-x-y.

Lemma L3_4. Assume x-y-z and y-x-z. Then x = y.

Lemma L3_5a. Assume x-y-v and y-z-v. Then x-y-z.
Lemma L3_5b. Assume x-y-v and y-z-v. Then x-y-v.

Lemma L3_6a. Assume x-y-z and x-z-r. Then y-z-r.
Lemma L3_6b. Assume x-y-z and x-z-r. Then x-y-r.

Lemma L3_7a. Assume x-y-z and y-z-r and y != z. Then x-z-r.
Proof.
	Take v such that x-z-v and z-v : z-r.
	Then y-z-v and z-v : z-r. Hence v = r.
qed.

Lemma L3_7b. Assume x-y-z and y-z-r and y != z. Then x-y-r.

# Existence of at least two points follows from A8.
# (All other axioms also hold in a one-point space.)
Lemma L3_13. x != y for some x, y.

Lemma L3_14. There exist z such that x-y-z and y != z.


Lemma L3_17. Assume x-y-z and u-v-z and x-p-u. Then there exist q such that (p-q-z and y-q-v).
Proof.
  x-p-u and z-v-u.
	Take r such that v-r-x and p-r-z. # A7 (Pasch).
	Take q such that r-q-z and v-q-y. # A7 (Pasch).
qed.


# This is definition 4.1 in SST. We say that the points x,y,z,r,u,v,w,p are in an
# inner five-segment-configuration whenever IFS(x,y,z,r,u,v,w,p).
#
Definition IFS. IFS(x,y,z,r,v,w,p,q) iff (x-y-z and v-w-p and x-z : v-p and y-z : w-p and x-r : v-q and z-r : p-q).

# We can swap x,y and v,w.
axiom L4_2. Assume IFS(x,y,z,r,v,w,p,q). Then y-r : w-q.

# If we have two three-point segments, with the same total length and each with a segment
# of the same length, then the remaining segments must also have the same length.i
#
# TODO: Write a proof for this.
#
axiom L4_3. Assume x-y-z and r-v-w and x-z : r-w and y-z : v-w. Then x-y : r-v.

Definition L4_4. x-y-z : u-v-w iff x-y : u-v and x-z : u-w and y-z : v-w.

Lemma L4_5. Assume x-y-z and x-z : r-w. Then there exists v such that (r-v-w and x-y-z : r-v-w).
Proof.
	Take u such that w-r-u and r != u. Then Take v such that u-r-v and r-v : x-y. Take g such that u-v-g and v-g : y-z. Then x-z : r-w. Therefore g = w.
qed.

Lemma L4_6. Assume x-y-z and x-y-z : r-v-w. Then r-v-w.
Proof.
	Take u such that r-u-w and x-y-z : r-u-w.
	Then r-u-w : r-v-w and IFS(r,u,w,u,r,u,w,v).
	Then u-u : u-v. Hence u = v. Hence r-v-w.
qed.

Lemma L4_11a. Assume Col(x,y,z). Then Col(y,z,x).
Lemma L4_11b. Assume Col(x,y,z). Then Col(z,x,y).
Lemma L4_11c. Assume Col(x,y,z). Then Col(z,y,x).
Lemma L4_11d. Assume Col(x,y,z). Then Col(y,x,z).
Lemma L4_11e. Assume Col(x,y,z). Then Col(x,z,y).

Lemma L4_12. Col(x,x,y).

Lemma L4_13. Assume Col(x,y,z) and x-z : r-w and r-v-w. Then Col(r,v,w).

Lemma L4_14_1. x-y-z : u-v-w iff y-x-z : v-u-w.
Lemma L4_14_2. x-y-z : u-v-w iff z-y-x : w-v-u.
Lemma L4_14_3. x-y-z : u-v-w iff x-z-y : u-w-v.

axiom L4_14. Assume Col(x,y,z) and x-y : r-v. Then there exists w such that x-y-z : r-v-w.

Definition L4_15. FS(x,y,z,r,v,w,p,q) iff Col(x,y,z) and x-y-z : v-w-p and x-r : v-q and y-r : w-q.

axiom L4_16. Assume FS(x,y,z,r,v,w,p,q) and x != y. Then z-r : p-q.




Lemma L4_17. Assume x != y and Col(x,y,z) and x-p : x-q and y-p :  y-q. Then z-p : z-q.
Proof.
	FS(x,y,z,p,x,y,z,q).
qed.


Lemma L4_18. Assume x != y and Col(x,y,z) and x-z : x-p and y-z : y-p. Then z = p.

Lemma L4_19. Assume x-z-y and x-z : x-p and y-z : y-p. Then z = p.
Proof.
  Assume x = y. Then x = z and x = p. Hence z = p.
  Assume x != y.
qed.

# The 11th axiom of Tarski's axiomatic system says that if x-y-w and x-z-w then
# either x-y-z or x-z-y. To show that it follows from the first ten axioms we first
# prove Lemma C5_1 from which we can easy deduce the 11th axiom.
#
# The definitions, lemmata and axioms C5_1a - C5_1p are not part of SST. We have opted
# for adding them to improve proof-checking speed and readability of the text.

Definition C5_1a. Betw5(x,y,z,r,p) iff x-y-z and x-y-r and x-y-p and x-z-r and x-z-p and x-r-p and y-z-r and y-z-p and y-r-p and z-r-p.

Let x~y~z~r~p stand for Betw5(x,y,z,r,p).

# The following 4 predicates state the already proven statements for different positions in the proof. They are not defined
# in the book "Metamathematische Methoden in der Geometrie.
# We use them because they seem to increase the performance of the proof assistant, when checked just before the next proving
# step.

Definition C5_1b. Th(x,y,z,r,p,q,g,h) iff x != y and x-y-z and x-y-r and x-r-p and r-p : z-r and x-z-q and z-q : z-r and z-q-h and r-p-g.

Definition C5_1c. Th2(x,y,z,r,p,q,g) iff x != y and x~y~z~q~g and x~y~r~p~g and r-p : z-r and z-q : z-r and y-p : g-z and y-g : g-y.

Definition C5_1d. Th3(x,y,z,r,p,q,g,u) iff Th2(x,y,z,r,p,q,g) and OFS(y,z,q,p,g,p,r,z) and p-q : z-r and z-u-p and r-u-q and IFS(r,u,q,z,r,u,q,p) and IFS(z,u,p,r,z,u,p,q) and u-r : u-q.

Definition C5_1e. Th4(x,y,z,r,p,q,g,u,v,w,h) iff Th3(x,y,z,r,p,q,g,u) and z != p and z != q and p-z-v and z-v : z-q and q-z-h and z-h : z-u and v-h-w and h-w : h-v.

# For the following 5 Statements we did not find a proof yet that gets checked positive by Naproche SAD
# They are all used in the proof of Lemma C5_1p and Lemma C5_1.

Lemma C5_1f. Assume x != y and x-y-z and x-y-r. Then there exist points a,b such that x-r-a and r-a : z-r and x-z-b and z-b : z-r.
Proof.
	Take point a such that x-r-a and r-a : z-r (by A4).
	Take point b such that x-z-b and z-b : z-r (by A4).
qed.

axiom C5_1g. If Th(x,y,z,r,p,q,g,h) then x~y~z~q~h and x~y~r~p~g.

axiom C5_1h. Assume Th(x,y,z,r,p,q,g,h) and x~y~z~q~h and x~y~r~p~g. Then y-p : h-z.

axiom C5_1i. Assume Th2(x,y,z,r,p,q,g) and OFS(y,z,q,p,g,p,r,z). Then p-q : z-r.

axiom C5_1j. Assume Th(x,y,z,r,p,q,g,h) and x~y~z~q~h and x~y~r~p~g and y-p : h-z. Then y-g : h-y.



Lemma C5_1k. Assume x != y and x-y-z and x-y-r and x-r-p and r-p : z-r and x-z-q and z-q : z-r and (z = p or r = q). Then x-z-r or x-r-z.

Lemma C5_1l. Assume x != y and x-y-z and x-y-r and x-r-p and r-p : z-r and x-z-q and z-q : z-r. Then there exist points s,t such that z-q-t and r-p-s.

Lemma C5_1m. Assume Th2(x,y,z,r,p,q,g). Then OFS(y,z,q,p,g,p,r,z).

Lemma C5_1n. Assume Th2(x,y,z,r,p,q,g) and OFS(y,z,q,p,g,p,r,z) and p-q : z-r. Then there exist u such that z-u-p and r-u-q.

Lemma C5_1o. Assume Th4(x,y,z,r,p,q,g,u,v,w,h). Then OFS(q,z,h,v,v,z,u,q) and h-v : u-q and h-w : u-r and OFS(q,u,r,z,v,h,w,z) and q-r : v-w and z-w : z-r and z-v : z-w.
Proof.
	OFS(q,z,h,v,v,z,u,q). Hence h-v : u-q. Hence h-w : u-r. # TODO: this step is slow.
	Therefore OFS(q,u,r,z,v,h,w,z). Hence q-r : v-w.
	If q != u then z-w : z-r. If q = u then q = r. # TODO: this step is slow.
	Then v = w. Therefore z-w : z-r.
	Hence z-v : z-w.
qed.

# The Idea to proof Lemma C5_1 is to extend the line x-z and x-r through two points p,q such that r-p : z-r and z-q : z-r.
# Then one can easy see , that if either z = p or r = q, x-y-z or x-z-y must hold.
# The following Lemma proofs that if there exist such points p and q then z = p or r = q must hold.
# To see that such points exist one has to use Axiom A4 twice.

Lemma C5_1p. Assume x != y and x-y-z and x-y-r and x-r-p and r-p : z-r and x-z-q and z-q : z-r. Then z = p or r = q.
Proof.
	Take points s,t such that z-q-t and r-p-s.
	Then Th(x,y,z,r,p,q,s,t).
	Then x~y~z~q~t and x~y~r~p~s.
	Then y-p : t-z.
	Then y-t : t-y.
	Then s = t.
	Then Th2(x,y,z,r,p,q,s).
	Then OFS(y,z,q,p,s,p,r,z).
	Then p-q : z-r.
	Take u such that z-u-p and r-u-q (by C5_1n).
	Then IFS(r,u,q,z,r,u,q,p).
	Then IFS(z,u,p,r,z,u,p,q).
	Then u-z : u-p.
	Then u-r : u-q.
	Assume z != p. Then z != q.
		Take v such that p-z-v and z-v : z-q.
		Take h such that q-z-h and z-h : z-u.
		Take w such that v-h-w and h-w : h-v.
		Then OFS(q,z,h,v,v,z,u,q) and h-v : u-q and h-w : u-r and
			OFS(q,u,r,z,v,h,w,z) and q-r : v-w and z-w : z-r and z-v : z-w (by C5_1o).
		Then h-v : h-w. z != p. Hence h != z. Col(h,z,q). Therefore q-v : q-w.
		Then z-v : z-w. z != q. Col(z,q,y). Therefore y-v : y-w.
		Then z-v : z-w. z != q. Col(z,q,s). Therefore s-v : s-w.
		Then y != s.
		Then q = r.
	Assume z = p.
qed.

Lemma D5_1. Assume x != y and x-y-z and x-y-r. Then x-z-r or x-r-z.
Proof.
	Take p,q such that x-r-p and r-p : z-r and x-z-q and z-q : z-r.
	Then z = p or r = q (by C5_1p). Therefore x-z-r or x-r-z (by C5_1k).
qed.

Lemma D5_2. Assume x != y and x-y-z and x-y-r. Then y-z-r or y-r-z.

Theorem D5_3. If x-y-w and x-z-w then x-y-z or x-z-y.
