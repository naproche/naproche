# THE MUTILATED CHECKERBOARD IN NAPROCHE

[read ZFC.ftl]

# Checkerboards

[synonym rank/ranks]
Signature. A rank is a notion.
Let r1, r2 denote ranks.
Axiom. r1 is setsized.
Signature. 1 is a rank.
Signature. 2 is a rank.
Signature. 3 is a rank.
Signature. 4 is a rank.
Signature. 5 is a rank.
Signature. 6 is a rank.
Signature. 7 is a rank.
Signature. 8 is a rank.
Definition. RANK = {1,2,3,4,5,6,7,8}.

[synonym file/files]
Signature. A file is a notion.
Let f1, f2 denote files.
Axiom. f1 is setsized.
Signature. aa is a file.
Signature. b is a file.
Signature. c is a file.
Signature. d is a file.
Signature. e is a file.
Signature. f is a file.
Signature. g is a file.
Signature. h is a file.
Definition. FILE = {aa,b,c,d,e,f,g,h}.

[synonym square/squares]
Signature. A square is a notion.
Axiom. (f1,r1) is a square.
Let sq, s1, s2, s3, s4 denote squares.

Definition. Checkerboard is the class of squares sq such that sq = (f1,r1) for some
element f1 of FILE and some element r1 of RANK.
Axiom. Checkerboard is a set.

# Preliminaries About Sets and Functions

Let A,B,C denote sets.

Definition. A subset of B is a set A such that 
every element of A is an element of B.

Axiom Extensionality. If A is a subset of B and B 
is a subset of A then A = B.

Definition. A proper subset of B is a subset A of B such that A != B.

Definition. A is disjoint from B iff there is no element of A that is
an element of B.

Definition. Assume that every element of C is a set. 
C is pairwise disjoint iff A and B are disjoint for all nonequal
elements A,B of C.

Definition. B \cap C = { x in B | x is an element of C}.

Definition. B \setminus C = { x in B | x is not an element of C}.

Lemma. Every set is an object.

Axiom. Let x,y,x1,y1 be objects. If (x,y) = (x1,y1) then x = x1 and y = y1. 

Let F,G denote functions.

Definition. F : A -> B iff Dom(F) = A and 
F(x) is an element of B for all elements x of A.

Definition. F : A <-> B iff F : A -> B and there exists G such that
G : B -> A and
(for all elements x of A G(F(x))=x) and
(for all elements y of B F(G(y))=y).

# Cardinalities of (Finite) Sets

Definition. A is equinumerous with B iff there is F such that F : A <-> B.

Lemma. Assume that A is equinumerous with B. Then B is equinumerous with A. 

Lemma. Assume that A is equinumerous with B and B is equinumerous with C.
Then A is equinumerous with C.
Proof. Take a function F1 such that F1 : A <-> B.
Take a function G1 such that G1 : B -> A and (for all elements x of A G1(F1(x))=x) and
(for all elements y of B F1(G1(y))=y).
Take a function F2 such that F2 : B <-> C.
Take a function G2 such that G2 : C -> B and (for all elements x of B G2(F2(x))=x) and
(for all elements y of C F2(G2(y))=y).
Define F(x) = F2(F1(x)) for x in A.
F : A <-> C. Indeed define G(y) = G1(G2(y)) for y in C.
qed.

Axiom. If A is a proper subset of B then A is not equinumerous with B.

# The Mutilated Checkerboard

Definition. Corners = {(aa,1),(h,8)}.

Definition. Mutilated Checkerboard = Checkerboard \setminus Corners.

# Dominos

Signature. r1 is vertically adjacent to r2 is a relation.
Axiom. If r1 is vertically adjacent to r2 then r2 is vertically adjacent to r1.
Axiom. 1 is vertically adjacent to 2.
Axiom. 2 is vertically adjacent to 3.
Axiom. 3 is vertically adjacent to 4.
Axiom. 4 is vertically adjacent to 5.
Axiom. 5 is vertically adjacent to 6.
Axiom. 6 is vertically adjacent to 7.
Axiom. 7 is vertically adjacent to 8.
 
Signature. f1 is horizontally adjacent to f2 is a relation.
Axiom. If f1 is horizontally adjacent to f2 then f2 is horizontally adjacent to f1.
Axiom. aa is horizontally adjacent to b.
Axiom. b is horizontally adjacent to c.
Axiom. c is horizontally adjacent to d.
Axiom. d is horizontally adjacent to e.
Axiom. e is horizontally adjacent to f.
Axiom. f is horizontally adjacent to g.
Axiom. g is horizontally adjacent to h.

Definition. s1 is adjacent to s2 iff there exist f1, r1, f2, r2 such that
s1=(f1,r1) and s2=(f2,r2) and ((f1=f2 and r1 is vertically adjacent to r2) or
(r1=r2 and f1 is horizontally adjacent to f2)).

[synonym domino/dominos]
Definition. A domino is a set D such that D = {s1,s2} for some
adjacent squares s1, s2.

# Tilings with dominos

Definition. A tiling with dominos is a pairwise disjoint class of dominos.

Let A denote a subset of Checkerboard.

Definition. A tiling of A with dominos is a tiling with dominos T
such that for every square sq sq is an element of A iff sq is an element 
of some element of T.

# We shall prove:
# Theorem. There is no tiling of Mutilated Checkerboard with dominos.

# Colors

Signature. sq is black is a relation.
Signature. sq is white is a relation.

Axiom. sq is black iff sq is not white.

Axiom. If s1 is adjacent to s2 then s1 is black iff s2 is white.

Axiom. (aa,1) is black.

Axiom. (h,8) is black.

Definition. Black is the class of black elements of Checkerboard.
Definition. White is the class of white elements of Checkerboard.
Lemma. Black is a set.
Lemma. White is a set.


# Counting Colors on Checkerboards

Signature. Let sq be an element of Checkerboard.
Swap sq is an element of Checkerboard.

Let r1 denote an element of RANK.

Axiom. Swap (aa,r1) = (b,r1).
Axiom. Swap (b,r1) = (aa,r1).
Axiom. Swap (c,r1) = (d,r1).
Axiom. Swap (d,r1) = (c,r1).
Axiom. Swap (e,r1) = (f,r1).
Axiom. Swap (f,r1) = (e,r1).
Axiom. Swap (g,r1) = (h,r1).
Axiom. Swap (h,r1) = (g,r1).

Lemma. Let sq be an element of Checkerboard.
Swap sq is adjacent to sq.
Proof.
Take f1, r2 such that sq = (f1,r2). r2 is an element of RANK.
Case f1 = aa. end.
Case f1 = b. end.
Case f1 = c. end.
Case f1 = d. end.
Case f1 = e. end.
Case f1 = f. end.
Case f1 = g. end.
qed.

Lemma. Let sq be an element of Checkerboard.
Swap Swap sq = sq.
Proof.
Take f1, r2 such that sq = (f1,r2). r2 is an element of RANK.
Case f1 = aa. end.
Case f1 = b. end.
Case f1 = c. end.
Case f1 = d. end.
Case f1 = e. end.
Case f1 = f. end.
Case f1 = g. end.
qed.

Lemma. Let sq be an element of Checkerboard.
sq is black iff Swap sq is white.

Lemma. Black is equinumerous with White.
Proof.
Define F(sq) = Swap sq for sq in Black.
F: Black -> White.
Define G(sq) = Swap sq for sq in White.
G: White -> Black.
For all elements sq of Black G(F(sq))=sq.
For all elements sq of White F(G(sq))=sq.
F : Black <-> White.
qed.

Signature. Assume that T is a tiling of A with dominos. Let sq be an element of A.
Sw(T,A,sq) is a square sq1 such that there is an element D of T
such that D = {sq,sq1}.

Lemma.  Assume that T is a tiling of A with dominos. Let sq be an element of A.
Then Sw(T,A,sq) is an element of A.
Proof. Let sq1 = Sw(T,A,sq).
Take an element D of T such that D = {sq,sq1}.
qed.
 
Lemma.  Assume that T is a tiling of A with dominos. Let sq be an element of A.
Then Sw(T,A,Sw(T,A,sq)) = sq.
Proof. Let sq1 = Sw(T,A,sq).
Take an element D1 of T such that D1 = {sq,sq1}.
Let sq2 = Sw(T,A,sq1).
Take an element D2 of T such that D2 = {sq1,sq2}.
sq = sq2.
qed.

Lemma.  Assume that T is a tiling of A with dominos. Let sq be a black element of A.
Then Sw(T,A,sq) is white.
Proof. Let sq1 = Sw(T,A,sq).
Take an element D1 of T such that D1 = {sq,sq1}.
qed.

# The Theorem

Lemma. Let T be a tiling of A with dominos. Then A \cap Black is 
equinumerous with A \cap White.

Proof.
Define F(sq) = Sw(T,A,sq) for sq in A \cap Black.
F: A \cap Black -> A \cap White.
Define G(sq) = Sw(T,A,sq) for sq in A \cap White.
G: A \cap White -> A \cap Black.
For all elements sq of A \cap Black G(F(sq))=sq.
For all elements sq of A \cap White F(G(sq))=sq.
F : A \cap Black <-> A \cap White.
qed.

Lemma. Mutilated Checkerboard \cap White = White.
Proof.
Mutilated Checkerboard \cap White is a subset of White.
White is a subset of Mutilated Checkerboard.
Proof. Let sq be an element of White.
sq != (aa,1). sq != (h,8). Indeed (h,8) is black.
qed.
qed.

Theorem. There is no tiling of Mutilated Checkerboard with dominos.
Proof by contradiction.
Assume T is a tiling of Mutilated Checkerboard with dominos.
Mutilated Checkerboard \cap Black is equinumerous with Mutilated Checkerboard \cap White.
Mutilated Checkerboard \cap Black is equinumerous with White.
Mutilated Checkerboard \cap Black is equinumerous with Black.
Contradiction. Indeed Mutilated Checkerboard \cap Black is a proper subset of Black.
qed. 


