[read classes.ftl]
[read vocabulary.ftl]

Signature. An integer is an object.

Signature. 0 is a integer.
Signature. 1 is a integer.
Signature. 2 is a integer.
Signature. 3 is a integer.
Signature. 4 is a integer.
Signature. 5 is a integer.
Signature. 6 is a integer.
Signature. 7 is a integer.

Definition. An integer mod eight is an integer x
  such that x = 0 or x = 1 or x = 2 or x = 3 or x = 4 or x = 5 or x = 6 or x = 7.

Let m, n, i, j, k, l denote integers mod eight.

Signature. A square is an object x.
Axiom. (m,n) is a square.
Axiom. Let x be a square. Then x = (m,n) for some integer mod eight m and some integer mod eight n.

Let x, y, z denote squares.

Definition. Check = {x | x is a square}.
Axiom. Check is a set.
Let the checkerboard stand for Check.

Axiom. Every subset of Check is Dedekind finite.

Definition. Corners = {(0,0), (7,7)}.

Definition. Mutil = Check -- Corners.

Let the mutilated checkerboard stand for Mutil.


Signature. Let m, n be integers. m is followed by n is a relation.

Let m ~ n stand for m is followed by n.

Axiom. If m ~ n then n ~ m.

Axiom. 0 ~ 1 ~ 2 ~ 3 ~ 4 ~ 5 ~ 6 ~ 7.

Definition.
    x is adjacent to y iff
    there exists integers b, c, d, e such that
    x = (b,c) and y = (d, e) and
    ((b = d and c ~ e) or (b ~ d and c = e)).

Definition.
    A domino is a set D such that D = {x, y} for some adjacent squares x, y.

Definition.
    A domino tiling is a disjoint family T such that
    every element of T is a domino.

Definition.
    Let A be a subset of the checkerboard.
    A domino tiling of A is a domino tiling T such that
    for every square x
    x is an element of A iff x is an element of some element of T.

Signature. x is black is a relation.
Let x is white stand for x is not black.

Axiom. (0,0) is black.
Axiom. (7,7) is black.

Axiom. If x is adjacent to y then x is black iff y is white.

Definition. Blck is the class of black elements of the checkerboard.
Definition. Wht is the class of white elements of the checkerboard.

Lemma. Blck is a set. Indeed Blck is a subclass of the checkerboard.
Lemma. Wht is a set. Indeed Wht is a subclass of the checkerboard.

Signature.
    Let x be an element of the checkerboard.
    Swap x is an element of the checkerboard.

Axiom. Swap(0,n) = (1,n) and Swap(1,n) = (0,n).
Axiom. Swap(2,n) = (3,n) and Swap(3,n) = (2,n).
Axiom. Swap(4,n) = (5,n) and Swap(5,n) = (4,n).
Axiom. Swap(6,n) = (7,n) and Swap(7,n) = (6,n).

Lemma.
    Let x be an element of the checkerboard.
    Swap x is adjacent to x.
Proof.
    Take integers mod eight i, j such that x = (i,j).
    Case i = 0. End.
    Case i = 1. End.
    Case i = 2. End.
    Case i = 3. End.
    Case i = 4. End.
    Case i = 5. End.
    Case i = 6. End.
    Thus i = 7.
End.

Lemma. 
    let x be an element of the checkerboard.
    Swap (Swap x) = x.
Proof.
    Take integers mod eight i,j such that x = (i,j).
    Case i = 0. End.
    Case i = 1. End.
    Case i = 2. End.
    Case i = 3. End.
    Case i = 4. End.
    Case i = 5. End.
    Case i = 6. End.
    Thus i = 7.
End.

Lemma.
    Let x be an element of the checkerboard.
    Then x is black iff Swap x is white.

#Lemma.
#    Let x be an element of the checkerboard.
#    Then x is white iff Swap x is black.

Lemma.
    Blck is equinumerous with Wht.
Proof.
    Define F(x) = Swap x for x in Blck.
    Define G(x) = Swap x for x in Wht.
    F(x) is white for all elements x of Dom F.
    G(y) is black for all elements y of Dom G.
    Then F : Blck -> Wht and G : Wht -> Blck.
    For all elements x of Blck we have G(F(x)) = x.
    For all elements x of Wht we have F(G(x)) = x.
    Thus F : Blck <-> Wht.
End.


Signature.
    Let A be a subset of the checkerboard.
    Let T be a domino tiling of A.
    Let x be an element of A.
    Sw(T,A,x) is a square y such that there is an element D of T
    such that D = {x, Sw(T,A,x)}.

Lemma.
    Let A be a subset of the checkerboard.
    Assume that T is a domino tiling of A.
    Let x be an element of A.
    Then Sw(T,A,x) is an element of A.
Proof.
    Let y = Sw(T,A,x).
    Take an element D of T such that D = {x, y}.
    Then y is an element of A.
End.

Lemma.
    Let A be a subset of the checkerboard.
    Assume that T is a domino tiling of A.
    Let x be an element of A.
    Then Sw(T,A,(Sw(T,A,x))) = x.
Proof.
    Let y = Sw(T,A,x).
    Take an element Y of T such that Y = {x, y}.
    Let z = Sw(T,A,y).
    Take an element Z of T such that Z = {y, z}.
    Then x = z.
End.


Lemma.
    Let A be a subset of the checkerboard.
    Assume that T is a domino tiling of A.
    Let x be a black element of A.
    Then Sw(T,A,x) is white.
Proof.
    Let y = Sw(T,A,x).
    Take an element Y of T such that Y = {x, y}.
    Then x is adjacent to y. Thus y is white.
End.

Lemma.
    Let A be a subset of the checkerboard.
    Assume that T is a domino tiling of A.
    Let x be a white element of A.
    Then Sw(T,A,x) is black.
Proof.
    Let y = Sw(T,A,x).
    Take an element Y of T such that Y = {x, y}.
    Then x is adjacent to y. Thus y is black.
End.

# The theorem
# -----------

Lemma.
    Let A be a subset of the checkerboard.
    Let T be a domino tiling of A.
    Then A /\ Blck is equinumerous with A /\ Wht.
Proof.
    Define F(x) = Sw(T,A,x) for x in A /\ Blck.
    Define G(x) = Sw(T,A,x) for x in A /\ Wht.
    F: A /\ Blck -> A /\ Wht.
    G: A /\ Wht -> A /\ Blck.
    For all elements x of A /\ Blck we have G(F(x))=x.
    For all elements x of A /\ Wht we have F(G(x))=x.
    Thus F : A /\ Blck <-> A /\ Wht.
End.

Lemma. Mutil /\ Wht = Wht.

Lemma. Mutil /\ Blck is a proper subset of Blck.
Proof.
    (0,0) is an element of Blck.
    (0,0) is not an element of Mutil.
    Thus (0,0) is not an element of Mutil /\ Blck.
End.

Theorem.
    The mutilated checkerboard has no domino tiling.
Proof by contradiction. Suppose the contrary.
    Take a domino tiling T of the mutilated checkerboard.
    Mutil /\ Blck is equinumerous with Mutil /\ Wht.
    Mutil /\ Blck is equinumerous with Wht.
    Mutil /\ Blck is equinumerous with Blck.
    Contradiction.
End.