# Axioms
# ======

# This is a collection of Naproche's built-in axioms. It is sometimes
# necessary to state them explicitly to make it easier for the reasoner to
# access them.


# Sets
# ----

Lemma. Let X be a set.
Then X is a class that is an object.

Lemma. Let X be a class that is an object.
Then X is a set.


# Functions
# ---------

Lemma. Let F be a function.
Then F is a map that is an object.

Lemma. Let F be a map that is an object.
Then F is a function.


# Classes
# --------

Lemma. Let X be a class and x be an element of X.
Then x is an object.

Lemma. Let X, Y be classes.
Assume that every element of X is an element of Y and every element of Y is an
element of X.
Then X = Y.

Lemma. Let X be a set and Y be a class.
Assume that every element of Y is an element of X.
Then Y is a set.
Proof.
  Define Z = {x in X | x is an element of Y}.
  Then Z is a set and Z = Y.
Qed.


# Maps
# ----

Lemma. Let F be a map.
Then Dom(F) is a class.

Lemma. Let F be a map and x be an element of Dom(F).
Then F(x) is an object.

Lemma. Let F, G be maps.
Assume Dom(F) = Dom(G) and for all elements x of Dom(F) we have F(x) = G(x).
Then F = G.


# Pairs
# -----

Lemma. Let x, y be objects.
Then (x,y) is an object.
