# Lists (Christian Schöner & Marcel Schütz, 2024)
# ===============================================

[read natural-numbers.ftl]

Let a, b, c denote objects.


# Lists
# -----

[synonym list/-s]
Signature. A list is an object.

Let L, L' denote lists.

Signature. [] is a list.
Signature. a : L is a list.

Axiom. L = [] or L = a : L' for some object a and some list L'.
Axiom. L -<- a : L.

Let [a] stand for a : [].
Let [a,b] stand for a : [b].
Let [a,b,c] stand for a : [b,c].


# Concatenation
# -------------

Signature. L ++ L' is a list.

Axiom. [] ++ L = L.

Axiom. (a : L') ++ L = a : (L' ++ L).


Lemma. L ++ [] = L for every list L.
Proof by induction on L.
  Let L be a list.

  Case L = []. Trivial.

  Case L = a : L' for some object a and some list L'.
    Consider an object a and a list L' such that L = a : L'.
    Then L' -<- L.
    Hence L' ++ [] = L'.
    Thus
      L ++ []
      = (a : L') ++ []
      = a : (L' ++ [])
      = a : L'
      = L.
  End.
Qed.

Lemma. L ++ (L' ++ L'') = (L ++ L') ++ L'' for any lists L, L', L''.
Proof by induction on L.
Let L be a list.
  Case L = []. Trivial.

  Case L = a : L''' for some object a and some list L'''.
    Consider an object a and a list L''' such that L = a : L'''.
    Then L''' -<- L.
    Let L',L'' be lists.
    Then L''' ++ (L' ++ L'') = (L''' ++ L') ++ L''.
    Thus
      L ++ (L' ++ L'') 
      = (a : L''') ++ (L' ++ L'')
      = a : (L''' ++ (L' ++ L''))
      = a : ((L''' ++ L') ++ L'')
      = (a : (L''' ++ L')) ++ L''
      = ((a : L''') ++ L') ++ L''
      = (L ++ L') ++ L''.
  End.
Qed.


# Reversion
# ---------

Signature. rev(L) is a list.

Axiom. rev([]) = [].

Axiom. rev(a : L) = rev(L) ++ [a].


Lemma. rev(L ++ L') = rev(L') ++ rev(L) for any lists L, L'.
Proof by induction on L.
  Let L,L' be lists.

  Case L = []. Trivial.

  Case L = a : L'' for some object a and some list L''.
    Take an object a and a list L'' such that L = a : L''.
    Then L'' -<- L.
    Hence rev(L'' ++ L') = rev(L') ++ rev(L'').
    Thus
      rev(L ++ L')
      = rev((a : L'') ++ L')
      = rev(a : (L'' ++ L'))
      = rev(L'' ++ L') ++ [a]
      = (rev(L') ++ rev(L'')) ++ [a]
      = rev(L') ++ (rev(L'') ++ [a])
      = rev(L') ++ rev(a : L'')
      = rev(L') ++ rev(L).
  End.
Qed.


Lemma. rev(rev(L)) = L for every list L.
Proof by induction on L.
  Let L be a list.

  Case L = []. Trivial.

  Case L = a : L' for some object a and some list L'.
    Take an object a and a list L' such that L = a : L'.
    Then L' -<- L.
    Hence rev(rev(L')) = L'.
    Thus
      rev(rev(L))
      = rev(rev(a : L'))
      = rev(rev(L') ++ [a])
      = rev([a]) ++ rev(rev(L'))
      = a : rev(rev(L'))
      = a : L'
      = L.
  End.
Qed.


# Length
# ------

Signature. The length of L is a natural number.
Let length(L) stand for the length of L.

Axiom. length([]) = 0.

Axiom. length(a : L) = length(L) + 1.


Lemma. length(L ++ L') = length(L) + length(L') for all lists L, L'.
Proof by induction on L.
  Let L be a list.

  Case L = []. Trivial.

  Case L = a : L'' for some object a and some list L''.
    Take an object a and a list L'' such that L = a : L''.
    Then L'' -<- L.
    Hence length(L'' ++ L') = length(L'') + length(L') for every list L'.
    Thus
      length(L ++ L')
      = length((a : L'') ++ L')
      = length(a : (L'' ++ L'))
      = length(L'' ++ L') + 1
      = (length(L'') + length(L')) + 1
      = (length(L'') + 1) + length(L')
      = length(a : L'') + length(L')
      = length(L) + length(L')
    for every list L'.
  End.
Qed.


Lemma. length(rev(L)) = length(L) for any list L.
Proof by induction on L.
  Let L be a list.

  Case L = []. Trivial.

  Case L = a : L' for some object a and some list L'.
    Take an object a and a list L' such that L = a : L'.
    Then L' -<- L.
    Hence length(rev(L')) = length(L').
    Thus
      length(rev(L))
      = length(rev(a : L'))
      = length(rev(L') ++ [a])
      = length([a]) + length(rev(L'))
      = 1 + length(rev(L'))
      = 1 + length(L')
      = length(L).
  End.
Qed.
