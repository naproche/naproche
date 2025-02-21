# The implicational propositional calculus

[read examples/lang/vocabulary.ftl]

Signature. 
    A formula is an object.

Let P, Q, R, S denote formulas.

Signature Implication. 
    P > Q is a formula.

Signature. 
    P is deducible is a relation.

Axiom Detachment. 
    Suppose P and P > Q are deducible.
    Then Q is deducible.

Axiom Implosion. 
    P > (Q > P) is deducible.

Axiom Chain. 
    (P > (Q > R)) > ((P > Q) > (P > R)) is deducible.

# Introductory example.
Proposition Weakening.
    (0) Assume Q is deducible.
    Then P > Q is deducible.
Proof.
    (1) Q > (P > Q) 
        is deducible (by Implosion).
    (2) P > Q 
        is deducible(by Detachment, 0, 1).
End.


Proposition WeakeningImplication.
    (0) Assume Q > R is deducible.
    Then (P > Q) > (P > R) is deducible.
Proof.
    (1) P > (Q > R)
        is deducible (by Weakening, 0).
    (2) (P > (Q > R)) > ((P > Q) > (P > R))
        is deducible (by Chain).
    (3) (P > Q) > (P > R)
        is deducible (by Detachment, 1, 2).
End.

Proposition Transitivity.
    (0) Assume P > Q and Q > R are deducible.
    Then P > R is deducible.
Proof.
    (1) (P > Q) > (P > R) 
        is deducible (by WeakeningImplication, 0).
    (2) P > R
        is deducible (by Detachment, 0, 1).
End.

# Just from the basic axioms.
Proposition Identity. 
    P > P is deducible.
Proof.
    (1) (P > ((P > P) > P)) > ((P > (P > P)) > (P > P))
        is deducible (by Chain).
    (2) P > ((P > P) > P)
        is deducible (by Implosion).
    (3) (P > (P > P)) > (P > P)
        is deducible (by 1, 2, Detachment).
    (4) P > (P > P)
        is deducible (by Implosion).
    (5) P > P
        is deducible (by 3, 4, Detachment).
End.



Proposition.
    (0) Suppose P > (P > Q) is deducible.
    Then P > Q is deducible.
Proof.
    (1) (P > (P > Q)) > ((P > P) > (P > Q))
        is deducible (by Chain).
    (2) (P > P) > (P > Q)
        is deducible (by 0, 1, Detachment).
    (3) P > P
        is deducible (by Identity).
    (4) P > Q
        is deducible (by 2, 3, Detachment).
End.



# Adding negation

Signature Falsum.
    F is a formula.

Let !P stand for P > F.

Axiom DoubleNegation.
    !!P > P is deducible.

Proposition Explosion.
    F > P is deducible.
Proof.
    (1) F > ((P > F) > F)
        is deducible (by Implosion).
    (2) (((P > F) > F)) > P
        is deducible (by DoubleNegation).
    (3) F > P
        is deducible (by Transitivity, 1, 2).
End.
