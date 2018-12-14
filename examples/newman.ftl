[synonym element/-s] [synonym system/-s] [synonym reduct/-s]

Signature ElmSort.  An element is a notion.
Signature RelSort.  A rewriting system is a notion.

Let a,b,c,d,u,v,w,x,y,z denote elements.
Let R,S,T denote rewriting systems.

Signature Reduct.   A reduct of x in R is an element.

Let x -R> y stand for y is a reduct of x in R.

Signature. x -R+> y is a relation.

Axiom TCDef.   x -R+> y <=> x -R> y \/ exists z : x -R> z -R+> y.
Axiom TCTrans.      x -R+> y -R+> z => x -R+> z.

Definition TCRDef.  x -R*> y <=> x = y \/ x -R+> y.
Lemma TCRTrans.     x -R*> y -R*> z => x -R*> z.

Definition CRDef.   R is confluent iff
    for all a,b,c  such that a -R*> b,c
    there exists d such that b,c -R*> d.

Definition WCRDef.  R is locally confluent iff
    for all a,b,c  such that a -R> b,c
    there exists d such that b,c -R*> d.

Definition Termin.  R is terminating iff for all a,b
    a -R+> b => b -<- a.

Definition NFRDef.  A normal form of x in R is an element y
                    such that x -R*> y and y has no reducts in R.

Lemma TermNF.   Let R be a terminating rewriting system.
                Every element x has a normal form in R.
Proof by induction. Obvious.

Lemma Newman.
    Any locally confluent terminating rewriting system is confluent.
Proof.
Let R be a rewriting system.
    Assume R is locally confluent and terminating.
    Let us demonstrate by induction that for all a,b,c
    such that a -R*> b,c there exists d such that b,c -R*> d.
    let a,b,c be elements.
        Assume a -R+> b,c.

        Take u such that a -R> u -R*> b.
        Take v such that a -R> v -R*> c.
        Take w such that u,v -R*> w.
        Take a normal form d of w in R.

        b -R*> d. Indeed take x such that b,d -R*> x.
        c -R*> d. Indeed take y such that c,d -R*> y.
    end.
qed.
