(*
Authors: Makarius Wenzel (2018)

Some Isabelle/Naproche examples for testing.
*)

section \<open>Naproche-SAD texts within the Isabelle context\<close>

theory Test
  imports Naproche.Naproche
begin

subsection \<open>Inlined text\<close>

declare [[naproche_isabelle]]

forthel \<open>
[synonym element/-s] [synonym system/-s] [synonym reduct/-s] [synonym term/-s]

Signature Rewriting system.  A rewriting system is a notion.
Signature Term. A term is an object.

Let a,b,c,d,u,v,w,x,y,z denote terms.
Let R,S,T denote rewriting systems.

Signature Reduct.   A reduct of x in R is a term.

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

Definition NFRDef.  A normal form of x in R is a term y
                    such that x -R*> y and y has no reducts in R.

Lemma TermNF.   Let R be a terminating rewriting system.
                Every term x has a normal form in R.
Proof by induction. Obvious.

Lemma Newman.
    Any locally confluent terminating rewriting system is confluent.
Proof.
Let R be a rewriting system.
    Assume R is locally confluent and terminating.
    Let us demonstrate by induction that for all a,b,c
    such that a -R*> b,c there exists d such that b,c -R*> d.
        Let a,b,c be terms.
        Let us show that if a -R+> b,c then thesis.
            Assume a -R+> b,c.

            Take u such that a -R> u -R*> b.
            Take v such that a -R> v -R*> c.
            Take w such that u,v -R*> w.
            Take a normal form d of w in R.
    
            b -R*> d. Indeed take x such that b,d -R*> x.
            c -R*> d. Indeed take y such that c,d -R*> y.
        End.
    End.
End.
\<close>

naproche_problems

naproche_problem 1
  using assms(12) assms(13) assms(14) by auto

naproche_problem 2
  by (metis assms(11) assms(13) assms(14) assms(17) assms(18) assms(19) assms(9))

naproche_problem 3
  by (metis assms(11) assms(13) assms(20) assms(22) assms(24))

naproche_problem 4
  by (metis assms(11) assms(13) assms(20) assms(22) assms(24))

naproche_problem 5
  using assms(16) assms(20) assms(21) assms(22) assms(25) assms(26) by blast

naproche_problem 6
  by (simp add: assms(19) assms(20) assms(21) assms(27))

naproche_problem 7
  by (smt (verit, del_insts) assms(11) assms(14) assms(17) assms(18) assms(20) assms(21) assms(22) assms(23) assms(25) assms(27) assms(28))

naproche_problem 8
  by (metis assms(11) assms(13) assms(18) assms(20) assms(27) assms(28) assms(29))

naproche_problem 9
  by (smt (verit, del_insts) assms(11) assms(14) assms(17) assms(18) assms(20) assms(21) assms(22) assms(23) assms(26) assms(27) assms(28))

naproche_problem 10
  by (metis assms(11) assms(13) assms(18) assms(20) assms(27) assms(28) assms(30))

naproche_problem 11
  by simp

naproche_problem 12
  using assms(13) assms(20) assms(22) assms(24) by blast

naproche_problem 13
  by simp



subsection \<open>External text file\<close>

declare [[naproche_prove = false]]

forthel_file \<open>$NAPROCHE_HOME/examples/newman.ftl\<close>
forthel_file \<open>$NAPROCHE_HOME/examples/newman.ftl.tex\<close>

end
