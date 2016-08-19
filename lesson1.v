(** * Mathematical Components, an introduction

objective and talks
-------------------------------------------- *)

(** ** Spam

the book
-------------------------------------------- *)

(** ** Lesson 1: SSR

    Tactic language
    Boolean reflection
-------------------------------------------- *)

(** ** Boolean reflection in a nutshell

    Bool datatype is simple
    Symbolic computation is automation
-------------------------------------------- *)

(** ** The emblematic example

to say:
 - .+1
 - lt
 - = true
 - = mean equiv
 - by []
 - elim
 - apply
 - rewrite
 
*)


From mathcomp Require Import all_ssreflect.
Module Leq.

Fixpoint leq (m n : nat) : bool :=
  match m, n with
  | p.+1, q.+1 => leq p q
  | 0, _ => true
  | _, _ => false
  end.

Local Notation "a <= b" := (leq a b).
Local Notation "a < b" := (leq a.+1 b).

Eval compute in 3 <= 7.
Eval compute in 6 <= 4.

Lemma leq0n n : (0 <= n) = true.
Proof.
(*D*)by []. Qed.

Lemma ltnS m n : (m.+1 <= n.+1) = (m <= n).
Proof.
(*D*)by []. Qed.

Lemma leqnn n : n <= n.
Proof.
(*D*) elim: n => [|m IHm].
(*D*)   by apply: leq0n.
(*D*) rewrite ltnS.
(*D*) by [].
(*D*) Qed.

End Leq.

(** ** A logic in bool

to say: 
 - andb negb orb
 - case

boolean connective, computation is progress, proof by cases *)

Module BoolLogic.

Definition negb b := if b then false else true.

Local Notation "~~ b" := (negb b).

Lemma negbK b : ~~ ~~ b = b.
Proof.
(*D*) case: b.
(*D*) by []. Qed.

Definition andb b1 b2 :=
(*D*) if b1 then b2 else false.

Local Notation "a && b" := (andb a b).

Lemma andbC b1 b2 : b1 && b2 = b2 && b1.
Proof.
(*D*) by case: b1; case: b2. Qed.

Definition orb b1 b2 :=
(*D*) if b1 then true else b2.

Local Notation "a || b" := (orb a b).

Lemma negb_and b1 b2 : ~~ (b1 && b2) = ~~ b1 || ~~ b2.
Proof.
(*D*) by case: b1; case: b2. Qed.

End BoolLogic.

(** ** Objective: infitude of primes

proof sketch

-------------------------------------------- *)

(** ** Requirements:

we need arithmetic (and a library)!
A bit of arithmetic, ssr style

to say:
 - move
 - rewrite //
 - Search
 - .. le .. le ..

-------------------------------------------- *)

About dvdn_fact.
About contraL.

Lemma example m p : prime p ->
  p %| m `! + 1 -> ~~ (p <= m).
Proof.
(*D*) move=> prime_p.
(*D*) apply: contraL.
(*D*) move=> leq_p_m.
(*D*) rewrite dvdn_addr.
(*D*)   rewrite gtnNdvd.
(*D*)     by [].
(*D*)     by [].
(*D*)   by apply: prime_gt1.
(*D*) apply: dvdn_fact.
(*D*) rewrite leq_p_m andbT.
(*D*) by apply: prime_gt0.
(*D*) Qed.

(** -------------------------------------------- *)

(** ** Bool is not enough

bla

to say: 
  - exists/curry howard
  - bool/Prop
  - reflect
*)

Module PropLogic.

Inductive and (A B:Prop) : Prop :=
  conj : A -> B -> A /\ B.

Local Notation "A /\ B" := (and A B).

Inductive ex (A:Type) (P:A -> Prop) : Prop :=
  ex_intro : forall x:A, P x -> ex (A:=A) P.

Local Notation "'exists' x , p" := (ex (fun x => p)).

End PropLogic.

(** -------------------------------------------- *)

(** ** Views and intro patterns

to say:
 - move= /andP[]
 - eqP
 - ==

-------------------------------------------- *)

(** ** Infinitude of primes *)

Lemma dvdn_fact m n : 0 < m <= n -> m %| n`!.
Proof.
(*D*) case: m => //= m; elim: n => //= n IHn; rewrite ltnS leq_eqVlt.
(*D*) by case/orP=> [/eqP-> | /IHn]; [apply: dvdn_mulr | apply: dvdn_mull].
(*D*) Qed.

Lemma prime_above m : exists2 p, m < p & prime p.
Proof.
(*D*) have /pdivP[p pr_p p_dv_m1]: 1 < m`! + 1 by rewrite addn1 ltnS fact_gt0.
(*D*) exists p => //; rewrite ltnNge; apply: contraL p_dv_m1 => p_le_m.
(*D*) by rewrite dvdn_addr ?dvdn_fact ?prime_gt0 // gtnNdvd ?prime_gt1.
(*D*) Qed.


