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

boolean connective, computation is progress, proof by cases
Objective: infitude of primes

proof sketch, we need arithmetic (and a library)!
A bit of arithmetic, ssr style

to say:
 - move
 - rewrite //
 - Search
 - .. le .. le ..

-------------------------------------------- *)

Lemma example m p : prime p ->
  p %| m `! + 1 -> ~~ (p <= m).
Proof.
move=> prime_p.
apply: contraL.
move=> leq_p_m.
rewrite dvdn_addr.
  rewrite gtnNdvd.
    by [].
    by [].
  by apply: prime_gt1.
apply: dvdn_fact.
rewrite leq_p_m andbT.
by apply: prime_gt0.
Qed.

(** ** Bool is not enough

bla

to say: 
  - exists/curry howard
  - bool/Prop
  - reflect

-------------------------------------------- *)

(** ** Views and intro patterns

to say:
 - move= /andP[]
 - eqP
 - ==

-------------------------------------------- *)

(** ** Infinitude of primes *)

Lemma dvdn_fact m n : 0 < m <= n -> m %| n`!.
Proof.
case: m => //= m; elim: n => //= n IHn; rewrite ltnS leq_eqVlt.
by case/orP=> [/eqP-> | /IHn]; [apply: dvdn_mulr | apply: dvdn_mull].
Qed.

Lemma prime_above m : exists2 p, m < p & prime p.
Proof.
have /pdivP[p pr_p p_dv_m1]: 1 < m`! + 1 by rewrite addn1 ltnS fact_gt0.
exists p => //; rewrite ltnNge; apply: contraL p_dv_m1 => p_le_m.
by rewrite dvdn_addr ?dvdn_fact ?prime_gt0 // gtnNdvd ?prime_gt1.
Qed.
