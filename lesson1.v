From mathcomp Require Import all_ssreflect.
(** #<div class='slide vfill'># 
* Mathematical Components, an introduction


 - Welcome!
 - Objective: help you enter the MC library
#</div># *) 

(** -------------------------------------------- *)

(** #<div class='slide vfill'># 
** Spam

#<a href="http://math-comp.github.io/math-comp/book">Mathematical Components (the book)</a>#

#<img src="http://math-comp.github.io/math-comp/book/cover-front-web.png"/>#

#</div>#
-------------------------------------------- *)

(** #<div class='slide vfill'>#  
** Propaganda

 - For Isabelle users: it is like HOL
 - For Coq users: it is simpler
 - For newcomers: it works
#</div># *)

(** -------------------------------------------- *)

(** #<div class='slide vfill'>#  
** Lesson 1 (of 4)

 - Boolean reflection
 - Tactic language
#</div># *)

(** -------------------------------------------- *)

(** #<div class='slide vfill'>#  
** Boolean reflection in a nutshell

 - Bool datatype to represent mere propositions
 - Symbolic computation is a predictable, pervasive,
   form of automation
#</div># *)

(** -------------------------------------------- *)

(** #<div class='slide'># 
** The emblematic example

to say: .+1 , lt , = true , = mean equiv , by [] , elim , apply , rewrite
 
*)

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
by [].
Qed.

Lemma ltnS m n : (m.+1 <= n.+1) = (m <= n).
Proof.
by [].
Qed.

Lemma leqnn n : n <= n.
Proof.
elim: n => [|m IHm].
  by apply: leq0n.
rewrite ltnS.
by [].
Qed.

End Leq.


(** -------------------------------------------- *)
  
(** #<div class='slide'># 
** A logic in bool

 - One can also place conectives in bool
 - Here symbolic computation means progress
 - In bool EM holds 

#<a class='file' href='http://math-comp.github.io/math-comp/htmldoc/mathcomp.ssreflect.ssrbool.html'>ssrbool</a>#
*)

Module BoolLogic.

Definition negb b := if b then false else true.

Local Notation "~~ b" := (negb b).

Lemma negbK b : ~~ ~~ b = b.
Proof.
case: b.
  by [].
by [].
Qed.

Definition andb b1 b2 :=
  if b1 then b2 else false.

Local Notation "a && b" := (andb a b).

Lemma andbC b1 b2 : b1 && b2 = b2 && b1.
Proof.
by case: b1; case: b2.
Qed.

Definition orb b1 b2 :=
  if b1 then true else b2.

Local Notation "a || b" := (orb a b).

Lemma negb_and b1 b2 : ~~ (b1 && b2) = ~~ b1 || ~~ b2.
Proof.
by case: b1; case: b2.
Qed.

End BoolLogic.

(** -------------------------------------------- *)

(** #<div class='slide vfill'>#  
** Objective: infinitude of primes

Let's take a number m and exhibit a prime bigger than it.

Every natural number greater than 1 has at least one prime divisor. 
If we take m! + 1, then such prime divisor p can be shown to be grater
than m as follows.

By contra position we assume p <= m and we show p does not divide m! + 1.

Being smaller than m, p|m!, hence to divide m! + 1, p should divide 1, 
that is not possible since p is prime, hence greater than 1.
#</div># *)

(** -------------------------------------------- *)

(** #<div class='slide'># 
** Some arithmetic

#<a class='file' href='http://math-comp.github.io/math-comp/htmldoc/mathcomp.ssreflect.ssrnat.html'>ssrnat</a>#
#<a class='file' href='http://math-comp.github.io/math-comp/htmldoc/mathcomp.ssreflect.prime.html'>prime</a>#
#<a class='file' href='http://math-comp.github.io/math-comp/htmldoc/mathcomp.ssreflect.div.html'>div</a>#

to say: move, rewrite //, Search, [.. <= .. <= ..]

<<
Lemma contraL c b : (c -> ~~ b) -> b -> ~~ c.
Lemma dvdn_fact m n : 0 < m <= n -> m %| n`!.
Lemma gtnNdvd n d : 0 < n -> n < d -> (d %| n) = false.
Lemma dvdn_addr m d n : d %| m -> (d %| m + n) = (d %| n).
Lemma dvdn_fact m n : 0 < m <= n -> m %| n`!.
>>
*)

Module ExampleArith.

Lemma example m p : prime p ->
  p %| m `! + 1 -> ~~ (p <= m).
Proof.
move=> prime_p.
Search "contra".
apply: contraL.
move=> leq_p_m.
Search dvdn addn.
rewrite dvdn_addr.
  Search eq (_ < _) (_ %| _).
  rewrite gtnNdvd.
    by [].
    by [].
  Search leq prime.
  by apply: prime_gt1.
apply: dvdn_fact.
rewrite leq_p_m andbT.
by apply: prime_gt0. 
Qed.

End ExampleArith.

(** -------------------------------------------- *)

(** #<div class='slide'># 
** Bool is not enough

 - The bool data type is not closed under general quantifiers
 - Coq provides the [Prop] world for propositions
 - We need a way to relate the two worlds

to say: exists/curry howard, bool/Prop, reflect

*)

Module PropLogic.

Inductive and (A B:Prop) : Prop :=
  conj (a : A) (b : B).

Local Notation "A /\ B" := (and A B).

Lemma andC A B : A /\ B <-> B /\ A.
Proof.
split.
   move=> [a b].
   by split.
move=> [a b].
by split.
Qed.

Inductive ex A (P : A -> Prop) : Prop :=
  ex_intro (x : A) (px : P x).

Local Notation "'exists' x , p" := (ex (fun x => p)) (at level 200).

Lemma andP (a b : bool) : reflect (a /\ b) (a && b).
Proof.
apply: (iffP idP); 
  last by move=> [-> ->].
case: a; case: b => //.
Admitted.

End PropLogic.

(** -------------------------------------------- *)

(** #<div class='slide'># 
** Views and intro patterns
  - Two ways to use a "reflect"
   
#<div id='here'></div>#

to say:
 - move= /andP[]
 - eqP
 - ==

-------------------------------------------- *)

(** #<div class='slide'># 
** Infinitude of primes 
<<
Lemma pdivP n : 1 < n -> exists2 p, prime p & p %| n.	
Lemma dvdn_mull d m n : d %| n -> d %| m * n.
Lemma dvdn_mulr d m n : d %| m -> d %| m * n.
>>
*)

Module Primes.

Lemma dvdn_fact m n : 0 < m <= n -> m %| n`!.
Proof.
case: m => //= m.
elim: n => //= n IHn.
rewrite ltnS leq_eqVlt.
move=> /orP xxx.
case: xxx => [ /eqP-> | /IHn ].
  by apply: dvdn_mulr.
by apply: dvdn_mull.
Qed.

Lemma prime_above m : exists2 p, prime p & m < p.
Proof.
have /pdivP[p pr_p p_dv_m1]: 1 < m`! + 1 by rewrite addn1 ltnS fact_gt0.
exists p => //. rewrite /= ltnNge.
apply: contraL p_dv_m1 => p_le_m.
by rewrite dvdn_addr ?dvdn_fact ?prime_gt0 // gtnNdvd ?prime_gt1.
Qed.

End Primes.

(** -------------------------------------------- *)

(**
#
<div id='prev' onclick='prev_slide()'></div>
<div id='next' onclick='next_slide()'></div>
<script>
alignWithTop = true;
current = 0;
window.onload = function() {
  slides = document.getElementsByClassName('slide');
}
function next_slide() {
  current++;
  if (current >= slides.length) { current = slides.length - 1; }
  var element = slides[current];
  console.log(element);
  element.scrollIntoView(alignWithTop);
}
function prev_slide() {
  current--;
  if (current < 0) { current = 0; }
  var element = slides[current];
  element.scrollIntoView(alignWithTop);
}
</script>
# *)
