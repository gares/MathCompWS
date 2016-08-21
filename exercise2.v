(* From mathcomp Require Import all_ssreflect. *)
From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Lemma sum_ord_const n m :  \sum_(i < n) m = n * m.
Proof.  by rewrite sum_nat_const card_ord. Qed.

(** 
  ----
  ** Exercise 1 
*)

(** 
   Prove the following state by induction and by following Gauss proof.
 *)

Lemma gauss_ex : forall n, (\sum_(i < n) i).*2 = n * n.-1.
Proof.

(**
   -----
  ** Hints 
   Different proofs are possible. Try them both!

   *** The direct one by simple induction
   - base case : 

Search _ (\big[_/_]_(_ < 0 | _ ) _).

   - inductive case : 

Search _ (_.*2) (_ * _).

Search _ muln ""D"".

Search _ muln ""C"".

   *** The tricky one without induction

       (1 + 2 + 3).*2 = (1 + 2 + 3) + (3 + 2 + 1) = ((1 + 3) + (2 + 2) + (3 + 1))
                      = 4 * 3



Check rev_ord_proof.
 
Print rev_ord.
 
Check (reindex_inj rev_ord_inj).

Check big_split.

Search _ (_.*2) (_ + _).

Check  sum_ord_const.

*)

(** 
  ----
   ** Exercise 2
*)

Lemma sum_odd1 : forall n, \sum_(i < n) (2 * i + 1) = n ^ 2.
Proof.
Qed.

(**
   -----
  ** Hints 

Check big_split.

Check big_distrr.

Chek gauss_ex.

Check sum_ord_const.

*)

(** 
  ----
  ** Exercise 3
*)

Lemma sum_exp : forall x n, x ^ n.+1 - 1 = (x - 1) * \sum_(i < n.+1) x ^ i.
Proof.
Qed.

(**
   -----
  ** Hints 

Check mulnBl.

Check big_distrr.

Check big_ord_recr.

Check big_ord_recl.

Check eq_bigr.

Check expnS.

*)


(**
  ----
 ** Exercise 4
*)

(** Prove the following state by induction and by using a similar trick
   as for Gauss noticing that n ^ 3 = n * (n ^ 2) *)

Lemma bound_square : forall n, \sum_(i < n) i ^ 2 <= n ^ 3.
Proof.

(**
   -----
  ** Hints 

Check expnS.

Check sum_ord_const.

Check big_ind2.

*)


(**
  ----
  ** Exercise 5 
*)

(**
  building a monoid law 
*)

Section cex.

Variable op2 : nat -> nat -> nat.

Hypothesis op2n0 : right_id 0 op2.

Hypothesis op20n : left_id 0 op2.

Hypothesis op2A : associative op2.

Hypothesis op2add : forall x y, op2 x y = x + y.

Canonical Structure op2Mon : Monoid.law 0 :=
  Monoid.Law op2A op20n op2n0.

Lemma ex_op2 : \big[op2/0]_(i < 3) i = 3.
Proof. by rewrite !big_ord_recr big_ord0 /= !op2add. Qed.

End cex.


(** 
  ----
  ** Exercise 6
*)

(** 
   Try to formalize the following problem 
*)

(** 
  Given a parking  where the boolean indicates if the slot is occupied or not 
*)

Definition parking n := 'I_n -> 'I_n -> bool.

(**
   Number of cars at line i 
*)               

Definition sumL n (p : parking n) i := \sum_(j < n) p i j.

(**
   Number of cars at column j 
*)

Definition sumC n (p : parking n) j := \sum_(i < n) p i j.

(**
   Show that if 0 < n there is always two lines, or two columns, or a column and a line
   that have the same numbers of cars 
*)

