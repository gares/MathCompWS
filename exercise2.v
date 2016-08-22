(* From mathcomp Require Import all_ssreflect. *)
From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma sum_ord_const n m : \sum_(i < n) m = n * m.
Proof. by rewrite sum_nat_const card_ord. Qed.

(** -------------------------------------------- *)

(** #<div class='slide'># *)

(** 
  ----
  ** Exercise 1 
*)

(** 
   Prove the following state by induction and by following Gauss proof.
 *)

Lemma gauss_ex n : (\sum_(i < n) i).*2 = n * n.-1.
Proof.
Qed.

(** Hints

induction *)

Check big_ord_recr.
Check big_ord0.
Check doubleD.
Check muln2.
Check mulnDr.
Check addn2.
Check mulnC.

(** Hints

Gauss (1 + 2 + 3).*2 = (1 + 2 + 3) + (3 + 2 + 1) = ((1 + 3) + (2 + 2) + (3 + 1) *)

Check addnn.
Check reindex_inj.
Check big_split.
Check sum_ord_const.
Print rev_ord.
Check rev_ord_proof.
Check rev_ord_inj.
Check eq_bigr.

(** -------------------------------------------- *)

(** #<div class='slide'># *)


(** 
  ----
   ** Exercise 2
*)

Lemma sum_odd1 n : \sum_(i < n) (2 * i + 1) = n ^ 2.
Proof.
Qed.

(** Hints *)

Check big_split.
Check big_distrr.
Check mul2n.
Check mulnDr.
Check addn1.

(** -------------------------------------------- *)

(** #<div class='slide'># *)


(** 
  ----
  ** Exercise 3
*)

Lemma sum_exp x n : x ^ n.+1 - 1 = (x - 1) * \sum_(i < n.+1) x ^ i.
Proof.
Qed.

(** Hints *)

Check mulnBl.
Check big_distrr.
Check big_ord_recr.
Check eq_bigr.


(** -------------------------------------------- *)

(** #<div class='slide'># *)


(**
  ----
 ** Exercise 4
*)

(** Prove the following state by induction and by using a similar trick
   as for Gauss noticing that n ^ 3 = n * (n ^ 2) *)

Lemma bound_square n : \sum_(i < n) i ^ 2 <= n ^ 3.
Proof.
Qed.

(** Hints *)

Check big_ind2.
Check leq_add.
Check leq_exp2r.
Check expnS.
Check ltnW.

(** -------------------------------------------- *)

(** #<div class='slide'># *)


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

(** Prove that *)
Lemma ex_op2 : \big[op2/0]_(i < 3) i = 3.
Proof.
Qed.

End cex.

(** -------------------------------------------- *)

(** #<div class='slide'># *)


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

(**
#
<script>
alignWithTop = true;
current = 0;
slides = [];
function select_current() {
  for (var i = 0; i < slides.length; i++) {
    var s = document.getElementById('slideno' + i);
    if (i == current) {
      s.setAttribute('class','slideno selected');
    } else {
      s.setAttribute('class','slideno');
    }
  }	
}
function init_slides() {
  var toolbar = document.getElementById('panel-wrapper');
  if (toolbar) {
  var tools = document.createElement("div");
  var tprev = document.createElement("div");
  var tnext = document.createElement("div");
  tools.setAttribute('id','tools');
  tprev.setAttribute('id','prev');
  tprev.setAttribute('onclick','prev_slide();');
  tnext.setAttribute('id','next');
  tnext.setAttribute('onclick','next_slide();');
  toolbar.appendChild(tools);
  tools.appendChild(tprev);
  tools.appendChild(tnext);
  
  slides = document.getElementsByClassName('slide');
  for (var i = 0; i < slides.length; i++) {
    var s = document.createElement("div");
    s.setAttribute('id','slideno' + i);
    s.setAttribute('class','slideno');
    s.setAttribute('onclick','goto_slide('+ i +');');
    s.innerHTML = i;
    tools.appendChild(s);
  }
  select_current();
  } else {
  //retry later
  setTimeout(init_slides,100);	  
  }
}
function on_screen(rect) {
  return (
    rect.top >= 0 &&
    rect.top <= (window.innerHeight || document.documentElement.clientHeight)
  );
}
function update_scrolled(){
  for (var i = 0; i < slides.length; i++) {
    var rect = slides[i].getBoundingClientRect();
      if (on_screen(rect)) {
        current = i;
        select_current();	
    }
  }
}
function goto_slide(n) {
  current = n;
  var element = slides[current];
  console.log(element);
  element.scrollIntoView(alignWithTop);
  select_current();
}
function next_slide() {
  current++;
  if (current >= slides.length) { current = slides.length - 1; }
  var element = slides[current];
  console.log(element);
  element.scrollIntoView(alignWithTop);
  select_current();
}
function prev_slide() {
  current--;
  if (current < 0) { current = 0; }
  var element = slides[current];
  element.scrollIntoView(alignWithTop);
  select_current();
}
window.onload = init_slides;
window.onscroll = update_scrolled;
</script>
# *)