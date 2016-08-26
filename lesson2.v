From mathcomp Require Import all_ssreflect all_algebra all_fingroup.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(** -------------------------------------------- *)

(** #<div class='slide'># 

** Lesson 2 MathCompWS ITP'2016 
#</div># *)


(** #<div class='slide'># 
** Big operators

   - a library to manipulate cumulative operators
   - an encapsulation of the fold function
*)

Section F.

(*
Fixpoint foldr f z s := if s is x :: s' then f x (foldr f z s') else z.
*)

Definition f x := x.*2.
Definition g x y := x + y.
Definition r := [::1; 2; 3].
Lemma bfold : foldr [eta (g \o f)] 0 r = 12.
Proof.
rewrite /=.
rewrite /f.
rewrite /g.
by [].
Qed.

End F.

(** #</div># *)

(** -------------------------------------------- *)

(**  #<div class='slide'>#  

   ** Notation

   - the basic \big notation
   - operations on elements of a list
   - special notations for usual case (\sum, \prod, \bigcap ..) 
*)

Lemma bfoldl : \big[addn/0]_(i <- [::1; 2; 3]) i.*2 = 12.
Proof.
set bigop := BigOp.bigop.
rewrite /bigop.
rewrite big_cons.
rewrite big_cons.
rewrite big_cons.
rewrite big_nil.
by [].
Qed.

Lemma bfoldlm : \big[muln/1]_(i <- [::1; 2; 3]) i.*2 = 48.
Proof.
set bigop := BigOp.bigop.
rewrite /bigop.
rewrite big_cons.
rewrite big_cons.
rewrite big_cons.
rewrite big_nil.
by [].
Qed.

(** #</div># *)

(** -------------------------------------------- *)

(**  #<div class='slide'>#  
   ** Range 
   - different ranges are provided
*)

Lemma bfoldl1 : \sum_(1 <= i < 4) i.*2 = 12.
Proof.
set bigop := BigOp.bigop.
rewrite /bigop.
have bl := big_ltn.
have be := big_geq.
rewrite bl.
  rewrite bl.
    rewrite bl.
      rewrite be.
        by [].
      by [].
    by [].
  by [].
by [].
Qed.

Lemma bfoldl2 : \sum_(i < 4) i.*2 = 12.
Proof.
set bigop := BigOp.bigop.
Print ordinal.
rewrite /bigop.
rewrite big_ord_recl.
Check lift.
Print bump.
rewrite /=.
rewrite big_ord_recl.
rewrite /=.
rewrite big_ord_recl.
rewrite big_ord_recl.
rewrite big_ord0.
by [].
Qed.
Qed.

Lemma bfoldl3 : \sum_(i : 'I_4) i.*2 = 12.
Proof.
exact: bfoldl2.
Qed.


(** #</div># *)

(** -------------------------------------------- *)

(**  #<div class='slide'>#  
   ** Filtering 
   - selecting some elements of the range 
*)

Lemma bfoldl4 : \sum_(i <- [::1; 2; 3; 4; 5; 6] | ~~ odd i) i = 12.
Proof.
set bigop := BigOp.bigop.
rewrite /bigop.
have bp0 := big_pred0.
have bC := big_hasC.
have bmc := big_mkcond.
pose x :=  \sum_(i < 8 | ~~ odd i) i.
pose y :=  \sum_(0 <= i < 8 | ~~ odd i) i.
rewrite big_cons.
rewrite /=.
rewrite big_cons.
rewrite /=.
rewrite big_cons.
rewrite /=.
rewrite big_cons.
rewrite /=.
rewrite big_cons.
rewrite /=.
rewrite big_cons.
rewrite /=.
rewrite big_nil.
by [].
Qed.


(** #</div># *)

(** -------------------------------------------- *)

(**  #<div class='slide'>#  
   ** Switching range
   - changing representation (big_nth, big_mkord).
*)

Lemma bswitch :  
  \sum_(i <- [::1; 2; 3]) i.*2 = \sum_(i < 3) (nth 0 [::1; 2; 3] i).*2.
Proof.
have bn := big_nth.
rewrite (big_nth 0).
rewrite /=.
have H1 := big_mkord.
rewrite big_mkord.
by [].
Qed.


(** #</div># *)

(** -------------------------------------------- *)

(**  #<div class='slide'>#  
   ** Few examples from the library
*)

(** 
   - prime.v
*)

Check divn_count_dvd.
Check logn_count_dvd.
Check dvdn_sum.
Check totient_count_coprime.
Check totientE.


(**- poly.v
*)

Check horner_sum.
Check nderiv_taylor.

(**

   - matrix.v
*)

Check expand_cofactor.
Check expand_det_row.

(** 
   - vector.v
*)

Check sumv_sup.
Check freeP.


(** #</div># *)

(** -------------------------------------------- *)

(**  #<div class='slide'>#  
  ** Big operators and equality
  - replacing function and/or predicate 
 *)

Lemma beql : 
  \sum_(i < 4 | odd i || ~~ odd i) i.*2 =  \sum_(i < 4) i.*2.
Proof.
have ebl := eq_bigl.
apply: eq_bigl  => /=.
move=> n.
by case: odd.
Qed.

Lemma beqr : 
  \sum_(i < 4) i.*2 = \sum_(i < 4) (i + i).
Proof.
have ebr := eq_bigr.
apply: eq_bigr.
rewrite /=.
move=> n _.
rewrite addnn.
by [].
Qed.

Lemma beq : 
  \sum_(i < 4 | odd i || ~~ odd i) i.*2 = \sum_(i < 4) (i + i).
Proof.
have eb := eq_big.
apply: eq_big => [n|i Hi]; first by case: odd.
by rewrite addnn.
Qed.

(** #</div># *)

(** -------------------------------------------- *)

(**  #<div class='slide'>#  
  ** Monoid structure
  - regrouping thanks to associativity
 *)

Lemma bmon1 : \sum_(i <- [::1; 2; 3]) i.*2 = 12.
Proof.
have bc := big_cat.
rewrite -[[::1; 2; 3]]/([::1] ++ [::2; 3]).
rewrite big_cat.
rewrite /=.
rewrite !big_cons !big_nil.
by [].
Qed.

Lemma bmon2 : \sum_(1 <= i < 4) i.*2 = 12.
Proof.
have bcn := big_cat_nat.
rewrite (big_cat_nat _ _ _ (isT: 1 <= 2)).
  rewrite /=.
  rewrite big_ltn //=.
  rewrite big_geq //.
  by rewrite 2?big_ltn //= big_geq.
by [].
Qed.

Lemma bmon3 : \sum_(i < 4) i.*2 = 12.
Proof.
have borl := big_ord_recl.
have borr := big_ord_recr.
rewrite big_ord_recr.
rewrite /=.
rewrite !big_ord_recr //=.
rewrite big_ord0.
by [].
Qed.

Lemma bmon4 : \sum_(i < 8 | ~~ odd i) i = 12.
Proof.
have H := big_mkcond.
rewrite big_mkcond.
rewrite /=.
rewrite !big_ord_recr /=.
rewrite big_ord0.
by [].
Qed.

(** #</div># *)

(** -------------------------------------------- *)

(**  #<div class='slide'>#  
  ** Abelian Monoid structure
  - dispatching thanks to communitativity
 *)


Lemma bab : \sum_(i < 4) i.*2 = 12.
Proof.
have bd1 := bigD1.
pose x := Ordinal (isT : 2 < 4).
rewrite (bigD1 x).
  rewrite /=.
  rewrite big_mkcond /=.
  rewrite !big_ord_recr /= big_ord0.
  by [].
by [].
Qed.

Lemma bab1 : \sum_(i < 4) (i + i.*2) = 18.
Proof.
have H := big_split.
rewrite big_split /=.
rewrite !big_ord_recr ?big_ord0 /=.
by [].
Qed.

Lemma bab2 :
  \sum_(i < 3) \sum_(j < 4) (i + j) = \sum_(i < 4) \sum_(j < 3) (i + j).
Proof.
have H := exchange_big.
have H1 := reindex_inj.
rewrite exchange_big.
rewrite /=.
apply: eq_bigr.
move=> i _.
apply: eq_bigr.
move=>   j _.
by rewrite addnC.
Qed.

(** #</div># *)

(** -------------------------------------------- *)

(**  #<div class='slide'>#  
  ** Distributivity
  - exchanging sum and product 
 *)

Lemma bab3 : \sum_(i < 4) (2 * i) = 2 * \sum_(i < 4) i.
Proof.
have H := big_distrr.
by rewrite big_distrr.
Qed.

Lemma bab4 : 
  (\prod_(i < 3) \sum_(j < 4) (i ^ j)) = 
  \sum_(f : {ffun 'I_3 -> 'I_4}) \prod_(i < 3) (i ^ (f i)).
Proof.
have H := big_distr_big.
have H1 := big_distr_big_dep.
rewrite  (big_distr_big ord0).
rewrite /=.
apply: eq_bigl.
move=> f.
rewrite /=.
apply/forallP.
rewrite /=.
by [].
Qed.

(** #</div># *)

(** -------------------------------------------- *)

(**  #<div class='slide'>#  
  ** Property, Relation and Morphism
   - higher-order properties 
 *)

Lemma bap n : ~~ odd (\sum_(i < n) i.*2). 
Proof.
have bi := big_ind.
have bi2 := big_ind2.
have bm := big_morph.
elim/big_ind: _.
- by [].
- move=> x y.
  rewrite odd_add.
  case: odd.
     by [].
  by [].
move=> i _.
by rewrite odd_double.
Qed.

(** #</div># *)

Definition leibnizn m n := m.+1 *  'C(m, n).

(** -------------------------------------------- *)

(**  #<div class='slide'>#  
     ** Leibniz Triangle
   *)


Notation "''L' ( n , m )" := (leibnizn n m)
  (at level 8, format "''L' ( n ,  m )") : nat_scope.

Lemma leibn0 n : 'L(n, 0) = n.+1.
Proof. by rewrite /leibnizn bin0 muln1. Qed.

Lemma leibnn n : 'L(n, n) = n.+1.
Proof. by rewrite /leibnizn binn muln1. Qed.

Lemma leibn_small m n : m < n -> 'L(m, n) = 0.
Proof. by move=> Hmn; rewrite /leibnizn bin_small ?muln0. Qed.

Lemma leibn_sub m n :  n <= m -> 'L(m, m - n) = 'L(m, n).
Proof. by move=> Lnm; rewrite /leibnizn bin_sub. Qed.
 
Lemma leibn_gt0 m n : n <= m -> 0 < 'L(m, n).
Proof. by move=> Lnm; rewrite /leibnizn muln_gt0 bin_gt0. Qed.

Lemma bin_up m n : m.+1 * 'C(m, n) = (m.+1 - n) * 'C(m.+1, n).
Proof.
elim: m n => [|m IHm] [|n] //.
case: (leqP m.+1 n)=> [H|H].
  by apply/eqP; rewrite bin_small // muln0 eq_sym muln_eq0 subn_eq0 ltnS H.
rewrite subSS mulSn {2}binS mulnDr !IHm addnA subSS -mulSn -subSn //.
by rewrite -mulnDr -binS.
Qed.

Lemma leibn_up m n : m.+2 * 'L(m, n) = (m.+1 - n) * 'L(m.+1, n).
Proof. by rewrite /leibnizn bin_up mulnCA. Qed.

Lemma bin_right m n : n.+1 * 'C(m.+1, n.+1) = (m.+1 - n) * 'C(m.+1, n).
Proof.
elim: m n => [|m IHm] [|n] //; first by rewrite bin0 bin1 muln1 mul1n.
rewrite [in RHS]binS subSS mulnDr -IHm -mulnDl -mul_Sm_binm.
case: (leqP n m.+1)=> [H|H]; first by rewrite addnS subnK.
by rewrite bin_small ?muln0 // ltnW.
Qed.

Lemma leibn_right m n : n.+1 * 'L(m.+1, n.+1) = (m.+1 - n) * 'L(m.+1, n).
Proof. by rewrite /leibnizn mulnCA bin_right mulnCA. Qed.

Lemma leibnS m n : 
  'L(m.+1, n.+1) * 'L(m.+1, n) = 'L(m, n) * ('L(m.+1, n.+1) + 'L(m.+1, n)).
Proof.
case: (leqP n m.+1) => H; last first.
  by rewrite leibn_small 1?ltnW // leibn_small.
apply/eqP.
have /eqn_pmul2l<- : m.+2 * n.+1 > 0 by [].
apply/eqP.
rewrite -[_.+2 * _ * _]mulnA [n.+1 * _]mulnA.
rewrite [in RHS]mulnCA -[_.+2 * _ * _ in RHS]mulnA.
rewrite mulnDr leibn_right.
rewrite mulnDr [m.+2 * (_.+1 * _) in RHS] mulnCA.
rewrite -{1}leibn_up [in RHS]mulnC mulnDl.
rewrite -mulnA ['L(_,_) * _]mulnC 2!mulnA.
rewrite -mulnDl; congr (_ * _).
rewrite [X in _ = X + _]mulnA [X in _ = _ + X]mulnA.
rewrite -mulnDl; congr (_ * _).
by rewrite [_ * _.+2 in RHS]mulnC -mulnDr addnS subnK.
Qed.

Lemma lcmn_swap a b c :
    a * c = b * (a + c) -> lcmn b c = lcmn a c.
Proof.
case: a => [|a].
  by move/eqP; rewrite add0n eq_sym muln_eq0=> /orP[] /eqP->; rewrite !(lcm0n,lcmn0). 
case: b => [|b].
  by move/eqP; rewrite muln_eq0=> /orP[] /eqP->; rewrite !(lcm0n,lcmn0).
case: c => [|c H].
  by move/eqP; rewrite addn0 eq_sym muln0 muln_eq0=> /orP[] /eqP->; 
     rewrite !(lcm0n,lcmn0).
apply/eqP.
have /eqn_pmul2r<- : a.+1 * gcdn b.+1 c.+1 > 0 by rewrite muln_gt0 gcdn_gt0.
  rewrite {2}muln_gcdr H [b.+1 * _]mulnC mulnDl gcdnDl.
  by rewrite mulnCA muln_lcm_gcd -muln_gcdl !mulnA muln_lcm_gcd [X in _ == X]mulnAC.
Qed.

Lemma leibn_lcm_swap m n :
   lcmn 'L(m.+1, n) 'L(m, n) = lcmn 'L(m.+1, n) 'L(m.+1, n.+1).
Proof.
rewrite ![lcmn 'L(m.+1, n) _]lcmnC.
by apply/lcmn_swap/leibnS.
Qed.

(** #</div># *)

(** -------------------------------------------- *)

(**  #<div class='slide'>#  
    ** Lcm bigop
   *)


Notation "\lcm_ ( i < n ) F" :=
 (\big[lcmn/1%N]_(i < n ) F%N) 
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \lcm_ ( i  <  n  ) '/  '  F ']'") : nat_scope.

Canonical Structure lcmn_moid : Monoid.law 1 :=
  Monoid.Law lcmnA lcm1n lcmn1.
Canonical lcmn_comoid := Monoid.ComLaw lcmnC.

Lemma leib_line n i k : lcmn 'L(n.+1, i) (\lcm_(j < k) 'L(n, i + j)) = 
                   \lcm_(j < k.+1) 'L(n.+1, i + j).
Proof.
elim: k i => [i|k1 IH i].
  by rewrite big_ord_recr !big_ord0 /= lcmn1 lcm1n addn0.
rewrite big_ord_recl /= addn0.
rewrite lcmnA leibn_lcm_swap.
rewrite (eq_bigr (fun j : 'I_k1 => 'L(n, i.+1 + j))).
rewrite -lcmnA.
rewrite IH.
rewrite [RHS]big_ord_recl.
rewrite addn0; congr (lcmn _ _).
by apply: eq_bigr => j _; rewrite addnS.
move=> j _.
by rewrite addnS.
Qed.

Lemma leib_corner n : \lcm_(i < n.+1) 'L(i, 0) = \lcm_(i < n.+1) 'L(n, i).
Proof.
elim: n => [|n IH]; first by rewrite !big_ord_recr !big_ord0 /=.
rewrite big_ord_recr /= IH lcmnC.
rewrite (eq_bigr (fun i : 'I_n.+1 => 'L(n, 0 + i))) //.
by rewrite leib_line.
Qed.

Lemma main_result n : 2^n.-1 <= \lcm_(i < n) i.+1.
Proof.
case: n => [|n /=]; first by rewrite big_ord0.
have <-: \lcm_(i < n.+1) 'L(i, 0) = \lcm_(i < n.+1) i.+1.
  by apply: eq_bigr => i _; rewrite leibn0.
rewrite leib_corner.
have -> : forall j,  \lcm_(i < j.+1) 'L(n, i) = n.+1 *  \lcm_(i < j.+1) 'C(n, i).
  elim=> [|j IH]; first by rewrite !big_ord_recr !big_ord0 /= !lcm1n.
  by rewrite big_ord_recr [in RHS]big_ord_recr /= IH muln_lcmr.
rewrite (expnDn 1 1) /=  (eq_bigr (fun i : 'I_n.+1 => 'C(n, i))) => 
       [|i _]; last by rewrite !exp1n !muln1.
have <- : forall n m,  \sum_(i < n) m = n * m.
  by move=> m1 n1; rewrite sum_nat_const card_ord.
apply: leq_sum => i _.
apply: dvdn_leq; last by rewrite (bigD1 i) //= dvdn_lcml.
apply big_ind => // [x y Hx Hy|x H]; first by rewrite lcmn_gt0 Hx.
by rewrite bin_gt0 -ltnS.
Qed.

(** #</div># *)

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