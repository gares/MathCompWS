From mathcomp Require Import all_ssreflect all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Obligation Tactic := idtac.

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** #<div class='slide vfill'># 
** The Matrix library

This library relies a lot on the #<a href="http://math-comp.github.io/math-comp/htmldoc/mathcomp.algebra.ssralg.html">algebraic hierarchy</a>#

Extensive documentation in the header of the library #<a href="http://math-comp.github.io/math-comp/htmldoc/mathcomp.algebra.matrix.html">matrix</a>#

----

* Roadmap for the lesson:
 - the theory of rings and fields
 - definition of matrices
 - main theorems
 - help with depend types
 - vector spaces as matrices

#</div>#
*)
Module DefinitionMatrices.
(**

#<div class='slide vfill'># 

** Defining Matrices

(Credits "ITP 2013 tutorial: The Mathematical Components library" by Enrico Tassi and Assia Mahboubi #<a href="http://ssr.msr-inria.inria.fr/doc/tutorial-itp13/">material here</a>#)

*)
Reserved Notation "''M[' R ]_ n"    (at level 8, n at level 2, format "''M[' R ]_ n").
Reserved Notation "''M[' R ]_ ( m , n )" (at level 8, format "''M[' R ]_ ( m ,  n )").

Reserved Notation "\matrix_ ( i , j ) E"
  (at level 36, E at level 36, i, j at level 50,
   format "\matrix_ ( i ,  j )  E").

Reserved Notation "x %:M"   (at level 8, format "x %:M").
Reserved Notation "A *m B" (at level 40, left associativity, format "A  *m  B").
Reserved Notation "A ^T"    (at level 8, format "A ^T").
Reserved Notation "\tr A"   (at level 10, A at level 8, format "\tr  A").
(**

** A matrix is a 2-dimension array

*)
Inductive matrix (R : Type) (m n : nat) : Type :=
  Matrix of {ffun 'I_m * 'I_n -> R}.
(**

Some notations : size inside parentheses, type of coefficients inside
square brackets. NB: In the library, the type of coefficients can also
be ommitted.

*)
Notation "''M[' R ]_ ( m , n )" := (matrix R m n) : type_scope.
Notation "''M[' R ]_ n" := 'M[R]_(n, n) : type_scope.

(* Test *)
Check 'M[nat]_(2,3).
Check 'M[nat]_2.
(**

"matrix" is just a tag over ffun: it inherits from its structure We
can "transfer" automatically all structures from the type of finite
functions by "trivial subTyping".

*)
Definition mx_val R m n (A : 'M[R]_(m,n)) : {ffun 'I_m * 'I_n -> R} :=
  let: Matrix g := A in g.

Canonical matrix_subType R m n :=
  Eval hnf in [newType for @mx_val R m n].

Definition matrix_eqMixin (R : eqType) m n :=
  Eval hnf in [eqMixin of 'M[R]_(m, n) by <:].
Canonical matrix_eqType (R : eqType) m n:=
  Eval hnf in EqType 'M[R]_(m, n) (matrix_eqMixin R m n).
Definition matrix_choiceMixin (R : choiceType) m n :=
  [choiceMixin of 'M[R]_(m, n) by <:].
Canonical matrix_choiceType (R : choiceType) m n :=
  Eval hnf in ChoiceType 'M[R]_(m, n) (matrix_choiceMixin R m n).
Definition matrix_countMixin (R : countType) m n :=
  [countMixin of 'M[R]_(m, n) by <:].
Canonical matrix_countType (R : countType) m n :=
  Eval hnf in CountType 'M[R]_(m, n) (matrix_countMixin R m n).
Canonical matrix_subCountType (R : countType) m n :=
  Eval hnf in [subCountType of 'M[R]_(m, n)].
Definition matrix_finMixin (R : finType) m n :=
  [finMixin of 'M[R]_(m, n) by <:].
Canonical matrix_finType (R : finType) m n :=
  Eval hnf in FinType 'M[R]_(m, n) (matrix_finMixin R m n).

(**
Test overloaded "_ == _" notation
*)
Check [eqType of 'M[nat]_2].
Check forall A : 'M[nat]_2, A == A.
(**

Since matrices over nat are comparable with _ == _, matrices over
matrices over nat are also comparable

*)
Check forall AA : 'M[ 'M[nat]_3 ]_2, AA == AA.
(**

We define a coercion in order to access elements as if matrices were
functions.

*)
Definition fun_of_mx R m n (A : 'M[R]_(m,n)) : 'I_m -> 'I_n -> R :=
fun i j => mx_val A (i, j).  Coercion fun_of_mx : matrix >-> Funclass.

Check forall (A : 'M[nat]_3) i j, A i j == 37.
(**

We provide a notation to build matrices from a general term.

*)
Definition mx_of_fun R m n (F : 'I_m -> 'I_n -> R) : 'M[R]_(m,n) :=
  Matrix [ffun ij => F ij.1 ij.2].
Notation "\matrix_ ( i , j ) E" := (mx_of_fun (fun i j => E))
  (at level 36, E at level 36, i, j at level 50) : ring_scope.

Check \matrix_(i,j) (i - j)%N  :  'M[nat]_(3,4).


End DefinitionMatrices.
(**
#</div>#
#<div class='slide vfill'># 
*)
Module MatrixProperties.
(**

** Main Theorems

We now show the most used theorems for matrix manipulation.

** mxE

mxE is an equation to compute a term in the matrix at given
coordinates: it extracts the general term of the matrix and compute
the substitution of indexes. It is generally the right move when you
have <pre>(A complicated matrix) i j</pre> in your goal.

*)
Check mxE.
(**

** matrixP 

matrixP is the "extensionality theorem" for matrices, it says two
matrices are equal if and only if all their coefficients are pairwise
equal.

*)
Check matrixP.
(**

** operations on matrices

*** specific operation: trace and transpose

(do not confuse the names)

*)
Print mxtrace.
Locate "\tr".

Print trmx.
Locate "^T".
(**

*** specific operation scalar matrix

*)
Print scalar_mx.
Locate "%:M".
(**

*** matrices on rings are provided with a R-module canonical structure.

But not a ring as the multiplication is heterogeneous.

*)
Lemma test1 (R : ringType) m n (A B : 'M[R]_(m,n)) : A + B = B + A.
Proof. exact: addrC. Qed.

Print mulmx.

Lemma test2 (R : ringType) m n (a : R) (A : 'M[R]_(m,n)) : a *: A = a%:M *m A.
Proof. by rewrite mul_scalar_mx. Qed.
(**

*** square matrices with explicit non zero size have a ring canonical structure.

This ring product coincides with the matrix product.

*)
Lemma test3 (R : ringType) n (A B : 'M[R]_n.+1) : A * B = A *m B.
Proof. reflexivity. Qed.
(**

*** specific operation: the determinant.

*)
Print determinant.
Locate "\det".
(**

*** square matrices on a commutative unit ring with explicit non zero size have a unit ring canonical structure.

and these notions of inversibility are definitionally equivalent.
*)
Lemma test4 (R : comUnitRingType) n (A : 'M[R]_n.+1) : 
  (unitmx A) = (A \is a GRing.unit)
  /\ (A \is a GRing.unit) = (\det A \is a GRing.unit).
Proof. split; reflexivity. Qed.

End MatrixProperties.

(*
#<div class='slide vfill'># 
** connexion with graphs
*)

Section mxgraph.

Variable (n' : nat) (R : realFieldType).
Let n := n'.+1.
Let T := 'I_n.
Implicit Types (A : 'M[R]_n) (x y z : T).

Definition adjacency (g : rel T) : 'M[R]_n :=
  \matrix_(i < n, j < n) (g i j)%:R.

Definition adjrel A : rel T := fun x y => A x y > 0.

Lemma adjacencyK g : adjrel (adjacency g) =2 g.
Proof. by move=> x y; rewrite /adjrel !mxE; case: g; rewrite // ltr01. Qed.

Notation "k .-path g x y" := [set p : k.-tuple _ | path g x p & last x p == y]
  (at level 2, g, x, y at next level, format "k .-path  g  x  y") : type_scope.

Lemma gpath_count k g x y : (adjacency g ^+ k) x y = #|k.-path g x y|%:R.
Proof.
elim: k=> [|k IHk] in x y *.
  rewrite expr0 mxE; congr _%:R.
  rewrite -sum1dep_card big_mkcond (bigD1 [tuple]) //=.
  by rewrite big1 ?addn0; [case: eqP|move=> t; rewrite tuple0].
rewrite exprS mxE -sum1dep_card.
pose reind := fun tp : T * k.-tuple T => [tuple of tp.1 :: tp.2].
rewrite (reindex reind) /=; last first.
  exists (fun tp => (tnth tp ord0, [tuple of behead tp])) => /=.
    by move=> [/= a q] _; rewrite tnth0 /=; congr (_, _); apply/val_inj.
  by move=> p _; case: (tupleP p) => a q /=; rewrite tnth0; apply/val_inj.
evar (F : 'I_n -> R); rewrite (eq_bigr F); last first.
  move=> i _; rewrite IHk -sum1dep_card natr_sum mulr_sumr.
  rewrite (eq_bigr (fun _ => if g x i then 1 else 0 : R)) /F //.
  by move=> q q_path /=; rewrite mulr1 mxE; case: (g).
rewrite /F {F} pair_big_dep /= natr_sum big_mkcond [RHS]big_mkcond /=.
by apply: eq_bigr=> -[/= a q] _; case: (g); case: path; case: eqP.
Qed.

Lemma gpath_exists k g x y :
  reflect (exists p, p \in k.-path g x y) (((adjacency g ^+ k) x y) > 0).
Proof.
rewrite gpath_count ltr0n card_gt0.
by apply: (iffP (set0Pn _)) => -[p]; exists p.
Qed.

Definition padj g : 'M[{poly R}]_n :=
  \matrix_(i, j) if i == j then 1 else if g i j then 'X else 0.

Lemma deg_padj g : (forall x, ~~ g x x) ->
  map_mx (fun p : {poly R} => (size p).-1%:R) (padj g) = adjacency g.
Proof.
move=> gNrefl; apply/matrixP=> i j; rewrite !mxE.
case: eqP=> [->|_] //=.
  by rewrite (negPf (gNrefl j)) size_polyC oner_eq0.
by case: g {gNrefl}; rewrite ?size_polyC ?size_polyX ?eqxx.
Qed.

Lemma g0path g x y : 0.-path g x y = if x == y then [set [tuple]] else set0.
Proof.
by apply/setP => p; rewrite !inE tuple0 /= !fun_if !inE eqxx; case: eqP.
Qed.

Lemma card_g0path g x y : #|0.-path g x y : {set 0.-tuple T}| = (x == y).
Proof. by rewrite g0path; case: eqP; rewrite ?cards1 ?cards0. Qed.

Lemma g1path g x y : 1.-path g x y = if g x y then [set [tuple y]]
                                     else set0 : {set 1.-tuple T}.
Proof.
apply/setP => p; rewrite !inE; case: (tupleP p) => z q; rewrite tuple0 /=.
rewrite (fun_if (fun s : {set _} => _ \in s)) !inE /=.
rewrite -[_ == _ :> _.-tuple _]val_eqE eqseq_cons eqxx andbT.
have [->|neq_zy] := altP eqP; first by case: g.
by rewrite andbF if_same.
Qed.

Lemma card_g1path g x y : #|1.-path g x y| = (g x y).
Proof. by rewrite g1path; case: g; rewrite ?cards1 ?cards0. Qed.

Lemma gSpath k g x y : 
  k.+1.-path g x y = [set [tuple of z :: (p : k.-tuple T)] 
                     | z in g x, p in k.-path g z y].
Proof.
apply/setP => p; rewrite !inE; case: (tupleP p) => z q /=; rewrite -andbA.
apply/idP/imset2P=> [/and3P [gxz pzq lz]|[z' q' z'P q'P [-> ->]]].
  by exists z q => //; rewrite inE pzq.
by apply/and3P; move: q'P; rewrite inE => /andP[].
Qed.

Lemma card_gSpath k g x y :
  #|k.+1.-path g x y| = (\sum_z g x z * #|k.-path g z y|)%N.
Proof.
rewrite (eq_bigr (fun z : T => \sum_(p : k.-tuple T)
  if [&& g x z, path g z p & last z p == y] then 1 else 0)%N); last first.
  move=> z _; rewrite -sum1dep_card big_distrr /= big_mkcond.
  by apply: eq_bigr=> p _; case: path; case: eqP; case: g.
symmetry; rewrite pair_big_dep /= -big_mkcond sum1dep_card gSpath.
rewrite -(@card_imset _ _ (fun p : T * k.-tuple T => [tuple of p.1 :: p.2]));
   last by move=> [a p] [b q] /= [->/val_inj->].
apply: eq_card => p.
apply/imsetP/imset2P=> [[/=[z q /=]]|[/= z q zP]].
  rewrite inE => /= /and3P [???] ->; exists z q => //.
  by rewrite inE; apply/andP.
rewrite inE => /andP [??] ->; exists (z, q) => //.
by rewrite inE /=; apply/and3P.
Qed.

Lemma coef_padjX k i (g : rel T) x y : (forall x, ~~ g x x) ->
  ((padj g ^+ k) x y)`_i = (#|i.-path g x y| * 'C(k, i))%:R.
Proof.
wlog -> : k i g x y / k = 1%N => [hwlog|]; last first.
  move=> gNrefl; rewrite expr1 !mxE !(fun_if (fun p : {poly _} => p`_i)).
  rewrite !coefC !coefX ?if_same.
  case: i => [|[|i]]; rewrite ?(binS, bin0, bin0n, muln0, muln1, if_same) //=.
    by rewrite card_g0path; case: eqP => [|]//; rewrite ?if_same.
  rewrite card_g1path; case: eqP => [->|] //; last by case: (g).
  by rewrite (negPf (gNrefl y)).
elim: k {-2}k (leqnn k) => [|K IHK] k le_k // in i g x y *.
  move: le_k; rewrite leqn0 => /eqP -> gNrefl.
  rewrite bin0n mxE coefMn coef1.
  have [->|_] := altP eqP; last by rewrite ?mul0rn ?muln0 ?mul0n.
  rewrite !muln1 mulr1n -sum1dep_card big_mkcond (bigD1 [tuple]) //=.
  by rewrite big1 ?addn0; [case: eqP|move=> t; rewrite tuple0 /= ?eqxx].
move=> gNrefl; case: k => [//|k] in le_k *; first by apply: IHK.
rewrite [_ ^+ _.+1](exprD _ 1) mxE coef_sum ?ltnS in le_k *.
case: i => [|i].
  evar (F : 'I_n -> R); rewrite !muln1 (eq_bigr F)=> [|z _]; last first.
    rewrite coefM big_ord1 subnn hwlog // bin0 IHK // bin0 !muln1 -!natrM.
    by rewrite !card_g0path /F.
  rewrite /F {F} -natr_sum card_g0path ?(maxn_idPr _) ?subn0 //.
  rewrite (bigD1 x) //= ?eqxx ?mul1n big1 ?addn0 -?natrM // => i.
  by rewrite eq_sym => /negPf->; rewrite mul0n.
evar (F : 'I_n -> R); rewrite (eq_bigr F)=> [|z _]; last first.
  rewrite coefM !big_ord_recl //.
  rewrite big1 ?addr0; last by move=> l; rewrite hwlog // muln0 mul0r.
  rewrite subn0 subSS subn0 [_`_(i.+1)]IHK // [_`_(i)]IHK//.
  rewrite !hwlog //= card_g0path card_g1path ?mulr1 ?expn1 ?muln1.
  by rewrite -!natrM !mulnA /F.
rewrite big_split /= (bigD1 x) // big1 /= ?addr0 ?eqxx ?mul1n; last first.
  by move=> z; rewrite eq_sym => /negPf->; rewrite ?mul0r.
by rewrite -natr_sum -!big_distrl /= -card_gSpath /= -natrD binS mulnDr.
Qed.

End mxgraph.

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
