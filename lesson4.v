From mathcomp Require Import all_ssreflect perm all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Obligation Tactic := idtac.

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
(** #<div class='slide'>#
* The Matrix library

This library relies a lot on the #<a target='_blank' class='file' href="http://math-comp.github.io/math-comp/htmldoc/mathcomp.algebra.ssralg.html">algebraic hierarchy</a>#

Extensive documentation in the header of the library #<a target='_blank' class='file' href="http://math-comp.github.io/math-comp/htmldoc/mathcomp.algebra.matrix.html">matrix</a>#

*)
(** -------------------------------------------- *)
(**
* Roadmap for the lesson:
 - General facts about matrices:
   - definition of matrices
   - main theorems to handle matrices (reduction and comparison)
   - generic (ring) notions
   - specific matrix notions
 - Doing a proper search using naming conventions
 - "Toy" application to graph theory:
   - adjacency matrix of a graph
   - stochastic matrices and page rank matrix
   - polynomial adjacency matrices (ref from litterature missing...)

*)
(** -------------------------------------------- *)
(**

* Out of the scope of this lesson
 - #<a target='_blank' class='file' href="http://math-comp.github.io/math-comp/htmldoc/mathcomp.algebra.mxalgebra.html">linear algebra library using only matrices (mxalgebra)</a>#
 - #<a target='_blank' class='file' href="http://math-comp.github.io/math-comp/htmldoc/mathcomp.algebra.vector.html">vector space library (vector)</a># (one has to decide with care whether to use vector or mxalgebra)
 - characters, representation, galois theory,...

*)
(** -------------------------------------------- *)
(** #<div class='slide'>#
* General facts about matrices
** Defining Matrices

(Credits "ITP 2013 tutorial: The Mathematical Components library" by Enrico Tassi and Assia Mahboubi #<a href="http://ssr.msr-inria.inria.fr/doc/tutorial-itp13/">material here</a>#)

*)
Module DefinitionMatrices.
Reserved Notation "''M[' R ]_ n"
  (at level 8, n at level 2, format "''M[' R ]_ n").
Reserved Notation "''M[' R ]_ ( m , n )"
  (at level 8, format "''M[' R ]_ ( m ,  n )").

Reserved Notation "\matrix_ ( i , j ) E"
  (at level 36, E at level 36, i, j at level 50,
   format "\matrix_ ( i ,  j )  E").

Reserved Notation "x %:M"   (at level 8, format "x %:M").
Reserved Notation "A *m B"
  (at level 40, left associativity, format "A  *m  B").
Reserved Notation "A ^T"    (at level 8, format "A ^T").
Reserved Notation "\tr A"
  (at level 10, A at level 8, format "\tr  A").

(** #</div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#
** A matrix is encoded as a 2-dimension array

*)
Inductive matrix (R : Type) (m n : nat) : Type :=
  Matrix of {ffun 'I_m * 'I_n -> R}.
(**

Some notations : size inside parentheses, type of coefficients inside square brackets. NB: In the library, the type of coefficients can also be ommitted.

*)
Notation "''M[' R ]_ ( m , n )" := (matrix R m n) : type_scope.
Notation "''M[' R ]_ n" := 'M[R]_(n, n) : type_scope.

(* Test *)
Check 'M[nat]_(2,3).
Check 'M[nat]_2.
(** #</div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#

"matrix" is just a tag over ffun: it inherits from its structure. We can "transfer" automatically all structures from the type of finite functions by "trivial subTyping".
*)
Definition mx_val R m n (A : 'M[R]_(m,n)) :
  {ffun 'I_m * 'I_n -> R} :=
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
  Eval hnf in ChoiceType 'M[R]_(m, n)
                         (matrix_choiceMixin R m n).
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
(** #</div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#

Test overloaded "_ == _" notation, given by the eqType canonical structure.
*)
Check [eqType of 'M[nat]_2].
Check forall A : 'M[nat]_2, A == A.
(**

Since matrices over nat are comparable with _ == _, matrices over matrices over nat are also comparable.

*)
Check forall AA : 'M[ 'M[nat]_3 ]_2, AA == AA.
(**

We define a coercion in order to access elements as if matrices were functions.

*)
Definition fun_of_mx R m n (A : 'M[R]_(m,n)) :
  'I_m -> 'I_n -> R :=
  fun i j => mx_val A (i, j).
Coercion fun_of_mx : matrix >-> Funclass.

Check forall (A : 'M[nat]_3) i j, A i j == 37.
(** #</div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#

We provide a notation to build matrices from a general term. This is the best way to define a matrix. One can also assemble blocks using row_mx, col_mx and block_mx, but most of the time, this might be a bad idea.

*)
Definition mx_of_fun R m n
  (F : 'I_m -> 'I_n -> R) : 'M[R]_(m,n) :=
  Matrix [ffun ij => F ij.1 ij.2].
Notation "\matrix_ ( i , j ) E" :=
  (mx_of_fun (fun i j => E))
  (at level 36, E at level 36, i, j at level 50) : ring_scope.

Check \matrix_(i,j) (i - j)%N  :  'M[nat]_(3,4).
(**
#</div>#
*)
End DefinitionMatrices.
Module MatrixProperties.
(** #</div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#
** Main Theorems

We now show the most used theorems for matrix manipulation.

*** mxE

mxE is an equation to compute a term in the matrix at given coordinates: it extracts the general term of the matrix and compute the substitution of indexes. It is generally the right move when you have <pre>(A complicated matrix) i j</pre> in your goal.

*)
Check mxE.
(**
*** matrixP

matrixP is the "extensionality theorem" for matrices, it says two matrices are equal if and only if all their coefficients are pairwise equal.

*)
Check matrixP.
(** #</div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#
** Ring operations on matrices

*** Matrices on rings are provided with a R-module canonical structure.

Mathematical components includes a library for many standard algebaric structures. This library provides generic operations (0, 1, +, *, ...) and theorems depending on how rich the structure is.

*)
Lemma test (R : ringType) m n (A B : 'M[R]_(m,n)) : A + B = B + A.
Proof. exact: addrC. Abort.
(**
However, the library does not contain heterogeneous multiplication, so we have a specific operation for that.
*)
Print mulmx.

Fail Lemma test (R : ringType) m n (A B : 'M[R]_(m, n)) :
  A * B = 0.

Lemma test (R : ringType) m n p
  (A : 'M[R]_(m, n)) (B C : 'M[R]_(n, p)) :
  A *m (B + C) = (A *m B) + (A *m C).
Proof. rewrite mulmxDr. Abort.
(** #</div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#
*** square matrices with non zero size have a ring canonical structure.

The generic ring product is available on square matrices with explicit nonzero size (ie size is convertible to n.+1). This ring product coincides with the matrix product (definitionally).

*)
Lemma test (R : ringType) n (A B : 'M[R]_n.+1) : A * B = B * A.
Proof. Fail rewrite mulrC. Abort.
(**


** Specific matrix operations

There are scalar_mx, trace, transpose and determinant operations, that are specific to matrices.

Builds a diagonal matrix from any element
*)
Print scalar_mx.
Locate "%:M".

Lemma test (R : ringType) m n (a : R) (A : 'M[R]_(m,n)) :
  a *: A = a%:M *m A.
Proof. by rewrite mul_scalar_mx. Abort.

Print mxtrace.
Locate "\tr".

Print trmx.
Locate "^T".

Print determinant.
Locate "\det".

End MatrixProperties.
(** #</div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#
* Naming conventions.

The two most important things to get your way out of a situation:
 - Knowing your math
 - Searching the library for what you think you know

For that you have the ssreflect Search command. To use its full power, one should combine seach by identifier (Coq definition), pattern (partial terms) and name (a string contained in the name of the theorem).

The two first methods are straightforward to use (except if you instanciate your patterns more than necessary), but searching by name requires to be aware of naming conventions.

*)
(** #</div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#
** Names in the library are usually obeying one of following the convention

 - #<pre>(condition_)?mainSymbol_suffixes</pre>#
 - #<pre>mainSymbol_suffixes(_condition)?</pre>#

Or in the presence of a property denoted by a nary or unary predicate:
 - #<pre>naryPredicate_mainSymbol+</pre>#
 - #<pre>mainSymbol_unaryPredicate</pre>#

** Where :

 - "mainSymbol" is the most meaningful part of the lemma. It generally
   is the head symbol of the right-hand side of an equation or the
   head symbol of a theorem. It can also simply be the main object of
   study, head symbol or not. It is usually either

  - one of the main symbols of the theory at hand. For example, for
    ssralg, it will be "opp", "add", "mul", etc...

  - or a special "canonical" operation, such as a ring morphism or a
    subtype predicate. e.g. "linear", "raddf", "rmorph", "rpred", etc ...

 - "condition" is used when the lemma applies under some hypothesis. As in

 - "suffixes" are there to refine what shape and/or what other symbols
   the lemma has. It can either be the name of a symbol ("add", "mul",
   etc...), or the (short) name of a predicate ("inj" for
   "injectivity", "id" for "identity", ...) or an abbreviation. We
   list here the main abbreviations.

  - A -- associativity, as in andbA : associative andb.
  - AC -- right commutativity.
  - ACA -- self-interchange (inner commutativity), e.g.,
        orbACA : (a || b) || (c || d) = (a || c) || (b || d).
  - b -- a boolean argument, as in andbb : idempotent andb.
  - C -- commutativity, as in andbC : commutative andb,
    or predicate complement, as in predC.
  - CA -- left commutativity.
  - D -- predicate difference, as in predD.
  - E -- elimination, as in negbFE : ~~ b = false -> b.
  - F or f -- boolean false, as in andbF : b && false = false.
  - I -- left/right injectivity, as in addbI : right_injective addb or predicate  intersection, as in predI.
  - l -- a left-hand operation, as andb_orl : left_distributive andb orb.
  - N or n -- boolean negation, as in andbN : a && (~~ a) = false.
  - P -- a characteristic property, often a reflection lemma, as in andP : reflec t (a /\ b) (a && b).
  - r -- a right-hand operation, as orb_andr : rightt_distributive orb andb.
  - T or t -- boolean truth, as in andbT: right_id true andb.
  - U -- predicate union, as in predU.
  - W -- weakening, as in in1W : {in D, forall x, P} -> forall x, P.

  - 0 -- ring 0, as in addr0 : x + 0 = x.
  - 1 -- ring 1, as in mulr1 : x * 1 = x.
  - D -- ring addition, as in linearD : f (u + v) = f u + f v.
  - B -- ring subtraction, as in opprB : - (x - y) = y - x.
  - M -- ring multiplication, as in invfM : (x * y)^-1 = x^-1 * y^-1.
  - Mn -- ring by nat multiplication, as in raddfMn : f (x *+ n) = f x *+ n.
  - N -- ring opposite, as in mulNr : (- x) * y = - (x * y).
  - V -- ring inverse, as in mulVr : x^-1 * x = 1.
  - X -- ring exponentiation, as in rmorphX : f (x ^+ n) = f x ^+ n.
  - Z -- (left) module scaling, as in linearZ : f (a *: v)  = s *: f v.

** My own search idiom

#<pre>Search _ "suffix1" "suffix2" (symbol|pattern)* in library.</pre>#

** Examples
*)
Module Conventions.

Search _ *%R "A" in GRing.Theory.

Search _ "unit" in ssralg.

Search _ "inj" in ssralg.

Search _ "rmorph" "M" in ssralg.

Search _ "rpred" "D" in ssralg.

End Conventions.
(** #</div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#

* Toy application to graph theory

We now illustrate the use of matrices on simple example of graph.  For simplicity, we take graphs on ordinal (type representing initial segments of natural numbers : [0, .., i-1])

In order to compare elements from a field with total order, we use the structure real field type from the library #<a target='_blank' class='file' href="http://math-comp.github.io/math-comp/htmldoc/mathcomp.algebra.ssrnum.html">numeric hierarchy</a>#. In practice this can be instanciated to rational numbers.

*)
Section mxgraph.

Variable (n' : nat) (R : realFieldType).
Let n := n'.+1.
Let T := 'I_n.
Implicit Types (A : 'M[R]_n) (x y z : T) (u v : 'rV[R]_n).
(**
** Definition of the adjacency matrix and partial inverse
*)
Definition adjacency (g : rel T) : 'M[R]_n :=
  \matrix_(i < n, j < n) (g i j)%:R.

Definition adjrel A : rel T := fun x y => A x y > 0.

Lemma adjacencyK g : adjrel (adjacency g) =2 g.
Proof.
by move=> x y; rewrite /adjrel !mxE; case: g; rewrite ?ltr01.
Qed.
(** #</div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#

Transposing the adjacency matrix reverses the graph
*)
Lemma tr_adjacencyK (g : rel T) :
  adjrel (adjacency g)^T =2 (fun x y => g y x).
Proof. Admitted.
(**
#<button onclick="hide('sol_tr_adjacencyK')">Solution</button>
<div id='sol_tr_adjacencyK' class='solution'>
<pre>
by move=> x y; rewrite /adjrel !mxE; case: g; rewrite ?ltr01.
</pre>
</div>
#
*)
(** #</div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#
** Graph paths

We define the set of paths in g from x to y of size k by comprehension, as the set of lists of size k, that end with y. Hence a path of size k goes through k+1 points, and in particular a path of size 0 starts and ends at the same point.

We start by posing a notation on the set of graphs.
*)
Notation "k .-path g x y" :=
  [set p : k.-tuple _ | path g x p & last x p == y]
  (at level 2, g, x, y at next level,
   format "k .-path  g  x  y") : type_scope.
(**
We can exhibit what are paths of size 0 and prove how many there are.
*)
Lemma g0path g x y :
  0.-path g x y = if x == y then [set [tuple]] else set0.
Proof.
by apply/setP => p; rewrite !inE tuple0 /= !fun_if !inE eqxx; case: eqP.
Qed.

Lemma card_g0path g x y :
  #|0.-path g x y : {set 0.-tuple T}| = (x == y).
Proof. by rewrite g0path; case: eqP; rewrite ?cards1 ?cards0. Qed.
(**
We can exhibit what are paths of size 1 and prove how many there are.
*)
Lemma g1path g x y :
  1.-path g x y = if g x y then [set [tuple y]]
                  else set0 : {set 1.-tuple T}.
Proof. Admitted.
(**
The cardinality proof is left as an exercise in finite types and finite sets, but contains nothing about matrices. You may as well skip it if you want to focus on matrices.
#
<button onclick="hide('sol_card_gSpath')">Solution</button>
<div id='sol_card_gSpath' class='solution'>
<pre>
apply/setP => p; rewrite !inE; case: (tupleP p) => z q; rewrite tuple0.
rewrite (fun_if (fun s : {set _} => _ \in s)) !inE /=.
rewrite -[_ == _ :> _.-tuple _]val_eqE eqseq_cons eqxx andbT.
by have [->|neq_zy] := altP eqP; [case: g| rewrite andbF if_same].
</pre>
</div>
#
*)
Lemma card_g1path g x y : #|1.-path g x y| = (g x y).
Proof.
by rewrite g1path; case: g; rewrite ?cards1 ?cards0.
Qed.
(**

We can exhibit what are paths of size n+1 and prove how many there are.

*)
Lemma gSpath k g x y : k.+1.-path g x y =
  [set p : k.+1.-tuple T | g x (thead p)
  & ([tuple of behead p] \in k.-path g (thead p) y)].
Proof.
by apply/setP => p; rewrite !inE; case: (tupleP p) => ??; rewrite theadE andbA.
Qed.

Lemma card_gSpath k g x y :
  #|k.+1.-path g x y| = (\sum_z g x z * #|k.-path g z y|)%N.
Proof. Admitted.
(**
The cardinality proof is left as an exercise in finite types and finite sets, but contains nothing about matrices. You may as well skip it if you want to focus on matrices.
#
<button onclick="hide('sol_card_gSpath')">Solution</button>
<div id='sol_card_gSpath' class='solution'>
<pre>
rewrite (eq_bigr (fun z : T => \sum_(p : k.-tuple T)
  if [&& g x z, path g z p & last z p == y] then 1 else 0)%N);
  last first.
  move=> z _; rewrite -sum1dep_card big_distrr /= big_mkcond.
  by apply: eq_bigr=> p _; case: path; case: eqP; case: g.
rewrite pair_big_dep /= -big_mkcond sum1dep_card.
rewrite -(@card_imset _ _
   (fun p : T * k.-tuple T => [tuple of p.1 :: p.2]));
   last by move=> [a p] [b q] /= [->/val_inj->].
rewrite gSpath; apply: eq_card=> p; rewrite !inE /=.
apply/idP/imsetP=> [|[[q z /=]]]; last by rewrite inE /= => ? ->.
exists (thead p, [tuple of behead p]); rewrite ?inE //=.
by case: (tupleP p) => //= ??; apply/val_inj.
</pre>
</div>
#
*)
(** #</div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#
** Counting the number of path using the adjacency matrix.

We show the correspondance between the kth power of the adjacency matrix and the number of paths of size k.

*)
Lemma gpath_count k g x y :
  (adjacency g ^+ k) x y = #|k.-path g x y|%:R.
Proof. Admitted.
(**
#<button onclick="hide('sol_gpath_count')">Solution</button>
<div id='sol_gpath_count' class='solution'>
<pre>
elim: k=> [|k IHk] in x y *; first by rewrite expr0 mxE card_g0path.
rewrite exprS mxE card_gSpath natr_sum; apply: eq_bigr => i _.
by rewrite natrM IHk mxE.
</pre>
</div>
#
*)
Lemma gpath_exists k g x y :
  reflect (exists p, p \in k.-path g x y)
          (((adjacency g ^+ k) x y) > 0).
Proof.
rewrite gpath_count ltr0n card_gt0.
by apply: (iffP (set0Pn _)) => -[p]; exists p.
Qed.
(** #</div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#
** Definition of stochastic matrices

First, we define the boolean definition, then the reflection lemma (which might be automated using Enrico and Benjamin's work on automated views.

Then we can start proving intersting properties, like the product of two stochastic matrices is stochastic.
*)
Definition stochastic m p (M : 'M[R]_(m,p)) :=
  [forall i, \sum_j M i j == 1].

Lemma stochasticP {m} {p} {M : 'M[R]_(m,p)} :
   reflect (forall i, \sum_j M i j = 1) (stochastic M).
Proof. exact/'forall_eqP. Qed.

Lemma mulmx_stochastic k m p (N : 'M[R]_(k, m)) (M : 'M[R]_(m, p)) :
  stochastic N -> stochastic M -> stochastic (N *m M).
Proof. Admitted.
(**
#<button onclick="hide('sol_mulmx_stochastic')">Solution</button>
<div id='sol_mulmx_stochastic' class='solution'>
<pre>
move=> u_stoc M_stoc; apply/stochasticP => i.
rewrite (eq_bigr _ (fun j _ => (mxE _ _ i j))) exchange_big /=.
rewrite (eq_bigr (fun j => N i j)) ?(stochasticP _) //.
by move=> l _; rewrite -mulr_sumr (stochasticP _) ?mulr1.
</pre>
</div>
#
*)
(** #</div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#
** Page rank

We define the page rank matrix and show it is stochastic.

*)
Definition page_rank (g : rel T) : 'M[R]_n :=
  \matrix_(i < n, j < n) ((g i j)%:R / \sum_k (g i k)%:R).

Lemma page_rank_gt0 g i j : page_rank g i j >= 0.
Proof.
by rewrite !mxE divr_ge0 ?ler0n ?sumr_ge0 // => k; rewrite ?ler0n.
Qed.

Lemma page_rank_stochastic (g : rel T) :
  (forall i, exists j, g i j) -> stochastic (page_rank g).
Proof. Admitted.
(**
#<button onclick="hide('sol_page_rank_stochastic')">Solution</button>
<div id='sol_page_rank_stochastic' class='solution'>
<pre>
move=> g_connects; apply/stochasticP => i.
rewrite (eq_bigr _ (fun j _ => (mxE _ _ i j))).
rewrite -mulr_suml divff //= -natr_sum pnatr_eq0 -big_mkcond /=.
rewrite sum1dep_card cards_eq0; apply/set0Pn.
by have [j ?] := g_connects i; exists j; rewrite inE.
Qed.
</pre>
</div>
#
*)
(** #</div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#
** Polynomial adjacency matrix

We define the polynomial adjacency matrix of a graph with no edges from vertices to themselves, as the matrix with 1 on the diagonal, polynomial X when there is an edge, and 0 if there is no connexion (between two different vertices).

First we show it is a generalisation of the adjacency matrix, as taking the degree of each polynomial in the matrix results in the previously define adjacency matrix.

*)
Definition padj g : 'M[{poly R}]_n :=
  \matrix_(i, j) if i == j then 1
                 else if g i j then 'X else 0.

Lemma deg_padj g : (forall x, ~~ g x x) ->
  map_mx (fun p : {poly R} => (size p).-1%:R) (padj g) =
  adjacency g.
Proof.
move=> gNrefl; apply/matrixP=> i j; rewrite !mxE.
case: eqP=> [->|_] //=.
  by rewrite (negPf (gNrefl j)) size_polyC oner_eq0.
by case: g {gNrefl}; rewrite ?size_polyC ?size_polyX ?eqxx.
Qed.
(** #</div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#
** Polynomial adjacency matrix

Then one can prove that there is a link beween the number of path of size i, and the ith coefficient of the polynomial in the corresponding coefficient of the matrix.

I was not aware of this result, does anyone know where one could find it in the litterature?

Warning: my own proof of this fact is currently 31 lines...

*)
Lemma coef_padjX k i (g : rel T) x y :
  (forall x, ~~ g x x) ->
  ((padj g ^+ k) x y)`_i =
  (#|i.-path g x y| * 'C(k, i))%:R.
Proof. Admitted.
(**
#
<button onclick="hide('sol_coef_padj')">Solution</button>
<div id='sol_coef_padj' class='solution'>
<pre>
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
</pre>
</div>
#
*)
(** #</div># *) End mxgraph. (**
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
  document.getElementById("document").style["padding-right"]="50px";
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
  for (var i = slides.length-1; i >= 0; i--) {
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
function hide (element_id) {
  element = document.getElementById(element_id);
    if (element.style.display != 'block') {
      element.style.display = 'block';
    } else {
      element.style.display = 'none';
    }
}
window.onload = init_slides;
window.onscroll = update_scrolled;
</script>
# *)