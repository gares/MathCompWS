From mathcomp Require Import all_ssreflect.
(** -------------------------------------------- *)

(** #<div class='slide vfill'>#  
** Lesson 3 (of 4)

 - Finite types

#</div># *)

(** -------------------------------------------- *)

(** #<div class='slide vfill'>#  
** Objective of this course

Understand the benefits and usage of finite types.

 - formation principle
 - A special case: ordinals
 - New tools : finite functions and finite set theory
 - Moving even closer to classical logic : choice and extensionality
#</div># *)

(** -------------------------------------------- *)

(** #<div class='slide'># 
** Formation principle

For a finite type, you can enumerate the elements
the enumeration is a simple piece of data (based on sequences)
 - The enumeration gives some computation principle
 - Elements of a finite type can be indexed

#</div># *)

(** -------------------------------------------- *)
  
(** #<div class='slide'># 
** The simplest finite types: ordinal numbers

Initial segments of natural numbers
- Building blocks or yardsticks for other finite types
- Usable as plain integers, thanks to coercions
*)

About Ordinal.

Example two_in_I_4 :=  Ordinal (isT : 2 < 4).

Fail Example five_in_I_4 : Ordinal (isT : 5 < 4).

(* For ordinal types that contain at least one elements, there
is an optimistic injection from nat. *)

Check inord.

(* Beware of hidden coercions when reading these statements. *)

Check inordK.

Check inord_val.

Example inord_val_3_4 : inord 2 = two_in_I_4 :> 'I_4.
Proof.
rewrite -[X in inord X]/(nat_of_ord two_in_I_4).
rewrite inord_val. by [].
Qed.
(** #</div># *)

(** -------------------------------------------- *)

(** #<div class='slide'>#  
** Finite type constructions

In the rest of this talk I will use the following pattern to
    verify that I have a finite type.
*)
Check [finType of 'I_4].

Fail Check [finType of nat].
(** New finite types can be built from existing ones
 - ordinal types are the usual examples of basic finite types
 - unit (with one element)
 - bool (with two elements)
 - cartesian product
 - disjoint sum
 - subtype
 - function type
*)
Check [finType of 'I_4 * 'I_3].

Definition twin_primes_lt100 :=
 {x : 'I_100 * 'I_100 | prime (fst x) &&
                      prime (snd x) && (snd x == (fst x) + 2 :> nat)}.

Check [finType of twin_primes_lt100].

Definition lesser_twin_100 :=
 {x : nat | prime x && prime (x + 2) && (x < 100)}.

Fail Check [finType of lesser_twin_100].
(* solution to make lesser_twin_100 a finite type at the end. *)

(** -------------------------------------------- *)

(** #<div class='slide'># 
** Building a finite type from scratch

An example: building an enumerated type, show that is
   finite

Exhibit an injection into another finite type.
*)
Module LessonSandBox1.

Inductive card_point : predArgType := W | E | N | S.

Definition cp2o d : 'I_4 :=
  match d with
    W => inord 0 | E => inord 1 | N => inord 2 | S => inord 3
  end.

Definition o2cp (n : 'I_4) :=
  match val n with
    0 => Some W | 1 => Some E | 2 => Some N | 3 => Some S | _ => None
  end.

Lemma cp_can : pcancel cp2o o2cp.
Proof.
case.
rewrite /o2cp. rewrite /=. rewrite inordK. by []. by [].
by rewrite /o2cp /= inordK.
by rewrite /o2cp /= inordK.
by rewrite /o2cp /= inordK.
Qed.

(** #<div class='slide'># 

The lemma cp_can means that there is an injection from card_point into
 a known finite type

A succession of helper theorem to add qualities
 - equality is decidable [eqType]
 - there is a canonical way to choose witnesses [choiceType]
 - the elements can be enumerated [countType]
 - the type [card_point] is finite.
#</div>#
*)

Canonical cp_eqType := EqType card_point (PcanEqMixin cp_can).
Canonical card_point_choiceType :=
    ChoiceType card_point (PcanChoiceMixin cp_can).
Canonical cp_countType :=
    CountType card_point (PcanCountMixin cp_can).
Canonical card_point_finType := FinType card_point (PcanFinMixin cp_can).

Check [finType of card_point].

End LessonSandBox1.

(** -------------------------------------------- *)

(** #<div class='slide'># 
** Tools about finiteness

More classical logic
 - Quantifications of decidable predicates become decidable.
 - Need to use special notations
*)

  
Check [forall x : 'I_4, x < 2] && [exists x :'I_4, 4 < x].

Check [forall x : {x : 'I_100 | prime x}, 1 < val x].

Check xchoose.

Search xchoose.

(** #</div class='slide'># *)
(** Proofs about quantified statements. *)

Example logical_proof : ~~([forall x : 'I_4, x < 2] &&
         [exists x : 'I_4, 4 < x]).
Proof.
Search _ (~~ (_ && _)).
rewrite negb_and. rewrite negb_forall. apply/orP; left.
apply/existsP. exists (Ordinal (isT : 2 < 4)).
by [].  (* let's think a little. *)
Qed.

Example logical_proof1 : ~~[exists x: 'I_4, 4 < x].
Proof.
rewrite negb_exists. apply/forallP. rewrite /=.
move => [[ | [ | [ | [ | a]]]] px] => /=.
by []. by []. by []. by [].
Fail rewrite {px}; by [].
by [].
Qed.
(** #</div># *)

(** --------------------------------------------
#<div class='slide'>#
** Finite functions

Function whose domain is a finite type

  - A finite type when the type for values is finite
  - A special notation for functions from ordinals
*)
Module LessonSandbox2.

Parameter T : finType.
Parameters x y : T.

Check [ffun z : T => z = y].
Check [ffun z : T => z == y].
Check [finType of {ffun T -> bool}].
Check [ffun i : 'I_2 => if val i == 0 then x else y].
Check [ffun i : 'I_2 => if i == ord0 then x else y] : T ^ 2.

Lemma finfun_proof : [ffun i : 'I_2 => if i == ord0 then x else y]
          (Ordinal (isT : 1 < 2)) = y.
Proof.
rewrite /=.  rewrite ffunE. rewrite /=. by [].
Qed.

Lemma finfun_proof2 : [ffun i : 'I_2 => if i == ord0 then x else y] =
  [ffun i : 'I_2 => if val i == 1 then y else x].
Proof.
apply/ffunP.
move => z. rewrite !ffunE /=.
case: z => [[ | [ | z']] pz].
    rewrite /=. by [].
  rewrite /=. by [].
rewrite /=. by [].
Qed.

(** #</div># *)

(** --------------------------------------------
#<div class='slide'>#

** Set theory over finite types
 - obviously finite sets over a finite type are finite
 - obviously the type of these sets is finite 
*)
Check [finType of {set T}].
Parameter A : {set T}.
Check #|A|.
Check #|[set: T]|.
Locate "#| _ |".
Check x \in A.
Check [set x].
Check [set x; y].

Lemma set_proof : (#|[set x; y]| == 2) = (x != y).
Proof.
Search card in finset.
rewrite cardsU1.
rewrite cards1 addnC addSn add0n.
rewrite in_set1.
rewrite eqSS.
rewrite eqb1.
by [].
Qed.

(** #</div># *)
(** --------------------------------------------
#<div class='slide'>#
** Finite types and big operators
 - Big operators are the natural tool to compute repeatedly over
   all elements of a finite type
 - Elements are picked in the fixed order given by the enumeration. *)
Parameter f : T -> nat.
Check \sum_(i : T) f i.
Check big_ord_recr.
Check big_ord_recl.
Check bigD1.
Check big_setID.
(** #</div># *)
(** --------------------------------------------
#<div class='slide'>#
** Finite graphs

Finite graphs are build on a finite type of nodes

Three approaches
  - Use a function to list all targets of edges
  - The graph of a relation
  - The graph of a function
*)
Definition mg := [:: (0,1); (1,0); (1,2); (3,3)].
Definition mgr : rel 'I_4 :=
   fun x y : 'I_4 => (val x, val y) \in mg.
Check rgraph mgr.
Check dfs_path (rgraph mgr) [::] ord0.
Lemma graph_proof : dfs_path (rgraph mgr) [::] ord0 (Ordinal (isT : 2 < 4)).
Search dfs_path.
Search _ (grel (rgraph _)).
have pp : path (grel (rgraph mgr)) ord0 [:: Ordinal (isT : 1 < 4); Ordinal (isT : 2 < 4)].
  rewrite /=. rewrite andbT; apply/andP; split. 
    rewrite mem_enum. by [].
  rewrite mem_enum. by [].
apply: (DfsPath pp).
  by [].
rewrite disjoint_sym.
apply: disjoint0.
Qed.

Parameters (z : T) (g : T -> seq T).
Hypothesis xny : x != y.
Hypothesis xnz : x != z.
Hypothesis ynz : y != z.
Hypothesis g_xyz :
  (g x == [::y]) && (g y == [:: x; z]).
  
Lemma graph_proof2 : dfs_path g [::] x z.
Proof.
have pp: path (grel g) x [::y;z].
  rewrite /= andbT.
  move/andP: g_xyz => [/eqP -> /eqP ->].
  rewrite !inE. rewrite !eqxx. rewrite orbT. by [].
apply (DfsPath pp).
  rewrite /=. by [].
rewrite disjoint_sym. rewrite disjoint0.
by [].
Qed.

(** --------------------------------------------
#<div class='slide'>#
** Exercises

Exercises taken from #<a href="http://www-sop.inria.fr/manifestations/MapSpringSchool/program.html">Map Spring School</a># (thanks to L. Rideau)
 
*)
Lemma inj_card_le (I J : finType) (f : I -> J) : injective f -> #|I| <= #|J|.

Lemma ord1 : forall i : 'I_1, i = ord0.

Lemma adds : forall (a b : T) (E : {set T}), 
    a != b -> a \notin E -> b \notin E ->
    #| a |:  (b |: E)| = #|E| + 2.

(** State and prove the following statements

 - E union F = (E minus F) union (F minus E) union (E inter F)
*)
(** #</div>#
*)

(** --------------------------------------------
#<div class='slide'># 
** Promised proof for lesser_twin_100 *)
Definition lesser_twin_100_in_ord (x : lesser_twin_100) : 'I_100.
case : x => x /andP [_ px]; exact (Ordinal px).
Defined.

Lemma build_andb (a b : bool) : a -> b -> a && b.
by move => -> ->. Qed.

Definition lesser_twin_from_ord (x : 'I_100) : option lesser_twin_100 :=
  match x with
  | Ordinal x px => 
     match Sumbool.sumbool_of_bool (prime x && prime (x + 2)) with
     | left h => Some (exist _ x (build_andb _ _ h px))
     | right h => None
     end
  end.

Lemma Pcan100 : pcancel lesser_twin_100_in_ord lesser_twin_from_ord.
Proof. case => x p /=.
case: (elimTF andP p) => p1 p2.
rewrite /lesser_twin_from_ord.
case: (Sumbool.sumbool_of_bool (prime x && prime (x + 2))).
  by move => a; congr Some; apply: val_inj => /=.
by rewrite p1.
Qed.

(** #</div># 

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
