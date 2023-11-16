(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id: FSetFacts.v 12097 2009-04-21 17:13:08Z msozeau $ *)

(** * Finite sets library, modified by Avi *)

(* Require Import DecidableTypeEx. *)
Require Export OrderedTypeNM.
Require Export FSetInterfaceNM.
Require Import SetoidClass.
Set Implicit Arguments.
Unset Strict Implicit.

(** * Specifications written using equivalences *)

Section IffSpec. 
Context {elt : Set}.
Context {E : OrderedType elt}.
Context {M : FSetInterfaceNM E}.

Variable s s' s'' : t.
Variable x y z : elt.

Definition eqb := if x == y then true else false.

Lemma In_eq_iff : x == y -> (In x s <-> In y s).
Proof.
split; apply In_1; [|symmetry]; auto.
Qed.

Lemma mem_iff : In x s <-> mem x s = true.
Proof.
split; [apply mem_1|apply mem_2].
Qed.

Lemma not_mem_iff : ~In x s <-> mem x s = false.
Proof.
rewrite mem_iff; destruct (mem x s); intuition.
Qed.

Lemma equal_iff : s[=]s' <-> equal s s' = true.
Proof. 
split; [apply equal_1|apply equal_2].
Qed.

Lemma subset_iff : s[<=]s' <-> subset s s' = true.
Proof. 
split; [apply subset_1|apply subset_2].
Qed.

Lemma empty_iff : In x empty <-> False.
Proof.
intuition; apply (empty_1 H).
Qed.

Lemma is_empty_iff : Empty s <-> is_empty s = true. 
Proof. 
split; [apply is_empty_1|apply is_empty_2].
Qed.

Lemma singleton_iff : In y (singleton x) <-> x == y.
Proof.
split; [apply singleton_1|apply singleton_2].
Qed.

Lemma add_iff : In y (add x s) <-> x == y \/ In y s.
Proof. 
split; [ | destruct 1; [apply add_1|apply add_2]]; auto.
destruct (x == y) as [F|F]; auto.
intro H; right; exact (add_3 F H).
Qed.

Lemma add_neq_iff : ~ x == y -> (In y (add x s)  <-> In y s).
Proof.
split; [apply add_3|apply add_2]; auto.
Qed.

Lemma remove_iff : In y (remove x s) <-> In y s /\ ~ x == y.
Proof.
split; [split; [apply remove_3 with x |] | destruct 1; apply remove_2]; auto.
intro.
apply (remove_1 H0 H).
Qed.

Lemma remove_neq_iff : ~ x == y -> (In y (remove x s) <-> In y s).
Proof.
split; [apply remove_3|apply remove_2]; auto.
Qed.

Lemma union_iff : In x (union s s') <-> In x s \/ In x s'.
Proof.
split; [apply union_1 | destruct 1; [apply union_2|apply union_3]]; auto.
Qed.

Lemma inter_iff : In x (inter s s') <-> In x s /\ In x s'.
Proof.
split; [split; [apply inter_1 with s' | apply inter_2 with s] | destruct 1; apply inter_3]; auto.
Qed.

Lemma diff_iff : In x (diff s s') <-> In x s /\ ~ In x s'.
Proof.
split; [split; [apply diff_1 with s' | apply diff_2 with s] | destruct 1; apply diff_3]; auto.
Qed.

Variable f : elt->bool.

Lemma filter_iff :  Proper (equiv ==> equiv) f -> (In x (filter f s) <-> In x s /\ f x = true).
Proof. 
split; [split; [apply filter_1 with f | apply filter_2 with s] | destruct 1; apply filter_3]; auto. 
Qed.

Lemma for_all_iff : Proper (equiv ==> equiv) f ->
  (For_all (fun x => f x = true) s <-> for_all f s = true).
Proof.
split; [apply for_all_1 | apply for_all_2]; auto.
Qed.
 
Lemma exists_iff : Proper (equiv ==> equiv) f ->
  (Exists (fun x => f x = true) s <-> exists_ f s = true).
Proof.
split; [apply exists_1 | apply exists_2]; auto.
Qed.

Lemma elements_iff : In x s <-> InA equiv x (elements s).
Proof. 
split; [apply elements_1 | apply elements_2].
Qed.

End IffSpec.

(** Useful tactic for simplifying expressions like [In y (add x (union s s'))] *)
  
Ltac set_iff := 
 repeat (progress (
  rewrite add_iff || rewrite remove_iff || rewrite singleton_iff 
  || rewrite union_iff || rewrite inter_iff || rewrite diff_iff
  || rewrite empty_iff)).

(**  * Specifications written using boolean predicates *)

Section BoolSpec.
Context {elt : Set}.
Context {E : OrderedType elt}.
Context {M : FSetInterfaceNM E}.

Variable s s' s'' : t.
Variable x y z : elt.

Lemma mem_b : x == y -> mem x s = mem y s.
Proof. 
intros.
generalize (mem_iff s x) (mem_iff s y)(In_eq_iff s H).
destruct (mem x s); destruct (mem y s); intuition.
Qed.

Lemma empty_b : mem y empty = false.
Proof.
generalize (empty_iff y)(mem_iff empty y).
destruct (mem y empty); intuition.
Qed.

Lemma add_b : mem y (add x s) = eqb x y || mem y s.
Proof.
generalize (mem_iff (add x s) y)(mem_iff s y)(add_iff s x y); unfold eqb.
destruct (x == y); destruct (mem y s); destruct (mem y (add x s)); simpl; intuition. 
contradiction.
Qed.

Lemma add_neq_b : ~ x == y -> mem y (add x s) = mem y s.
Proof.
intros; generalize (mem_iff (add x s) y)(mem_iff s y)(add_neq_iff s H).
destruct (mem y s); destruct (mem y (add x s)); intuition.
Qed.

Lemma remove_b : mem y (remove x s) = mem y s && negb (eqb x y).
Proof.
generalize (mem_iff (remove x s) y)(mem_iff s y)(remove_iff s x y); unfold eqb.
destruct (x == y); destruct (mem y s); destruct (mem y (remove x s)); simpl; intuition.
Qed.

Lemma remove_neq_b : ~ x == y -> mem y (remove x s) = mem y s.
Proof.
intros; generalize (mem_iff (remove x s) y)(mem_iff s y)(remove_neq_iff s H).
destruct (mem y s); destruct (mem y (remove x s)); intuition.
Qed.

Lemma singleton_b : mem y (singleton x) = eqb x y.
Proof. 
generalize (mem_iff (singleton x) y)(singleton_iff x y); unfold eqb.
destruct (x == y); destruct (mem y (singleton x)); intuition.
contradiction.
Qed.

Lemma union_b : mem x (union s s') = mem x s || mem x s'.
Proof.
generalize (mem_iff (union s s') x)(mem_iff s x)(mem_iff s' x)(union_iff s s' x).
destruct (mem x s); destruct (mem x s'); destruct (mem x (union s s')); intuition.
Qed.

Lemma inter_b : mem x (inter s s') = mem x s && mem x s'.
Proof.
generalize (mem_iff (inter s s') x)(mem_iff s x)(mem_iff s' x)(inter_iff s s' x).
destruct (mem x s); destruct (mem x s'); destruct (mem x (inter s s')); intuition.
Qed.

Lemma diff_b : mem x (diff s s') = mem x s && negb (mem x s').
Proof.
generalize (mem_iff (diff s s') x)(mem_iff s x)(mem_iff s' x)(diff_iff s s' x).
destruct (mem x s); destruct (mem x s'); destruct (mem x (diff s s')); simpl; intuition.
Qed.

Lemma elements_b : mem x s = existsb (eqb x) (elements s).
Proof.
generalize (mem_iff s x)(elements_iff s x)(existsb_exists (eqb x) (elements s)).
rewrite InA_alt.
destruct (mem x s); destruct (existsb (eqb x) (elements s)); auto; intros.
symmetry.
rewrite H1.
destruct H0 as (H0,_).
destruct H0 as (a,(Ha1,Ha2)); [ intuition |].
exists a; intuition.
unfold eqb; destruct (x == a); auto.
rewrite <- H.
rewrite H0.
destruct H1 as (H1,_).
destruct H1 as (a,(Ha1,Ha2)); [intuition|].
exists a; intuition.
unfold eqb in *; destruct (x == a); auto; discriminate.
Qed.

Variable f : elt->bool.

Lemma filter_b : Proper (equiv ==> equiv) f -> mem x (filter f s) = mem x s && f x.
Proof. 
intros.
generalize (mem_iff (filter f s) x)(mem_iff s x)(filter_iff s x H).
destruct (mem x s); destruct (mem x (filter f s)); destruct (f x); simpl; intuition.
Qed.

Lemma for_all_b :  Proper (equiv ==> equiv) f ->
  for_all f s = forallb f (elements s).
Proof.
intros.
generalize (forallb_forall f (elements s))(for_all_iff s H)(elements_iff s).
unfold For_all.
destruct (forallb f (elements s)); destruct (for_all f s); auto; intros.
rewrite <- H1; intros.
destruct H0 as (H0,_).
rewrite (H2 x0) in H3.
rewrite (InA_alt equiv x0 (elements s)) in H3.
destruct H3 as (a,(Ha1,Ha2)).
rewrite (H _ _ Ha1).
apply H0; auto.
symmetry.
rewrite H0; intros.
destruct H1 as (_,H1).
apply H1; auto.
rewrite H2.
rewrite InA_alt; eauto.
eexists; split; [reflexivity|eauto].
Qed.

Lemma exists_b :  Proper (equiv ==> equiv) f ->
  exists_ f s = existsb f (elements s).
Proof.
intros.
generalize (existsb_exists f (elements s))(exists_iff s H)(elements_iff s).
unfold Exists.
destruct (existsb f (elements s)); destruct (exists_ f s); auto; intros.
rewrite <- H1; intros.
destruct H0 as (H0,_).
destruct H0 as (a,(Ha1,Ha2)); auto.
exists a; split; auto.
rewrite H2; rewrite InA_alt; eauto.
eexists. split; [reflexivity|eauto].
symmetry.
rewrite H0.
destruct H1 as (_,H1).
destruct H1 as (a,(Ha1,Ha2)); auto.
rewrite (H2 a) in Ha1.
rewrite (InA_alt equiv a (elements s)) in Ha1.
destruct Ha1 as (b,(Hb1,Hb2)).
exists b; auto.
rewrite <- (H _ _ Hb1); auto.
Qed.

End BoolSpec.

Section Morphisms.
Context {elt : Set}.
Context {E : OrderedType elt}.
Context {M : FSetInterfaceNM E}.

Global Instance Equal_equiv : Equivalence Equal.
Proof. rewrite <- equivIsEqual. typeclasses eauto. Qed.


Global Instance In_m : Proper (equiv ==> Equal ==> iff) In.
Proof.
unfold Equal; intros x y H s s' H0.
rewrite (In_eq_iff s H); auto.
Qed.

Global Instance In_m' : Proper (equiv ==> equiv ==> iff) In.
Proof. rewrite equivIsEqual. typeclasses eauto. Qed.

Global Instance is_empty_m : Proper (equiv==>equiv) is_empty.
Proof.
unfold Equal; intros s s' H.
generalize (is_empty_iff s)(is_empty_iff s').
destruct (is_empty s); destruct (is_empty s'); 
 unfold Empty; auto; clsubst*; intuition.
Qed.

Ltac unp := unfold Proper, respectful.

Global Instance Empty_m : Proper (equiv ==> iff) Empty.
Proof. unp;
intros. do 2 rewrite is_empty_iff; rewrite H; intuition.
Qed.

Global Instance mem_m : Proper (equiv ==> equiv ==> equiv) mem.
Proof. unp.
rewrite equivIsEqual; unfold Equal; intros x y H s s' H0.
generalize (H0 x); clear H0; rewrite (In_eq_iff s' H).
generalize (mem_iff s x)(mem_iff s' y).
destruct (mem x s); destruct (mem y s'); intuition.
Qed.

Global Instance singleton_m : Proper (equiv ==> equiv) singleton.
Proof. unp.
rewrite equivIsEqual. intros x y H a.
do 2 rewrite singleton_iff; clsubst*; intuition. 
Qed.

Global Instance add_m : Proper (equiv ==> equiv ==> equiv) add.
Proof. unp. rewrite equivIsEqual.
unfold Equal; intros x y H s s' H0 a.
do 2 rewrite add_iff; rewrite H; rewrite H0; intuition.
Qed.

Global Instance remove_m : Proper (equiv ==> equiv ==> equiv) remove.
Proof. unp. rewrite equivIsEqual.
unfold Equal; intros x y H s s' H0 a.
do 2 rewrite remove_iff; rewrite H; rewrite H0; intuition.
Qed.

Global Instance union_m : Proper (equiv ==> equiv ==> equiv) union.
Proof. unp; rewrite equivIsEqual.
unfold Equal; intros s s' H s'' s''' H0 a.
do 2 rewrite union_iff; rewrite H; rewrite H0; intuition.
Qed.

Global Instance inter_m : Proper (equiv ==> equiv ==> equiv) inter.
Proof. unp; rewrite equivIsEqual.
unfold Equal; intros s s' H s'' s''' H0 a.
do 2 rewrite inter_iff; rewrite H; rewrite H0; intuition.
Qed.

Global Instance diff_m : Proper (equiv ==> equiv ==> equiv) diff.
Proof. unp; rewrite equivIsEqual.
unfold Equal; intros s s' H s'' s''' H0 a.
do 2 rewrite diff_iff; rewrite H; rewrite H0; intuition.
Qed.

Global Instance Subset_m : Proper (equiv ==> equiv ==> iff) Subset.
Proof. unp; rewrite equivIsEqual.
unfold Equal, Subset. intuition.
  apply -> H0. apply H1. apply <- H. auto.
  apply <- H0. apply H1. apply -> H. auto.
Qed.

Global Instance Equal_equiv_subr : subrelation Equal equiv | 9.
Proof. rewrite equivIsEqual. typeclasses eauto. Qed.

Global Instance equiv_Equal_subr : subrelation equiv Equal | 9.
Proof. rewrite equivIsEqual. typeclasses eauto. Qed.

Global Instance subset_m : Proper (equiv ==> equiv ==> equiv) subset.
Proof. unp. rewrite equivIsEqual.
intros s s' H s'' s''' H0.
generalize (subset_iff s s'') (subset_iff s' s''').
rewrite <- equivIsEqual in H, H0.
destruct (subset s s''); destruct (subset s' s'''); auto; clsubst*; intuition.
Qed.

Global Instance equal_m : Proper (equiv ==> equiv ==> equiv) equal.
Proof. unp. rewrite equivIsEqual.
intros s s' H s'' s''' H0.
generalize (equal_iff s s'') (equal_iff s' s''').
rewrite <- equivIsEqual in H, H0 |- *.
destruct (equal s s''); destruct (equal s' s'''); auto; clsubst*; intuition.
Qed.

(* [Subset] is a setoid order *)

Global Instance Subset_refl : Reflexive Subset.
Proof. do 2 red; auto. Qed.

Global Instance Subset_trans : Transitive Subset.
Proof. red; unfold Subset; eauto. Qed.

Add Relation t Subset
 reflexivity proved by Subset_refl
 transitivity proved by Subset_trans
 as SubsetSetoid.

Global Instance In_s_m : Proper (equiv ==> Subset ++> Basics.impl) In | 1.
Proof. unp. unfold Subset, Basics.impl. intros. clsubst*. auto. Qed.

Global Instance Empty_s_m : Proper (Subset --> Basics.impl) Empty.
Proof. unp; unfold Subset, Empty, Basics.impl; firstorder. Qed.

Global Instance add_s_m : Proper (equiv ==> Subset ++> Subset) add.
Proof.
unfold Subset; intros x y H s s' H0 a.
do 2 rewrite add_iff; rewrite H; intuition.
Qed.

Global Instance remove_s_m : Proper (equiv ==> Subset ++> Subset) remove.
Proof.
unfold Subset; intros x y H s s' H0 a.
do 2 rewrite remove_iff; rewrite H; intuition.
Qed.

Global Instance union_s_m : Proper (Subset ++> Subset ++> Subset) union.
Proof.
unfold Equal; intros s s' H s'' s''' H0 a.
do 2 rewrite union_iff; intuition.
Qed.

Global Instance inter_s_m : Proper (Subset ++> Subset ++> Subset) inter.
Proof.
unfold Equal; intros s s' H s'' s''' H0 a.
do 2 rewrite inter_iff; intuition.
Qed.

Global Instance diff_s_m : Proper (Subset ++> Subset --> Subset) diff.
Proof.
unfold Subset; intros s s' H s'' s''' H0 a.
do 2 rewrite diff_iff; intuition.
Qed.

(* [fold], [filter], [for_all], [exists_] and [partition] cannot be proved morphism
   without additional hypothesis on [f]. For instance: *)

Global Instance filter_equal : forall (f:elt->bool), Proper (equiv ==> equiv) f ->
  Proper (equiv ==> equiv) (filter f).
Proof. unp. rewrite equivIsEqual. unfold Equal; intros.
repeat rewrite filter_iff; auto; rewrite H0; tauto.
Qed.

Lemma filter_ext : forall (f f':elt->bool), Proper (equiv ==> equiv) f -> (forall x, f x = f' x) ->
 forall s s', s[=]s' -> filter f s [=] filter f' s'.
Proof.
intros f f' Hf Hff' s s' Hss' x. do 2 (rewrite filter_iff; auto).
rewrite Hff', Hss'; intuition.
unp. intros; rewrite <- 2 Hff'; auto.
Qed.

Require Import RelationClasses.
Lemma PERleft `{p:PER A R} x y : R x y -> R x x.
Proof. intros; transitivity y; [idtac|symmetry]; assumption. Qed.

Lemma PERright `{p:PER A R} x y : R x y -> R y y.
Proof. intros; transitivity x; [symmetry|idtac]; assumption. Qed.

Global Instance filter_m :
  Proper ((equiv ==> equiv) ==> equiv ==> equiv) filter.
intros f1 f2 pf.
pose (PERleft pf). pose (PERright pf).
unp. rewrite equivIsEqual. intros.
apply filter_ext; auto.
intros. apply pf. reflexivity.
Qed.

Global Instance filter_subset (f:elt->bool) : Proper (equiv ==> equiv) f -> 
  Proper (Subset ==> Subset) (filter f).
Proof. unp.
unfold Subset; intros; rewrite filter_iff in H1 |- *; intuition.
Qed.

Global Instance Equal_Subset_subr : subrelation Equal Subset | 9.
Proof. unfold Subset, Equal. do 4 red. intros. apply -> H. auto. Qed.

(* For [elements], [min_elt], [max_elt] and [choose], we would need setoid
   structures on [list elt] and [option elt]. *)

(* Later:
Add Morphism cardinal ; cardinal_m.
*)

End Morphisms.

(** Now comes variants for self-contained weak sets and for full sets.
    For these variants, only one argument is necessary. Thanks to
    the subtyping [WS<=S], the [Facts] functor which is meant to be
    used on modules [(M:S)] can simply be an alias of [WFacts]. *)

