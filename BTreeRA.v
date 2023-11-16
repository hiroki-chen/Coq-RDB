(* Copyright (c) 2009, Harvard University
 * All rights reserved.
 *
 * Authors: Avraham Shinnar, Ryan Wisnesky, Gregory Malecha
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * - Redistributions of source code must retain the above copyright notice,
 *   this list of conditions and the following disclaimer.
 * - Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 * - The names of contributors may not be used to endorse or promote products
 *   derived from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE
 * LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR 
 * CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
 * SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
 * INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
 * CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 *)

Require Import BPlusTreeImplModel.
Require Import DataModel RelationalModel.
Require Import Ynot.
Require Import List.
Require Import SetoidList.
Require Import SetoidClass.
Require Import RelationClasses.
Require Import SetoidDec.

Module OT := OrderedTypeNM.

Require Import FSetInterfaceNM.
Require Import FSetDecide.

Global Instance perm_equiv A: Equivalence (@Permutation A).
Proof. split; red.
  apply Permutation_refl.
  apply Permutation_sym.
  apply Permutation_trans.
Qed.


Ltac respectful_iff_to_impl R :=
  match R with
    | (@respectful ?A ?B ?R1 ?R2) => let R2' := respectful_iff_to_impl R2 in 
      constr:(@respectful A B R1 R2')
    | iff => Basics.impl
    | ?x => x
  end.

Ltac proper_iff_to_impl := intros; 
  match goal with 
    [|- Proper ?R ?P] => let R' := respectful_iff_to_impl R in 
      cut (Proper R' P); [solve [intro H; split; intros; eapply H; eauto; symmetry; eauto]|unp; unfold Basics.impl]
  end.

Ltac pintro := (proper_iff_to_impl || unp).

(* basic facts about map/fold.  Should be in stdlib *)
(** stolen from avi's stdlib *)
Definition compose {A B C} (f:B->C) g := fun x:A => f (g x).
Lemma map_foldr_fusion {A B C: Type} (f:B->A->A) (g:C->B) (z:A) (l:list C):
  (fold_right f z) (map g l) = fold_right (compose f g) z l.
Proof.    
  unfold compose; intros; revert z. 
  induction l; simpl; intuition congruence.
Qed.

Lemma foldr_app {A B : Type} (f:B->A->A) l l' i :
  fold_right f i (l++l') = fold_right f (fold_right f i l') l.
Proof.
  induction l.
  simpl; auto.
  simpl; intros.
  f_equal; auto.
Qed.

Lemma foldlr {A B : Type} (f:A->B->A) l i :
  fold_left f l i = fold_right (fun x y => f y x) i (rev l).
Proof.
  induction l.
  simpl; auto.
  intros.
  simpl.
  rewrite foldr_app; simpl; auto.
Qed.

Lemma map_foldl_fusion {A B C: Type} (f:A->B->A) (g:C->B) (z:A) (l:list C):
  (fold_left f (map g l)) z = fold_left (fun x => compose (f x) g) l z.
Proof.
  intros.
  rewrite foldlr, foldlr, <- map_rev, map_foldr_fusion.
  reflexivity.
Qed.

(* basic facts about eqlist, equivlist, ... 
   these should be in the standard library
   *)
Instance eqlistA_refl {A} (P:relation A) {r:Reflexive P} : Reflexive (eqlistA P).
Proof. red; induction x; intuition. Qed.


Instance eqlistA_sym  {A} (P:relation A) {s:Symmetric P} : Symmetric (eqlistA P).
Proof. red.
  induction x; intuition; inversion H; intuition; subst;
  inversion H0; intuition; subst.
Qed.


Instance eqlistA_trans {A} (P:relation A) {t:Transitive P} : Transitive (eqlistA P).
Proof. red.
  induction x; intuition; inversion H; intuition; subst;
  inversion H0; intuition; subst.
  apply eqlistA_cons.
  transitivity x'; eauto.
  eapply IHx; eauto.
Qed.

Instance eqlistA_equ {A} (P:relation A) {equ:Equivalence P} : Equivalence (eqlistA P).
Proof. split; typeclasses eauto. Qed.

Lemma eqlistA_trans' : forall A P {s:Symmetric P} {t:Transitive P} (x y: list A) z,
  eqlistA P x y -> 
  eqlistA P x z -> 
  eqlistA P z y.
Proof.
  intros. eapply eqlistA_trans; eauto. 
  symmetry; auto.
Qed.

Global Instance equivlistA_equ {A} (R:relation A) : Equivalence (equivlistA R).
Proof.
  unfold equivlistA.
  split; red;  intros; intuition.
  apply <- H; auto.
  apply -> H; auto.
  apply -> H0; apply -> H; auto.
  apply <- H; apply <- H0; auto.
Qed.

Global Instance in_eqlistA_prop A (R:relation A) {s:Symmetric R} {t:Transitive R}
  : Proper (eq ==> (eqlistA R) ==> iff) (InA R).
Proof.
  unfold Proper, respectful.
  induction x0; inversion 1; subst; intuition.
  inversion H0; inversion H; subst.
  left. transitivity a; auto.
  right. eapply IHx0; eauto.
  
  inversion H0; inversion H; subst.
  left. transitivity x'; auto.
  right. eapply IHx0; eauto.
Qed.

Global Instance in_equivlistA_prop {A} (R:relation A) 
  : Proper (eq ==> (equivlistA R) ==> iff) (InA R).
Proof.
  unfold Proper, respectful, equivlistA.
  intros. subst. auto.
Qed.

Global Instance in_prop {A} (R:relation A) {s:Symmetric R} {t:Transitive R}
  : Proper (R ==> eq ==> iff) (InA R).
Proof.
  unfold Proper, respectful, equivlistA.
  intros. subst. induction y0; intuition; try inversion H0;
  inversion H2; subst; auto;
  constructor; 
    eapply @transitivity; eauto.
Qed.

Global Instance map_eqlistA {A B} eqA eqB f {r:Reflexive eqA}: Proper (eqA ==> eqB) f ->
Proper ((eqlistA eqA) ==> (eqlistA eqB)) (@map A B f).
Proof. unfold Proper, respectful. induction x; destruct y; simpl in *; intuition; inversion H0. 
  subst. constructor; auto.
Qed.

Instance equiv_eqlistA {A} (R:relation A) {s:Symmetric R} {t:Transitive R} : subrelation (eqlistA R) (equivlistA R).
Proof.
  repeat red. intuition.
  rewrite H in H0. auto.
  rewrite <- H in H0. auto.
Qed.

Section specs.

Variable (F:forall (I: Typing), DBSet I).
Variable J : Typing.

(* orders based on the key *)
 Definition key : Set := Tuple J.
 Definition value : key -> Set := fun _:key => unit.

Definition eqTuple' (x y: sigTS value) : Prop := 
 eqTuple (projT1S x) (projT1S y).

Definition ltTuple' (x y: sigTS value) : Prop := 
 ltTuple (projT1S x) (projT1S y).

Global Instance eqTuple'_equ : Equivalence eqTuple'.
unfold eqTuple'. split; red; intuition. transitivity (projT1S y); auto.
Qed.

Definition eqTuple'_set : Setoid (sigTS value) := Build_Setoid eqTuple'_equ.
Existing Instance eqTuple'_set.

(* specialize SortA_equivlistA_eqlistA to the 's *)
Lemma sortlt_equivlistA_eqlistA x y: 
  sort ltTuple' x -> sort ltTuple' y -> equivlistA eqTuple' x y -> eqlistA eqTuple' x y.
intros.
eapply SortA_equivlistA_eqlistA; eauto; instantiate; intuition; unfold ltTuple', eqTuple' in *; toEquiv.
  rewrite H2; auto.
  rewrite H3 in H2. auto.
  rewrite H3 in H2; elim (ltTuple_not_eq H2); reflexivity.
  rewrite <- H3; auto.
  rewrite H2; auto.
Qed.

Instance lelistA_eqlistA : Proper (eq ==> (eqlistA eqTuple') ==> iff) (lelistA ltTuple').
Proof.
unfold Proper, respectful; intros; subst.
unfold ltTuple', eqTuple' in *.
split; induction 1; inversion H0; subst; constructor.
rewrite H3 in H; auto.
rewrite H4; auto.
Qed.

Lemma lelistA'_eq x k v0 v l :
     eqTuple (A:=J) x k
  -> lelistA ltTuple' (existTS value x v0) l
  -> lelistA ltTuple' (existTS value k v) l.
Proof.
  induction l; auto. constructor; auto. unfold ltTuple' in *. inversion H0; simpl in *. 
  subst.  rewrite <- H. auto.
Qed.

Lemma elements_2' x s : InA (eqTuple (A:=J)) x (elements s) -> In (FSetInterfaceNM:=(F J)) x s.
Proof.
  intros. apply (elements_2 H).
Qed.

Lemma elements_1' x s : In (FSetInterfaceNM:=(F J)) x s -> InA (eqTuple (A:=J)) x (elements s).
Proof.
  intros. apply (elements_1 H).
Qed.

(* some facts about fsets. *)

Lemma eqlistA_nil {A} (R:relation A) t : eqlistA R t nil -> t = nil.
Proof. destruct t; inversion 1; trivial. Qed.

Lemma empty_elements_nil I : (elements (empty0 F I)) = nil.
Proof.
  intros. remember (elements (empty0 F I)) as e.
  destruct e; intuition.
  cut (In t (empty0 F I)).
    intro K; elim (empty_1 K).
  apply elements_2.
  rewrite <- Heqe.
  left. reflexivity.
Qed.


Lemma add_empty_elements x : eqlistA (@eqTuple J) (elements (add x (empty0 F J))) (x::nil).
Proof.
  intros. remember (elements (add x (empty0 F J))) as e.
  destruct e; intuition.
  assert (H:In x (add x (empty0 F J))). 
    apply  add_1; reflexivity.
  apply elements_1 in H. rewrite <- Heqe in H. inversion H.

  destruct (x == t).
    constructor. symmetry; auto.
    destruct e; intuition.
    assert (H:InA equiv t0 (t :: t0 :: e)).
      right; left; reflexivity.
    rewrite Heqe in H.
    apply elements_2 in H.
    assert (s:sort (@ltTuple J) (t::t0::e)).
      rewrite Heqe. apply elements_3.
    apply add_3 in H.
     elim (empty_1 H).

    destruct (x == t0); auto.
      inversion s. inversion H3. subst.
      rewrite <- e0, <- e1 in H5. elim (ltTuple_not_eq H5); reflexivity.

      assert (InA equiv t (t::e)) by (left; reflexivity).
      rewrite Heqe in H. apply elements_2 in H.
      apply add_3 in H; auto.
      elim (empty_1 H).
Qed.

Lemma fold_right_add_id x :
 fold_right (fun x0 : key => add x0) (empty0 F J) (@elements (Tuple J) (tupleOrd J) (F J) x) == x.
Proof.
intros.
  unfold DBRel.
  intros.
  rewrite equivIsEqual.
 split; intros H.
   apply elements_2.
   induction (elements x); simpl in *; intros.
     elim (@empty_1 _ _ (F J) _ H).
     destruct (a == a0).
       left. auto.
       right. apply IHl. eapply add_3; eauto. symmetry; auto.
   apply elements_1 in H.
   induction (elements x); simpl in *; intros.
     inversion H. 
     inversion H; subst.
       apply add_1. symmetry; auto.
       apply add_2. auto.
Qed.

(* facts about union *)
Lemma union_empty_idl J x : union (empty0 F J) x == x.
Proof.
  intros. rewrite equivIsEqual. split; intros.
    apply union_1 in H. intuition. elim (empty_1 H0).
    apply union_3; auto.
Qed.

Lemma union_empty_idr J x : union x (empty0 F J) == x.
Proof.
  intros. rewrite equivIsEqual. split; intros.
    apply union_1 in H. intuition. elim (empty_1 H0).
    apply union_2; auto.
Qed.

(* facts about select *)
Lemma select_false f k l: Proper (equiv ==> equiv) f -> (f k = true -> False) ->
  select (F:=F) (I:=J) f (add k l) == select (F:=F) (I:=J) f l.
Proof.
unfold DBRel; intros.
rewrite equivIsEqual. split; intros.
  pose (filter_1 H H1).
  pose (filter_2 H H1).
  apply filter_3; trivial.
  eapply add_3; eauto.
  intro. rewrite <- H2 in e.
  apply H0; auto.

  apply filter_3; trivial.
    apply add_2; eapply filter_1; eauto.
    eapply filter_2; eauto.
Qed.

Lemma select_true f k l: Proper (equiv ==> equiv) f -> f k = true ->
  select (F:=F) (I:=J) f (add k l) == add k (select (F:=F) (I:=J) f l).
Proof.
unfold DBRel; intros.
rewrite equivIsEqual. split; intros.
  destruct (k == a); [auto|].
  apply add_2.
  pose (filter_1 H H1).
  pose (filter_2 H H1).
  eapply filter_3; trivial.
  eapply add_3; eauto.

  
  destruct (k == a).
    apply filter_3; auto.
    rewrite <- e; auto.

    apply add_3 in H1; trivial.
    
    apply filter_3; auto.
     apply filter_1 in H1; auto.
     apply filter_2 in H1; auto.
Qed.

Lemma select_empty_empty f : Proper (equiv ==> equiv) f -> (select f (empty0 F J)) == empty0 F J.
Proof.
  unfold DBRel. intros. rewrite equivIsEqual. split; intros.
    eapply filter_1; auto.
    elim (empty_1 H0).
Qed.

Lemma select_empty_elements_nil f : Proper (equiv ==> equiv) f -> (elements (select f (empty0 F J))) = nil.
Proof.
  intros.
  apply eqlistA_nil with (R:=@eqTuple J).
  rewrite <- empty_elements_nil.
  rewrite select_empty_empty; auto.
  reflexivity.
Qed.

Lemma prodRel_emptyl_elements_nil I x0 : (elements (prodRel (F:=F) (I:=I) (J:=J) (empty0 F I) x0)) = nil.
Proof.
  intros.
  unfold prodRel. rewrite fold_1.
  rewrite empty_elements_nil. simpl.
  rewrite empty_elements_nil.
  trivial.
Qed.

Lemma add_el_equiv k l : equivlistA (@eqTuple J) (elements (add (FSetInterfaceNM:=(F J)) k l)) (k::elements l).
Proof.
  split; intros.
  destruct (k == x).
    symmetry in e; auto.
    right. apply elements_1'. eapply add_3; eauto.
  
  inversion H; subst; simpl; apply elements_1'. 
    symmetry in H1; auto.
    auto.
Qed.


Instance foldl_compat {A B : Type} (eqA:relation A) (eqB:relation B) {r:Reflexive eqB}:
Proper ((eqA ==> eqB ==> eqA) ==>  (eqlistA eqB) ==> eqA ==> eqA) (@fold_left A B) | 7.
Proof.  unfold Proper, respectful.
  induction x0; destruct y0; simpl in *; intuition; inversion H0; subst; intuition.
Qed.

Lemma fold_left_add_equiv I (f:Tuple J->Tuple I) l l' s :   
  Proper (equiv ==> equiv) f -> eqlistA (@eqTuple J) l l' ->
(fold_left (fun (a : t) (e : Tuple J) => add (FSetInterfaceNM:=(F I)) (f e) a)
           l s) ==
(fold_left (fun (a : t) (e : Tuple J) => add (f e) a)
           l' s).
Proof.
  intros.
  apply foldl_compat with (eqB:=@eqTuple J); intuition.
  unfold respectful. intros.
  apply add_push; auto.
Qed.

(* facts about entry_eq *)

Definition value_eq_ok 
 : forall J (k1 k2 : Tuple J), 
    k1 == k2 -> 
  (fun _ : Tuple J => unit) k1 = (fun _ : Tuple J => unit) k2.
Proof.
intros.
 unfold value. reflexivity.
Qed.

Lemma eqTuple_entry_eq (J : Typing) a t :
     eqTuple (A:=J) a t
  <-> @entry_eq _ (fun _ : Tuple J => unit) (tupleOrd J) (value_eq_ok J) (existTS (fun _ : Tuple J => unit) a tt)
       (existTS (fun _ : Tuple J => unit) t tt).
Proof.
  intros. unfold entry_eq.
  match goal with
    [|- context [key_eq_dec ?R ?P1 ?P2]] => destruct (key_eq_dec R P1 P2)
  end; simpl in *; intuition.
  match goal with
    [|- _ = ?x] => destruct x
  end; auto.
Qed.

Global Instance entry_eq_refl: 
   @Reflexive (@sigTS (Tuple J) (value))
     (@entry_eq (Tuple J) (value) (tupleOrd J)  (value_eq_ok J)).
Proof.
  intros. red.
  unfold entry_eq. intros.
  repeat match goal with
    | [|- context [key_eq_dec ?R ?P1 ?P2]] => destruct (key_eq_dec R P1 P2)
    | [H: context [key_eq_dec ?R ?P1 ?P2] |- _] => destruct (key_eq_dec R P1 P2)
  end; simpl in *; intuition.
  match goal with
    [|- ?x = ?y] => destruct y; destruct x
  end; intuition.
Qed.

Global Instance entry_eq_sym : 
   @Symmetric (@sigTS (Tuple J) (value))
     (@entry_eq (Tuple J) (value) (tupleOrd J)  (value_eq_ok J)).
Proof.
  intros. red.
  unfold entry_eq. intros.
  repeat match goal with
    | [|- context [key_eq_dec ?R ?P1 ?P2]] => destruct (key_eq_dec R P1 P2)
    | [H: context [key_eq_dec ?R ?P1 ?P2] |- _] => destruct (key_eq_dec R P1 P2)
  end; simpl in *; intuition.
  match goal with
    [|- ?x = ?y] => destruct x; destruct y
  end; intuition.
Qed.

Global Instance entry_eq_trans : 
   @Transitive (@sigTS (Tuple J) (value))
     (@entry_eq (Tuple J) (value) (tupleOrd J)  (value_eq_ok J)).
Proof.
  intros. red.
  unfold entry_eq. intros.
  repeat match goal with
    | [|- context [key_eq_dec ?R ?P1 ?P2]] => destruct (key_eq_dec R P1 P2)
    | [H: context [key_eq_dec ?R ?P1 ?P2] |- _] => destruct (key_eq_dec R P1 P2)
  end; simpl in *; intuition.
  match goal with
    [|- ?x = ?y] => destruct x; destruct y
  end; intuition.
  elim c. transitivity (projT1S y); auto.
Qed.

Global Instance entry_eq_equ : @Equivalence (@sigTS (Tuple J) (value))
     (@entry_eq (Tuple J) (value) (tupleOrd J)  (value_eq_ok J)).
Proof. split; typeclasses eauto. Qed.

(* Isomorphism between models *)
Definition conv_el := (fun x : key => existTS (value) x tt).

Definition conv : DBRel (A:=J) (F J) -> Model (value) := (fun l => (map conv_el (elements l))).

Definition unconv : Model (value) -> DBRel (A:=J) (F J) :=
  (fun m => (fold_right (fun x => FSetInterfaceNM.add (projT1S x)) (empty0 F J) m)).

Instance conv_el_proper : Proper ((@eqTuple J) ==> eqTuple') conv_el.
Proof.
  unfold conv_el, Proper, respectful, eqTuple'. simpl. auto.
Qed.

Lemma conv_empty_nil : conv (empty0 F J) = nil.
Proof.
  unfold conv, conv_el. intros. 
  rewrite empty_elements_nil. simpl. auto.
Qed.

Lemma conv_select_empty_nil f : Proper (equiv ==> equiv) f -> conv (select f (empty0 F J)) = nil.
Proof.
  unfold conv, conv_el. intros. 
  rewrite select_empty_elements_nil; simpl; auto.
Qed.

Lemma conv_add_cons : forall x0, 
eqlistA (eqTuple') (conv (add x0 (empty0 F J)))
     (existTS (value) x0 tt :: nil).
Proof.
 intros. unfold conv.
 apply (map_eqlistA (@eqTuple J) (eqTuple') (conv_el)
   _ (elements (add x0 (empty0 F J))) (x0::nil)).
 apply add_empty_elements.
Qed.

Lemma conv_el_lelistA a l : lelistA (ltTuple (A:=J)) a l -> lelistA (ltTuple') (conv_el a) (map conv_el l).
Proof.  
  induction l; simpl; auto; inversion 1; intuition.
Qed.

Lemma conv_el_sort l : sort (@ltTuple J) l -> sort (ltTuple') (map conv_el l).
Proof.
  Hint Resolve conv_el_lelistA.
  induction l; simpl; auto; inversion 1; subst;
  constructor; auto.
Qed.
  
Lemma conv_sort x : sort (ltTuple') (conv x).
Proof.
  intros. apply conv_el_sort; auto. 
Qed.
Hint Resolve conv_sort.

Lemma eqTuple'_ina x l : InA (eqTuple') x (map conv_el l) <-> InA (@eqTuple J) (projT1S x) l.
Proof.
  unfold eqTuple', conv_el.
  destruct x; simpl.
  induction l; simpl; intuition; (inversion H||inversion H1); subst; simpl in *; intuition.
Qed.

Global Instance conv_prop_equiv : Proper (equiv ==> equivlistA (eqTuple')) (conv).
Proof.
  unfold DBRel, Proper, respectful. intros.
  rewrite equivIsEqual in H.
  unfold equivlistA.
  unfold conv. split; intros G;
  apply -> eqTuple'_ina in G; 
  apply <- eqTuple'_ina; 
    pose (elements_2 G) as G'.
     apply H in G'; pose (elements_1 G') as i; auto.
     pose (proj2 (H _) G'). pose (elements_1 i); auto.
Qed.

Theorem iso2 : forall x, unconv (conv x) == x.
Proof.
 unfold unconv, conv; intros.
 rewrite map_foldr_fusion. unfold compose; simpl.
 apply fold_right_add_id.
Qed.

Theorem iso1_equiv : forall (x: Model (value)), 
 equivlistA (eqTuple') (conv (unconv x)) x.
Proof.
  split; intros; induction x; simpl in *; intuition.
    rewrite conv_empty_nil in H. inversion H.
    
    unfold conv in H.
    apply eqTuple'_ina in H.
    apply elements_2' in H.
    destruct (projT1S x0 == projT1S a); auto.
    symmetry in c; apply add_3 in H; auto.
    apply elements_1' in H.
    apply <- eqTuple'_ina in H. auto.
    
    inversion H.

    unfold conv. apply <- eqTuple'_ina. apply elements_1'.
    inversion H; subst.
      apply add_1. symmetry; auto.
      apply add_2. apply elements_2'. apply -> eqTuple'_ina. auto.
Qed.

Theorem iso1_equiv' : forall (x: Model (value)), 
  equivlistA (eqTuple') (map conv_el (elements (unconv x))) x.
Proof.
  intros.
  pose iso1_equiv as is. unfold conv in is. auto.
Qed.

Theorem iso1 : forall (x: Model (value)), 
 @sort _ (ltTuple') x -> 
 eqlistA (eqTuple') (conv (unconv x)) x.
Proof.
  Hint Resolve iso1_equiv.
  intros. eapply sortlt_equivlistA_eqlistA; eauto.
Qed.

Instance unconv_prop : Proper (eqlistA (eqTuple') ==> equiv) (unconv).
Proof.
  unfold DBRel, Proper, respectful.
  induction x; inversion 1; subst; simpl.
    reflexivity.
    destruct a; destruct x'.
    inversion H. subst.
    toEquiv.
    apply add_push; auto.
Qed.

(* some more about entry_eq *)

Lemma eqlistA_entry_eq l l' :
     eqlistA (eqTuple (A:=J)) l l'
  <-> eqlistA (entry_eq (tupleOrd J)  (value_eq_ok J)) (map conv_el l) (map conv_el l').
Proof. 
  induction l; destruct l'; simpl; intuition; inversion H;
  subst; constructor. 
    apply -> eqTuple_entry_eq; auto. 
    apply -> IHl; auto.
    apply <- eqTuple_entry_eq; auto. 
    apply <- IHl; auto.
Qed.

Lemma eqTuple'_entry_eq x y : eqTuple' x y <-> entry_eq (tupleOrd J)  (value_eq_ok J) x y.
Proof.
  unfold eqTuple'; destruct x; destruct y; destruct v; destruct v0; intros.
  apply eqTuple_entry_eq; auto.
Qed.

Lemma eqTuple'_entry_eq_list R R' : 
  eqlistA (eqTuple') R R' <-> eqlistA (entry_eq (tupleOrd J)  (value_eq_ok J)) R R'.
Proof.
  Hint Resolve eqTuple'_entry_eq.
  induction R; destruct R'; intuition; 
  inversion H; auto; constructor.
    apply -> eqTuple'_entry_eq; auto.
    apply -> IHR; auto.
    apply <- eqTuple'_entry_eq; auto.
    apply <- IHR; auto.
Qed.
Theorem rep_prop : forall n p R R',
  eqlistA (@eqTuple') R R' ->
  rep n (tupleOrd J)  (value_eq_ok J) p R ==> rep n (tupleOrd J)  (value_eq_ok J) p R'.
Proof.
  intros. unfold rep'. unfold rep. sep fail auto. 
  cut (eqlistA (entry_eq (tupleOrd J)  (value_eq_ok J)) R'
    (as_map (value) v1)).
  sep fail auto. 
  eapply eqlistA_trans';
    try typeclasses eauto.
  eauto.
  apply -> eqTuple'_entry_eq_list; auto.
Qed.

Theorem rep_conv_prop : forall n p R R',
  R == R' ->
  rep n (tupleOrd J)  (value_eq_ok J) p (conv R) ==> rep n (tupleOrd J)  (value_eq_ok J) p (conv R').
Proof.
  intros. 
  apply rep_prop.
  apply sortlt_equivlistA_eqlistA; auto.
  rewrite H; reflexivity.
Qed.

Lemma iso1_in_repf n p1 P : sort (ltTuple') P ->
  rep n (tupleOrd J)  (value_eq_ok J) p1 (conv (unconv P)) ==>
  rep n (tupleOrd J)  (value_eq_ok J) p1 P.
Proof.
intros.
apply rep_prop.
apply iso1; auto.
Qed.

Lemma iso1_in_repb n  p1 P : sort (ltTuple') P ->
  rep n (tupleOrd J)  (value_eq_ok J) p1 P ==> rep n (tupleOrd J)  (value_eq_ok J) p1
  (conv (unconv P)).
intros.
apply rep_prop.
symmetry.
apply iso1; auto.
Qed.

(* these should be in Ynot *)
Global Instance himp_refl' : Reflexive hprop_imp.
red; apply himp_refl.
Qed.

Global Instance himp_trans' : Transitive hprop_imp.
red; intros; eapply himp_trans; eauto.
Qed.

Require Import Eqdep.
(* some facts about specLookup *)
Lemma spec_lookup_in k l :
  match specLookup (tupleOrd J)  (value_eq_ok J)  k l with
       | None => ~ In k (unconv l)
       | Some x => In k (unconv l)
     end.
Proof.
  induction l; simpl; intuition.
  elim (empty_1 H).
  destruct a; simpl.
  destruct (  @equiv_dec (Tuple J) (eqTupleSetoid J)
         (@OrderedTypeNM.ordEq_dec (Tuple J) (tupleOrd J)) x k).
  generalize (value_eq_ok J x k e).
  intros. rewrite (UIP_refl _ _ e0).
  auto. 

  destruct (specLookup (tupleOrd J) ( (value_eq_ok J)) k l); auto.
  intro. elim IHl. 
  eapply add_3; eauto.
Qed.

(* some facts about specInsert *)
Lemma insert_head_sorted x0 v x: lelistA (ltTuple') (existTS (value) x0 v) x ->
   (@specInsert (key) _ (tupleOrd J) x0 v x) = existTS _ x0 v :: x.
Proof.
  induction x; simpl; intuition.
  destruct a.
  inversion H; subst.
  unfold ltTuple' in *; simpl in *.
  destruct (compTuple (A:=J) x1 x0); intuition.
    rewrite H1 in l; elim (ltTuple_not_eq l); reflexivity.
    elim (ltTuple_not_eq H1); symmetry; auto.
Qed.

Lemma lelistA'_lt_insert x k v v0 l :
     ltTuple (A:=J) x k
  -> lelistA (ltTuple') (existTS (value) x v0) l
  -> lelistA (ltTuple') (existTS (value) x v0)
     (specInsert (tupleOrd J) k v l).
Proof.
  induction l; simpl; unfold ltTuple'; intuition.
  destruct a; simpl in *.
  destruct (compTuple (A:=J) x0 k); intuition.
  inversion H0; subst. simpl in *. auto.
Qed.

Lemma specInsert_sort l k v : sort (ltTuple') l -> 
  sort (ltTuple') (specInsert (tupleOrd J) k v l).
Proof.
  induction l; simpl; intuition.
  inversion H; subst. destruct a. simpl.
  destruct (compTuple (A:=J) x k); intuition; constructor; auto.
  eapply lelistA'_lt_insert; eauto.
  eapply lelistA'_eq; eauto.
Qed.

Lemma eqTuple'_dec : (forall x y : sigTS value, {eqTuple' x y} + {~ eqTuple' x y}).
Proof.
  unfold eqTuple'. destruct x; destruct y. simpl.
  destruct (compTuple x x0); intuition; right; intro LL;
  eelim ltTuple_not_eq; eauto. symmetry; eauto.
Qed.

Lemma specInsert_lelistA_inv l a k v :
     lelistA (ltTuple') a (specInsert (tupleOrd J) k v l)
  -> lelistA (ltTuple') a l.
Proof.
  induction l; simpl; intuition.
  destruct a; simpl in *.
  destruct (compTuple (A:=J) x k); simpl in *; intuition;
    inversion H; subst; unfold ltTuple' in *; simpl in *; constructor; simpl; auto.
    rewrite e; auto.
    rewrite <- l0; auto.
Qed.

Lemma specInsert_sort_inv l k v :
     sort (ltTuple') (specInsert (tupleOrd J) k v l)
  -> sort (ltTuple') l.
Proof.
  induction l; simpl; intuition.
  destruct a. simpl in *.
  destruct (compTuple (A:=J) x k); simpl in *; intuition.
  inversion H; subst. constructor. eapply IHl; eauto.
  eapply specInsert_lelistA_inv; eauto.
  inversion H; subst. constructor; auto.
  eapply lelistA'_eq; eauto. symmetry; auto.
  inversion H; auto.
Qed.

Lemma specInserted_in x v k v1 l : 
     eqTuple x k 
  -> InA (eqTuple') (existTS (value) x v) (specInsert (tupleOrd J) k v1 l).
Proof.
  induction l; simpl; intuition.
  destruct a; simpl in *.
  destruct (compTuple (A:=J) x0 k); simpl; intuition.
Qed.

Lemma specInsert_cons x k v l :
 InA (eqTuple') x (specInsert (tupleOrd J) k v l) ->
 InA (eqTuple') x (existTS (value) k v :: l).
Proof.
  induction l; simpl; intuition.
  destruct a; simpl in *.
  destruct (compTuple (A:=J) x0 k); simpl; intuition;
    inversion H; intuition. 
  subst. inversion H3; auto.
Qed.

Lemma spec_add_insert_equivl' k v l l' :
   forall x : sigTS (value),
    (InA (eqTuple') x l <-> InA (eqTuple') x l') ->
   (InA (eqTuple') x (specInsert (tupleOrd J) k v l) <->
   InA (eqTuple') x (conv (add k (unconv l')))).
Proof. Hint Resolve @add_3 @add_2 @union_2 @union_3.
  induction l; simpl; intuition.
  inversion H; subst; intuition.
      apply <- eqTuple'_ina; eapply elements_1'.
      simpl in *. apply add_1. symmetry. auto.

      inversion H0.
      unfold conv in H.
      pose ((proj1 (eqTuple'_ina  _ _)) H) as i.
      apply elements_2' in i.
      destruct ((projT1S x) == k).
        auto.
        apply add_3 in i; [|symmetry; auto].
        apply elements_1' in i.
        apply <- eqTuple'_ina  in i.
        rewrite iso1_equiv' in i.
        pose (H1 i) as ii. inversion ii.
        
      destruct a; simpl in *.
      destruct (compTuple (A:=J) x0 k).
        destruct ((projT1S x) == x0).
          apply <- eqTuple'_ina. simpl.
          apply elements_1'. apply add_2.
          apply elements_2'.
          apply -> eqTuple'_ina.
          rewrite iso1_equiv'.
          eapply H0;  auto.
          
          inversion H; subst.
            elim (c H3).
          
          eapply IHl; eauto.
          intuition.
            inversion H4; auto. subst.
            elim (c H5).
        apply <- eqTuple'_ina. apply elements_1'.
        apply add_2. apply elements_2'.
        apply -> eqTuple'_ina.
        rewrite iso1_equiv'. apply H0.
        inversion H; auto.
        subst. constructor. rewrite H3. unfold eqTuple'. simpl. symmetry. auto.

        destruct ((projT1S x) == x0).
          apply <- eqTuple'_ina. simpl.
          apply elements_1'. apply add_2.
          apply elements_2'.
          apply -> eqTuple'_ina.
          rewrite iso1_equiv'. eapply H0;  auto.
        destruct ((projT1S x) == k).
          eapply IHl; intuition.
            inversion H3; auto. subst. elim (c H4).
            destruct x; simpl in *.
            apply specInserted_in; auto.
          apply <- eqTuple'_ina. 
          apply elements_1'. apply add_2.
          apply elements_2'.
          apply -> eqTuple'_ina.
          rewrite iso1_equiv'. eapply H0;  auto.
          inversion H; subst; auto. elim (c0 H3).

  destruct a; simpl in *.
  destruct (compTuple (A:=J) x0 k).
    destruct (projT1S x == x0); auto.
     apply InA_cons_tl. eapply IHl; eauto.
     intuition. inversion H3; auto. subst. elim (c H4).

    cut (InA (eqTuple') x (specInsert (tupleOrd J) k v l)).
      intros. eapply specInsert_cons; eauto.
   
   destruct (k == projT1S x). destruct x. eapply specInserted_in. symmetry; auto.
   apply <- IHl; intuition.
   apply <- eqTuple'_ina. apply elements_1'.
   pose ((proj1 (eqTuple'_ina _ _) H)) as i.
   apply elements_2' in i.
     apply add_3 in i; [|auto]. apply add_2. simpl.  apply add_2.
     apply elements_1' in i.
     apply eqTuple'_ina in i.
     rewrite iso1_equiv'  in i. pose (H1 i) as ii.
     apply elements_2'. apply (proj1 (eqTuple'_ina _ _ )).
     rewrite iso1_equiv'.
     inversion ii; auto; subst.
       subst. elim c. rewrite <- e. symmetry. auto.
     inversion H2; auto. subst. unfold eqTuple' in H4.
     rewrite e in H4. symmetry in H4. elim (c H4).

     destruct (projT1S x == x0); auto.
     cut (InA (eqTuple') x (specInsert (tupleOrd J) k v l)).
       intros. apply specInsert_cons  in H2. inversion H2; auto.
     eapply IHl; eauto; intuition.
     inversion H3; auto. subst. elim (c H4).
Qed.

Lemma spec_add_insert_equivl k v l l' :
  equivlistA (eqTuple') l l'
  -> equivlistA (eqTuple')
    (specInsert (tupleOrd J) k v l)
    (conv (add k (unconv l'))).
Proof.
  unfold equivlistA. intros.
  apply spec_add_insert_equivl'; intuition;
  [apply -> H | apply  <- H]; auto.
Qed.

Lemma spec_add_insert_eq k v l l' : sort ltTuple' l ->
  equivlistA (eqTuple') l l'
  -> eqlistA (eqTuple')
    (specInsert (tupleOrd J) k v l)
    (conv (add k (unconv l'))).
Proof.
  unfold equivlistA. intros.
  apply sortlt_equivlistA_eqlistA; auto.
  apply specInsert_sort; auto.
  apply spec_add_insert_equivl; auto.
Qed.

Lemma spec_add_insert_eq' k v l l' : sort ltTuple' l ->
  equivlistA (eqTuple') l (conv l')
  -> eqlistA (eqTuple')
    (specInsert (tupleOrd J) k v l)
    (conv (add k l')).
Proof.
  unfold equivlistA. intros.
  transitivity (conv (add k (unconv (conv l')))).
  apply spec_add_insert_eq; auto.
  apply sortlt_equivlistA_eqlistA; auto.
  rewrite iso2. reflexivity.
Qed.

Lemma conv_el_proper_inv x y : eqTuple' (conv_el x) (conv_el y) -> eqTuple (A:=J) x y.
Proof.
  unfold conv_el, eqTuple'. intros x y H.
  simpl in H. auto.
Qed.

Lemma map_conv_el_proper_inv x y : eqlistA eqTuple' (map conv_el x) (map conv_el y) -> eqlistA (eqTuple (A:=J)) x y.
Proof.
  induction x as [|a x' IHx]; destruct y as [|b y']; simpl; inversion 1; subst; intuition.
Qed.

Lemma map_conv_proj l : eqlistA eqTuple' (map conv_el (map (@projT1S _ _) l)) l.
Proof.
  unfold conv_el. induction l; simpl; intuition.
  constructor; auto.
  red; simpl; reflexivity.
Qed.

Lemma map_proj_conv l : eqlistA (@eqTuple J) (map (@projT1S _ _) (map conv_el l)) l.
Proof.
  unfold conv_el. induction l; simpl; intuition.
Qed.

Lemma spec_add_insert_eq'' k v l l' : sort ltTuple' l ->
  equivlistA (eqTuple') l (conv l')
  -> eqlistA (@eqTuple J)
    (map (@projT1S _ _) (specInsert (tupleOrd J) k v l))
    (elements (add k l')).
Proof.
  intros. eapply map_conv_el_proper_inv.
  rewrite map_conv_proj.
  rewrite spec_add_insert_eq'; eauto.
  reflexivity.
Qed.

Lemma add_same (I : Typing) k l : add k (add k l) == add (FSetInterfaceNM:=(F I)) k l.
Proof. 
  intros. rewrite equivIsEqual.
  split; intros; (destruct (k == a); [apply add_1; auto|eapply add_3; eauto]).
Qed.

Lemma add_assoc (I : Typing) k1 k2 l : add k1 (add k2 l) == add (FSetInterfaceNM:=(F I)) k2 (add k1 l).
Proof.
  intros. rewrite equivIsEqual. split; intros.
  destruct (k2 == a); [auto|].
  destruct (k1 == a); [auto|].
  apply add_3 in H; [|auto]. apply add_3 in H; auto.

  destruct (k1 == a); [auto|].
  destruct (k2 == a); [auto|].
  apply add_3 in H; [|auto]. apply add_3 in H; auto.
Qed.

(* TODO: clean up this proof.  In particular, there are some lemmas that should be factored out *)
Lemma mapASet_add (I : Typing) f (k0 : Tuple J) (l : t) : Proper (equiv ==> equiv) f ->
   (mapASet (A':=F J) (F I) f (add k0 l)) ==
   (add (f k0) (mapASet (A':=F J) (F I) f l)).
Proof.
intros.  unfold mapASet.
repeat rewrite fold_1.
rewrite fold_left_add_equiv; auto.
2: symmetry; apply spec_add_insert_eq''; try reflexivity; auto.
instantiate (1:=tt).
unfold conv.
pose (elements_3 l).
set (l' := elements l) in *.
set (e:=@empty (Tuple I) (tupleOrd I) (F I)).
clearbody s; clearbody l'; clearbody e; clear l.
revert e.
induction l'; simpl; intuition.
inversion s; subst.
destruct (compTuple (A:=J) a k0); simpl in *; auto.
rewrite fold_left_add_equiv; auto.
2: apply map_proj_conv. clear IHl'. revert e.
induction l'; simpl; intuition.
rewrite e0. symmetry.  apply add_same.
transitivity (fold_left (fun (a1 : t) (e1 : Tuple J) => add (f e1) a1) l' (add (f k0) (add (f a0) e))).
 eapply foldl_compat with (eqB:=(@eqTuple J)); intuition.
 unfold respectful; intros; apply add_push; auto. rewrite H1. reflexivity.
 apply add_assoc.
 rewrite IHl'; auto.
 apply add_push; intuition.
 eapply foldl_compat with (eqB:=(@eqTuple J)); intuition.
 unfold respectful; intros; apply add_push; auto. rewrite H1. reflexivity.
 apply add_assoc.
 inversion H2; subst.
 constructor; auto.
 inversion H5; subst; constructor.
 inversion H3; subst. inversion H5; subst.
 transitivity a0; auto.
 
 inversion s. inversion H4. auto.

 inversion H3; inversion H2; inversion H8; subst; constructor.
 transitivity a0; auto.

 rewrite fold_left_add_equiv; auto.
 2: apply map_proj_conv.
 rewrite <- IHl'; auto.
 rewrite insert_head_sorted.
 simpl.
 setoid_rewrite fold_left_add_equiv at 2; auto; [| apply map_proj_conv].
 apply foldl_compat with (eqB := (@eqTuple J)); intuition.
 unfold respectful; intros; apply add_push; auto. rewrite H4. reflexivity.
 apply add_assoc.

 inversion H3; subst; constructor.
 unfold ltTuple'. simpl. transitivity a; auto.
Qed.

Instance fuseTuples_prop I k : Proper (equiv ==> equiv) (fuseTuples (I:=I) (J:=J) k).
Proof.
  unfold Proper, respectful. intros.
  induction I; simpl; intuition; destruct k; simpl.
    reflexivity.
    apply IHI.
Qed.

Lemma prod1_add I k k0 l: 
  (prod1 (F:=F) (I:=I) (J:=J) k (add k0 l)) == add (fuseTuples k k0) (prod1 k l).
Proof.
  unfold prod1. intros.
  apply mapASet_add.
  apply fuseTuples_prop.
Qed.

(*(* some facts about specDelete *)
Lemma specDelete_in k l k' : (InA eqTuple' k' l /\ k =/= (projT1S k')) <-> InA eqTuple' k' (specDelete (tupleOrd J) l k).
Proof.
  induction l as [| a l IHl]; simpl; split; try solve[intuition]; intro H.
  inversion H.
  destruct a; simpl. intuition.
  inversion H0; destruct (compTuple (A:=J) x k); subst; intuition.
  red in H2; simpl in H2. elim H1. rewrite H2. symmetry; auto.
  right. apply -> IHl. auto.
  right. apply -> IHl. auto.
  destruct a; simpl in *.
  destruct (compTuple (A:=J) x k); subst; auto.
  inversion H; subst; intuition.
   intro. elim (ltTuple_not_eq l0). rewrite H0. symmetry. auto. 
   right; apply <- IHl; auto.
   apply <- IHl; auto.
  intuition.
   intro. rewrite H0 in e.
  inversion H; subst; intuition.
   intro. elim (ltTuple_not_eq l0). rewrite H0. symmetry. auto. 
   right; apply <- IHl; auto.
   apply <- IHl; auto.


  inversion H; subst; intuition.
  right. apply <- IHl; auto.
  
  

Instance specDelete_equiv : Proper (equivlistA eqTuple' ==> eq ==> equivlistA eqTuple') (specDelete (tupleOrd J)).
Proof.
  unfold Proper, respectful. intros. subst. revert H.


  equivlistA (eqTuple') l l'
  -> equivlistA (eqTuple')
    (specDelete (tupleOrd J) l k)
    (conv (remove k (unconv l'))).

Lemma spec_delete_remove k l l' :
  equivlistA (eqTuple') l l'
  -> equivlistA (eqTuple')
    (specDelete (tupleOrd J) l k)
    (conv (remove k (unconv l'))).
Proof.
  unfold equivlistA. intros.
  
  apply spec_add_insert_equivl'; intuition;
  [apply -> H | apply  <- H]; auto.
Qed.
*)

(* specUnion and its relation to union *)

Definition specUnion : Model (value) ->
  Model (value) -> Model (value) := 
  @fold_right (Model (value)) (sigTS (value))
  (fun x y => @specInsert (key) (value)
                (tupleOrd J) (projT1S x) (projT2S x) y).


Lemma union_nil x :  @sort _ (ltTuple') x -> eqlistA (eqTuple') x (specUnion nil x).
Proof.
  induction x; simpl; intuition.
  destruct a. inversion H; subst. simpl in *.
  rewrite insert_head_sorted.
  constructor; auto. 
  unfold eqTuple'. reflexivity.
  rewrite <- IHx; auto.
Qed.

Lemma unconv_union_conv x : 
  x == unconv (specUnion nil (conv x)).
Proof.
  intros. 
  rewrite <- union_nil, iso2; intuition.
Qed.

Lemma specInsert_cons_in x k v l :
 List.In  x (specInsert (tupleOrd J) k v l) ->
 List.In  x (existTS (value) k v :: l).
Proof.
  induction l; simpl; intuition.
  destruct a; simpl in *.
  destruct (compTuple (A:=J) x0 k); simpl; intuition;
    inversion H; intuition. 
Qed.

(*
Lemma specInsert_nodup l k v : NoDupA eqTuple' l -> 
  NoDupA eqTuple' (@specInsert key value (tupleOrd J) k v l).
Proof. Hint Constructors NoDupA.
  induction l; simpl; intuition. constructor; intuition. inversion H0.
  inversion H; subst. destruct a. simpl.
  destruct (compTuple (A:=J) x k); intuition; constructor; auto;
  intro inn.
    pose (specInsert_cons _ _ _ _ inn). inversion i. subst.
      elim (ltTuple_not_eq l0); auto.
      elim H2; auto.
    elim H2. assert (e2:eqTuple' (existTS value x v0) (existTS value k v)) by auto.
    rewrite e2. auto.
    pose (IHl k v H3).
    

    pose (specInsert_cons _ _ _ _ inn). inversion i. subst.
      elim (ltTuple_not_eq l0); auto.
      elim H2; auto.
    elim H2. assert (e2:eqTuple' (existTS value x v0) (existTS value k v)) by auto.

    unfold value in v, v0. destruct v; destruct v0. 
  eapply lelistA'_lt_insert; eauto.


Lemma specInsert_nodup l k v : NoDup l -> 
  NoDup (@specInsert key value (tupleOrd J) k v l).
Proof. Hint Constructors NoDup.
  induction l; simpl; intuition.
  inversion H; subst. destruct a. simpl.
  destruct (compTuple (A:=J) x k); intuition; constructor; auto;
  intro inn.
    pose (specInsert_cons_in _ _ _ _ inn). inversion i.
      inversion H0. subst x. elim (ltTuple_not_eq l0); reflexivity.
      elim H2; auto.
    elim H2.
    unfold value in v, v0. destruct v; destruct v0. 
  eapply lelistA'_lt_insert; eauto.
  eapply lelistA'_eq; eauto.
Qed.
*)

Lemma specUnion_sort l1 l2 :
  sort (ltTuple') l1 -> sort (ltTuple') (specUnion l1 l2).
Proof.
  induction l2; simpl; intuition.
  eapply specInsert_sort; auto.
Qed.

Lemma union_add1 a x x0 :
  (union x0 (add (FSetInterfaceNM:=(F J)) a x)) ==  (add (FSetInterfaceNM:=(F J)) a (union x0 x)).
Proof. Hint Resolve @add_3 @add_2 @union_2 @union_3.
  intros.
  rewrite equivIsEqual. split; intros H.
  apply union_1 in H. destruct H as [H|H]; auto.
    destruct (a == a0); [auto|].
    eapply add_3 in H; eauto.

    destruct (a == a0).
      auto.
      eapply add_3 in H; [|auto].
      eapply union_1 in H. destruct H; auto.
Qed.

Lemma spec_union_union' x x0: sort (ltTuple') (specUnion x0 x) -> eqlistA (eqTuple')
  (specUnion x0 x) (conv (union (unconv x0) (unconv x))).
Proof.
  intros. simpl. eapply sortlt_equivlistA_eqlistA; eauto.
  rename H into s.
  revert x0 s.
  induction x; simpl.
    induction x0; simpl;
      split; intros.
        inversion H.
        unfold conv in H. apply eqTuple'_ina in H.
        pose (elements_2 H) as ii.
        destruct (union_1 ii) as [HH|HH]; elim (empty_1 HH).
        
        apply <- eqTuple'_ina.
        apply (@elements_1 _ _ (F J)).
        apply union_2.
          inversion H; subst.
            apply add_1. symmetry. auto.
            apply add_2.
            inversion s.
            pose ((proj1 (IHx0 H3 _)) H1) as i.
            apply (eqTuple'_ina x) in i.
            pose (elements_2 i) as i'.
            destruct (union_1 i'); auto.
            elim (empty_1 H5).

        unfold conv in H.
        apply eqTuple'_ina in H.
        pose (elements_2 H) as i.
        apply union_1 in i. destruct i.
        destruct ((projT1S a) == (projT1S x)).
          left; symmetry in e; auto.
          apply add_3 in H0; auto.
          right. apply elements_1 in H0.
          simpl in H0. apply <- eqTuple'_ina in H0.
          pose (iso1 x0) as is. unfold conv in is.
          inversion s.
          rewrite is in H0; auto.

    elim (empty_1 H0).
    intros.
    rewrite union_add1.
    pose (specInsert_sort_inv _ _ _ s) as s'.
    rewrite (spec_add_insert_equivl _ (projT2S a)); [|apply IHx; auto].
    rewrite iso2. reflexivity.
Qed.

Lemma spec_union_union x0 x: (unconv (specUnion (conv x0) (conv x))) == (union x0 x).
Proof.
intros.
rewrite (spec_union_union' (conv x) (conv x0)).
rewrite iso2.
apply union_push; apply iso2.
apply specUnion_sort; unfold conv; apply conv_el_sort;
eapply elements_3.
Qed.

Definition unionm R l := (specUnion (conv R) l).

Lemma unionm_sorted x x0 : sort (@ltTuple') (unionm x x0).
Proof.
  induction x0; simpl; intuition.
  apply specInsert_sort; auto.
Qed.

End specs.

Lemma conv_prodRel_emptyl_nil F I J x0 : conv F _ (prodRel (F:=F) (I:=I) (J:=J) (empty0 F I) x0) = nil.
Proof.
  unfold conv, conv_el. intros.
  rewrite prodRel_emptyl_elements_nil. simpl. trivial.
Qed.

Lemma prod1_empty F I J k : (prod1 (F:=F) (I:=I) (J:=J) k (empty0 F J)) == empty0 F (I ++ J).
Proof.
  intros. unfold prod1, mapASet, empty0. rewrite fold_1, empty_elements_nil. reflexivity.
Qed.

Lemma inter_emptyl_empty F J x0 : (inter (empty0 F J) x0) == empty0 F J.
Proof.
  intros. rewrite equivIsEqual. split; intros.
    apply inter_1 in H; auto.
    elim (empty_1 H).
Qed.

Lemma inter_emptyl_elements_nil F J x0 : (elements (inter (empty0 F J) x0)) = nil.
Proof.
  intros.
  apply eqlistA_nil with (R:=@eqTuple J).
  rewrite <- (@empty_elements_nil F J).
  rewrite inter_emptyl_empty. reflexivity.
Qed.

Lemma conv_inter_emptyl F J x0 : (conv F J (inter (empty0 F J) x0)) = nil.
Proof.
  intros. unfold conv. rewrite inter_emptyl_elements_nil. reflexivity.
Qed.


Lemma diff_emptyl_empty F J x0 : (diff (empty0 F J) x0) == empty0 F J.
Proof.
  intros. rewrite equivIsEqual. split; intros.
    apply diff_1 in H; auto.
    elim (empty_1 H).
Qed.

Lemma diff_emptyl_elements_nil F J x0 : (elements (diff (empty0 F J) x0)) = nil.
Proof.
  intros.
  apply eqlistA_nil with (R:=@eqTuple J).
  rewrite <- (@empty_elements_nil F J).
  rewrite diff_emptyl_empty. reflexivity.
Qed.

Lemma conv_diff_emptyl F J x0 : (conv F J (diff (empty0 F J) x0)) = nil.
Proof.
  intros. unfold conv. rewrite diff_emptyl_elements_nil. reflexivity.
Qed.

Lemma fold_left_up1_equiv (F:forall x, DBSet x) I J x1 l l' s : 
  eqlistA (@eqTuple _) l l' ->
  (fold_left (fun (a : DBRel (A:=I ++ J) (F (I ++ J))) (e : Tuple I) =>
      union a (prod1 (F:=F) (I:=I) (J:=J) e x1))
  l s)
  == 
  (fold_left (fun (a : DBRel (A:=I ++ J) (F (I ++ J))) 
    (e : Tuple I) => union a (prod1 (F:=F) (I:=I) (J:=J) e x1))
  l' s).
Proof.
  intros.
  apply foldl_compat with (eqB:=@eqTuple _); intuition.
  unfold respectful. intros.
  apply union_push; auto.
  apply prod1_push; auto. reflexivity.
Qed.

Lemma union_assoc (F:forall x, DBSet x) (J:Typing) a b c 
  : union (FSetInterfaceNM:=(F J)) (union a b) c == union a (union b c).
Proof.
  Hint Resolve @union_2 @union_3.
  intros. rewrite equivIsEqual. split; intros; apply union_1 in H.
  destruct H; [apply union_1 in H; destruct H|]; auto.
  destruct H; [|apply union_1 in H; destruct H]; auto.
Qed.

Lemma union_comm (F:forall x, DBSet x) (J:Typing) a b :
  union (FSetInterfaceNM:=(F J)) a b == union (FSetInterfaceNM:=(F J)) b a.
Proof.
  intros. rewrite equivIsEqual. split; intros; 
  apply union_1 in H; destruct H; auto.
Qed.

Lemma union_same (F:forall x, DBSet x) (J:Typing) a b :
  a == b -> union (FSetInterfaceNM:=(F J)) a b == a.
Proof.
  intros. rewrite equivIsEqual. split; intros.
  apply union_1 in H0. destruct H0; auto.
  rewrite equivIsEqual in H. apply <- (H a0). auto.
  apply union_2; auto.
Qed.

(* TODO: clean up.  refactor.  also note similarity with mapASet_add *)
Lemma prodRel_add F I J k l x1 :
  prodRel (F:=F) (I:=I) (J:=J) (add k l) x1 == 
  union (prodRel (F:=F) (I:=I) (J:=J) l x1)
  (prod1 (F:=F) (I:=I) (J:=J) k x1).
Proof.
  Hint Resolve conv_sort.
  intros. unfold prodRel.
  repeat rewrite fold_1. unfold RelationalModel.union.
  
  rewrite fold_left_up1_equiv.

  2: symmetry; apply spec_add_insert_eq''; try reflexivity; auto.
  instantiate (1:=tt).
  unfold conv.
  pose (elements_3 l).
  set (l' := elements l) in *.
  set (e:=empty0 F (I ++ J)).
  clearbody s; clearbody l'; clearbody e; clear l.
  revert e.
  induction l'; simpl; intuition.
  inversion s; subst. specialize (IHl' H1).
  destruct (compTuple a k); simpl in *; auto.

  rewrite fold_left_up1_equiv.
  2: apply map_proj_conv.
  transitivity( union
     (fold_left
        (fun (a0 : DBRel (A:=I ++ J) (F (I ++ J))) (e1 : Tuple I) =>
         union a0 (prod1 (F:=F) (I:=I) (J:=J) e1 x1)) l'
        (union e (prod1 (F:=F) (I:=I) (J:=J) k x1)))
     (prod1 (F:=F) (I:=I) (J:=J) k x1)).
  Focus 2.
  apply union_push; intuition.
  eapply foldl_compat with (eqB:=(@eqTuple _)); intuition.
  unfold respectful; intros. apply union_push; intuition. apply prod1_push; intuition.
  apply union_push; intuition. apply prod1_push; intuition.
  set ((prod1 (F:=F) (I:=I) (J:=J) k x1)).
  clear. revert e. induction l'; simpl; intuition.
    rewrite union_assoc. apply union_push; intuition. symmetry; apply union_same; intuition.
    transitivity (fold_left
     (fun (a0 : DBRel (A:=I ++ J) (F (I ++ J))) (e0 : Tuple I) =>
      union a0 (prod1 (F:=F) (I:=I) (J:=J) e0 x1)) l'
     (union (union e (prod1 (F:=F) (I:=I) (J:=J) a x1)) d)).
 eapply foldl_compat with (eqB:=(@eqTuple _)); intuition.
  unfold respectful; intros. apply union_push; intuition. apply prod1_push; intuition.
  rewrite union_assoc. rewrite union_comm. rewrite union_assoc. rewrite union_comm.
  apply union_push; intuition. rewrite union_comm. reflexivity.
  rewrite IHl'. apply union_push; intuition.
 eapply foldl_compat with (eqB:=(@eqTuple _)); intuition.
  unfold respectful; intros. apply union_push; intuition. apply prod1_push; intuition.
  rewrite union_assoc. rewrite union_comm. rewrite union_assoc. rewrite union_comm.
  apply union_push; intuition. rewrite union_comm. reflexivity.

 rewrite fold_left_up1_equiv.
 2: apply map_proj_conv.
 rewrite <- IHl'; auto.
 rewrite (@insert_head_sorted I).
 simpl.
 2:
 inversion H2; subst; constructor;
 unfold ltTuple'; simpl; transitivity a; auto.

 apply foldl_compat with (eqB := (@eqTuple _)); intuition.
  unfold respectful; intros. apply union_push; intuition. apply prod1_push; intuition.
  symmetry. apply map_proj_conv.

  repeat rewrite union_assoc.
  apply union_push; intuition. 
  apply union_comm.
Qed.

 Global Instance eqlistA_app {A} (R:relation A) : Proper (eqlistA R ==> eqlistA R ==> eqlistA R) (@app A).
 Proof. pintro; induction 1; simpl; intuition. Qed.

 Global Instance eqlistA_rev {A} (R:relation A) : Proper (eqlistA R ==> eqlistA R) (@rev A).
 Proof. pintro; induction 1; simpl; intuition.  apply eqlistA_app; intuition. Qed.

 Global Instance ltTuple'_entryEq J : Proper (entry_eq (tupleOrd J)  (value_eq_ok J) ==> entry_eq (tupleOrd J)  (value_eq_ok J) ==> iff) (ltTuple' J).
 intros. pintro.
 unfold ltTuple', entry_eq. destruct x; destruct y; destruct x1; destruct y; simpl in *.
  repeat match goal with
    | [|- context [key_eq_dec ?R ?P1 ?P2]] => destruct (key_eq_dec R P1 P2)
    | [H: context [key_eq_dec ?R ?P1 ?P2] |- _] => destruct (key_eq_dec R P1 P2)
  end; simpl in *; intuition.
  toEquiv. clsubst*. auto.
 Qed.

 Global Instance eqli_lelistA J : Proper (entry_eq (tupleOrd J)  (value_eq_ok J) ==> eqlistA (entry_eq (tupleOrd J)  (value_eq_ok J) ) ==> iff) (lelistA (ltTuple' J)).
 Proof. pintro. 
   induction x0; inversion 1; simpl; subst; intuition.
   inversion H1; subst. constructor. rewrite <- H, <- H3. auto.
 Qed.

 Global Instance eqli_sort J : Proper (eqlistA (entry_eq (tupleOrd J)  (value_eq_ok J)) ==> iff) (sort (ltTuple' J) ).
 Proof. pintro.
   induction x; inversion 1; subst; intuition.
   inversion H0; subst.
   constructor; auto. rewrite <- H4, <- H2. auto.
 Qed.

 (* how is this not in the standard library? *)
 Lemma NoDup_perm' {A} (l1 l2:list A) : Permutation l1 l2 -> NoDup l1 -> NoDup l2.
 Proof. intros A.
   set (P:=fun (l1 l2:list A) => NoDup l1 -> NoDup l2).
   cut (forall l l', Permutation l l' -> P l l').
   intros. eapply H; eauto.
   intros; apply (Permutation_ind_bis P); unfold P; clear P; try clear H l l'; simpl; auto; intros.
(* skip *)
  inversion H1. constructor; auto. intro In. elim H4. eapply Permutation_in; eauto. eapply Permutation_sym; auto.
(* swap *)
  inversion H1. inversion H5. subst. constructor; auto. intro inn. 
  inversion inn; subst. 
    apply H4; intuition. 
    apply H8.  eapply Permutation_in; eauto. eapply Permutation_sym; auto.
  constructor; auto. intro inn. apply H4. right. eapply Permutation_in; eauto. eapply Permutation_sym; auto.
 Qed.

 Global Instance NoDup_perm {A} : Proper (@Permutation A ==> iff) (@NoDup A).
 Proof. unp; split; apply NoDup_perm'; auto. apply Permutation_sym. auto. Qed.


 Global Instance Permutation_inA (A : Type) R (x : A) : Proper (@Permutation A ==> iff) (InA R x).
 Proof. pintro. 
   set (fun l l' => InA R x l -> InA R x l').
   eapply (Permutation_ind_bis P); unfold P; clear P; simpl; auto; intuition.
   inversion H1; subst; intuition.
   inversion H1; intuition. inversion H3; intuition.
 Qed.

 (* how is this not in the standard library? *)
 Lemma NoDupA_perm' {A} R {s:Symmetric R} (l1 l2:list A) : Permutation l1 l2 -> NoDupA R l1 -> NoDupA R l2.
 Proof. intros A R s.
   set (P:=fun (l1 l2:list A) => NoDupA R l1 -> NoDupA R l2).
   cut (forall l l', Permutation l l' -> P l l').
   intros. eapply H; eauto.
   intros; apply (Permutation_ind_bis P); unfold P; clear P; try clear H l l'; simpl; auto; intros.
(* skip *)
  inversion H1. constructor; auto. intro In. subst. elim H4. eapply Permutation_inA; eauto.
(* swap *)
  inversion H1. inversion H5. subst. constructor; auto. intro inn. 
  inversion inn; subst. 
    apply H4; intuition. 
    apply H8.  eapply Permutation_inA; eauto.
  constructor; auto. intro inn. apply H4. right. eapply Permutation_inA; eauto.
 Qed.

 Global Instance NoDupA_perm {A} R {s:Symmetric R} : Proper (@Permutation A ==> iff) (NoDupA R).
 Proof. unp; split; apply NoDupA_perm'; auto. symmetry; auto. Qed.
   
 Lemma unconv_perm F J v1 v2 : NoDup v1 -> Permutation v1 v2 -> unconv F J v1 == unconv F J v2.
 Proof.
   unfold DBRel. intros F J.
   set (P:=fun v1 v2 => NoDup v1 -> unconv F J v1 == unconv F J v2).
   cut (forall l l', Permutation l l' -> P l l').
   intros. eapply H; eauto.
   intros; apply (Permutation_ind_bis P); unfold P; clear P; try clear H l l'; simpl; auto; intros.
   (* nil *)
   reflexivity.
   (* skip *)
   inversion H1. rewrite H0; intuition.
   (* swap *)
   inversion H1. inversion H5. rewrite add_assoc. rewrite H0; intuition.
   (* trans *)
   rewrite H0, H2; intuition. rewrite <- H. auto.
 Qed.

 Lemma sort_skip {A} (R:relation A) {t:Transitive R} a b l: sort R (a::b::l) -> sort R (a::l).
 Proof.
   inversion 2; inversion H2; subst. constructor; auto.
   inversion H7; auto; inversion H3; auto; subst.
   constructor. transitivity b; auto.
 Qed.

 Global Instance ltTuple'_trans J : Transitive (ltTuple' J).
 Proof. unfold ltTuple'; red; intros. rewrite H. auto. Qed.

 Lemma sort_nin J a l : sort (ltTuple' J) (a::l) -> ~ List.In a l.
 Proof.
   induction l; simpl; intuition; subst.
     inversion H. inversion H3. elim (ltTuple_not_eq H5); reflexivity.
     apply IHl; auto.
     eapply sort_skip; eauto. typeclasses eauto.
 Qed.
     
 Lemma sort_nodup J l : (sort (ltTuple' J)) l -> NoDup l.
 Proof.
   induction l; simpl; intuition.
     constructor.
   inversion H. constructor; auto.
   subst. apply sort_nin; auto.
 Qed.

 Lemma sort_ninA J l a: sort (ltTuple' J) (a::l) -> ~ InA (eqTuple' J) a l.
 Proof.
   induction l; simpl; intuition; subst.
     inversion H0. 
     inversion H; inversion H0; subst.
     inversion H4. elim (ltTuple_not_eq H2); auto.
     apply (IHl a0); auto.
     eapply sort_skip; eauto. typeclasses eauto.
 Qed.

 Lemma sort_nodupA J l : (sort (ltTuple' J)) l -> NoDupA (eqTuple' J) l.
 Proof.
   induction l; simpl; intuition.
   inversion H. subst. constructor; auto.
   apply sort_ninA; auto.
 Qed.

 Lemma eqc_unconvrev F J v0 x0 : eqlistA (entry_eq (tupleOrd J)  (value_eq_ok J)) (conv F J x0) v0
   ->  unconv F J (rev v0) == unconv F J v0.
 Proof.
   intros. assert (p:Permutation (rev v0) v0) by (apply Permutation_sym; apply Permutation_rev).
   apply unconv_perm; auto. 
   eapply NoDup_perm; eauto. 
   apply sort_nodup. eapply eqli_sort.
     symmetry; eauto.
     auto.
 Qed.
 
 Lemma equncrev F J v0 x0 : eqlistA (entry_eq (tupleOrd J) (value_eq_ok J)) (conv F J x0) v0
   ->  unconv F J (rev v0) == x0.
 Proof.
   intros. rewrite eqc_unconvrev; [|eauto].
   setoid_rewrite <- iso2 at 2.
   apply unconv_prop. symmetry. apply <- eqTuple'_entry_eq_list. auto.
 Qed.

Hint Resolve specUnion_sort.

Lemma equncspunrev F J x x0 v0 : eqlistA (entry_eq (tupleOrd J) (value_eq_ok J)) (conv F J x) v0
   -> unconv F J (specUnion J (conv F J x0) (rev v0)) ==
      unconv F J (specUnion J (conv F J x0) (conv F J x)).
Proof.
  intros.
  pose (equncrev _ _ _ _ H) as e.
  apply unconv_prop.
  apply sortlt_equivlistA_eqlistA; auto.
  repeat rewrite (spec_union_union' F); eauto.
  apply conv_prop_equiv.
  repeat rewrite iso2. rewrite e.
  reflexivity.
Qed.

(*
Lemma specInsert_perm J k v (l1 l2:Model (value J)) : sort (@ltTuple' _) l1 -> Permutation l1 l2 ->
  Permutation (specInsert (value:=value J) (tupleOrd J) k v l1) (specInsert (value:=value J) (tupleOrd J) k v l2).
Proof. intros J k v. Hint Constructors Permutation.
   set (P:=fun (l1 l2:list _) => sort (ltTuple' _) l1 -> NoDupA (eqTuple' _) l2 -> Permutation (specInsert (tupleOrd J) k v l1) (specInsert (tupleOrd J) k v l2)).
   cut (forall l l', Permutation l l' -> P l l').
   intros; eapply H; eauto. eapply NoDupA_perm. typeclasses eauto. symmetry; eauto. apply sort_nodupA; auto.
   intros; apply (Permutation_ind_bis P); unfold P; clear P; try clear H l l'; simpl; auto; intros; inversion H1; subst.
(* skip *)
   inversion H2.
   destruct x; simpl. destruct (compTuple x k); auto.
(* swap *)
   Ltac sk := apply perm_skip. Ltac sw := (eapply perm_trans; [apply perm_swap | auto]).
   inversion H5; inversion H2. inversion H12; subst.
   destruct x; destruct y; simpl. destruct (compTuple x0 k); destruct (compTuple x k); auto;
   try solve [try sk; try sw]. sw. sk. sw.
   inversion H6; subst. unfold ltTuple' in *; simpl in *. eelim ltTuple_not_eq; eauto. rewrite e0; auto.
   
*) 
   

Require Import RAInterface.

Module Type BTreeParams.
  Parameter SIZE : nat.
  Parameter Mk_Set : forall (I: Typing), DBSet I.
  Parameter BPT : forall (J:Typing), bpt_map SIZE (value J) (tupleOrd J)  (value_eq_ok J).
End BTreeParams.

Module BTreeImpl (PARAMS:BTreeParams): RAInterface.
 Import PARAMS.

 Definition F := Mk_Set.

 Definition u : Typing -> Set := fun I => BptMap.

 Definition rep' {J: Typing} : u J -> DBRel (F J) -> hprop
  := fun p r => (@rep SIZE (key J) (value J) (tupleOrd J)  (value_eq_ok J) p (conv F J r)).

Local Open Scope hprop_scope.
Local Open Scope stsepi_scope.

Instance In_1p (J:Typing) : Proper (equiv ==> equiv ==> iff) (@In _ _ (F J)).
intros.
cut (forall a x y, equiv x y -> @In _ _ (F J) a x -> In a y).
unfold Proper, respectful; intros.
intuition; eapply In_1.
eauto.
eapply H; eauto.
symmetry; eauto.
eapply H. symmetry; eauto.
eauto.

intros.
rewrite equivIsEqual in H.
eapply H. auto.
Qed.

Definition iter_fn_type J T (I:T->Model (value J)->hprop) (tm:[Model (value J)]) := 
  forall k v acc lm, 
    STsep (lm ~~ I acc lm)
    (fun a:T => lm ~~ I a (lm ++ existTS _ k v :: nil)).

 Definition impNewEmpty : forall J,
   STsep (__)
         (fun r: u J => rep' r (empty0 F J)).
 Proof.
 intros.
 refine {{@bpt_new _ _ _ _  (value_eq_ok J) (BPT J)}};
   unfold rep'; try rewrite conv_empty_nil; sep fail auto.
 Qed.

 Definition impFree : forall J (R: [DBRel (F J)]) p,
   STsep (R ~~ rep' p R )
         (fun _: unit => __).
 Proof. intros.
   refine {{@bpt_free _ _ _ _  (value_eq_ok J) (BPT J) p (R ~~~ conv F J R)}};
     unfold rep'; sep fail auto.
 Qed.

 Definition selectI J f : u J ->Model (value J) -> hprop 
   := (fun a l => rep' a (select (I:=J) f (unconv F J (rev l)))).

 (* really, select should let c have some scratch space, but this is sufficient for now *)
(* Definition select_insert J f tm : Proper (equiv ==> equiv) f -> 
   forall (P:hprop)
  (c:forall k:key J, STsep P (fun r => [r = f k] * P)),
   iter_fn_type J (u J) (fun a l => P * (selectI J f) a l) tm.
   *)

 Definition select_insert J f tm : Proper (equiv ==> equiv) f -> 
  forall (c:forall k:key J, STsep __ (fun r => [r = f k])),
   iter_fn_type J (u J) (selectI J f) tm.
 Proof.
   unfold iter_fn_type.
   intros.
   refine (
       b <- c k <@> _
     ; if bool_dec b true
       then x <- bpt_insert (BPT J) acc k v (lm ~~~ (conv F J (select (I:=J) f (unconv F J (rev lm))))) <@> ([f k = true])
          ; {{Return acc}}
       else {{Return acc}})
   ; unfold selectI, rep'; sep fail auto.

  apply rep_prop.
  apply sortlt_equivlistA_eqlistA; auto. apply specInsert_sort; auto.
  rewrite distr_rev. simpl.
  
  rewrite select_true; auto.
  setoid_rewrite <- iso2 at 3.
  apply spec_add_insert_equivl.
  reflexivity.
   
  apply rep_prop.
  apply sortlt_equivlistA_eqlistA; auto.
  rewrite distr_rev. simpl.
  rewrite select_false; auto. reflexivity.
 Qed.


 Definition impSelect_comp : forall J f, Proper (equiv ==> equiv) f -> forall (R1: [DBRel (F J)])
    (p1: u J), 
    forall (c:forall k:key J, STsep __ (fun r => [r = f k])),
      STsep (R1 ~~ rep' p1 R1)
    (fun r: u J => R1 ~~ rep' p1 R1 * rep' r (select f R1)).
 intros. 
 refine (x <- impNewEmpty J <@> _
       ; {{ (@bpt_orderedIterate _ _ _ _  (value_eq_ok J) (BPT J) (u J) p1
         (selectI J f))
         (R1 ~~~ conv F J R1)
         (select_insert J f (R1 ~~~ conv F J R1) H c)
         x
         }}); unfold selectI, rep'; sep fail auto.

 apply rep_prop.
 rewrite conv_empty_nil, conv_select_empty_nil; auto.
 apply rep_conv_prop.
 apply select_push; auto.
 apply equncrev; auto.
Qed.

 Definition impSelect : forall J f, Proper (equiv ==> equiv) f -> forall (R1: [DBRel (F J)])
    (p1: u J), STsep (R1 ~~ rep' p1 R1)
    (fun r: u J => R1 ~~ rep' p1 R1 * rep' r (select f R1)).
 intros. 
 refine {{impSelect_comp J f H R1 p1 (fun k => SepReturn (f k))}}; sep fail auto.
 Qed.

Definition unionI J R1 p1 : unit ->Model (value J) -> hprop 
  := (fun a l => R1 ~~ rep' p1 (unconv F J (unionm F J R1 (rev l)))).

Definition union_insert J R1 p1 tm : iter_fn_type J unit (unionI J R1 p1) tm.
Proof.
  Hint Resolve unionm_sorted.
  unfold iter_fn_type.
intros.
refine (x <- bpt_insert (BPT J) p1 k v (R1 ~~~' lm ~~~ unionm F J R1 (rev lm))
  ; {{Return tt}}); unfold unionI, rep'; sep fail auto.

apply iso1_in_repf; auto.
rewrite distr_rev. simpl.
eapply himp_trans; [|apply iso1_in_repb].
sep fail auto.
apply specInsert_sort; auto.
Qed.


Definition impUnion : forall J (R1 R2: [DBRel (F J)])
  (p1 p2: u J), STsep (R1 ~~ R2 ~~ rep' p1 R1 * rep' p2 R2)
  (fun _:unit => R1 ~~ R2 ~~ rep' p1 (union R1 R2) * rep' p2 R2 ).
Proof.
  intros. Hint Resolve unconv_union_conv spec_union_union conv_sort.
  
  refine ({{@bpt_orderedIterate _ _ _ _  (value_eq_ok J) (BPT J) unit p2
    (unionI J R1 p1)
    (R2 ~~~ conv F J R2)
    (union_insert J R1 p1 (R2 ~~~ conv F J R2))
    tt
  }}); unfold unionI, unionm; sep fail auto.
  unfold rep'. apply rep_prop.
  apply sortlt_equivlistA_eqlistA; auto.
  apply conv_prop_equiv. symmetry; apply iso2.
  apply rep_prop. 
  apply sortlt_equivlistA_eqlistA; auto.
  apply conv_prop_equiv.
  rewrite <- spec_union_union.
  apply equncspunrev; auto.
Qed.

 Definition impDupl : forall J (R: [DBRel (F J)]) r,
  STsep (R ~~ rep' r R)
        (fun r': u J => R ~~ rep' r R * rep' r' R).
 Proof.
   intros.
   refine (x <- impNewEmpty J <@> _
         ; impUnion J [empty0 F J] R x r
        ;; {{Return x}}); unfold rep'; sep fail auto.

   apply rep_conv_prop; apply union_empty_idl.
 Qed.

 (* darn it!  this should just be impSelect_comp with mem, but irrelevance bites! *)
 Definition interI J (dest:u J) p2 R2: unit ->Model (value J) -> hprop 
   := (fun a l => R2 ~~ rep' p2 R2 * rep' dest (inter (unconv F J (rev l)) R2)).

 Lemma inter_skipl J k x1 x2 :  ~ In k x2 -> inter (FSetInterfaceNM:=(F J)) (add k x1) x2 == inter x1 x2.
 Proof.
   intros. rewrite equivIsEqual. split; intros.
   apply inter_3.
   destruct (k == a).
       apply inter_2 in H0. rewrite <- e in H0. intuition.
       apply inter_1 in H0. apply add_3 in H0; eauto.
     apply inter_2 in H0. auto.
   apply inter_3.
     apply add_2. apply inter_1 in H0. auto.
     apply inter_2 in H0. auto.
 Qed.

 Lemma inter_addl J k x1 x2 :  In k x2 -> inter (FSetInterfaceNM:=(F J)) (add k x1) x2 == add k (inter x1 x2).
   intros. rewrite equivIsEqual. split; intros.
   destruct (k == a); [auto|].
   apply add_2. apply inter_3.
     apply inter_1 in H0. apply add_3 in H0; eauto.
     apply inter_2 in H0. auto.

   destruct (k == a).
     apply inter_3; auto. rewrite <- e. auto.

     apply add_3 in H0; [|auto].
     apply inter_3.
       apply add_2. apply inter_1 in H0. auto.
       apply inter_2 in H0. auto.
Qed.

 Definition inter_insert J dest p2 R2 tm : iter_fn_type _ _ (interI J dest p2 R2) tm.
 Proof.
   unfold iter_fn_type.
   intros.
   refine (ans <- bpt_lookup (BPT _) p2 k (R2 ~~~ conv F _ R2) <@> (R2 ~~ lm ~~ rep' dest (inter (unconv F J (rev lm)) R2))
     ; match ans with
         | Some ans' =>
           x <- bpt_insert (BPT _) dest k v (R2 ~~~' lm ~~~ (conv F J (inter (unconv F J (rev lm)) R2))) <@> 
           (R2 ~~ rep' p2 R2 * [Some ans' = specLookup (tupleOrd J)  (value_eq_ok J) k (conv F _ R2)])
          ; {{Return tt}}
         | None =>
           {{Return tt}}
       end
   )
   ; unfold interI, rep'; unfold key in *; sep fail auto.

   apply rep_prop.
   apply sortlt_equivlistA_eqlistA; auto.
   apply specInsert_sort; auto.
   rewrite (@spec_add_insert_equivl F J); [|reflexivity].
   apply conv_prop_equiv.
   rewrite distr_rev. simpl.
   rewrite inter_addl. rewrite iso2. reflexivity.
   pose (spec_lookup_in F J k (conv F J x2)) as sli.
   rewrite <- H in sli. rewrite iso2 in sli. auto.
   
   apply rep_conv_prop.
   symmetry. rewrite distr_rev. simpl. apply inter_skipl.
   generalize (spec_lookup_in F J k (conv F J x1)).
   destruct (specLookup (tupleOrd J) (value_eq_ok J) k (conv F J x1)).
  
 2: rewrite iso2; trivial.

 intros. intuition.
 unfold value in *. 
 specialize (@spec_lookup_in Mk_Set J k (conv F J x1)); intros.
 unfold key in *. rewrite <- H in *. auto.
Qed.

 Definition impInter : forall J (R1 R2: [DBRel (F J)])
    (p1 p2: u J), STsep (R1 ~~ R2 ~~ rep' p1 R1 * rep' p2 R2)
    (fun r: u J => R1 ~~ R2 ~~ 
      rep' p1 R1 * rep' p2 R2 * rep' r (inter R1 R2) ).
 Proof.
   intros.
   refine (x <- impNewEmpty _ <@> _
     ; @bpt_orderedIterate _ _ _ _ (value_eq_ok J) (BPT _) _ p1
       (interI J x p2 R2)
       (R1 ~~~ conv F _ R1)
       (inter_insert J x p2 R2 (R1 ~~~ conv F _ R1))
       tt
    ;; {{Return x}}
  ); unfold interI, rep'; sep fail auto.
   rewrite conv_empty_nil, conv_inter_emptyl. reflexivity.

   apply rep_conv_prop.
   apply inter_push; try reflexivity.
   apply equncrev; auto.
Qed.

 (* darn it!  this should just be impSelect_comp with mem, but irrelevance bites! *)
 Definition diffI J (dest:u J) p2 R2: unit ->Model (value J) -> hprop 
   := (fun a l => R2 ~~ rep' p2 R2 * rep' dest (diff (unconv F J (rev l)) R2)).

 Lemma diff_skipl J k x1 x2 :  In k x2 -> diff (FSetInterfaceNM:=(F J)) (add k x1) x2 == diff x1 x2.
 Proof.
   intros. rewrite equivIsEqual. split; intros.
   apply diff_3; [|eapply diff_2; eauto].
     destruct (k == a).
     apply diff_2 in H0; elim H0; rewrite <- e; auto.
     apply diff_1 in H0. apply add_3 in H0; auto.

   apply diff_3.
     apply add_2. eapply diff_1; eauto.
     eapply diff_2; eauto.
 Qed.

 Lemma diff_addl J k x1 x2 :  ~In k x2 -> diff (FSetInterfaceNM:=(F J)) (add k x1) x2 == add k (diff x1 x2).
   intros. rewrite equivIsEqual. split; intros.
   destruct (k == a); [auto|].
   apply add_2. apply diff_3.
     apply diff_1 in H0. apply add_3 in H0; eauto.
     apply diff_2 in H0. auto.

   destruct (k == a).
     apply diff_3; auto. rewrite <- e. auto.

     apply add_3 in H0; [|auto].
     apply diff_3.
       apply add_2. apply diff_1 in H0. auto.
       apply diff_2 in H0. auto.
Qed.

 Definition diff_insert J dest p2 R2 tm : iter_fn_type _ _ (diffI J dest p2 R2) tm.
 Proof.
   unfold iter_fn_type.
   intros.
   refine (ans <- bpt_lookup (BPT _) p2 k (R2 ~~~ conv F _ R2) <@> (R2 ~~ lm ~~ rep' dest (diff (unconv F J (rev lm)) R2))
     ; match ans with
         | Some ans' =>
           {{Return tt}}
         | None =>
           x <- bpt_insert (BPT _) dest k v (R2 ~~~' lm ~~~ (conv F J (diff (unconv F J (rev lm)) R2))) <@> 
           (R2 ~~ rep' p2 R2 * [None = specLookup (tupleOrd J)  (value_eq_ok J) k (conv F _ R2)])
          ; {{Return tt}}
       end
   )
   ; unfold diffI, rep'; unfold key in *; sep fail auto. 
   
   apply rep_conv_prop.
   symmetry. rewrite distr_rev. simpl. 
   apply diff_skipl.
   generalize (spec_lookup_in F J k (conv F J x1)) as sli.
   destruct (specLookup (tupleOrd J)  (value_eq_ok J) k (conv F J x1)); subst.
   rewrite iso2. auto.
   rewrite iso2. intros. elimtype False. apply H0.
   pose (spec_lookup_in F J k (conv F J x1)) as sli.
   unfold value, key in *.
   rewrite <- H in sli. auto. rewrite iso2 in sli. auto.
   

(*   destruct (specLookup (tupleOrd J) k (conv F J x1)); sep fail auto. *)

   apply rep_prop.
   apply sortlt_equivlistA_eqlistA; auto.
   apply specInsert_sort; auto.   
   rewrite (@spec_add_insert_equivl F J); [|reflexivity].
   apply conv_prop_equiv.
   rewrite distr_rev. simpl.
   rewrite diff_addl. rewrite iso2. reflexivity.
   pose (spec_lookup_in F J k (conv F J x2)) as sli.
   rewrite <- H in sli.
   rewrite iso2 in sli. auto.
 Qed.

 Definition impDiff : forall J (R1 R2: [DBRel (F J)])
    (p1 p2: u J), STsep (R1 ~~ R2 ~~ rep' p1 R1 * rep' p2 R2)
    (fun r: u J => R1 ~~ R2 ~~ 
      rep' p1 R1 * rep' p2 R2 * rep' r (diff R1 R2) ).
 Proof.
   intros.
   refine (x <- impNewEmpty _ <@> _
     ; @bpt_orderedIterate _ _ _ _  (value_eq_ok J) (BPT _) _ p1
       (diffI J x p2 R2)
       (R1 ~~~ conv F _ R1)
       (diff_insert J x p2 R2 (R1 ~~~ conv F _ R1))
       tt
    ;; {{Return x}}
  ); unfold diffI, rep'; sep fail auto.
   rewrite conv_empty_nil, conv_diff_emptyl. reflexivity.

   apply rep_conv_prop.
   apply diff_push; try reflexivity.
   apply equncrev; auto.
Qed.

 Definition impLookup : forall J (R1 : [DBRel (F J)])
    (p1: u J) k, STsep (R1 ~~ rep' p1 R1)
    (fun r: option (value J k) => R1 ~~
      rep' p1 R1 * [match r with
       | None => ~ In k R1
       | Some x => In k R1
                    end]).
 Proof.
   intros.
   refine {{bpt_lookup (BPT _) p1 k (R1 ~~~ conv F _ R1)}}; sep fail auto.
   cut (match specLookup (tupleOrd J)  (value_eq_ok J) k (conv F J x) with
    | Some _ => In k x
    | None => In k x -> False
    end); unfold key in *; sep fail auto;
   generalize (@spec_lookup_in F J k (conv F J x));
   destruct (specLookup (tupleOrd J)  (value_eq_ok J) k (conv F J x));
   rewrite iso2; auto;
   destruct v; sep fail auto.
 Qed.

 Definition impMember : forall J (R1 : [DBRel (F J)])
    (p1: u J) k, STsep (R1 ~~ rep' p1 R1)
    (fun r: bool => R1 ~~
      rep' p1 R1 * [r = mem k R1]).
 Proof.
   intros.
   refine (ans <- bpt_lookup (BPT _) p1 k (R1 ~~~ conv F _ R1)
     ; match ans with
         | Some ans' =>
           {{Return true}}
         | None =>
           {{Return false}}
       end)
   ; unfold rep'; unfold key in *; sep fail auto;
   unfold key in H;
   generalize (@spec_lookup_in F J k (conv F J x));
   destruct (specLookup (tupleOrd J)  (value_eq_ok J) k (conv F J x)); intuition;
   pose (FSetFacts.mem_iff (unconv F J (conv F J x)) k) as i;
     rewrite iso2 in i; rewrite iso2 in H0; try discriminate.

   apply i in H0. sep fail auto.
   specialize (spec_lookup_in Mk_Set _ k (conv F J x)).
     unfold value,key in *. rewrite <- H. rewrite iso2.  intro; elimtype False; auto.
   specialize (spec_lookup_in Mk_Set _ k (conv F J x)).
     unfold value,key in *. rewrite <- H. rewrite iso2.  intro; elimtype False; auto.
   destruct (mem k x); intuition. sep fail auto.
Qed.

Definition impFromList J p (R:[DBRel (F J)]) (l:list (Tuple J)) 
  : STsep (R ~~ rep' p R)
  (fun r:unit => R ~~ rep' p (unconv F _ (unionm F J R (map (conv_el J) l)))).
Proof.
  refine (fix impFromList J p R l
    := match l return 
         STsep (R ~~ rep' p R)
         (fun r:unit => R ~~ rep' p (unconv F _ (unionm F J R (map (conv_el J) l)))) with
         | nil => {{Return tt}}
         | x :: l' => 
           (impFromList J p R l')
           ;; z <- bpt_insert (BPT J) p x tt (R ~~~ unionm F J R (map (conv_el J) l'))
           ; {{Return tt}}
       end); unfold rep';  sep fail auto.
    apply rep_conv_prop. rewrite iso2. reflexivity.
    apply rep_prop.
    apply sortlt_equivlistA_eqlistA; auto.
    rewrite iso1; auto. reflexivity.
    
    apply rep_prop.
    apply sortlt_equivlistA_eqlistA; auto. apply specInsert_sort; auto.
    rewrite iso1. reflexivity.
    apply specInsert_sort. auto.
  Qed.

  Definition impFromRel J p (R:[DBRel (F J)]) (R2:DBRel (F J))
    : STsep (R ~~ rep' p R)
    (fun r:unit => R ~~ rep' p (union R R2)).
  Proof.
    intros.
    refine {{impFromList J p R (elements R2)}}; unfold rep'; sep fail auto.
    apply rep_conv_prop.
    rewrite <- spec_union_union. reflexivity.
  Qed.

 Definition impNew : forall J (R: DBRel (F J)),
   STsep (__)
         (fun r: u J => rep' r R).
 Proof.
   intros.
   refine (x <- impNewEmpty J
         ; impFromRel J x _ R
        ;; {{Return x}}); unfold rep'; sep fail auto.
   apply rep_conv_prop. apply union_empty_idl.
 Qed.

 Definition prod1I I J (k:key I) (p:u (I++J)) R1 : unit ->Model (value J) -> hprop 
   := (fun a l => R1 ~~ rep' p (union R1 (prod1 k (unconv F J (rev l))))).

 Definition impProd1_insert I J k p R1 tm : iter_fn_type _ _ (prod1I I J k p R1) tm.
 Proof.
   unfold iter_fn_type.
   intros.

   refine (x <- bpt_insert (BPT (I++J)) p (fuseTuples k k0) v 
     (lm ~~~' R1 ~~~ conv F (I++J) (union R1 (prod1 k (unconv F J (rev lm))))) 
     <@> _
     ; {{Return acc}}); unfold prod1I, rep'; sep fail auto.
   apply rep_prop.
   apply sortlt_equivlistA_eqlistA; auto. apply specInsert_sort; auto.
   rewrite distr_rev. simpl.
   transitivity (
     (conv F (I ++ J)
        (add (fuseTuples k k0) 
          (unconv F _ (conv F _ 
            (union x2 
              (prod1 (F:=F) (I:=I) (J:=J) k (unconv F J (rev x0))))))))).
   apply spec_add_insert_equivl. reflexivity.

   apply conv_prop_equiv. rewrite iso2, <- union_add1. apply union_push; intuition.
   rewrite prod1_add. reflexivity.
Qed.

Definition impProd1 : forall I J k (R1: [DBRel (F J)]) (R2: [DBRel (F (I++J))])
  (p1: u J) (p2:u (I++J)), STsep (R1 ~~ R2 ~~ rep' p1 R1 * rep' p2 R2)
  (fun _:unit => R1 ~~ R2 ~~ rep' p1 R1 * rep' p2 (union R2 (prod1 k R1))).
Proof.
  intros. Hint Resolve unconv_union_conv spec_union_union conv_sort.
  
  refine ({{@bpt_orderedIterate _ _ _ _ (value_eq_ok J) (BPT J)  _ p1
    (prod1I I J k p2 R2)
    (R1 ~~~ conv F J R1)
    (impProd1_insert I J k p2 R2 (R1 ~~~ conv F J R1))
    tt
  }}); unfold prod1I, rep'; sep fail auto.
  apply rep_conv_prop.
(*
   Existing Instance union_push.
   rewrite prod1_empty.
*)
  symmetry.
  transitivity (union x (empty0 F (I++J))).
  apply union_push; [reflexivity|].
  rewrite prod1_empty; reflexivity.
  rewrite union_empty_idr; reflexivity.
  
  apply rep_conv_prop.
  apply union_push; [reflexivity|].
  apply prod1_push; [reflexivity|].
  apply equncrev; auto.
Qed.

 Definition prodRelI I J (p2:u J) (dest:u (I++J)) R1 : unit ->Model (value I) -> hprop 
   := (fun a l => R1 ~~ rep' p2 R1 * rep' dest (prodRel (unconv F I (rev l)) R1)).

 Definition impProdRelI_insert I J p2 dest R1 tm : iter_fn_type _ _ (prodRelI I J p2 dest R1) tm.
 Proof.
   unfold iter_fn_type.
   intros.

   refine {{impProd1 I J k R1 
     (lm ~~~' R1 ~~~ prodRel (unconv F _ (rev lm)) R1)
     p2 dest}}; unfold prodRelI, rep'; sep fail auto;
   apply rep_conv_prop.
   rewrite distr_rev; simpl.
   rewrite prodRel_add. reflexivity.
 Qed.

 Definition impProd : forall I J (R1: [DBRel (F I)]) (R2: [DBRel (F J)])
    (p1: u I) (p2: u J), 
    STsep (R1 ~~ R2 ~~ rep' p1 R1 * rep' p2 R2)
    (fun r: u (I++J) => R1 ~~ R2 ~~ 
      rep' p1 R1 * rep' p2 R2 * rep' r (prodRel R1 R2) ).
 Proof.
   intros.
   refine (x <- impNewEmpty (I++J) <@> _
     ; @bpt_orderedIterate _ _ _ _ _ (BPT _) _ p1
       (prodRelI I J p2 x R2)
       (R1 ~~~ conv F _ R1)
       (impProdRelI_insert I J p2 x R2 (R1 ~~~ conv F _ R1))
       tt
    ;; {{Return x}}
  ); unfold prod1I, prodRelI, rep'; sep fail auto.
   rewrite conv_empty_nil, conv_prodRel_emptyl_nil. reflexivity.

   apply rep_conv_prop.
   apply prod_push; [|reflexivity].
   apply equncrev; auto.
 Qed.

  Definition projI J l (pf:bounded J l) (p:u _) : unit ->Model (value J) -> hprop 
   := (fun a l' => rep' p (gprojRel pf (unconv F J (rev l')))).

  Lemma gprojRel_add J l pf L k: 
    (gprojRel (F:=F) (l:=l) (I:=J) pf (add k L)) ==
    (add (gprojTuple pf k) (gprojRel (F:=F) (l:=l) (I:=J) pf L)).
  Proof.
    intros.
    unfold gprojRel.
    apply mapASet_add.
    typeclasses eauto.
  Qed.

 Definition proj_insert J l (pf:bounded J l) p tm :
   iter_fn_type J unit (projI J l pf p) tm.
 Proof.
   unfold iter_fn_type.
   intros.
   refine (
     x <- bpt_insert (BPT _) p (gprojTuple pf k) v (lm ~~~ (conv F _ (gprojRel (I:=J) pf (unconv F _ (rev lm))))) 
     ;  {{Return tt}})
   ; unfold projI, rep'; sep fail auto.
  apply rep_prop.
  apply sortlt_equivlistA_eqlistA; auto. apply specInsert_sort; auto.
  rewrite distr_rev; simpl.
  rewrite gprojRel_add.
  setoid_rewrite <- iso2 at 3.
  apply spec_add_insert_equivl.
  reflexivity.
 Qed.

 Definition impProj : forall J l (pf: bounded J l) (R1: [DBRel (F J)]) 
   (p1: u J), STsep (R1 ~~ rep' p1 R1)
     (fun r: u (nthTyps pf) => R1 ~~ rep' p1 R1 * rep' r (gprojRel pf R1)).
 Proof.
   intros.
   refine (x <- impNewEmpty _ <@> _
        ; (@bpt_orderedIterate _ _ _ _ _ (BPT _) unit p1
          (projI J l pf x))
        (R1 ~~~ conv F _ R1)
        (proj_insert _ l pf x (R1 ~~~ conv F _ R1))
        tt
       ;; {{Return x}})
   ; unfold projI, rep'; sep fail auto; 
     apply rep_conv_prop.
   unfold gprojRel, mapASet. rewrite fold_1. rewrite empty_elements_nil. simpl. reflexivity.
   apply gprojRel_push.
   apply equncrev; auto.
 Qed.

 Definition rep'_push : forall (I : Typing) (x : u I) (e e' : DBRel (F I)),
   e [=] e' -> rep' x e ==> rep' x e'.
 Proof.
  intros. rewrite <- equivIsEqual in H. 
  apply rep_conv_prop. auto.
 Qed.
 

(* adding these to the top breaks things *)
Require Import Basis.
Require Import Ascii. 
Require Import String.
 
Open Scope string_scope.

 Definition impPrint : forall I (R: [DBRel (F I)]) p,
   STsep (R ~~ rep' p R)
         (fun _: unit => R ~~ rep' p R).
 intros. refine ({{ (@bpt_iterate _ _ _ _ _ (BPT _) unit p
          (fun _ _ => __) (R ~~~ conv F I R) )
          (fun k v _ _ => {{ printString' (printTuple k nil) }}) tt }} );
 sep fail auto.
Qed.

Definition impSerialize : forall I (R: [DBRel (F I)]) p,
   STsep (R ~~ rep' p R)
         (fun res : string => R ~~ rep' p R).
Check bpt_iterate.
Print iterateType.
intros.
refine ( r <- @bpt_orderedIterate _ _ _ _ _ (BPT _) (list ascii) p
                (fun _ _ => __) (R ~~~ conv F I R) 
                (fun k v acc _ => {{ Return (printTuple k acc) }}) nil ;
         {{ Return (la2str r) }} );
 sep fail ltac:(eauto).
Qed.

End BTreeImpl.
