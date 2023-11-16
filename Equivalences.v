(* Copyright (c) 2009, Harvard University
 * All rights reserved.
 *
 * Authors: Avraham Shinnar, Ryan Wisnesky
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

Require Import Assumptions DataModel OrderedTypeNM FSetInterfaceNM 
 List String RelationalModel.
Require Import SetoidClass.
Require Import RelationClasses.

Module FS := FSetInterfaceNM.

Set Implicit Arguments. Unset Strict Implicit.

Hint Unfold Proper respectful.
Ltac unp := unfold Proper, respectful.

(* this stuff should move *)
Require Import List Sorting SetoidList.

Section X.

Variable F : forall I, DBSet I.
Variable A : Typing.

Notation "s [=] t" := (Equal s t) (at level 70, no associativity).
Notation "s [<=] t" := (Subset s t) (at level 70, no associativity).

Ltac poses P := let H := fresh "posesH" in pose (H := P); clearbody H.
Ltac unf := unfold Equal, equal, Subset, select, union, 
 inter, diff, empty0.


Ltac fset_simpl_c L :=
    match goal with
      | [H: ?X && ?Y = true |- _] => 
          destruct (andTjoin H); clear H; fset_simpl_c L
      | [|- ?X && ?Y = true] => apply andTsplit; fset_simpl_c L
      | [|- ?X /\ ?Y] => split; intros; fset_simpl_c L
      | [H: FSetInterfaceNM.In _ (FSetInterfaceNM.empty) |- _] => elim (FSetInterfaceNM.empty_1 H)
      | [H1:(@FSetInterfaceNM.In ?E ?T ?W ?a (FSetInterfaceNM.filter ?f ?R)) |- _] => 
        let HH := fresh "HH" in 
          assert (HH: Proper (equiv ==> equiv) f) by L;
            let HH2 := fresh "ffact" in let HH3 := fresh "ffact" in 
              pose (HH2 := FSetInterfaceNM.filter_2 HH H1); clearbody HH2; 
                pose (HH3 := FSetInterfaceNM.filter_1 HH H1); clearbody HH3; clear HH;
                  simpl in HH2; clear H1; rename HH3 into H1; fset_simpl_c L
      | [H:FSetInterfaceNM.In _ (FSetInterfaceNM.union _ _) |- _] => 
  destruct (FSetInterfaceNM.union_1 H); clear H; fset_simpl_c L
      | [H:FSetInterfaceNM.In _ (FSetInterfaceNM.inter _ _) |- _] => 
  poses (FSetInterfaceNM.inter_1 H); poses (FSetInterfaceNM.inter_2 H); clear H
      | [H:FSetInterfaceNM.In _ (FSetInterfaceNM.diff _ _) |- _] => 
  poses (FSetInterfaceNM.diff_1 H); poses (FSetInterfaceNM.diff_2 H); clear H
      | [|- (@FSetInterfaceNM.In ?E ?T ?W ?a (FSetInterfaceNM.filter ?f ?R))] => 
        eapply FSetInterfaceNM.filter_3; fset_simpl_c L
      | [|- (@FSetInterfaceNM.In ?E ?T ?W ?a (FSetInterfaceNM.inter _ _))] => 
        eapply FSetInterfaceNM.inter_3; fset_simpl_c L
      | [|- (@FSetInterfaceNM.In ?E ?T ?W ?a (FSetInterfaceNM.diff _ _))] => 
        eapply FSetInterfaceNM.diff_3; fset_simpl_c L
      | [|- ~ FSetInterfaceNM.In _ _] => intro
(*       | [H:~ FSetInterfaceNM.In _ _ |- ~ FSetInterfaceNM.In _ _] =>  *)
(*         solve[let HH := fresh "HH" in  *)
(*           intro HH; elim H; clear H; fset_simpl_c L] *)
      | _ => progress L
    end.

Ltac unfs :=  unfold FS.Equal, FS.Subset, iff in *; intros.
Ltac fset_simpl := unf; repeat (unfs; fset_simpl_c auto).

Lemma select_imp f1 f2 : 
  Proper (equiv ==> equiv) f1 -> 
  Proper (equiv ==> equiv) f2 ->
  (forall x, f1 x = true -> f2 x = true) ->
  forall R, (select (F:=F) (I:=A) f1 R) [<=] select f2 R.
Proof.
  unf. Hint Resolve FS.filter_imp. auto.
Qed.

Variable P : Tuple A -> bool. 
Variables R1 R2 : DBRel (F A).
Variable Pcompat : Proper (equiv ==> equiv) P.


Hint Resolve proper_and.


Lemma select_conj P1 P2 R : 
  Proper (equiv ==> equiv) P1 ->
  Proper (equiv ==> equiv) P2 -> 
  select (I:=A) (F:=F) (fun x => P1 x && P2 x) R [=] select P1 (select P2 R).
Proof.
  fset_simpl. 
Qed.


Lemma select_comm P1 P2 R : 
  Proper (equiv ==> equiv) P1 ->
  Proper (equiv ==> equiv) P2 -> 
  select P1 (select (I:=A) (F:=F) P2 R) [=] select P2 (select P1 R).
Proof. 
 fset_simpl. 
Qed. 

Lemma select_union :
  select P (union R1 R2) [=] union (select P R1) (select P R2).
Proof. 
 fset_simpl. 
Qed.

Lemma select_inter :
  select P (inter R1 R2) [=] inter (select P R1) (select P R2).
Proof. 
  fset_simpl. 
Qed.

Lemma select_diff :
  select P (diff R1 R2) [=] diff (select P R1) (select P R2).
Proof. 
 fset_simpl. 
Qed.

Lemma select_inter1 :
  select P (inter R1 R2) [=] inter (select P R1) R2.
Proof. 
 fset_simpl. 
Qed.

Lemma select_inter2 :
  select P (inter R1 R2) [=] inter (select P R1) R2.
Proof. 
 fset_simpl. 
Qed.

Lemma select_empty P : Proper (equiv ==> equiv) P ->
  (select P (empty0 F A)) [=] empty0 F A.
Proof. 
 fset_simpl. 
Qed.

Variable R : DBRel (F A).

Lemma union_empty0 : (union R (empty0 F A)) [=] R.
Proof. 
 fset_simpl. 
Qed.

Lemma empty_union : (union (empty0 F A) R) [=] R.
Proof. 
 fset_simpl. 
Qed.

Lemma inter_empty : (inter R (empty0 F A)) [=] empty0 _ _.
Proof. 
 fset_simpl. 
Qed.

Lemma empty_inter : (inter (empty0 F A) R) [=] empty0 _ _.
Proof. 
 fset_simpl. 
Qed.

Lemma diff_empty : (diff R (empty0 F A)) [=] R.
Proof. 
 fset_simpl. 
Qed. 

Lemma empty_diff : (diff (empty0 F A) R) [=] empty0 _ _.
Proof. 
 fset_simpl. 
Qed.

Lemma empty_sub : empty0 F A [<=] R.
Proof. 
 fset_simpl. 
Qed. 

Lemma sub_empty : R [<=] empty0 _ _ -> R [=] empty0 F A.
Proof. 
 fset_simpl. 
Qed. 

End X.

    Lemma add_same (F: forall I, DBSet I) 
(I : Typing) k l : add k (add k l) == add (FSetInterfaceNM:=(F I)) k l.
    Proof. 
      intros. rewrite equivIsEqual.
      split; intros; (destruct (k == a); [apply add_1; auto|eapply add_3; eauto]).
    Qed.
    
    Lemma add_assoc (F: forall I, DBSet I) (I : Typing) k1 k2 l 
     : add k1 (add k2 l) == add (FSetInterfaceNM:=(F I)) k2 (add k1 l).
    Proof. 
      intros. rewrite equivIsEqual. split; intros.
      destruct (k2 == a); [auto|].
      destruct (k1 == a); [auto|].
      apply add_3 in H; [|auto]. apply add_3 in H; auto.
      
      destruct (k1 == a); [auto|].
      destruct (k2 == a); [auto|].
      apply add_3 in H; [|auto]. apply add_3 in H; auto.
    Qed.

    Instance foldl_compat {A B : Type} (eqA:relation A) (eqB:relation B) {r:Reflexive eqB}:
    Proper ((eqA ==> eqB ==> eqA) ==>  (eqlistA eqB) ==> eqA ==> eqA) (@fold_left A B) | 7.
    Proof.  unfold Proper, respectful.
      induction x0; destruct y0; simpl in *; intuition; inversion H0; subst; intuition.
    Qed.

    Lemma empty_elements_nil (F: forall I, DBSet I) I : (elements (empty0 F I)) = nil.
    Proof.
      intros. remember (elements (empty0 F I)) as e.
      destruct e; intuition.
      cut (FSetInterfaceNM.In t (empty0 F I)).
      intro K; elim (empty_1 K).
      apply elements_2.
      rewrite <- Heqe.
      left. reflexivity.
    Qed.

    Instance In_1p (F: forall I, DBSet I) (J:Typing) 
      : Proper (equiv ==> equiv ==> iff) (@FSetInterfaceNM.In _ _ (F J)).
    intros.
    cut (forall a x y, x == y -> @FSetInterfaceNM.In _ _ (F J) a x -> FSetInterfaceNM.In a y).
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

  Lemma prod1_empty (F: forall I, DBSet I) I J k 
    : (prod1 (F:=F) (I:=I) (J:=J) k (empty0 F J)) == empty0 F (I ++ J).
  Proof.
    intros. unfold prod1, mapASet.
    rewrite fold_1, empty_elements_nil. reflexivity.
  Qed.
  
  Lemma empty_elements_nileq (F: forall I, DBSet I) I a 
    : a == empty0 F I -> elements a = nil.
  Proof.
    unfold DBRel. intros.
    rewrite equivIsEqual in H.
    assert (forall x,  InA equiv x (elements a) <-> InA equiv x (elements (empty0 F I))).
    split; intros HH; apply elements_2 in HH; apply elements_1; destruct (H x); auto.
    
    destruct (elements a); intuition.
    rewrite empty_elements_nil in H0.
    absurd (InA equiv t nil).
    intro GG; inversion GG.
    apply -> H0. intuition.
  Qed.

  Lemma union_same (F: forall I, DBSet I) (J:Typing) a b :
    a == b -> union (F:=F) (I:=J) a b == a.
  Proof.
    unfold union, DBRel.
    intros. rewrite equivIsEqual. split; intros.
    apply union_1 in H0. destruct H0; auto.
    rewrite equivIsEqual in H. apply <- (H a0). auto.
    apply union_2; auto.
  Qed.

  (** end copied from Bridge *)

  Lemma fold_left_add_through (F: forall I, DBSet I) 
    I J (f:Tuple I->Tuple J) k l t : Proper (equiv ==> equiv) f ->
    (fold_left (fun a e => add (FSetInterfaceNM:=(F J)) (f e) a) l
      (add k t)) ==
    (add k (fold_left (fun a e => add (f e) a) l t)).
  Proof.
    induction l; simpl fold_left; intuition.
    rewrite <- IHl; auto. apply foldl_compat with (eqB:=@eqTuple I); intuition.
    unfold respectful; intros; apply add_push; toEquiv; auto.
    apply add_assoc.
  Qed.

  Lemma mapASet_elim': forall (F: forall I, DBSet I) I J f S x (prop:Proper (equiv ==> equiv) f),
      (FSetInterfaceNM.In x (mapASet (F J) f S)  
      <-> exists y, InA (@eqTuple I) y (elements (FSetInterfaceNM:=F I) S) /\ f y == x).
  Proof.
    unfold mapASet. intros. rewrite fold_1.

    assert (nin:~ FSetInterfaceNM.In (FSetInterfaceNM:=F J) x empty) by apply empty_1.
    revert nin.
    generalize (@empty _ _ (F J)).
    intros.

    induction (elements S); simpl; intuition.
      destruct H. destruct H.
      eelim (empty_1 (FSetInterfaceNM:=F I)).
      apply elements_2. rewrite empty_elements_nil. eauto. 
      
      pose (fold_left_add_through (f a) l t prop).
      rewrite equivIsEqual in e.
      rewrite (e x) in H1.
      destruct ((f a) == x).
      exists a. intuition.
      apply add_3 in H1; auto.
      intuition. destruct H2. intuition. eauto.


      pose (fold_left_add_through (f a) l t prop).
      rewrite equivIsEqual in e.
      apply <- (e x).
      destruct ((f a) == x);[auto|].
      apply add_2.
      destruct H1. destruct H1. inversion H1; subst.
        rewrite <- H4 in c; contradiction.
      apply H0. eauto.
  Qed.

  Lemma mapASet_elim: forall (F: forall I, DBSet I) I J f S x (prop:Proper (equiv ==> equiv) f), 
      (FSetInterfaceNM.In x (mapASet (F J) f S)  
      <-> exists y, FSetInterfaceNM.In (FSetInterfaceNM:=(F I)) y S /\ f y == x).
  Proof.
    intros. destruct (mapASet_elim' S x prop). intuition.
      destruct H2. exists x0; intuition.
      destruct H1. apply H0. exists x0; intuition.
      apply (elements_1 H2).
  Qed.

  Lemma FSIn_dec `{fs:FSetInterfaceNM elt} a t : {FSetInterfaceNM.In a t} + {~ FSetInterfaceNM.In a t}.
  Proof.
    intros.
    assert ({InA equiv a (elements t)} + {~ InA equiv a (elements t)})
    by (apply InA_dec; apply equiv_dec).
    destruct H; intuition.
  Qed.

  Lemma inprod1_fuse (F: forall I, DBSet I) I J (x:Tuple (I++J)) (a:Tuple I) (b:DBRel (A:=J) (F J)) :  
    (FSetInterfaceNM.In x (prod1 (F:=F) (I:=I) (J:=J) a b))
    <->
    (exists b1, FSetInterfaceNM.In b1 b /\ (fuseTuples a b1) == x).
  Proof.
    intros. unfold prod1. apply mapASet_elim.
    typeclasses eauto.
  Qed.

  Lemma in_acc_fold_union (F: forall I, DBSet I) I J f x l acc :
      FSetInterfaceNM.In x acc -> 
      FSetInterfaceNM.In x
     (fold_left
        (fun (a0 : DBRel (A:=I) (F I)) (e : Tuple J) =>
         union (F:=F) (I:=I) a0 (f e)) l
        acc).
  Proof.
    induction l; simpl; intros; trivial.
    apply IHl. apply union_2. auto.
  Qed.

  Lemma iter_union_fuse: forall (F: forall I, DBSet I) I J (e1: DBRel (F I)) 
    (e2: DBRel (F J)) (x: Tuple (I++J)),
    (FSetInterfaceNM.In x
    (fold
      (fun (a : Tuple I) (y : DBRel (A:=I ++ J) (F (I ++ J))) =>
        union (F:=F) (I:=I ++ J) y
        (prod1 (F:=F) (I:=I) (J:=J) a e2))
      e1 (empty0 F (I ++ J)))) <->
    (exists a, FSetInterfaceNM.In a e1 /\
      exists b, FSetInterfaceNM.In b e2 /\ x == fuseTuples a b).
  Proof.
    intros. rewrite fold_1. split. 
      intros.
      cut (exists a : Tuple I,
        InA equiv a (elements e1) /\
        (exists b : Tuple J,
          FSetInterfaceNM.In b e2 /\ x == fuseTuples (I:=I) (J:=J) a b)).
      destruct 1. exists x0. intuition.
    assert (nin:~ FSetInterfaceNM.In x (empty0 F (I++J))) by apply empty_1.
    revert nin.
    revert H.
    generalize (empty0 F (I++J)).
    induction (elements e1); simpl in *; intuition. 
    destruct (FSIn_dec x (union (F:=F) (I:=I ++ J) d (prod1 (F:=F) (I:=I) (J:=J) a e2))) .
      apply union_1 in i. intuition.
      destruct ((proj1 (inprod1_fuse _ _ _) H0)).
      exists a. intuition. exists x0. intuition.

      destruct (IHl _ H n).
      exists x0. intuition.

      intros.
      destruct H. destruct H. destruct H0. destruct H0.
      apply elements_1 in H.
      generalize (empty0 F (I++J)).
      induction (elements e1); simpl; inversion H; subst.
      
      intros.
      apply in_acc_fold_union. apply union_3.
      apply <- inprod1_fuse. rewrite H3 in H1. 
      exists x1. intuition.
      
      intros.
      eapply IHl; eauto.
  Qed.

Lemma In_eq_rec : forall F I J (X: DBRel (F I)) (pf: I = J) x,
  FSetInterfaceNM.In x X -> FSetInterfaceNM.In 
  (eq_rec I Tuple  x J pf) 
  (eq_rec I (fun t => DBRel (F t)) X J pf).
Proof.
  intros. destruct pf. simpl. auto.
Qed.


  Lemma prod_empty1 (F: forall I, DBSet I) I J a b : 
       a == empty0 F I
    -> prodRel a b == empty0 F (I++J).
  Proof.
    unfold prodRel, DBRel. intros.
    rewrite fold_1.
    rewrite empty_elements_nileq; auto. simpl.
    intuition.
  Qed.

  Lemma prod_empty2 (F: forall I, DBSet I) I J a b : 
       b == empty0 F J
    -> prodRel a b == empty0 F (I++J).
  Proof.
    unfold prodRel. intros.
    rewrite fold_1. 
    induction (elements a); simpl; intuition.
    eapply transitivity; [|apply IHl].
    apply foldl_compat with (eqB:=@eqTuple _); intuition.
      unfold respectful; intros. rewrite H0, H1. reflexivity.
      rewrite H. rewrite prod1_empty. apply union_same. reflexivity.
  Qed.

  Lemma proj1_prod_id (F: forall I, DBSet I) I J a b pf: 
       b =/= empty0 F J
    -> gprojRel pf (prodRel a b) == @cast1 I _ (fun x => @DBRel x (F x)) a (nth_seq0_eq pf).
  Proof.
    unfold DBRel; intros. symmetry.
    unfold gprojRel, prodRel.
    rewrite equivIsEqual. split; intros.
      apply <- mapASet_elim; [|typeclasses eauto].
      assert (pf1:(nthTyps (l:=seq 0 (length I)) (I:=I ++ J)
            pf)=I) by (symmetry; apply nth_seq0_eq).
      assert (exists elb, In elb (elements b)).
        rewrite equivIsEqual in H.
        unfold complement, FSetInterfaceNM.Equal in H.
        assert (H':~((forall a : Tuple J,
         InA equiv a (elements b) <-> FSetInterfaceNM.In a (empty0 F J)))).
         intro G. elim H. split; intros.
           apply -> G. apply elements_1. auto.
           apply elements_2. apply <- G. auto.
        destruct (elements b).
          elim H'. split; intros H1; [inversion H1| elim (empty_1 H1)].
          exists t. intuition.

      destruct H1 as [elb inelb].
      exists (fuseTuples (cast1  a0 pf1) elb). split.
        apply <- iter_union_fuse.
        exists (@cast1 _ _ Tuple a0 pf1). split.
          eapply in_cast1_switch; eauto.
          exists elb. intuition.
          apply elements_2. apply <- InA_alt. exists elb; intuition.

        rewrite gprojTuple_fuseTuples_id.
        rewrite cast1_nest. rewrite cast1_simpl. reflexivity.
      
      apply -> mapASet_elim in H0; [|typeclasses eauto].
      destruct H0. destruct H0.
      rewrite <- H1. clear H1.
      apply iter_union_fuse in H0.
      destruct H0. destruct H0. destruct H1. destruct H1.
      rewrite H2.
      rewrite gprojTuple_fuseTuples_id.
      revert H0. clear.
      generalize ((nth_seq0_eq pf)). intros.
    generalize e. rewrite <- e. intros. repeat rewrite cast1_simpl. auto.
  Qed.

  Lemma proj1_prod_id_pf (F: forall I, DBSet I) I J a b : 
       b =/= empty0 F J
    -> let pf := (bounded_app_weaken (seq_bounded0 I) J) in
      gprojRel pf (prodRel a b) == @cast1 I _ (fun x => @DBRel x (F x)) a (nth_seq0_eq pf).
  Proof. intros. apply proj1_prod_id; auto. Qed.
