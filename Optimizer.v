(* Copyright (c) 2009, Harvard University
 * All rights reserved.
 *
 * Authors: Ryan Wisnesky, Avraham Shinnar
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

Require Import Assumptions DataModel OrderedTypeNM FSetInterfaceNM List String.
Require Import SetoidClass.
Require Import RelationClasses.
Require Import RelationalModel.
Require Import Equivalences.
Require Import Eqdep.

Set Implicit Arguments. Unset Strict Implicit.

Definition ra_rewrite : Type := forall I, 
  raExp (fun _ => string) I -> raExp (fun _ => string) I.

Definition semantics_preserving (f: ra_rewrite) : Prop :=
 forall F G (E: Env F G) I (e: raExp (fun _ => string) I), 
   (@raDenote F I (@inst F I G E e)) == 
   (@raDenote F I (@inst F I G E (@f I e))).

Definition id_rewrite : ra_rewrite := fun I e => e.

Lemma id_rewrite_preserve : semantics_preserving id_rewrite.
Proof.
 unfold semantics_preserving. unfold id_rewrite.
 intros. reflexivity.
Qed.

Definition id_rewrite_2 (I: Typing) (e: raExp (fun _ => string) I) : raExp (fun _ => string) I.
refine (fix id_rewrite_2 (I: Typing) (e: raExp (fun _ => string) I) 
  : raExp (fun _ => string) I :=
  match e as e' in raExp _ I' return raExp (fun _ => string) I' with
    | emptyExp i => emptyExp _ i
    | varExp i v =>  varExp v 
    | unionExp i r r0 =>  unionExp (id_rewrite_2  i r) (id_rewrite_2  i r0)
    | interExp i r r0 =>  interExp (id_rewrite_2 i r) (id_rewrite_2  i r0)
    | selectExp i r f => selectExp (id_rewrite_2  i r) f 
    | gprojExp i l pf r => gprojExp pf (id_rewrite_2  i r)
    | prodExp  i J0 r0 r1 =>  
      prodExp (id_rewrite_2  i r0) (id_rewrite_2  _ r1)
  end  ). 
Defined.
  
(* this should move to relationalmodel *)
Instance whereDenoteProper' I (e: whereExp I) 
: Proper (equiv ==> equiv) (whereDenote e).
apply whereDenoteProper.
Defined.

Lemma id_rewrite_2_preserve : semantics_preserving id_rewrite_2.
Proof.
 unfold semantics_preserving. 
 intros.
 induction e.
  simpl. reflexivity.
  simpl. reflexivity.
  simpl. rewrite IHe1. rewrite IHe2. reflexivity.
  simpl. rewrite IHe1. rewrite IHe2. reflexivity.
  simpl. rewrite IHe. reflexivity.
  simpl. rewrite IHe. reflexivity.
  simpl. rewrite IHe1. rewrite IHe2. reflexivity.
Qed.

Require Import List.

(* ******************************
     select true x = x,
     select false x = 0
     select P (select Q R) = select (P /\ Q) R
  ******************************************************************** *)

Lemma select_true_cancel : forall F I G (E: Env F G) e,
 select (F:=F) (I:=I) (whereDenote (trueExp I)) 
 (raDenote  e) == raDenote (F:=F) e.
Proof.
 intros. unfold select.
 unfold DBRel. rewrite @equivIsEqual.
 red. intros. intuition.
 apply FSetInterfaceNM.filter_1 with (f := whereDenote (trueExp I)).
 apply whereDenoteProper. assumption.
Qed.

Lemma select_false_cancel : forall F I G (E: Env F G) e,
 select (F:=F) (I:=I) (whereDenote (falseExp I)) 
 (raDenote  e) == raDenote (F:=F) (emptyExp _ _).
Proof.
 intros. unfold select.
 unfold DBRel. rewrite @equivIsEqual.
 red. intros. split; intros H.

 generalize  (FSetInterfaceNM.filter_2 (whereDenoteProper _) H); simpl.
 intuition.
 
 simpl in H. elim (empty_1 H).
Qed.

Definition sel_rw (I: Typing) (e: raExp (fun _ => string) I) : raExp (fun _ => string) I.
refine (fix sel_rw (I: Typing) (e: raExp (fun _ => string) I) : raExp (fun _ => string) I :=
  match e as e' in raExp _ I' return raExp (fun _ => string) I' with
    | emptyExp i => emptyExp _ i
    | varExp i r0 =>  varExp r0 
    | unionExp i r r0 =>  unionExp 
       (sel_rw  i r) (sel_rw  i r0)
    | interExp i r r0 =>  interExp 
       (sel_rw  i r) (sel_rw  i r0)
    | selectExp i r f => match f with
                           | trueExp => (sel_rw i r)
                           | falseExp => emptyExp _ _
                           | x => 
                             (match (sel_rw  i r) as e' in raExp _ I' return i=I'->raExp _ I' with
                               | selectExp i' r' f' => fun _ => selectExp r' (andExp _ f')
                               | y' => fun _ => _
                             end(refl_equal i))
                         end 
    | gprojExp i l pf r => gprojExp pf (sel_rw  i r)
    | prodExp  i J0 r0 r1 =>  
      prodExp (sel_rw  i r0) (sel_rw  _ r1)
  end  ); subst;
(exact (selectExp y' f) || exact f).
Defined.

Lemma sel_rw_preserve : semantics_preserving sel_rw.
Proof.
 unfold semantics_preserving. 
 intros.
 induction e; simpl; 
 try (rewrite IHe1; rewrite IHe2);
 try (rewrite IHe); try reflexivity; 
 destruct w; simpl; try reflexivity;
  [eapply select_true_cancel; eauto|
  eapply select_false_cancel; eauto|..];

 remember (sel_rw e) as sr;
 destruct sr; simpl in *; try reflexivity;
 rewrite <- select_conj; try reflexivity; 
 intros x y H; rewrite H; reflexivity.
Qed.

(* select P (select Q R)) *)

(* union empty x = x ***********************************************************)

Definition empty_cancel_rewrite (I: Typing) (e: raExp (fun _ => string) I) : raExp (fun _ => string) I.
refine (fix empty_cancel_rewrite (I: Typing) (e: raExp (fun _ => string) I) : raExp (fun _ => string) I :=
  match e as e' in raExp _ I' return raExp _ I' with
    | emptyExp i => emptyExp _ i
    | varExp i r0 =>  varExp r0 
    | unionExp i r r0 => 
      match r with
        | emptyExp i0 => empty_cancel_rewrite  i r0
        | x => unionExp (empty_cancel_rewrite  i r) 
                        (empty_cancel_rewrite  i r0)
      end
    | interExp i r r0 =>  interExp (empty_cancel_rewrite  i r) 
                                   (empty_cancel_rewrite  i r0)
    | selectExp i r f => selectExp (empty_cancel_rewrite  i r) f 
    | gprojExp i l pf r => gprojExp pf (empty_cancel_rewrite  i r)
    | prodExp  i J0 r0 r1 =>  
      prodExp (empty_cancel_rewrite  i r0) (empty_cancel_rewrite  _ r1)
  end  ). 
Defined.

Lemma empty_cancel_rewrite_preserve : semantics_preserving empty_cancel_rewrite.
Proof.
 unfold semantics_preserving. 
 intros.
 induction e; simpl; 
 try (rewrite IHe1; rewrite IHe2);
 try (rewrite IHe); try reflexivity;
 destruct e1; simpl; try reflexivity.
  rewrite IHe1. rewrite <- IHe2.
  simpl. unfold DBRel. rewrite @equivIsEqual.
  apply  empty_union.
Qed.

(**** now some more, non-cost decreasing optimizations *)

Definition backprojnth_opt n l
  := nth_error (A:=nat) l n.

Lemma nthTyps_len i l pf : length (nthTyps (l:=l) (I:=i) pf) = length l.
Proof.
  induction l; simpl; auto.
  destruct pf. simpl. auto.
Qed.

Lemma backprojnth_opt_same n l (pf0 : n < length l)
  : match backprojnth_opt n l with
      | None => False
      | Some v => True
    end.
Proof. red.
  induction n; simpl;
    destruct l; simpl; auto; intros; try solve[inversion pf0].
  apply IHn. omega.
Qed.

Definition backprojnth i n l pf (pf0 : n < length (nthTyps (l:=l) (I:=i) pf)) : nat.
Proof. intros.
  rewrite nthTyps_len in pf0.
remember (backprojnth_opt n l).
generalize (backprojnth_opt_same pf0).
destruct (backprojnth_opt n l); intro H.
apply n0.
elim H.
Defined.

Lemma backprojnth_toopt i n l pf (pf0 : n < length (nthTyps (l:=l) (I:=i) pf)) :
  match backprojnth_opt n l with
    | None => False
    | Some x => backprojnth pf0 = x
  end.
Proof.
  intros. unfold backprojnth.
  generalize dependent ((backprojnth_opt_same (n:=n) (l:=l)
            (eq_ind (length (nthTyps (l:=l) (I:=i) pf))
               (fun n0 : nat => n < n0) pf0 (length l)
               (nthTyps_len (i:=i) (l:=l) pf)))).
  destruct (backprojnth_opt n l); intro H.
  auto.
  elim H.
Qed.

Lemma backprojnth_opt_bounded i n l pf (pf0 : n < length (nthTyps (l:=l) (I:=i) pf)) : 
  match backprojnth_opt n l with
    | None => False
    | Some m => m < length i
  end.
Proof. red.
  induction n; simpl;
    destruct l; simpl; auto; intros; try solve[inversion pf0].
  destruct pf0; intuition.
  generalize dependent pf. destruct pf. simpl. intros.
  eapply IHn. eapply down_1. eauto.
Qed.

Lemma backprojnth_bounded i n l pf (pf0 : n < length (nthTyps (l:=l) (I:=i) pf)) : 
  backprojnth (i:=i) (n:=n) (l:=l) (pf:=pf) pf0 < length i.
Proof.
  unfold backprojnth. intros.
  generalize dependent (backprojnth_opt_same (n:=n) (l:=l)
        (eq_ind (length (nthTyps (l:=l) (I:=i) pf)) 
           (fun n0 : nat => n < n0) pf0 (length l)
           (nthTyps_len (i:=i) (l:=l) pf))).
  generalize (backprojnth_opt_bounded pf0).
  destruct (backprojnth_opt n l); intuition.
Qed.

Lemma backprojnth_opt_nil n : backprojnth_opt n nil = None.
Proof. induction n; simpl; auto. Qed.

Lemma nthTyp_backprojnth i l n pf pf1 pf2 : 
  (nthTyp  (n:=n) (I:=nthTyps (l:=l) (I:=i) pf) pf1) = nthTyp (I:=i) (n:=backprojnth pf1) pf2.
Proof.
  intros.
  generalize (backprojnth_toopt pf1).
  remember (backprojnth_opt n l).
  destruct e; intuition.
  generalize dependent pf2. rewrite H.
  clear H. revert l n pf pf1 n0 Heqe.
  
  
  induction l; simpl; intros.
    rewrite backprojnth_opt_nil in Heqe; discriminate.
  destruct pf; simpl in *; destruct n; simpl in *.
    inversion Heqe; subst; apply nthTyp_pf_irrel.
  apply IHl; auto.
Qed.

Definition atomicExp_shiftback i l pf ty (w:atomicExp (nthTyps (l:=l) (I:=i) pf) ty) : atomicExp i ty.
Proof.
  intros.
  refine(match w with
    | atom _ c => atom _ c
    | var n pf => _
  end).
rewrite (nthTyp_backprojnth (backprojnth_bounded _)).
apply var.
Defined.

Definition compareExp_shiftback i l pf t (w:compareExp (nthTyps (l:=l) (I:=i) pf) t) : compareExp i t
  := match w with
       | compareEq a b => compareEq (atomicExp_shiftback a) (atomicExp_shiftback b)
       | compareLt a b => compareLt (atomicExp_shiftback a) (atomicExp_shiftback b)
       | compareGt a b => compareGt (atomicExp_shiftback a) (atomicExp_shiftback b)
     end.

Fixpoint whereExp_shiftback i l pf (w:whereExp (nthTyps (l:=l) (I:=i) pf)) : whereExp i
 := match w with
      | trueExp  => trueExp _
      | falseExp => falseExp _
      | compExp _ c => compExp (compareExp_shiftback c)
      | andExp e1 e2 => andExp (whereExp_shiftback e1) (whereExp_shiftback e2)
      | orExp  e1 e2 => orExp (whereExp_shiftback e1) (whereExp_shiftback e2)
      | notExp e => notExp (whereExp_shiftback e)
    end.

Lemma bounded_inlen l2 I :  bounded I l2 -> forall n, In n l2 -> n < length I.
Proof. induction l2; simpl; intuition. Qed.

Definition permnat_comb i (l1 l2:list nat) 
 (pf1: bounded i l1)
 (pf2 : bounded (nthTyps (l:=l1) (I:=i) pf1) l2) : list nat.
Proof.
intros.
refine ((fix map (l : list nat) : bounded (nthTyps (l:=l1) (I:=i) pf1) l -> list nat :=
  match l return bounded (nthTyps (l:=l1) (I:=i) pf1) l -> list nat with
    | nil => fun _ => nil
    | a :: tl => fun pf => (@backprojnth i a l1 pf1 (let '(conj a b) := pf in a) :: map tl (let '(conj a b) := pf in b))
  end) l2 pf2).
Defined.

Lemma bounded_permnat_comb i' l' l pf' pf : bounded i' (permnat_comb (i:=i') (l1:=l') (l2:=l) (pf1:=pf') pf).
Proof.
  induction l; simpl; intuition.
  destruct pf. apply backprojnth_bounded.
Qed.
  
Lemma permnat_comb_nth i' l' l pf' pf pf_: 
  (nthTyps (l:=permnat_comb (i:=i') (l1:=l') (l2:=l) (pf1:=pf') pf) (I:=i') pf_)
  =
  (nthTyps (l:=l) (I:=nthTyps (l:=l') (I:=i') pf') pf).
Proof.
  induction l; simpl; intuition.
  destruct pf; destruct pf_. f_equal.
    rewrite <- nthTyp_backprojnth. apply nthTyp_pf_irrel.
    rewrite IHl. apply nthTyps_pf_irrel.
Qed.

Definition proj_proj (I: Typing) (e: raExp (fun _ => string) I) : raExp (fun _ => string) I.
refine (fix proj_proj (I: Typing) (e: raExp (fun _ => string) I) : raExp (fun _ => string) I :=
  match e as e' in raExp _ I' return raExp (fun _ => string) I' with
    | emptyExp i => emptyExp _ i
    | varExp i r0 =>  varExp r0 
    | unionExp i r r0 =>  unionExp 
       (proj_proj  i r) (proj_proj  i r0)
    | interExp i r r0 =>  interExp 
       (proj_proj  i r) (proj_proj  i r0)
    | selectExp i r f => 
      (match (proj_proj i r) as e' in raExp _ I' return i=I'->raExp _ _ with
         | gprojExp i' l' pf' r' => fun _ => _
         | y' => fun _ => _
       end(refl_equal i))
    | gprojExp i l pf r => 
      (match (proj_proj  i r) as e' in raExp _ I' return i=I'->raExp _ _ with
         (* note that we don't yet do anything special here *)
         | gprojExp i' l' pf' r' => fun _ => _
         | y' => fun _ => _
       end(refl_equal i))
    | prodExp  i J0 r0 r1 =>  
      prodExp (proj_proj  i r0) (proj_proj  _ r1)
  end  ); subst.
exact (selectExp y' f).
exact (selectExp y' f).
exact (selectExp y' f).
exact (selectExp y' f).
exact (selectExp y' f).
(* push selection throught projection *)
refine (gprojExp pf' (selectExp r' _)). apply (whereExp_shiftback f).
exact (selectExp y' f).
exact (gprojExp pf r).
exact (gprojExp pf r).
exact (gprojExp pf r).
exact (gprojExp pf r).
exact (gprojExp pf r).
pose (@gprojExp (fun _ : Typing => string) i' (permnat_comb pf) (bounded_permnat_comb _) r') as rcomb.
rewrite permnat_comb_nth in rcomb. exact rcomb.
exact (gprojExp pf r).
Defined.

Lemma backprojnth_shift I n a l l0 b pf0 : backprojnth (i:=I) (n:=S n) (l:=a :: l) (pf:=conj l0 b) pf0 = 
  backprojnth (i:=I) (n:=n) (l:=l) (pf:=b)
  (down_1 (a:=n) (b:=length (nthTyps (l:=l) (I:=I) b)) pf0).
Proof.
  unfold backprojnth. simpl. intros.
  generalize (backprojnth_opt_same (n:=S n) (l:=a :: l)
        (eq_ind (S (length (nthTyps (l:=l) (I:=I) b)))
           (fun n0 : nat => S n < n0) pf0 (S (length l))
           (nthTyps_len (i:=I) (l:=a :: l) (conj l0 b)))).
generalize ((backprojnth_opt_same (n:=n) (l:=l)
        (eq_ind (length (nthTyps (l:=l) (I:=I) b)) 
           (fun n0 : nat => n < n0)
           (down_1 (a:=n) (b:=length (nthTyps (l:=l) (I:=I) b)) pf0)
           (length l) (nthTyps_len (i:=I) (l:=l) b)))).
simpl.
  generalize dependent (backprojnth_opt n l). intros.
  destruct e; intuition.
Qed.

Lemma gprojTuple_atomic_shiftback_id I l pf t x a y : 
  gprojTuple (l:=l) (I:=I) pf y == a ->
  atomicDenote (t:=t) x a == atomicDenote (atomicExp_shiftback (i:=I) (l:=l) (pf:=pf) x) y.
Proof.
  destruct x; simpl. reflexivity.
  intros.
   generalize dependent (backprojnth_bounded (i:=I) (n:=n) (l:=l) (pf:=pf) pf0). intros.
   generalize dependent (nthTyp_backprojnth (i:=I) (l:=l) (n:=n) (pf:=pf) (pf1:=pf0) l0).
   intros.

  transitivity (let aaarrg :=
    projTupleN (I:=I)
    (n:=backprojnth (i:=I) (n:=n) (l:=l) (pf:=pf) pf0)
    l0 y in
    let aaarrg0 :=
      eq_rec_r (fun t0 : typ => Tuple (t0 :: nil)) aaarrg
      e in fst aaarrg0);
  simpl.
  Focus 2.
   generalize dependent (backprojnth (i:=I) (n:=n) (l:=l) (pf:=pf) pf0). intros.
   generalize e. rewrite e. clear e. intros.
   rewrite (UIP_refl _ _ e). reflexivity.

  cut ((projTupleN (I:=nthTyps (l:=l) (I:=I) pf) (n:=n) pf0 a) ==
     (eq_rec_r (fun t0 : typ => (typDenote t0 * unit)%type)
        (projTupleN (I:=I) (n:=backprojnth (i:=I) (n:=n) (l:=l) (pf:=pf) pf0)
           l0 y) e)). intro GG. simpl in GG; intuition.
  rewrite <- H.
  clear.
  revert pf n pf0 y l0 e.
  induction l; simpl in *. inversion pf0.
  destruct pf. intros. split; trivial.
  destruct n; simpl in *.
  Focus 2.
  generalize dependent l1.
  rewrite backprojnth_shift. intros.
  eapply IHl.

  unfold backprojnth in *. simpl in *. clear.
  cut ((projTupleN (I:=I) (n:=a) l0 y) == (eq_rec_r (fun t0 : typ => (typDenote t0 * unit)%type)
        (projTupleN (I:=I) (n:=a) l1 y) e)). simpl; intuition.
  assert (nthTyp (I:=I) (n:=a) l1 :: nil = nthTyp (I:=I) (n:=a) l0 :: nil) by (f_equal; auto).
  rewrite (projTupleN_pf_irrel H).
  generalize dependent H. generalize e. rewrite e. intros.
  rewrite cast1_simpl. rewrite (UIP_refl _ _ e0). simpl. intuition.
  reflexivity.
Qed.

Lemma gprojTuple_compare_shiftback_id I l pf t c a y : 
  gprojTuple (l:=l) (I:=I) pf y == a ->
  compareDenote (t:=t) c a == compareDenote (compareExp_shiftback (i:=I) (l:=l) (pf:=pf) c) y.
Proof.
  intros.
  pose (fun t x => gprojTuple_atomic_shiftback_id (t:=t) x H) as r.
  destruct c; simpl; intros;
  elim_comp; elim_comp; auto; repeat rewrite <- r in *;
  (rewrite H1 in H0 || rewrite H0 in H1);  order.
Qed.

Lemma gprojTuple_shiftback_id I l pf w a y : 
  gprojTuple (l:=l) (I:=I) pf y == a ->
  whereDenote w a == whereDenote (whereExp_shiftback (i:=I) (l:=l) (pf:=pf) w) y.
Proof.
  induction w; simpl; auto; intros.
    rewrite <- gprojTuple_compare_shiftback_id; eauto.
  rewrite IHw1, IHw2; eauto.
  rewrite IHw1, IHw2; eauto.
  rewrite IHw; eauto.
Qed.

Lemma select_gprojRel_reorder F I l pf w (d : DBRel (A:=I) (F I)) :
  select (F:=F) (I:=nthTyps (l:=l) (I:=I) pf) (whereDenote w)
  (gprojRel (F:=F) (l:=l) (I:=I) pf d) ==
  gprojRel (F:=F) (l:=l) (I:=I) pf
  (select (F:=F) (I:=I)
    (whereDenote (whereExp_shiftback (i:=I) (l:=l) (pf:=pf) w)) d).
Proof.
  unfold gprojRel.
  unfold DBRel. intros. rewrite equivIsEqual. split; intros. 
    pose (filter_1 (whereDenoteProper _) H) as inn.
    pose (filter_2 (whereDenoteProper _) H) as sat. clearbody inn sat.
    apply -> mapASet_elim in inn; [|typeclasses eauto].
    apply <- mapASet_elim; [|typeclasses eauto].
    destruct inn as [y [yin eqa]]. 
    exists y. split; trivial.
    apply filter_3. typeclasses eauto.
    auto. erewrite <- gprojTuple_shiftback_id; eauto.

    apply -> mapASet_elim in H; [|typeclasses eauto].
    destruct H as [y [yin eqa]].
    pose (filter_1 (whereDenoteProper _) yin) as inn.
    pose (filter_2 (whereDenoteProper _) yin) as sat. clearbody inn sat.
    erewrite <- gprojTuple_shiftback_id in sat; [|eauto].
    apply filter_3; [typeclasses eauto|..|auto].
    apply <- mapASet_elim; [|typeclasses eauto].
    exists y. intuition.
Qed.

Ltac bto := match goal with
  [|- context [@backprojnth ?I ?a0 ?l ?pf1 ?pf2]] => generalize (@backprojnth_toopt I a0 l pf1 pf2); intro
end.

Lemma  eq_rec_pf_irrel A B C D x pf1 pf2 : @eq_rec A B C D x pf1 = @eq_rec A B C D x pf2.
Proof.
  intros. destruct pf1.  rewrite (UIP_refl _ _ pf2). simpl. reflexivity.
Qed.

Lemma projTupleN_comb I l0 a pf0 pf7 z pf5 pf6:
  (projTupleN (I:=nthTyps (l:=l0) (I:=I) pf0) (n:=a) pf7
    (gprojTuple (l:=l0) (I:=I) pf0 z)) = 
  eq_rec_r Tuple
  (projTupleN (I:=I)
    (n:=backprojnth (i:=I) (n:=a) (l:=l0) (pf:=pf0)
      pf7) pf5 z) pf6.
Proof.
 induction l0; simpl. inversion pf7.
 destruct pf0. intros. bto.
 destruct a0; simpl in *.
   generalize dependent (backprojnth (i:=I) (n:=0) (l:=a :: l0) (pf:=conj l b) pf7).
   intros. subst.
   rewrite (projTupleN_pf_irrel pf6).
   generalize dependent (projTupleN (I:=I) (n:=a) l z). generalize dependent (nthTyp (I:=I) (n:=a) l). clear.
   intros. inversion pf6. destruct H0. rewrite cast1_simpl. destruct t0; simpl. unfold eq_rec_r.
   rewrite (UIP_refl _ _ (eq_sym pf6)). simpl. destruct t1. reflexivity.
 
 assert (pf5':backprojnth (i:=I) (n:=a0) (l:=l0) (pf:=b)
    (down_1 (a:=a0) (b:=length (nthTyps (l:=l0) (I:=I) b)) pf7) < 
  length I) by apply backprojnth_bounded.
 assert (pf6'  : nthTyp (I:=nthTyps (l:=l0) (I:=I) b) (n:=a0)
                (down_1 (a:=a0) (b:=length (nthTyps (l:=l0) (I:=I) b)) pf7)
              :: nil =
              nthTyp (I:=I)
                (n:=backprojnth (i:=I) (n:=a0) (l:=l0) (pf:=b)
                      (down_1 (a:=a0) (b:=length (nthTyps (l:=l0) (I:=I) b))
                         pf7)) pf5' :: nil)
  by (f_equal; apply nthTyp_backprojnth).
 rewrite (IHl0 a0 b (down_1 (a:=a0) (b:=length (nthTyps (l:=l0) (I:=I) b)) pf7)
 z pf5' pf6').
 clear.
 generalize (@backprojnth_shift I a0 a l0 l b pf7).
 intros GG. destruct GG.
 unfold eq_rec_r.
 assert (ntheq: nthTyp (I:=I)
              (n:=backprojnth (i:=I) (n:=S a0) (l:=
                    a :: l0) (pf:=conj l b) pf7) pf5' :: nil =
            nthTyp (I:=I)
              (n:=backprojnth (i:=I) (n:=S a0) (l:=
                    a :: l0) (pf:=conj l b) pf7) pf5 :: nil)
   by (f_equal; apply nthTyp_pf_irrel).
 rewrite (projTupleN_pf_irrel ntheq).
 clear.
 destruct ntheq. rewrite cast1_simpl.
  fold bounded.
 generalize dependent (@projTupleN I
           (@backprojnth I (S a0) (@cons nat a l0)
              (@conj (lt a (@length typ I)) (bounded I l0) l b) pf7) pf5' z).
 generalize dependent (down_1 (a:=a0) (b:=length (nthTyps (l:=l0) (I:=I) b)) pf7).
 intros. clear.
 generalize dependent (nthTyp (I:=nthTyps (l:=l0) (I:=I) b) (n:=a0) l1).
 intros.
 erewrite (eq_rec_pf_irrel). reflexivity.
Qed.

Lemma gprojTuple_comb I l0 l pf0 pf b z pf3 :
  gprojTuple (l:=l) (I:=nthTyps (l:=l0) (I:=I) pf0) pf
  (gprojTuple (l:=l0) (I:=I) pf0 z) ==
  eq_rec_r Tuple
  (gprojTuple (l:=permnat_comb (i:=I) (l1:=l0) (l2:=l) (pf1:=pf0) pf)
    (I:=I) b z) pf3.
Proof.
 intros I l0 l pf0. revert l.
 induction l; simpl; trivial.
 destruct pf; destruct b0. simpl. split.
Focus 2.
inversion pf3.
rewrite (IHl b b0 z H1).
generalize dependent (gprojTuple (l:=permnat_comb (i:=I) (l1:=l0) (l2:=l) (pf1:=pf0) b)
           (I:=I) b0 z).
destruct H1.
generalize dependent (nthTyps (l:=l) (I:=nthTyps (l:=l0) (I:=I) pf0) b).
unfold eq_rec_r. intros.
rewrite (UIP_refl _ _ (@eq_sym Typing t t (@eq_refl (list typ) t))).
generalize dependent (@fst (typDenote (@nthTyp I (@backprojnth I a l0 pf0 l1) l2))
                 unit (@projTupleN I (@backprojnth I a l0 pf0 l1) l2 z)).
simpl.
generalize dependent (backprojnth (i:=I) (n:=a) (l:=l0) (pf:=pf0) l1).
clear. intros. 
inversion pf3. destruct H1.
rewrite (UIP_refl _ _ (eq_sym pf3)). simpl. reflexivity.
(* finished subgoal 2 *)
inversion pf3.
assert (nthTyp (I:=nthTyps (l:=l0) (I:=I) pf0) (n:=a) l1::nil =
       nthTyp (I:=I) (n:=backprojnth (i:=I) (n:=a) (l:=l0) (pf:=pf0) l1) l2::nil)
by (f_equal; auto).
rewrite (projTupleN_comb _ H).
generalize dependent (gprojTuple (l:=permnat_comb (i:=I) (l1:=l0) (l2:=l) (pf1:=pf0) b)
          (I:=I) b0 z).
generalize dependent (backprojnth (i:=I) (n:=a) (l:=l0) (pf:=pf0) l1). clear.
intros.
generalize dependent (projTupleN (I:=I) (n:=n) l2 z).
destruct t0. simpl.
destruct H0.
inversion pf3.
destruct H1.
unfold eq_rec_r.
rewrite (UIP_refl _ _ (@eq_sym Typing
              (@cons typ (@nthTyp (@nthTyps l0 I pf0) a l1) (@nil typ))
              (@cons typ (@nthTyp (@nthTyps l0 I pf0) a l1) (@nil typ)) H)).
rewrite (UIP_refl _ _ (eq_sym pf3)). simpl. reflexivity.
Qed.

Lemma in_eq_rec_b :
  forall (F : forall x : Typing, DBSet x) (I J : Typing)
    (X : DBRel (A:=J) (F J)) (pf : J = I) (x : Tuple I),
  FSetInterfaceNM.In x
    (eq_rec J (fun t : Typing => DBRel (A:=t) (F t)) X I pf)
  ->   FSetInterfaceNM.In (eq_rec I Tuple x J (eq_sym pf)) X.
Proof. intros. destruct pf. auto. Qed.

Lemma gprojRel_comb F I d l l0 pf0 pf b e:
    gprojRel (F:=F) (l:=l) (I:=nthTyps (l:=l0) (I:=I) pf0) pf
     (gprojRel (F:=F) (l:=l0) (I:=I) pf0 d) ==
   eq_rec
     (nthTyps (l:=permnat_comb (i:=I) (l1:=l0) (l2:=l) (pf1:=pf0) pf) (I:=I)
        b) (fun t : Typing => DBRel (A:=t) (F t))
     (gprojRel (F:=F) (l:=permnat_comb (i:=I) (l1:=l0) (l2:=l) (pf1:=pf0) pf)
        (I:=I) b d) (nthTyps (l:=l) (I:=nthTyps (l:=l0) (I:=I) pf0) pf) e.
Proof.
  intros.
  
  unfold DBRel, gprojRel. rewrite equivIsEqual. intro a; split; intro inna.
   apply -> mapASet_elim in inna; [|typeclasses eauto].
   destruct inna as [y [inny eqa]].
   apply -> mapASet_elim in inny; [|typeclasses eauto].
   destruct inny as [z [innz eqy]].
   rewrite <- eqy in eqa.

   rewrite (gprojTuple_comb _ (eq_sym e)) in eqa.
   clear eqy.
   generalize dependent (permnat_comb (i:=I) (l1:=l0) (l2:=l) (pf1:=pf0) pf).
   generalize dependent (nthTyps (l:=l) (I:=nthTyps (l:=l0) (I:=I) pf0) pf).
   destruct e. simpl. unfold eq_rec_r. 
   rewrite (UIP_refl _ _ (eq_sym (eq_refl (nthTyps (l:=l1) (I:=I) b)))).
   simpl. intros.
   apply <- mapASet_elim; [|typeclasses eauto]. eauto.

   apply <- mapASet_elim; [|typeclasses eauto]. 
   apply in_eq_rec_b in inna.
   apply -> mapASet_elim in inna; [|typeclasses eauto]. 
   destruct inna as [y [inny eqa]].
   exists (gprojTuple (l:=l0) pf0 y).
   split.
     apply <- mapASet_elim; [|typeclasses eauto]. 
     exists y; intuition.
     
     rewrite (gprojTuple_comb _ (eq_sym e)).
     revert eqa. clear.
     generalize dependent (permnat_comb (i:=I) (l1:=l0) (l2:=l) (pf1:=pf0) pf). destruct e.
     unfold eq_rec_r. simpl.
     auto.
  Qed.
   
Lemma proj_proj_preserve : semantics_preserving proj_proj.
Proof.
 unfold semantics_preserving. 
 intros.
 induction e; simpl; 
 try (rewrite IHe1; rewrite IHe2);
 try (rewrite IHe); try reflexivity;

 remember (proj_proj e) as sr;
 destruct sr; simpl in *; try rewrite IHe; try reflexivity.
 apply select_gprojRel_reorder.
 unfold eq_rec_r.
 rewrite (UIP_refl _ _ (eq_sym (eq_refl (nthTyps (l:=l0) (I:=I) pf0)))).
 simpl. clear.
 generalize dependent (permnat_comb_nth (i':=I) (l':=l0) (l:=l) (pf':=pf0) (pf:=pf)
              (bounded_permnat_comb (i':=I) (l':=l0) (l:=l) (pf':=pf0) pf)).
 generalize dependent (bounded_permnat_comb (i':=I) (l':=l0) (l:=l) (pf':=pf0) pf).
 intros.
 transitivity (eq_rec
   (nthTyps
     (l:=permnat_comb (i:=I) (l1:=l0) (l2:=l)
       (pf1:=pf0) pf) (I:=I) b)
   (fun t : Typing => DBRel (A:=t) (F t)) 
   (gprojRel (F:=F) 
   (l:=permnat_comb (i:=I) (l1:=l0) (l2:=l) (pf1:=pf0) pf)
   b (raDenote (F:=F) (inst (F:=F) (G:=G) E sr)))
   (nthTyps (l:=l) (I:=nthTyps (l:=l0) (I:=I) pf0)
     pf)
   (permnat_comb_nth (i':=I) (l':=l0) (l:=l)
     (pf':=pf0) (pf:=pf) b)).
 apply gprojRel_comb.
 generalize dependent (permnat_comb_nth (i':=I) (l':=l0) (l:=l) (pf':=pf0) (pf:=pf) b).
 generalize dependent (permnat_comb (i:=I) (l1:=l0) (l2:=l) (pf1:=pf0) pf).
 generalize dependent (nthTyps (l:=l) (I:=nthTyps (l:=l0) (I:=I) pf0) pf).
 destruct e. intros. rewrite (UIP_refl _ _ e). simpl. reflexivity.
Qed.


(*
Section test.
Let I:Typing := nt :: unt :: nt :: opt nt :: nil.
Let testE := fun x: Typing => string.
Let l1 := (0::1::2::nil).
Let l2 := (1::0::3::nil).
Lemma test_pf2 : bounded I l2. compute; intuition. Qed.
Lemma test_pf1 : bounded (nthTyps (l:=l2) (I:=I) test_pf2) l1.
repeat (compute; match goal with [|- context[match ?X with | conj _ _ => _ end]] => destruct X end; 
  intuition).
Qed.

Let e := gprojExp test_pf1 (gprojExp test_pf2 (emptyExp testE _)).
Eval compute in (e, proj_proj e).
End test.
*)




(* Cost Estimation ******************************************)
Section CostEst.

Require Import Min Max.

Variable cardInter : nat -> nat -> nat.
Variable cardUnion : nat -> nat -> nat.
Variable cardSelect : nat -> nat.

Hypothesis inter_up : forall a b c d,
 a <= c -> b <= d -> cardInter a b <= cardInter c d.

Hypothesis union_up : forall a b c d,
 a <= c -> b <= d -> cardUnion a b <= cardUnion c d.

Hypothesis union_inc_1 : forall a b, a <= cardUnion a b.
Hypothesis union_inc_2 : forall a b, b <= cardUnion a b.

Hypothesis select_up : forall n n', n <= n' -> cardSelect n <= cardSelect n'.
Hypothesis select_inc : forall n, n = cardSelect n.

(* units = time to compare two tuples or construct one tuple *)

(* (cost, relation size) *)
Hypothesis F: forall I, DBSet I.
Hypothesis G: Ctx.
Hypothesis E: Env F G.

Fixpoint costDenote (I: Typing) (e: raExp _ I) : (nat * nat) :=
  match e with
    | varExp i r0 => (FS.cardinal (lookup r0 i E), FS.cardinal (lookup r0 i E))
    | unionExp d r r0 =>
      match costDenote r , costDenote r0 with
        | (rc, rs) , (r0c, r0s) =>
          (rc + r0c + (rs * r0s), cardUnion rs r0s)
      end
    | interExp d r r0 =>
      match costDenote r , costDenote r0 with
        | (rc, rs) , (r0c, r0s) =>
          (rc + r0c + (rs * r0s), cardInter rs r0s)
      end
    | selectExp d r f  =>
      match costDenote r with
        | (rc, rs) => (rc + rs, cardSelect rs)
      end
    | emptyExp _ => (0, 0)
    | gprojExp d f pf r => match costDenote r with
                            | (rc, rs) =>
                              (rc + rs, rs)
                          end
    | prodExp i j r r0 => match costDenote r , costDenote r0 with
                            | (rc, rs) , (r0c, r0s) =>
                              (rc + r0c + (rs * r0s), rs * r0s)
                          end
  end.

Definition cost_decreasing (f: ra_rewrite) : Prop :=
 forall I e, fst (costDenote (f I e)) <=
                   fst (costDenote  e).

Lemma id_rewrite_cost_decreasing : cost_decreasing id_rewrite.
Proof.
 unfold cost_decreasing. unfold id_rewrite.
 intros. omega.
Qed.

(* Showing decreasing cost is mostly a matter of arithmetic
   under <=.  These facts/axioms about the cost model are also used: *)

Lemma ob1 : forall x y,
  min x y = x -> x <= y.
Proof. 
intros.
pose (le_min_r x y).
pose (le_min_l x y).
rewrite H in l. assumption.
Qed.

Lemma ob2 : forall x y,
 min x y = y -> y <= x.
intros. apply ob1. rewrite (min_comm y x ). assumption.
Qed.

(* Omega doesn't always solve these systems, so these
   lemmas essentially act like push lemmas for <= + *.
   There is no doubt a setoid structure here. *)
Lemma rem_plus: forall a b c d,
 a <= c -> b <= d -> a + b <= c + d.
Proof.
 intros. omega.
Qed.

Lemma rem_times' : forall a b c,
 b <= c -> a * b <= a * c.
Proof.
 intros. induction a.
  simpl. omega.
  simpl in *. apply rem_plus. assumption. assumption.
Qed.

Require Import Mult.

Lemma rem_times : forall a b c d,
 a <= c -> b <= d -> a * b <= c * d.
Proof.
 intros.
 apply mult_le_compat. assumption. assumption.
Qed. 

(* The rest of these lemmas are somewhat arbitrary places
   where omega got stuck. *)
Lemma zero_lt : forall x, 0 <= x.
Proof.
 intros. omega.
Qed.

Lemma omega_confuse : forall n n0 n1 n3 n4 n5,
 n3 <= n -> n4 <= n0 -> n5 <= n1 ->
  n3 + n4 + n3 * n5 <= n + n0 + n * n1.
Proof.
 intros. apply rem_plus. omega. apply rem_times. 
 assumption. assumption.
Qed.

Lemma omega_confuseH : forall n5 n6 n3 n4 n1 n n2 n0,
 n5 + n6 <= n3 + n4 ->
  n6 <= n4 ->
   n1 <= n ->
  n2 <= n0 ->
   n5 + n6 + n1 + n6 * n2 <= n3 + n4 + n + n4 * n0.
Proof.
 intros.
 apply rem_plus. apply rem_plus. assumption. assumption.
 apply rem_times. assumption. assumption.
Qed.

Lemma omega_confuseX : forall n n2 n3 n4 n0 n5 n1 n6,
 n3 <= n -> n4 <= n0 -> n5 <= n1 -> n6 <= n2 ->
   n3 + n5 + n4 * n6 <= n + n1 + n0 * n2.
Proof.
 intros.
 apply rem_plus. apply rem_plus. assumption. assumption.
 apply rem_times. assumption. assumption.
Qed.

Lemma omega_confuse1 : forall n0 n2 n4 n6,
 n4 <= n0 -> n6 <= n2 -> n4 * n6 <= n0 * n2.
Proof.
 intros. apply rem_times. assumption. assumption. 
Qed.

Lemma omega_confuse2 : forall n0 n2 n4 n6,
 n4 <= n0 -> n6 <= n2 -> n4 + n6 <= n0 + n2.
Proof.
 intros. apply rem_plus. assumption. assumption.
Qed.

Lemma jj : forall x, x - 0 = x.
 intros. omega.
Qed.

Lemma jjj : forall n0 n2, n2 <= n0 -> n2 <= cardUnion 0 n0.
intros. pose (union_inc_2 0 n0). 
omega.
Qed.

Lemma kkk: forall n5 n6 n3 n4 n1 n2 n n0,
  n5 + n6 <= n3 + n4 ->
  cardSelect n6 <= cardSelect n4 ->
  n1 <= n ->
  n2 <= n0 ->
   n5 + n6 + n1 + cardSelect n6 * n2 <= n3 + n4 + n + cardSelect n4 * n0.
Proof.
 intros.
 apply rem_plus. omega. apply rem_times. assumption. assumption.
Qed.

Lemma mmm : forall n5 n6 n3 n4 n1 n2 n n0,
  n5 + n6 <= n3 + n4 ->
  cardSelect n6 <= cardSelect n4 ->
   n1 <= n ->
   n2 <= n0 ->
   cardUnion (cardSelect n6) n2 <= cardUnion (cardSelect n4) n0.
Proof.
 intros. apply union_up. assumption. assumption.
Qed.

Lemma nnn : forall n9 n3 n n10 n4 n7 n1 n8 n2 n5 n0 n6,
  n9 + n3 + n10 * n4 <= n7 + n1 + n8 * n2 ->
 cardInter n10 n4 <= cardInter n8 n2 ->
  n5 <= n ->
  n6 <= n0 ->
   n9 + n3 + n10 * n4 + n5 + cardInter n10 n4 * n6 <=
   n7 + n1 + n8 * n2 + n + cardInter n8 n2 * n0.
Proof.
intros. 
 apply rem_plus. omega. apply rem_times. assumption. assumption.
Qed.

Lemma uuu : forall n12 n6 n11 n7 n1 n8 n2 n5 n n0,
  n11 <= n7 + n1 + n8 * n2 ->
   n12 <= cardUnion n8 n2 ->
  n5 <= n ->
   n6 <= n0 ->
   n11 + n5 + n12 * n6 <= n7 + n1 + n8 * n2 + n + cardUnion n8 n2 * n0.
Proof.
 intros. apply rem_plus. omega. apply rem_times. assumption. assumption.
Qed.

Lemma vvv : forall n n6 n7 n1 n8 n2 n12 n0 n5 n11,
   n11 <= n7 + n1 + n8 * n2 ->
   n12 <= cardUnion n8 n2 ->
  n5 <= n ->
   n6 <= n0 ->
   cardUnion n12 n6 <= cardUnion (cardUnion n8 n2) n0.
Proof.
 intros. apply union_up. assumption. assumption.
Qed.

Lemma xxx : 
forall (I : Typing) (e : raExp _ I),
   fst (costDenote (id_rewrite_2 e)) <= fst (costDenote e) /\
   snd (costDenote (id_rewrite_2 e)) <= snd (costDenote e) .
Proof.
 intros;
  induction e;
   try (simpl; omega);
   try (simpl;
        destruct (costDenote e1);
        destruct (costDenote e2);
        destruct (costDenote (id_rewrite_2 e1));
        destruct (costDenote (id_rewrite_2 e2));
        destruct IHe1; destruct IHe2; simpl in *;
        split; [ apply omega_confuseX; try assumption | 
          try (apply card_up; try assumption);
          try (apply inter_up; try assumption);
          try (apply omega_confuse1) ]; 
 try assumption  );
 try (simpl in *;
  destruct (costDenote e);
  destruct (costDenote (id_rewrite_2 e));
  destruct IHe; simpl in *; split;
  try apply omega_confuse2; try assumption; try apply select_up; try assumption).
  apply union_up; auto.
Qed.
 
Lemma id_rewrite2_cost_decreasing : cost_decreasing id_rewrite_2.
Proof.
 unfold cost_decreasing. intros.
 pose (xxx e). destruct a. assumption.
Qed.

Lemma yyy :
forall (I : Typing) (e : raExp _ I),
   fst (costDenote (empty_cancel_rewrite e)) <= fst (costDenote e) /\
   snd (costDenote (empty_cancel_rewrite e)) <= snd (costDenote e) .
Proof.
 intros;
  induction e;
   try (simpl; omega);
    try (simpl;
        destruct (costDenote e);
        destruct (costDenote (empty_cancel_rewrite e));
        destruct IHe; simpl in *;
           split; try omega; apply card_up2; omega);
try (simpl;
        destruct (costDenote e1);
        destruct (costDenote e2);
        destruct (costDenote (empty_cancel_rewrite e1));
        destruct (costDenote (empty_cancel_rewrite e2));
        destruct IHe1; destruct IHe2; simpl in *; 
        split; [ apply omega_confuseX; try assumption |
                 try (apply omega_confuse'; try assumption);
                 try (apply omega_confuse1; try assumption);
                 try (apply omega_confuse''; try assumption) ] );
    (try apply inter_up; try assumption).

simpl in *.
 destruct e1; simpl in *;
 try (destruct (costDenote e2);
    destruct (costDenote (empty_cancel_rewrite e2));
    destruct (costDenote e1);
    destruct (costDenote (empty_cancel_rewrite e1));
    simpl in *; destruct IHe2; destruct IHe1; split; [ try (apply kkk; assumption);
                                                       try (apply omega_confuseH; assumption) 
                                                     | try (eapply mmm; eassumption); 
                                                       try (apply union_up; assumption) ] );
  try (destruct (costDenote e2);
       destruct (costDenote e1_2);
       destruct (costDenote (empty_cancel_rewrite e1_2));
       destruct (costDenote (empty_cancel_rewrite e2));
       destruct (costDenote e1_1);
       destruct (costDenote (empty_cancel_rewrite e1_1));
       simpl in *; destruct IHe2; destruct IHe1; split; [ try (apply nnn; assumption); 
                                                          try (apply kkk; assumption);
                                                          try (apply omega_confuseH; assumption) 
                                                     | try (eapply mmm; eassumption); 
                                                       try (apply union_up; assumption) ]).
2 : destruct (costDenote e2);
    destruct (costDenote (empty_cancel_rewrite e2));
    simpl in *; destruct IHe2; split; [ apply omega_confuse2; try apply omega_confuse2; try omega; try assumption;
                                        apply omega_confuse1; omega | apply union_up; omega; assumption ].
1 : destruct (costDenote e2);
    destruct (costDenote (empty_cancel_rewrite e2));
    simpl in *; destruct IHe2; split; [ omega | apply jjj; trivial ].
 
 remember (
   costDenote 
            match e1_1 in (raExp _ t) return (raExp (fun _ : Typing => string) I) with
            | emptyExp _ => empty_cancel_rewrite e1_2
            | varExp _ _ =>
              @unionExp (fun _ : Typing => string) I
              (@empty_cancel_rewrite  I e1_1)
              (@empty_cancel_rewrite  I e1_2)
            | unionExp _ _ _ =>
                unionExp (empty_cancel_rewrite e1_1)
                  (empty_cancel_rewrite e1_2)
            | interExp _ _ _ =>
                unionExp (empty_cancel_rewrite e1_1)
                  (empty_cancel_rewrite e1_2)
            | selectExp _ _ _ =>
                unionExp (empty_cancel_rewrite e1_1)
                  (empty_cancel_rewrite e1_2)
            | gprojExp _ _ _ _ =>
                unionExp (empty_cancel_rewrite e1_1)
                  (empty_cancel_rewrite e1_2)
            | prodExp _ _ _ _ =>
                unionExp (empty_cancel_rewrite e1_1)
                  (empty_cancel_rewrite e1_2) 
            end); simpl in *.
 rewrite <- Heqp in H2. rewrite <- Heqp in H1. rewrite <- Heqp.
 destruct p.
 apply uuu; assumption .

   remember (
   costDenote 
            match e1_1 with
            | emptyExp _ => empty_cancel_rewrite e1_2
            | varExp _ _ =>
                unionExp (empty_cancel_rewrite e1_1)
                  (empty_cancel_rewrite e1_2)
            | unionExp _ _ _ =>
                unionExp (empty_cancel_rewrite e1_1)
                  (empty_cancel_rewrite e1_2)
            | interExp _ _ _ =>
                unionExp (empty_cancel_rewrite e1_1)
                  (empty_cancel_rewrite e1_2)
            | selectExp _ _ _ =>
                unionExp (empty_cancel_rewrite e1_1)
                  (empty_cancel_rewrite e1_2)
            | gprojExp _ _ _ _ =>
                unionExp (empty_cancel_rewrite e1_1)
                  (empty_cancel_rewrite e1_2)
            | prodExp _ _ _ _ =>
                unionExp (empty_cancel_rewrite e1_1)
                  (empty_cancel_rewrite e1_2) 
            end); simpl in *. 
 rewrite <- Heqp in H2. rewrite <- Heqp in H1. rewrite <- Heqp.
 destruct p.
 eapply vvv; eassumption .

 simpl. destruct (costDenote e); destruct (costDenote (empty_cancel_rewrite e)); simpl in *.
 intuition.
Qed.

Lemma empty_cancel_rewrite_decrease : cost_decreasing empty_cancel_rewrite.
Proof.
 unfold cost_decreasing.  
 intros. pose (yyy e). destruct a. assumption.
Qed.

Ltac gpdest :=
  match goal with
    [|- context[match ?X with | (_, _) => _ end] ] => destruct X
  end.

Require Import Arith.

Lemma sel_rw_cost_decreasingIH :
forall (I : Typing) (e : raExp _ I),
   fst (costDenote (sel_rw e)) <= fst (costDenote e) /\
   snd (costDenote (sel_rw e)) <= snd (costDenote e) .
Proof.
  induction e; simpl; auto; repeat gpdest; simpl in *; intuition;
    try solve [apply rem_plus; [omega| apply rem_times; auto]].

    induction w; simpl; try omega;
      generalize dependent (sel_rw e); destruct r; simpl; 
        intros; try omega; auto; repeat gpdest; simpl in *; auto; try omega.
    
    induction w; simpl; try omega;
      generalize dependent (sel_rw e); destruct r; simpl; 
        intros; try omega; auto; repeat gpdest; simpl in *; auto; try omega;
          pose (select_inc n0); omega.

    apply rem_times; auto.
Qed.

Lemma sel_rw_decrease : cost_decreasing sel_rw.
Proof. red. intros. eapply sel_rw_cost_decreasingIH. Qed.

(* An example cost model *)

Definition cardInter' (a b: nat) := min a b. 
Definition cardUnion' (a b: nat) := a + b.
Definition cardSelect' (a: nat) := a.

Lemma inter_up' : forall a b c d,
 a <= c -> b <= d -> cardInter' a b <= cardInter' c d.
Proof.
 intros. unfold cardInter'.
 destruct (min_dec a b).
 destruct (min_dec c d).
 rewrite e. rewrite e0. assumption.
 rewrite e. rewrite e0. 
  assert (a <= b). apply ob1; assumption.
  assert (d <= c). apply ob2. assumption. omega.
 destruct (min_dec c d).
  assert (b <= a). apply ob2; assumption.
  assert (c <= d). apply ob1. assumption. omega.
 rewrite e. rewrite e0. assumption.
Qed. 

Lemma union_up' : forall a b c d,
 a <= c -> b <= d -> cardUnion' a b <= cardUnion' c d.
Proof.
 unfold cardUnion'. intros. omega.
Qed. 

Lemma union_inc_1' : forall a b, a <= cardUnion' a b.
Proof.
 intros. unfold cardUnion'. omega.
Qed.

Lemma union_inc_2' : forall a b, b <= cardUnion' a b.
Proof.
 intros. unfold cardUnion'. omega.
Qed.

Lemma select_up' : forall n n', 
n <= n' -> cardSelect' n <= cardSelect' n'.
Proof.
 unfold cardSelect'. intros. omega.
Qed.

Lemma select_inc' : forall n, n = cardSelect' n.
Proof.
 unfold cardSelect'. intros. omega.
Qed.

End CostEst.

(* should move to relationalmodel *)

Ltac redep := match goal with
   | [H: _ = _ |- _ ] => generalize H; 
        rewrite <- H; clear H; intro H; rewrite <- !eq_rec_eq; clear H
 end.

Lemma raDenote_eq_rec_eq_rec : forall F G E I J pfx r,
  raDenote (F:=F)  
  (inst (F:=F) (G:=G) E
    (eq_rec I (fun t : Typing => raExp (fun _ : Typing => string) t) r J pfx))
  == eq_rec I (fun t : Typing => DBRel (F t)) 
  (raDenote (inst (F:=F) (G:=G) E r)) J pfx.
intros.
induction r; simpl;
  redep; try reflexivity.
Qed.

(* Semantic Optimization ***************************************************)

(* Semantic optimizations get to use Info about the database.
   They should conditionally rewrite based on this information. *)
Definition ra_sem_rewrite : Type :=
 Info -> ra_rewrite.
 
Definition sem_preserving (f: ra_sem_rewrite) : Prop :=
 forall F G (E: Env F G) m I (e: raExp (fun _ : Typing => string) I), 
   accurate m E -> 
   (raDenote (F:=F) (inst E e)) == 
   (raDenote (F:=F) (inst E (f m I e))).

Definition id_sem : ra_sem_rewrite := fun m => id_rewrite_2.

Lemma id_sem_preserve : sem_preserving id_sem.
Proof.
 unfold sem_preserving. 
 intros.
 induction e.
  simpl. reflexivity.
  simpl. reflexivity.
  simpl. rewrite (IHe1 ). rewrite (IHe2 ). reflexivity.
  simpl. rewrite (IHe1 ). rewrite (IHe2 ). reflexivity.
  simpl. rewrite (IHe ). reflexivity.
  simpl. rewrite (IHe ). reflexivity.
  simpl. rewrite (IHe1 ). rewrite (IHe2 ). reflexivity.
Qed.

Definition var_remove (m: Info) I
 (e: raExp (fun _ : Typing => string) I) : 
     raExp (fun _ : Typing => string) I.
intros m.
refine (fix var_remove (I: Typing) (e: raExp _ I) : raExp _ I :=
  match e as e' in raExp _ I' return raExp _ I' with
    | emptyExp i => emptyExp _ i
    | varExp i r0 => 
      if tbl_empty (m r0 i)
        then emptyExp _ i
        else varExp r0
    | unionExp i r r0 =>  unionExp (var_remove i r) (var_remove i  r0)
    | interExp i r r0 => interExp (var_remove i  r) (var_remove i  r0)
    | selectExp i r f =>  selectExp (var_remove i  r) f 
    | gprojExp i l pf r =>  @gprojExp _ i l pf (@var_remove i  r)
    | prodExp  i J0 r0 r1 =>  
      prodExp (var_remove i  r0) (var_remove _  r1)
  end ).
Defined. 

Lemma var_rem_preserve : sem_preserving var_remove.
Proof.
 intros.   
 unfold sem_preserving.
 induction e.
  simpl. reflexivity.
  simpl. intros. pose (H v I). clearbody y. destruct (m v I).
   simpl. destruct tbl_empty. simpl in *. assumption.
   simpl in *. reflexivity.
   simpl. intros. rewrite (IHe1 ). rewrite (IHe2 ). reflexivity. assumption. assumption.
   simpl. intros. rewrite (IHe1 ). rewrite (IHe2 ). reflexivity. assumption. assumption.
   simpl. intros. rewrite (IHe ). reflexivity.  assumption. 
   simpl. intros. rewrite (IHe ). reflexivity.  assumption.
   simpl. intros. rewrite (IHe1 ). rewrite (IHe2 ). reflexivity.  assumption. assumption. 
Qed.

Definition natlist_eq_dec : forall (l l': list nat), {l = l'} + {l <> l'}.
intros. repeat decide equality.
Qed.

Definition proj_prod_opt (m: Info) 
 (I: Typing) (e: raExp (fun _ : Typing => string) I) : raExp (fun _ : Typing => string) I.
intros m.
refine (fix proj_prod_opt (I: Typing) (e: raExp (fun _ : Typing => string) I) 
  : raExp (fun _ : Typing => string) I :=
  match e as e' in raExp _ I' return I = I' -> raExp (fun _ : Typing => string) I' with
    | emptyExp i => fun pf2 => emptyExp _ i
    | varExp i r0 => fun pf2 =>  varExp r0 
    | unionExp i r r0 => fun pf2 =>  unionExp (proj_prod_opt i r) (proj_prod_opt i r0)
    | interExp i r r0 => fun pf2 =>  interExp (proj_prod_opt i r) (proj_prod_opt i r0)
    | selectExp i r f => fun pf2 =>  selectExp (proj_prod_opt i r) f 
    | gprojExp i l pf r =>  fun pf2 => 
      match r in raExp _ J return i = J -> _ with 
        (* yay! we found a proj of a product *)
        | prodExp i0 J1 r0 r1 => fun pf3 => 
            match r1 with
              | varExp jj vv =>  
                match tbl_empty (m vv jj) with
                  | true =>  gprojExp pf (proj_prod_opt _  r)
                  | false => 
                    match natlist_eq_dec l (seq 0 (length i0)) with        
                      | left pf1 =>  _
                      | right pf1 => gprojExp pf (proj_prod_opt _  r)
                    end
                end
              | _ => gprojExp pf (proj_prod_opt _  r)
            end
        | _ =>  fun pf3 => gprojExp pf (proj_prod_opt _  r)
      end (refl_equal _)
    | prodExp  i J0 r0 r1 => fun pf2 =>  
      prodExp (proj_prod_opt i r0) (proj_prod_opt _ r1)
  end (refl_equal _) ).
  clear e r r1 . 
  subst i. subst I. subst l.  
 erewrite <-  ( @nth_seq_eq nil i0 J1).
 apply proj_prod_opt.
 exact r0.
Defined.

Lemma sd' : forall F I I0
(  d : DBRel (A:=I0) (F I0))
(  y : d =/= empty0 F I0),
   forall (pf : bounded (I ++ I0) (seq 0 (length I)))
     (e : I = nthTyps (l:=seq 0 (length I)) (I:=I ++ I0) pf)
     (d0 : DBRel (A:=I) (F I)),
   gprojRel (F:=F) (l:=seq 0 (length I)) (I:=I ++ I0) pf
     (prodRel (F:=F) (I:=I) (J:=I0) d0 d) ==
   eq_rec I (fun t : Typing => DBRel (A:=t) (F t)) d0
     (nthTyps (l:=seq 0 (length I)) (I:=I ++ I0) pf) e.
Proof.
 intros.
 rewrite (@proj1_prod_id F I I0 d0 d pf y).
 rewrite (cast1_pf_irrel (u:=fun x : Typing => DBRel (A:=x) (F x)) d0 (nth_seq0_eq pf) e).
 clear. destruct e. reflexivity.
Qed.

Lemma sd : sem_preserving proj_prod_opt.
Proof.
 intros.   
 unfold sem_preserving.
 intros. 
 induction e.
  simpl. reflexivity.
  simpl. reflexivity.
   simpl. intros. rewrite (IHe1 ). rewrite (IHe2 ). reflexivity. 
   simpl. intros. rewrite (IHe1 ). rewrite (IHe2 ). reflexivity. 
   simpl. intros. rewrite (IHe ). reflexivity.

Focus 2.
   simpl. intros. rewrite (IHe1 ). rewrite (IHe2 ). reflexivity.

  destruct e. 
   simpl. reflexivity.
   simpl. reflexivity.
   simpl. rewrite IHe. simpl. reflexivity.
   simpl. rewrite IHe. simpl. reflexivity.
   simpl. rewrite IHe. simpl. reflexivity.
   simpl. rewrite IHe. simpl. reflexivity.
   
   destruct e2; try (simpl; rewrite IHe; reflexivity).

   simpl in *. 

   remember (tbl_empty (m s I0)).
   destruct b;  try (simpl; rewrite IHe; reflexivity).

   destruct (natlist_eq_dec l (seq 0 (length I)));
    try (simpl; rewrite IHe; reflexivity).

 unfold eq_rec_r. rewrite <- eq_rec_eq. 
 generalize pf. clear pf. 
 generalize e. rewrite e. simpl.
 intros. rewrite <- eq_rec_eq. clear e. clear l. clear e0.
 pose (H s I0). rewrite <- Heqb in y.
 remember ((lookup (F:=F) s I0 (G:=G) E)).
 clear Heqd. clear Heqb. clear H. simpl in *.
 rewrite IHe.

 generalize (proj_prod_opt m e1). 
 generalize ((nth_seq_eq (K:=nil) (I:=I) (J:=I0) pf)).
 intros. 
 rewrite (@raDenote_eq_rec_eq_rec F G E I _ e).
 generalize ((raDenote (F:=F) (inst (F:=F) (G:=G) E r))).
 clear r. clear IHe G E m e1. clear s. 
 generalize dependent pf. simpl.
 apply sd'. assumption.
Qed.

Definition optimize' m I (e: raExp _ I) := 
 proj_prod_opt m (empty_cancel_rewrite (proj_proj (sel_rw e))).

Theorem thm1 : sem_preserving optimize'.
Proof.
 unfold sem_preserving.
 unfold optimize'.
 intros.
 rewrite (@sel_rw_preserve _).
 rewrite (@proj_proj_preserve _).
 rewrite (@empty_cancel_rewrite_preserve _).
 rewrite (@sd _ _ _ m).
  reflexivity. assumption.
Qed.

Require Import Ynot.
Open Scope hprop_scope.
Open Scope stsep_scope.
Require Import FSetInterfaceNM.
Definition optimize F m I G (E: [Env F G]) (e: raExp _ I) :
 STsep (E ~~ [accurate (F:=F) m E])
       (fun e': raExp _ I => E ~~ 
         [ (raDenote (inst E e)) [=] raDenote (inst E e')] * [accurate (F:=F) m E]).
intros. 
refine ( {{ Return optimize' m e <@> (E ~~ [accurate (F:=F) m E]) }} ).
sep fail auto.
sep fail auto.
cut (Equal (raDenote (F:=F) (inst (F:=F) (G:=G) x e))
      (raDenote (F:=F) (inst (F:=F) (G:=G) x (optimize' m e)))).
intros. sep fail auto.
pose (@thm1 F G x m I e H) . 
unfold DBRel.
rewrite <- equivIsEqual in *. assumption.
Qed.
