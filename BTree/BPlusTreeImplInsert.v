(* Copyright (c) 2009, Harvard University
 * All rights reserved.
 *
 * Authors: Gregory Malecha
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

Require Import Ynot Array.
Require Import Peano_dec Compare_dec.
Require Import Minus Div2.
Require Import Even.
Require Import Think ThinkList ThinkArith.

Require Import BPlusTreeImplModel.
Require Import BPlusTreeTactics.
Require Import BPlusTreeImplLookup.


Require Import OrderedTypeNM.
Require Import Setoid SetoidClass.
Require Import LiftOrder.

Set Implicit Arguments.

Section BPlusTreeImpl.

  Variable SIZE : nat.
  Variable pfMin : SIZE > 1.
  Variable SIZE_even : even SIZE.

  Variable key : Set.
  Variable value : key -> Set.

  (** Ordering on Keys **)
  Variable KOT : OrderedType key.
  Variable value_eq : forall k1 k2 : key, k1 == k2 -> value k1 = value k2.

  Notation "'SIZE_S'" := (SIZE_S pfMin).
  Notation "'ptree'" := (ptree value).
  Notation "'rep''"    := (rep' SIZE value).
  Notation "'repBranch'" := (repBranch value).
  Notation "'repBranch_nextPtr'" := (repBranch_nextPtr value).
  Notation "'key_between'" := (key_between KOT).
  Notation "'KLsorted'" := (KLsorted KOT).
  Notation "'contextual'" := (contextual value KOT).
  Notation "'lastKey'" := (lastKey).
  Notation "'inv'" := (inv value KOT).
  Notation "'Model'" := (Model value).
  Notation "'as_map'" := (as_map value).
  Notation "'repLeaf'" := repLeaf.
  Notation "'lastPtr'" := (lastPtr value).
  Notation "'firstPtr'" := (firstPtr value).
  Notation "'ptrFor'" := (ptrFor value).
  Notation "'rep'" := (@rep SIZE key value KOT value_eq).
  Notation "'BranchCell' h" := (sigTS (fun _:key => ptree h)) (at level 50).
  Notation "'MinK'" := (@MinK key).
  Notation "'MaxK'" := (@MaxK key).
  Notation "'BptMap'" := BptMap.
  Notation "'tH'" := (tH value).

  Opaque BPlusTreeImplModel.inv.
  Opaque BPlusTreeImplModel.MinK.
  Opaque BPlusTreeImplModel.MaxK.

  Open Local Scope hprop_scope.
  Open Local Scope stsepi_scope.


  (** Specification **)
  Hypothesis tK : key.
  Hypothesis tV : value tK.
  Definition RT := option (value tK).
  Definition Q (mpre : Model) (rt : option (value tK)) (mpost : Model) :=
    [rt = specLookup _ value_eq tK mpre] * [mpost = specInsert _ tK tV mpre].
  
  Lemma KLsorted_weakApp : forall i oh min mid max,
    KLsorted value min i mid ->
    KLsorted value mid oh max ->
    KLsorted value min (i ++ oh) max.
  Proof.
    intros.
    apply (KLsorted_app KOT i oh max min).
    split.
      eapply KLsorted_narrow_max; eauto.
      eapply sorted_prop_le; eauto; intuition.
      apply KLsorted_lastkey_lt_max. auto.
  Qed.

  Lemma inv0_sort p x0 x1 x: inv 0 (p, x1) x0 x = KLsorted value x0 x1 x.
    reflexivity.
  Qed.

  Lemma InsertLocalTail : forall (ol i : list (sigTS value)) (min' min max : LiftOrder key),
    KLsorted _ min i max ->
    KLsorted _ min' ol min ->
    key_between min tK max ->
    specInsert KOT tK tV (ol ++ i) = ol ++ specInsert KOT tK tV i.
  Proof. Transparent BPlusTreeImplModel.KLsorted. unfold BPlusTreeImplModel.key_between. 
    induction ol.
      simpl; intros. unfold BPlusTreeImplModel.KLsorted in H0. destruct H0; auto.

      intros. destruct H0. destruct H1.
      cut (Val (projT1S a) <<= min); intros.
      simpl. destruct (ordCompare (projT1S a) tK).
        f_equal. eapply IHol; eauto. 
        elimtype False. destruct H4.
          rewrite e in H4. rewrite H4 in H1. order.
          rewrite e in H4. rewrite H4 in H1. order.
        elimtype False. destruct H4.
          rewrite H1 in H4. simpl in H4. rewrite o in H4. order.
          rewrite <- H4 in H1. simpl in H1. rewrite o in H1. order.
     eapply sorted_min_max. eauto.
  Qed.

  Lemma InsertLocalHead : forall (i oh : list (sigTS value)) (min max max' : LiftOrder key),
    KLsorted _ min i max ->
    KLsorted _ max oh max' ->
    key_between min tK max ->
    specInsert KOT tK tV (i ++ oh) = specInsert KOT tK tV i ++ oh.
  Proof. Transparent BPlusTreeImplModel.KLsorted. unfold BPlusTreeImplModel.key_between. 
    induction i.
      simpl; intros. unfold BPlusTreeImplModel.KLsorted in H. destruct H.
      destruct oh. simpl. auto.
      simpl. destruct H1. destruct H0.
      destruct (ordCompare (projT1S s) tK).
        elimtype False. rewrite H0 in H2. destruct H2. 
           simpl in H2. rewrite o in H2. order.
           simpl in H2. rewrite H2 in o. order.
        elimtype False. destruct H2.
          rewrite H0 in H2. rewrite e in *. order.
          rewrite e in H0. rewrite H2 in H0. order.
        auto.
      destruct oh. simpl. auto.
      simpl. destruct H1. destruct H0.
      destruct (ordCompare (projT1S s) tK).
        elimtype False. destruct H2. 
          rewrite <- H2 in H0. simpl in H0. rewrite o in H0. order.
          rewrite <- H2 in H0. simpl in H0. rewrite o in H0. order.
        elimtype False.  destruct H2.
          rewrite <- H2 in H0. simpl in H0. rewrite e in H0. order.
          rewrite <- H2 in H0. simpl in H0. rewrite e in H0. order.
        auto.
      
      intros. simpl. destruct H1. destruct H.
      destruct (ordCompare (projT1S a) tK); try reflexivity; eauto.
        simpl. f_equal. eauto.
  Qed.

  Theorem HimpInsert : forall (min' min max max' : LiftOrder key) (i i' ol oh : list (sigTS value)) rt,
    KLsorted _ min i max ->
    KLsorted _ min i' max ->
    KLsorted _ min' ol min ->
    KLsorted _ max oh max' ->
    key_between min tK max ->
    Q i rt i' ==> Q (ol ++ i ++ oh) rt (ol ++ i' ++ oh).
  Proof. unfold Q.
    intros. intro_pure.
    repeat rewrite specLookup_append.
    cut (specLookup KOT value_eq tK oh = None); intros. rewrite H6.
    cut (specLookup KOT value_eq tK ol = None); intros. rewrite H7.

    erewrite InsertLocalTail. erewrite InsertLocalHead; eauto.
    destruct (specLookup KOT value_eq tK i); sep fail auto.
      Focus 2. eauto. instantiate (1 := max').
      eapply KLsorted_weakApp; eauto.
      destruct H3. split. auto. apply sorted_min_max in H2. rewrite H8. auto.
      eapply specLookup_lt_all; eauto.
      unfold BPlusTreeImplModel.key_between in H3. tauto.
      eapply specLookup_gt_all; eauto.
      unfold BPlusTreeImplModel.key_between in H3. tauto.
  Qed.

  (** Other pure facts **)

  Global Instance proper_Val_lt {A:Set} {s:OrderedType A} :
  Proper (ordLt ==> ordLt) (@Val A). 
  Proof. unfold Proper, respectful; auto. Qed.

  Global Instance lastKey_prop : Proper (eq ==> equiv ==> equiv) (lastKey (key:=key) (T:=value)).
  Proof. unfold Proper, respectful; induction x; simpl; intros; subst; simpl; intuition. Qed.

  Global Instance lastKey_prop_le : Proper (eq ==> ordLe ==> ordLe) (lastKey (key:=key) (T:=value)).
  Proof. unfold Proper, respectful; induction x; simpl; intros; subst; simpl; intuition. Qed.

  Lemma specInsert_lastKey' : forall x1 x0 x, (** MOVE **)
    lastKey x1 x0 << Val tK ->
    KLsorted value x0 x1 x ->
    specInsert KOT tK tV x1 = x1 ++ existTS value tK tV :: nil.
  Proof.
    intros x1 x0 x l i. 
    revert x0 x l i.
    induction x1; simpl; intuition. destruct a; simpl in *. destruct i.
    fold sorted in *. simpl projT1S in *.
    destruct (ordCompare x2 tK); simpl.
      eauto.
      elimtype False. revert H H0 l e. clear.
      induction x1; simpl; intuition; 
        try (rewrite e in l; elim (ordLt_irrefl l)).
       apply H0; auto.
        eapply sorted_prop_le; eauto; intuition. left; auto.
        pose (@ordLe_ordLt_trans _ _ (lastKey (key:=key) (T:=value) x1 (Val x2))) as o.
        eapply o; eauto.
        rewrite H1. apply ordLt_irrefl.

      elimtype False. revert H H0 l o. clear.
      induction x1; simpl; intuition; 
        try (rewrite o in l; elim (ordLt_irrefl l)).
       apply H0; auto.
        eapply sorted_prop_le; eauto; intuition. left; auto.
        pose (@ordLe_ordLt_trans _ _ (lastKey (key:=key) (T:=value) x1 (Val x2))) as o'.
        eapply o'; eauto.
        rewrite H1. apply ordLt_irrefl.
  Qed.

  Lemma specInsert_lastKey : forall p x1 x0 x, (** MOVE **)
    lastKey x1 x0 << Val tK ->
    inv 0 (p, x1) x0 x ->
    specInsert KOT tK tV x1 = x1 ++ existTS value tK tV :: nil.
  Proof.
    intros. rewrite inv0_sort in H0. eapply specInsert_lastKey'; eauto.
  Qed.

  Lemma replaceNth_nil T i (kv:T) : replaceNth i nil kv = kv::nil.
  Proof.
    unfold replaceNth. simpl. intros.  norm list. auto.
  Qed.

  Lemma replaceNth_shift T i a x1 (kv:T) : replaceNth (S i) (a :: x1) kv = a::replaceNth i x1 kv.
  Proof.
    unfold replaceNth. intros. simpl. auto.
  Qed.

  Lemma replaceNth0 T a x1 (kv:T) : replaceNth 0 (a :: x1) kv = kv::x1.
  Proof.
    unfold replaceNth. intros. simpl. auto.
  Qed.

  Hint Rewrite replaceNth_nil replaceNth_shift replaceNth0 : norm_list_rw.
  Hint Immediate replaceNth_nil replaceNth_shift replaceNth0: norm_list.

  Lemma KLsorted_add_last : forall x1 x0 max x,
    lastKey x1 x0 << Val tK -> KLsorted value x0 x1 max -> Val tK <<= x ->
    KLsorted value x0 (x1 ++ existTS value tK tV :: nil) x.
  Proof.
  intros.
  apply <- (KLsorted_app KOT x1 (existTS value tK tV::nil)). split.
    eapply KLsorted_narrow_max; eauto.
  constructor; auto.
  Qed.

  Lemma inv_replaceNth : forall p x1 x0 x i k' v',
    inv 0 (p, x1) x0 x ->
    Some (existTS value k' v') = nth_error x1 i ->
    k' == tK ->
    inv 0 (p, replaceNth i x1 (existTS value tK tV)) x0 x.
  Proof.
    intros p x1 x0 x n k' v' i. rewrite inv0_sort in *. clear p.
    revert x0 x n k' v' i. induction x1; simpl; intuition.
      norm list in *; discriminate.
      destruct n; norm list; simpl in *; inversion i; fold sorted in *;
        destruct a; simpl projT1S in *.
        inversion H; subst.
        rewrite H0 in H1.
        constructor; auto; simpl.
        eapply sorted_prop; eauto; right; try rewrite H0; reflexivity.
      
        inversion i; constructor; auto.
        eapply IHx1; eauto.
   Qed.

   Lemma sorted_nth_lt_max x1 x n k' v' a: (nth_error x1 n) = (Some (existTS _ k' v')) ->
     KLsorted value (Val a) x1 x -> a << k'.
   Proof.
     induction x1; simpl; intros. 
       norm list in H. discriminate.
       inversion H0; fold sorted in *.
       destruct n; norm list in H.
         destruct a; inversion H. subst. auto.
         eapply IHx1; eauto.
         eapply sorted_prop_le; eauto; intuition.
         left. apply H1. reflexivity.
   Qed.

   Lemma specInsert_replaceNth : forall p x1 x0 x i k' v',
     inv 0 (p, x1) x0 x ->
     Some (existTS value k' v') = nth_error x1 i ->
     k' == tK ->
     replaceNth i x1 (existTS value tK tV) = specInsert KOT tK tV x1.
   Proof. intros p x1 x0 x n k' v' i. rewrite inv0_sort in *. clear p.
     revert x0 x n k' v' i.
     induction x1; simpl; intros. 
       norm list; auto.
       destruct n; norm list; norm list in H.
         destruct a; inversion H; subst; simpl; elim_comp_eq x2 tK; auto.

         inversion i; fold sorted in *.
         erewrite IHx1; eauto.
         elim_comp_lt (projT1S a) tK; auto.
         rewrite <- H0.
         eapply sorted_nth_lt_max; eauto.
   Qed.

   Require Import Eqdep.
   Lemma specLookup_replaceNth : forall p x1 x0 x i k' v' (pf : k' == tK),
     inv 0 (p, x1) x0 x ->
     Some (existTS value k' v') = nth_error x1 i ->
     Some
     match value_eq k' tK pf in (_ = x4) return x4 with
       | eq_refl => v'
     end = specLookup KOT value_eq tK x1.
   Proof.
     intros p x1 x0 x n k' v' pf i. rewrite inv0_sort in *. clear p.
     revert x0 x n k' v' pf i.
     induction x1; simpl; intros. 
       norm list in H; discriminate.
       destruct n; norm list in H.
         destruct a; inversion H; subst; simpl.
         destruct (equiv_dec x2 tK); [|contradiction].
         generalize (value_eq x2 tK pf);
         generalize (value_eq _ _ e).
         intros. generalize e0 e1. rewrite <- e0.
         intros. rewrite (UIP_refl _ _ e2); rewrite (UIP_refl _ _ e3).
         auto.

       inversion i; fold sorted in *.
       erewrite IHx1; eauto.
       destruct (equiv_dec (projT1S a) tK); auto.
       destruct a; simpl projT1S in *.
       pose (sorted_nth_lt_max _ _ _ _ (eq_sym H) H1).
       rewrite e, pf in o.
       eelim ordLt_irrefl; eauto.
  Qed.
    
  Lemma length_insert : forall T (X : T) x1 i s0 max,
    nth_error (X :: skipn i x1) (max - i) = Some s0 ->
    length (firstn i x1) = i ->
    length (firstn max (firstn i x1 ++ X :: skipn i x1)) = max.
  Proof.
    intros. apply firstn_length_l. rewrite app_length. simpl.
    rewrite H0.
    pose (len:=nth_error_len' _ _ H). simpl in len. 
    omega.
  Qed.

  Lemma length_insert'' : forall x1 i, i <= SIZE ->
    length (existTS value tK tV :: skipn i x1) <= SIZE - i ->
    length (firstn i x1) = i -> 
    length (firstn i x1 ++ existTS value tK tV :: skipn i x1) <= SIZE.
  Proof.
    intros. rewrite app_length. rewrite H1.
    omega.
  Qed.

  Lemma lookup_too_early l k min max :
       KLsorted value min l max
    -> Val k << min 
    -> specLookup KOT value_eq k l = None.
  Proof.
    induction l; auto; intros.
    destruct a; inversion H; simpl. fold sorted in *.
    rewrite H1 in H0.
    destruct (equiv_dec x k).
      rewrite e in H0. elim (ordLt_irrefl H0).
      eapply IHl; eauto.
  Qed.

  Lemma KLsorted_min_lastKey l min max : KLsorted value min l max -> min <<= lastKey l min.
  Proof.
    induction l; simpl; intuition.
    inversion H; fold sorted in *.
    rewrite H0. eauto.
  Qed.

  Lemma lookup_too_late' l k min max :
       KLsorted value min l max
    -> lastKey l min << Val k  
    -> specLookup KOT value_eq k l = None.
  Proof.
    induction l; auto; intros.
    destruct a; inversion H; simpl. fold sorted in *; simpl projT1S in *.
    simpl lastKey in H0.
    rewrite (IHl _ _ _ H2 H0).
    destruct (equiv_dec x k); auto.
    rewrite <- e in H0.
    rewrite <- (KLsorted_min_lastKey _ _ _ H2) in H0.
    abstraction.
  Qed.

  Lemma lookup_too_late l k min max :
       KLsorted value min l max
    -> max << Val k  
    -> specLookup KOT value_eq k l = None.
  Proof.
    intros. eapply lookup_too_late'; eauto.
    rewrite (KLsorted_lastkey_lt_max _ _ _ _ H). auto.
  Qed.

  (* TODO: copied from BPlusTreeImplLookup. move! *)
  Require Import Eqdep.
  Lemma specLookup_append : forall (a b : Model) k,
    specLookup KOT value_eq k (a ++ b) = match specLookup KOT value_eq k a with
                                           | None => specLookup KOT value_eq k b
                                           | Some x => Some x
                                         end.
  Proof.
    induction a. auto.
    simpl. intros. destruct (equiv_dec (projT1S a) k); intros; auto.
      destruct a. simpl in *. clear.
      generalize dependent v. generalize (value_eq _ _ e).
      intro. generalize dependent e. generalize e0. rewrite e0. intros. 
      rewrite (UIP_refl _ _ e1). auto.
  Qed.

  Lemma lookup_not_in_mid l1 l2 min mid1 mid2 max k :
       KLsorted value min l1 mid1
    -> KLsorted value mid2 l2 max
    -> mid1 << Val k  
    -> Val k << mid2
    -> specLookup KOT value_eq k (l1++l2) = None.
  Proof.
    intros.
    rewrite specLookup_append.
    erewrite lookup_too_late, lookup_too_early; eauto.
  Qed.

  Lemma KLsorted_split_around x1 i k' v' k min max:
    Some (existTS value k' v') = nth_error x1 i -> 
    k << k' ->
    (KLsorted value min x1 max 
  -> 
   (KLsorted value min (firstn i x1) (Val k') /\
    KLsorted value (Val k) (skipn i x1) max)).
  Proof.
    induction x1; intros. 
      norm list in H; discriminate.
    inversion H1. fold sorted in *.
    destruct i; simpl; norm list in H.
      destruct a; inversion H; simpl in *. subst.
      intuition. constructor; auto.
    split.
      constructor; auto. eapply IHx1; eauto.
      eapply IHx1; eauto.
  Qed.

  Lemma sorted_minlast l i min max :
       KLsorted value min l max
    -> min <<= lastKey (firstn i l) min.
  Proof.
    induction l; intros.
      norm list. simpl. reflexivity.
    inversion H; fold sorted in *.
    destruct i; simpl.
     reflexivity.
   rewrite (IHl i _ max).
     rewrite H0. reflexivity.
     eapply sorted_prop_le; eauto; intuition.
     left; auto.
  Qed.

  Lemma specLookup_None' : forall x1 x0 x k' i v',
    KLsorted value x0 x1 x ->
    tK << k' -> 
    lastKey (firstn i x1) x0 << Val tK ->
    Some (existTS value k' v') = nth_error x1 i ->
    None = specLookup KOT value_eq tK x1.
  Proof.
    induction x1; intros. norm list in H2; discriminate.
    inversion H; fold sorted in *.
    destruct i; simpl in H2; destruct a; inversion H2; subst; simpl;
      destruct (equiv_dec x2 tK). 
      false_order. 
      symmetry; eapply lookup_too_early; eauto.
      simpl firstn in H1. simpl lastKey in H1.
      rewrite <- e in H1. simpl in H4.
    elim (ordLt_nle H1). eapply sorted_minlast; eauto.
    eapply IHx1; eauto. simpl in *. auto.
  Qed.


  Lemma KLsorted_split_insert : forall x1 x0 x k' i v' ,
       KLsorted value x0 x1 x
    -> tK << k' 
    -> lastKey (firstn i x1) x0 << Val tK
    -> Some (existTS value k' v') = nth_error x1 i
    -> KLsorted value x0
      (firstn i x1 ++ existTS value tK tV :: skipn i x1) x.
  Proof.
    intros.
    destruct (KLsorted_split_around _ _ _ _ _ H2 H0 H).
    apply <- (KLsorted_app KOT (firstn i x1) (existTS value tK tV :: skipn i x1)). split.
      eapply KLsorted_narrow_max; eauto.
      constructor; auto.
  Qed.

  Lemma KLsorted_min_le_max l1 min max : KLsorted value min l1 max -> min <<= max.
  Proof.
    intros. transitivity (lastKey l1 min).
      eapply KLsorted_min_lastKey; eauto.
      eapply KLsorted_lastkey_lt_max; eauto.
  Qed.

  Lemma KLsorted_boundin x1 i min x s0 n:
    KLsorted value min (skipn n x1) x
    -> nth_error (skipn i x1) (n - i) = Some s0
    -> KLsorted value min (s0 :: nil) x.
  Proof.
    induction x1; intros.
    norm list in H0. discriminate.
    destruct i. simpl in *. norm arith in H0.
      destruct n; simpl in *.
        inversion H0. subst. inversion H. constructor; auto.
        eapply KLsorted_min_le_max; eauto.

        eapply IHx1 with (i:=0); eauto. norm arith. auto.
        
      simpl in *.
      destruct n; simpl in *.
        inversion H; fold sorted in *.
        pose (wholesort:=H2). clearbody wholesort.
        rewrite <- (firstn_skipn i x1) in H2.
        destruct (skipn i x1); try discriminate.
        inversion H0; subst.
        apply -> (KLsorted_app _ (firstn i x1) (s0 :: l)) in H2. destruct H2.
        inversion H3. fold sorted in *.
        constructor.
          rewrite H1.
          pose (KLsorted_min_lastKey _ _  _ H2).
          rewrite o. auto.
          
          pose (KLsorted_min_lastKey _ _  _ H5).
          rewrite o.
          pose (KLsorted_lastkey_lt_max _ _  _ _ H5).
          auto.

        eapply IHx1; eauto.
  Qed.

  Lemma KLsorted_addend : forall x1 x0 x i s0,
       KLsorted value x0 x1 x
    -> nth_error (skipn i x1) (SIZE - i) = Some s0
    -> KLsorted value x0 (firstn SIZE x1 ++ s0 :: nil) x.
  Proof.
    intros.
    rewrite <- (firstn_skipn SIZE x1) in H.
    apply -> (KLsorted_app KOT (firstn SIZE x1) (skipn SIZE x1)) in H.
    destruct H.
    eapply KLsorted_weakApp.
    eapply H.
    eapply KLsorted_boundin; eauto.
  Qed.

  Lemma KLsorted_split' : forall x1 x0 x k' i v' s0,
       KLsorted value x0 x1 x
    -> tK << k' 
    -> lastKey (firstn i x1) x0 << Val tK
    -> Some (existTS value k' v') = nth_error x1 i
    -> nth_error (existTS value tK tV :: skipn i x1) (SIZE - i) = Some s0
    -> KLsorted value x0
      (firstn SIZE (firstn i x1 ++ existTS value tK tV :: skipn i x1) ++
        s0 :: nil) x.
  Proof.
    intros.
    eapply KLsorted_addend with (i:=i).
    eapply KLsorted_split_insert; eauto.
    norm list. norm arith. simpl. 
    rewrite firstn_length_l. norm arith. auto.
    symmetry in H2. apply nth_error_len' in H2. omega.
  Qed.

  Lemma specLookup_end : forall x1 x i x0,
    KLsorted value x0 x1 x ->
    i = length x1 ->
    lastKey (firstn i x1) x0 << Val tK ->
    None = specLookup KOT value_eq tK x1.
  Proof.
    intros. subst. norm list in H1. symmetry.
    eapply lookup_too_late; [eapply KLsorted_narrow_max|]; eauto.
  Qed.

  Lemma KLsorted_end : forall x1 i x0 x,
    KLsorted value x0 x1 x ->
    Val tK <<= x ->
    i = length x1 ->
    lastKey (firstn i x1) x0 << Val tK ->
    KLsorted value x0 (x1 ++ existTS value tK tV :: nil) x.
  Proof.
    intros. subst. norm list in H2.
    eapply KLsorted_weakApp.
    eapply KLsorted_narrow_max; eauto.
    constructor; auto.
  Qed.

  Lemma specInsert_end : forall x1 x i x0,
    KLsorted value x0 x1 x ->
    i = length x1 ->
    lastKey (firstn i x1) x0 << Val tK ->
    x1 ++ existTS value tK tV :: nil = specInsert KOT tK tV x1.
  Proof.
    intros. subst. norm list in H1. symmetry. eapply specInsert_lastKey'; eauto.
  Qed.

  (** Implementation **)
  Require Import ArrayOps.
  Require Import BPlusTreeImplLocalComputeHelp.

  Notation "'op'" := (BPlusTreeImplLocalComputeHelp.op key).
  Notation "'repOp'" := (@BPlusTreeImplLocalComputeHelp.repOp SIZE key value KOT).
  Notation "'opModel'" := (@BPlusTreeImplLocalComputeHelp.opModel key value).
  Notation "'as_mapOp'" := (BPlusTreeImplLocalComputeHelp.as_mapOp value).
  Notation "'firstPtrOp'" := (@BPlusTreeImplLocalComputeHelp.firstPtrOp key value).

  Definition RES (n : nat) := (RT * sigT (fun o:op => [opModel n o]%type))%type.

  Definition P  := __.

  Section splitFn.

    Lemma nth_error_match_eta : forall T (x1 : list T) i,
      match nth_error (firstn (S i) x1) i with
        | Some v => Some v
        | None => None
      end = nth_error x1 i.
    Proof. clear.
      intros. norm list. destruct (nth_error x1 i); auto.
    Qed.
    Hint Immediate nth_error_match_eta.

    Lemma sorted_lastKey : forall x1 min max,
      KLsorted value min x1 max -> lastKey x1 min <<= max. 
    Proof. clear.
      induction x1. auto.
        intros. destruct H. simpl.
        eapply IHx1. unfold BPlusTreeImplModel.KLsorted. auto.
    Qed.
    Lemma sorted_lastKey_default : forall x1 min max,
      KLsorted value min x1 max -> min <<= lastKey x1 min.
    Proof.
      induction x1. simpl; intuition.
      unfold BPlusTreeImplModel.KLsorted in *. simpl; intros. destruct H.
      specialize (IHx1 _ _ H0). rewrite <- IHx1. left. auto. 
    Qed.

    Lemma length_firstn_hint : forall T (x1 : list T),
      length (firstn (S (div2 SIZE)) x1) <= SIZE.
    Proof.
      intros. cut (length (firstn (S (div2 SIZE)) x1) <= S (div2 SIZE)); eauto with norm_list_length.
    Qed.
    Lemma length_skipn_hint : forall T (x1 : list T) val,
      length x1 = SIZE ->
      length (skipn (S (div2 SIZE)) (x1 ++ val :: nil)) <= SIZE.
    Proof.
      intros. rewrite length_skipn. rewrite app_length. simpl. norm arith. rewrite H. rewrite <- (twice_half SIZE) at 1; auto. rewrite <- (twice_half SIZE) at 4; auto.
      omega.
    Qed.

    Lemma skipn_app_first : forall T i (ls ls' : list T),
      i <= length ls -> skipn i (ls ++ ls') = skipn i ls ++ ls'.
    Proof.
      induction i; destruct ls; intros; norm list.
        auto. auto. simpl in *. elimtype False; omega. simpl in *; apply IHi; auto.
    Qed.

    Lemma KLsorted_firstn : forall x2 x0 v x val,
      Some v = nth_error x2 (div2 SIZE) ->
      length x2 = SIZE ->
      KLsorted value x0 (x2 ++ val :: nil) x ->
      KLsorted value x0 (firstn (S (div2 SIZE)) x2) (Val (projT1S v)).
    Proof.
      intros. rewrite <- (firstn_skipn (S (div2 SIZE)) x2) in H1.
      repeat rewrite app_ass in H1. 
      destruct (KLsorted_app _ (firstn (S (div2 SIZE)) x2) (skipn (S (div2 SIZE)) x2 ++ val :: nil) x x0).
      specialize (H2 H1). destruct H2.
      erewrite firstn_nth_error_expand in H2; try (symmetry; eassumption).
      erewrite firstn_nth_error_expand; try (symmetry; eassumption).
      rewrite lastKey_last in *; auto.
    Qed.
    Lemma KLsorted_skipn : forall x2 x0 v x val,
      Some v = nth_error x2 (div2 SIZE) ->
      KLsorted value x0 (x2 ++ val :: nil) x ->
      KLsorted value (Val (projT1S v)) (skipn (S (div2 SIZE)) (x2 ++ val :: nil)) x.
    Proof. clear.
      intros. rewrite <- (firstn_skipn (S (div2 SIZE)) x2) in H0.
      repeat rewrite app_ass in H0.
      destruct (KLsorted_app _ (firstn (S (div2 SIZE)) x2) (skipn (S (div2 SIZE)) x2 ++ val :: nil) x x0).
      specialize (H1 H0). destruct H1. clear H2.
      cutrewrite (skipn (S (div2 SIZE)) (x2 ++ val :: nil) = skipn (S (div2 SIZE)) x2 ++ val :: nil).
      erewrite firstn_nth_error_expand in H3; try (symmetry; eassumption). rewrite lastKey_last in *. auto.
      cut (S (div2 SIZE) <= length x2); eauto with norm_list_length; intros. 
      rewrite skipn_app_first; auto.
    Qed.
    Lemma specInsert_holds : forall x1 x2 val,
      length x2 = SIZE ->
      specInsert KOT tK tV x1 = x2 ++ val :: nil ->
      firstn (S (div2 SIZE)) x2 ++ skipn (S (div2 SIZE)) (x2 ++ val :: nil) = specInsert KOT tK tV x1.
    Proof.
      intros; rewrite H0.
      rewrite skipn_app_first. repeat rewrite <- app_ass. rewrite firstn_skipn. auto.
      rewrite H. destruct SIZE; try solve [ elimtype False; omega ].  destruct n; try solve [ elimtype False; omega ]. auto.
    Qed.

    Lemma exc2opt_id : forall T (x: option T), exc2opt x = x. (** defined elsewhere **)
      destruct x; auto.
    Qed.
    Lemma div2x_lt_x : forall x, x > 1 -> div2 x < x. 
      induction x using ind_0_1_SS; intros; try solve [ elimtype False; omega ]. auto.
    Qed.

    Hint Resolve length_skipn_hint KLsorted_firstn KLsorted_skipn length_firstn_hint specInsert_holds.

  Opaque firstn skipn nth_error.
  Definition splitFn : forall (p : ptr) (ary : array) (nxt : option ptr) (val : sigTS value)
    (ls ls' : [list (sigTS value)]) (min max : [LiftOrder key]),
    STsep (ls ~~ ls' ~~ min ~~ max ~~ 
            p ~~> mkNode 0 ary nxt *
            {@ p :~~ array_plus ary i in
              p ~~> exc2opt (nth_error ls i) | i <- 0 + SIZE } *
            [length ls = SIZE] * [length ls' = SIZE] * 
            [KLsorted value min (ls ++ val :: nil) max] *
            [specInsert _ tK tV ls' = ls ++ val :: nil] * [None = specLookup _ value_eq tK ls'] * [array_length ary = SIZE])
          (fun res:RES 0 => ls' ~~ min ~~ max ~~ m :~~ projT2 (snd res) in
            repOp 0 (projT1 (snd res)) m min max nxt * Q ls' (fst res) (as_mapOp _ _ m) *
            [firstPtrOp _ _ m = p]).
    refine (fun p ary nxt val ls ls' min max =>      
      aryR <- @array_splitEnd _ _ ary SIZE val [val]%inhabited (fun x:sigTS value => x) ls _ SIZE_even <@> _ ;
      pR <- New (mkNode 0 aryR nxt) ;
      p ::= mkNode 0 ary (Some pR) ;;
      kv <- sub_array ary (div2 SIZE) (fun v:option (sigTS value) => ls ~~
        [v = nth_error ls (div2 SIZE)]) <@> _;
      let _:option (sigTS value) := kv in
      match kv as kv' return kv = kv' -> _ with
        | None   => fun pfKv => {{ !!! }}
        | Some v => fun pfKv =>
          {{ Return (None, existT (fun o:op => [opModel 0 o]%type) 
                               (Split p (projT1S v) pR)
                               (ls ~~~ ((p, firstn (S (div2 SIZE)) ls), (pR, skipn (S (div2 SIZE)) (ls ++ val :: nil))))) }}
      end (refl_equal _)); try rewrite pfKv in *.
  Proof.
    solve [ auto ].
    solve [ sep2 fail bpt_elim; sep_unify ].
    solve [ sep_unify ].
    solve [ sep_unify ].
    solve [ sep_unify ].
    solve [ sep2 fail bpt_elim; sep_unify ].
    solve [ sep_unify ].

    solve [ sep2 fail bpt_elim; sep_unify ].
    solve [ sep_unify ].
    solve [ sep_unify ].
    sep2 fail bpt_elim.
      generalize dependent x4. rewrite H6 in *; clear H6. norm pair in *.
      cbv [BPlusTreeImplLocalComputeHelp.repOp]. unfold Q. intros.
      unfold BPlusTreeImplModel.rep'. red_prems. rewrite <- H4; clear H4.
      unfold BPlusTreeImplModel.repLeaf. norm pair. sep2 fail bpt_elim. norm arith.
    sep2 fail bpt_elim.      
        rewrite exc2opt_id. norm arith. norm list. auto.
        norm arith.
      search_prem ltac:(search_conc ltac:(apply himp_split; [ apply iter_imp | ])).
        sep fail auto; norm arith. auto. 
      search_prem ltac:(search_conc ltac:(apply himp_split; [ apply iter_imp | ])).
        sep fail auto; norm arith. auto.
      search_prem ltac:(search_conc ltac:(apply himp_split; [ apply iter_imp | ])).
        sep fail auto; norm arith. auto.
      Transparent BPlusTreeImplModel.inv. unfold BPlusTreeImplModel.inv.
      simpl. solve [ sep2 fail bpt_elim; sep_unify ].

    sep2 fail bpt_elim. elimtype False.
      cut (length x2 <= div2 SIZE); eauto with norm_list_length.
      cut (div2 SIZE < SIZE); try omega.
      apply div2x_lt_x; auto.
    sep fail auto.
  Qed.

  End splitFn.


  Section insertFn.
      
    Lemma split_specLookup : forall (x1 : list (sigTS value)) x0 x,
      KLsorted _ x0 x1 x ->
      lastKey x1 x0 << Val tK ->
      None = specLookup KOT value_eq tK x1.
    Proof. Transparent BPlusTreeImplModel.inv BPlusTreeImplModel.KLsorted.
      unfold BPlusTreeImplModel.KLsorted in *.
      induction x1; simpl; intros; auto.
        destruct (equiv_dec (projT1S a) tK).
          elimtype False. destruct H.
          cut (Val (projT1S a) << Val tK). intros. rewrite e in *. order.
          clear e.

      generalize (sorted_lastKey_default _ _ _ H1); intros.
      rewrite <- H2 in H0. auto.
        
      destruct H. specialize (IHx1 _ _ H1). auto.
    Qed.

    Hint Immediate specInsert_lastKey split_specLookup.

    Hint Immediate exc2opt_id.
    Lemma length_recur : forall T i (x:T) x1,
      Some x = nth_error x1 i ->
      S i <= length x1.
    Proof.
      intros. cut (i < length x1); eauto with norm_list_length.
    Qed.

    Lemma lastKey_recur : forall k' v' x1 i x0,
      k' << tK ->
      Some (existTS value k' v') = nth_error x1 i ->
      lastKey (firstn (S i) x1) x0 << Val tK.
    Proof.
      intros. erewrite firstn_nth_error_expand; try (symmetry; eassumption).
      rewrite lastKey_last. auto.
    Qed.
    Hint Resolve length_recur lastKey_recur.

    Lemma exc2opt_nth_error_replace_nth : forall x1 i,
      i < length x1 ->
      Some (existTS value tK tV) = exc2opt (nth_error (replaceNth i x1 (existTS value tK tV)) (i - 0)).
    Proof.
      unfold replaceNth. intros. norm list. cutrewrite (length (firstn i x1) = i); eauto with norm_list_length.
      norm arith. auto.
    Qed.
    Hint Resolve exc2opt_nth_error_replace_nth.

    Lemma himp_iter_replaceNth_prefix : forall x1 i ary,
      i <= length x1 ->
      {@hprop_unpack (array_plus ary i0) (fun p0 : ptr => p0 ~~> exc2opt (nth_error x1 i0)) | i0 <- (0) + i} ==>
      {@hprop_unpack (array_plus ary i0)
        (fun p0 : ptr => p0 ~~> exc2opt (nth_error (replaceNth i x1 (existTS value tK tV)) (i0 - 0))) | i0 <- (0) + i}.
    Proof.
      intros; apply iter_imp; intros. sep fail auto. unfold replaceNth. norm arith.
      rewrite nth_error_app_first; [ | cut (length (firstn i x1) = i ); eauto with norm_list_length ].
      norm list. auto.
    Qed.
    Lemma himp_iter_replaceNth_suffix : forall x1 i ary,
      i <= length x1 ->
      {@hprop_unpack (array_plus ary i0) (fun p0 : ptr => p0 ~~> exc2opt (nth_error x1 i0)) | i0 <- (S i) + SIZE - S i} ==>
      {@hprop_unpack (array_plus ary i0)
        (fun p0 : ptr =>
          p0 ~~>
          exc2opt (nth_error (replaceNth i x1 (existTS value tK tV)) (i0 - 0)))
        | i0 <- (S i) + SIZE - S i}.
    Proof.
      intros; apply iter_imp; sep fail auto. norm arith. unfold replaceNth. 
      rewrite nth_error_app_second; [ | eauto with norm_list_length ].
      cut (length (firstn i x1) = i); eauto with norm_list_length; intros. rewrite H3.
      Change (i0 - i) into (S (i0 - S i)) using omega. norm list.
      f_equal; f_equal; omega.
    Qed.
    Hint Resolve himp_iter_replaceNth_prefix himp_iter_replaceNth_suffix.

    Hint Resolve inv_replaceNth specInsert_replaceNth specLookup_replaceNth length_replaceNth.

    Lemma reindexing1 : forall T i (x1 x3 : list T) ary,
      skipn i x1 = x3 ->
      {@hprop_unpack (array_plus ary i0)
        (fun p0 : ptr => p0 ~~> exc2opt (nth_error x1 i0)) | i0 <- (S i) + SIZE - S i} ==>
      {@hprop_unpack (array_plus ary i0)
        (fun p0 : ptr =>
          p0 ~~>
          match nth_error x3 (i0 - i) with
            | Some v => Some v
            | None => None
          end) | i0 <- (S i) + pred (SIZE - i)}.
    Proof.
      intros. Change (SIZE - S i) into (pred (SIZE - i)) using omega.
      apply iter_imp; sep fail auto. norm list.
      Change (i + (i0 - i)) into i0 using omega. destruct (nth_error x1 i0); sep fail auto.
    Qed.
    Hint Resolve reindexing1.

    Lemma key_between_right : forall a b c,
      key_between a b c -> Val b <<= c.
    Proof. unfold BPlusTreeImplModel.key_between; intuition. Qed.
    Hint Immediate key_between_right.

    Lemma length_bound_replaceNth : forall T i x1 (X:T),
      i < SIZE -> length x1 <= SIZE -> i <= length x1 ->
      length (replaceNth i x1 X) <= SIZE.
    Proof.
      unfold replaceNth. intros; rewrite app_length.
      destruct (lt_eq_lt_dec  i (length x1)). destruct s. 
      cutrewrite (length (firstn i x1) = i); eauto with norm_list_length.
      cut (length (skipn (S i) x1) = length x1 - S i); intros.
      simpl in *. rewrite H2. omega.
      apply length_skipn.
      norm list. simpl. omega.
      elimtype False. omega.
    Qed.
    Lemma specInsert_split' : forall k' v' x1 i x0 x s0 max,
      tK << k' -> length x1 <= max ->
      Some (existTS value k' v') = nth_error x1 i ->
      KLsorted value x0 x1 x ->
      nth_error (existTS value tK tV :: skipn i x1) (max - i) = Some s0 ->
      lastKey (firstn i x1) x0 << Val tK ->
      specInsert KOT tK tV x1 =
        firstn max (firstn i x1 ++ existTS value tK tV :: skipn i x1) ++ s0 :: nil.
    Proof.
      induction x1; simpl; intros.
        norm list in H1; discriminate.
        destruct i. norm list in *. inversion H1. simpl.
        elim_comp_gt k' tK. rewrite <- H6 in *.
        norm arith in *.
        cut (max < length (existTS value tK tV :: existTS value k' v' :: x1)); eauto with norm_list_length; intros.
        simpl length in H5. cut (max = S (length x1)); eauto; intros. subst. norm list. f_equal.
        norm list in H3. rewrite <- firstn_nth_error_expand; eauto. norm list. auto.

        elim_comp_lt (projT1S a) tK.
        destruct max. elimtype False; omega. rewrite firstn_red_S. rewrite skipn_red_S.
        simpl app. f_equal. eapply IHx1; eauto. destruct H2. intuition eauto.
        norm list in H4. simpl in H4. auto.
        
        destruct H2.  rewrite <- (firstn_skipn i x1) in H5. destruct (KLsorted_app _ (firstn i x1) (skipn i x1) x (Val (projT1S a))).
        apply H6 in H5. destruct H5. eapply sorted_min_max in H5.
        cut (Val (projT1S a) << Val tK); auto. destruct H5. rewrite H5. auto. rewrite H5. auto.
      Qed.
      Lemma length_is_SIZE : forall T x1 (X : T) i s0,
        length x1 <= SIZE -> i <= length x1 ->
        nth_error (X :: skipn i x1) (SIZE - i) = Some s0 ->
        length x1 = SIZE.
      Proof.
        intros. cut (SIZE - i < length (X :: skipn i x1)); eauto with norm_list_length; intros.
        simpl in H2. rewrite length_skipn in H2. omega. 
      Qed.

      Lemma KLsorted_insert : forall x0 x1 x k' i v',
        KLsorted value x0 x1 x ->
        lastKey  (firstn i x1) x0 << Val tK ->
        tK << k' ->
        Some (existTS value k' v') = nth_error x1 i ->
        KLsorted value x0 (firstn i x1 ++ existTS value tK tV :: skipn i x1) x.
      Proof.
        intros.
        rewrite <- (firstn_skipn i x1) in H.
        apply -> (KLsorted_app _ (firstn i x1) (skipn i x1)) in H. destruct H.
        eapply KLsorted_weakApp. eauto.
        constructor; eauto. simpl. erewrite nth_error_skipn_cons in *; eauto.
        destruct H3. simpl. intuition.
      Qed.

      Lemma specInsert_insert : forall x0 x1 x k' i v',
        KLsorted value x0 x1 x ->
        lastKey  (firstn i x1) x0 << Val tK ->
        tK << k' -> 
        Some (existTS value k' v') = nth_error x1 i ->
        firstn i x1 ++ existTS value tK tV :: skipn i x1 = specInsert KOT tK tV x1.
      Proof.
        intros. symmetry. rewrite <- (firstn_skipn i x1) at 1.
        rewrite <- (firstn_skipn i x1) in H. destruct (KLsorted_app _ (firstn i x1) (skipn i x1) x x0).
        apply H3 in H. erewrite InsertLocalTail.
        f_equal. erewrite nth_error_skipn_cons; eauto. simpl. elim_comp_gt k' tK. auto.
        destruct H; eassumption. destruct H; eassumption. split; auto.
        destruct H. erewrite nth_error_skipn_cons in H5; eauto. simpl in H5. destruct H5. eapply sorted_min_max in H6.
        simpl projT1S in *. destruct H6. left. rewrite H1. auto. rewrite H1. right. auto.
      Qed.

  Definition insertFn : forall (p : ptr) (ary : array) (nxt : option ptr)
    (ls : [list (sigTS value)]) (min max : [LiftOrder key]),
    STsep (ls ~~ min ~~ max ~~
            p ~~> mkNode 0 ary nxt * repLeaf ary 0 SIZE ls * [KLsorted _ min ls max] *
            [key_between min tK max] * [length ls <= SIZE] * [array_length ary = SIZE] * P)
          (fun r:RES 0 => min ~~ max ~~ ls ~~ m :~~ projT2 (snd r) in
            repOp 0 (projT1 (snd r)) m min max nxt * Q ls (fst r) (as_mapOp _ _ m) *
            [firstPtrOp _ _ m = p]).
    refine (fun p ary nxt ls min max =>
      {{ Fix (fun (n:nat) => min ~~ max ~~ ls ~~
               p ~~> mkNode 0 ary nxt *
               {@ p :~~ array_plus ary i in
                 p ~~> exc2opt (nth_error ls i) | i <- 0 + SIZE } *
               [n <= length ls] * [n <= SIZE] * [length ls <= SIZE] *
               [lastKey (firstn n ls) min << Val tK] * [key_between min tK max] *
               [inv 0 (p,ls) min max] * [array_length ary = SIZE])
             (fun _ (res:RES 0) => min ~~ max ~~ ls ~~ m :~~ projT2 (snd res) in
               repOp 0 (projT1 (snd res)) m min max nxt * Q ls (fst res) (as_mapOp _ _ m) *
               [firstPtrOp _ _ m = p])
             (fun self i =>
               if le_lt_dec SIZE i then
                 {{ splitFn p ary nxt (existTS value tK tV) ls ls min max }}
               else
                 okv <- sub_array ary i (fun v:option (sigTS value) => ls ~~ 
                   [v = nth_error ls i]) <@> _ ;
                 match okv as okv' return okv = okv' -> _ with 
                   | None => fun pfOkv => 
                     upd_array ary i (Some (existTS _ tK tV)) <@> _ ;;
                     {{ Return (None, existT (fun o:op => [opModel 0 o]%type) (Merge key p) (ls ~~~ (p, ls ++ existTS _ tK tV :: nil))) }}
                   | Some (existTS k' v') => fun pfOkv => 
                     match ordCompare k' tK with
                       | LT _  => {{ self (S i) <@> _ }}
                       | EQ pf => 
                         upd_array ary i (Some (existTS _ tK tV)) <@> _ ;; 
                         {{ Return (Some 
                         match value_eq _ _ pf in _ = x return x with
                           | refl_equal => v'
                         end, existT (fun o:op => [opModel 0 o]%type) (Merge key p) (ls ~~~ (p, replaceNth i ls (existTS _ tK tV)))) }}
                       | GT _ => 
                         extra <- array_shiftInsert ary i (SIZE - i) (existTS _ tK tV) [existTS _ tK tV]%inhabited (fun x => x) (ls ~~~ skipn i ls) <@> _ ;
                         match extra as extra' return extra = extra' -> _ with
                           | None    => fun pfExtra =>
                             {{ Return (None, existT (fun o:op => [opModel 0 o]%type) (Merge key p) (ls ~~~ (p, firstn i ls ++ existTS value _ tV :: skipn i ls))) }}
                           | Some v' => fun pfExtra =>
                             {{ splitFn p ary nxt v' (ls ~~~ firstn SIZE (firstn i ls ++ existTS value _ tV :: skipn i ls)) ls min max }}
                         end (refl_equal _)
                     end
                 end (refl_equal _)) 0 }});
    try clear self; try rewrite pfOkv in *; try unfold Q; try rewrite pfExtra in *.
  Proof.
    Hint Resolve KLsorted_add_last.
    solve [ sep2 ltac:(combine_le_le) bpt_elim; norm list; sep2 fail bpt_elim; sep_unify ].
    solve [ sep2 fail bpt_elim; sep_unify ].

    solve [ sep2 fail bpt_elim; sep_unify ].
    solve [ sep_unify ].
    solve [ sep2 fail bpt_elim; [ rewrite H3; symmetry; auto | sep_unify ] ].
    solve [ sep2 fail bpt_elim; sep_unify ].
  
    solve [ sep2 fail bpt_elim; sep_unify ].
    solve [ sep_unify ].
    solve [ sep_unify ].
    sep2 fail bpt_elim.
      generalize dependent x3. rewrite H4 in *; clear H4. Opaque BPlusTreeImplModel.inv. simpl.
      intros; red_prems. rewrite <- H3 in *; clear H3. simpl. norm arith.
      unfold BPlusTreeImplModel.repLeaf. do 2 sep2 ltac:(norm arith) bpt_elim. norm arith.
      Hint Immediate length_bound_replaceNth.
      sep2 fail bpt_elim. norm arith. sep2 fail bpt_elim. sep_unify.
    
    sep2 fail bpt_elim. 
      rewrite <- H3. norm list. norm arith. rewrite <- H5; auto.
      norm arith.
      solve [ sep2 fail bpt_elim; sep_unify ].
    solve [ sep_unify ].
    sep2 fail bpt_elim.
      case_eq (nth_error (x2 :: x3) (SIZE - i)); intros; rewrite H14 in *; try discriminate.
      search_conc ltac:(eapply himp_rsubst; [ eapply join_sep; eapply H7 | ]). 
      cut (length (firstn i x1) = i); eauto with norm_list_length; intros.
      search_prem ltac:(search_conc ltac:(apply himp_split; [ apply iter_imp | ])).
        sep fail auto. rewrite <- H4. norm list. auto.
      search_prem ltac:(search_conc ltac:(apply himp_split; [ apply iter_imp | ])).
        sep fail auto. rewrite <- H4. rewrite <- H2. norm list. rewrite H15. rewrite <- H3. auto.
      rewrite <- H4. rewrite H13 in *. rewrite <- H2 in *. rewrite <- H3 in *. inversion H5.

      Hint Resolve length_insert specLookup_None' KLsorted_split'.
      Transparent BPlusTreeImplModel.inv. simpl in H11.
      Hint Immediate specInsert_split' length_is_SIZE.
      solve [ sep2 fail bpt_elim; sep_unify ].
    
    solve [ sep2 fail bpt_elim; sep_unify ].
    solve [ eapply himp_refl_emp ].
    sep2 fail bpt_elim.
      generalize dependent x4. rewrite H6 in *. simpl. 
      intros; red_prems. rewrite <- H4 in *. simpl. sep2 fail bpt_elim.
      rewrite <- H3 in *. rewrite <- H2 in *.
      cut (length (firstn i x1) = i); eauto with norm_list_length; intros.
      search_conc ltac:(eapply himp_rsubst; [ eapply join_sep; try eapply H8 | ]). norm arith.
      search_prem ltac:(search_conc ltac:(apply himp_split; [ apply iter_imp | ])).
        sep2 fail bpt_elim. norm list. norm arith. auto. sep fail auto.
      search_prem ltac:(search_conc ltac:(apply himp_split; [ apply iter_imp | ])).
        sep2 fail bpt_elim; auto. norm arith. norm list. rewrite H20. auto.
      Hint Resolve length_insert'' KLsorted_insert specInsert_insert.
      solve [ sep2 fail bpt_elim; sep_unify ].

    solve [ sep2 fail bpt_elim; sep_unify ].
    solve [ sep_unify ].
    solve [ sep_unify ].
    sep2 fail bpt_elim.
      generalize dependent x3. rewrite H4 in *; clear H4. simpl.
      intros; red_prems. rewrite <- H3 in *; clear H3. simpl. sep2 fail bpt_elim.
      unfold BPlusTreeImplModel.repLeaf.
      cut (length x1 <= i); eauto with norm_list_length; intros. combine_le_le.
      sep2 fail bpt_elim.
        norm list. rewrite <- H16. norm arith. norm list. auto.
      norm arith.
      search_prem ltac:(search_conc ltac:(apply himp_split; [ apply iter_imp | ])).
        sep fail auto. norm list. auto.
      search_prem ltac:(search_conc ltac:(apply himp_split; [ apply iter_imp | ])).
        sep fail auto.  norm list. norm arith. auto.
      Hint Resolve KLsorted_end specLookup_end specInsert_end.
      solve [ sep2 fail bpt_elim; sep_unify ].

    sep2 fail bpt_elim. unfold BPlusTreeImplModel.repLeaf.
      search_prem ltac:(search_conc ltac:(apply himp_split; [ apply iter_imp | ])).
        intros; norm arith; auto.
      simpl. unfold BPlusTreeImplModel.key_between in H3. sep2 fail bpt_elim. sep_unify.

    solve [ sep2 fail bpt_elim; sep_unify ].
  Qed.
  
  End insertFn.

End BPlusTreeImpl.
  
