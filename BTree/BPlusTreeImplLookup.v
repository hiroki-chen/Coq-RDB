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
Require Import ArrayOps.

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
  Definition RT := option (value tK).
  Definition P  := __.
  Definition Q (mpre : Model) (rt : option (value tK)) (mpost : Model) :=
    [rt = specLookup _ value_eq tK mpre] * [mpre = mpost].

  Require Import Eqdep.
  Lemma specLookup_equiv : forall (a b : Model),
    eqlistA (entry_eq _ value_eq) a b -> forall k, specLookup _ value_eq k a = specLookup _ value_eq k b.
  Proof.
    induction a; destruct b; simpl; inversion 1; auto. subst.
    destruct a; destruct s.  unfold entry_eq in H3; simpl in *.
    intros k.
    destruct (key_eq_dec _ x x0); intuition.
    destruct (equiv_dec x k); destruct (equiv_dec x0 k).
    rewrite H3.
    generalize (value_eq _ _ e0).
    generalize (value_eq _ _ e1).
    destruct e2. clear. intros.
    generalize (value_eq _ _ e). destruct e1.
    clear.
    rewrite (UIP_refl _ _ e0). simpl. auto.
    
    elimtype False. elim c. rewrite <- e. auto.
    elimtype False. elim c. rewrite e. auto.
    
    apply IHa; auto.
  Qed.

  Lemma specLookup_append : forall (a b : Model),
    specLookup KOT value_eq tK (a ++ b) = match specLookup KOT value_eq tK a with
                                            | None => specLookup KOT value_eq tK b
                                            | Some x => Some x
                                          end.
  Proof.
    induction a. auto.
    simpl. destruct (equiv_dec (projT1S a) tK); intros; auto.
      destruct a. simpl in *. clear.
      generalize dependent v. generalize (value_eq _ _ e).
      intro. generalize dependent e. generalize e0. rewrite e0. intros. 
      rewrite (UIP_refl _ _ e1). auto.
  Qed.

  Lemma sorted_min_max : forall ol k max',
    sorted _ (fun v : sigTS value => Val (projT1S v)) k ol max' ->
    k << max' \/ k == max'.
  Proof. clear.
    induction ol. auto.
    intros. destruct H. destruct (IHol _ _ H0). left. rewrite H. auto. left. rewrite <- H1. auto.
  Qed.

  Lemma specLookup_lt_all : forall ol min' max' k,
    KLsorted value min' ol max' ->
    max' << Val k ->
    specLookup KOT value_eq k ol = None.
  Proof. clear. Transparent BPlusTreeImplModel.KLsorted. 
    induction ol; auto.
    simpl; intros. destruct H.
    destruct (equiv_dec (projT1S a) k).
      elimtype False.
      cut (Val k << max' \/ Val k == max'); intros.
      rewrite e in *; clear e. destruct H2. 
        rewrite H0 in *. eapply ordLt_not_eq_LO. eapply H2. reflexivity.
        eapply ordLt_not_eq_LO. eapply H0. symmetry. auto.
        generalize (sorted_min_max _ _ _ H1); intros. destruct H2. left. rewrite e in H2. auto. right. rewrite e in H2. auto.
      eapply IHol; eauto.
  Qed.

  Lemma specLookup_gt_all : forall ol min' max' k,
    KLsorted value min' ol max' ->
    Val k << min' \/ Val k == min' ->
    specLookup KOT value_eq k ol = None.
  Proof. clear. Transparent BPlusTreeImplModel.KLsorted. 
    induction ol; auto.
    intros. destruct H; simpl.
      destruct (equiv_dec (projT1S a) k).
      elimtype False.
      rewrite e in H. destruct H0. rewrite H in H0. eapply ordLt_not_eq_LO. eapply H0. reflexivity.
        rewrite H0 in *. eapply ordLt_not_eq_LO. eapply H. reflexivity.
      
      eapply IHol; eauto. destruct H0. left. rewrite H0. auto. left. rewrite H0. auto.
  Qed.

  Theorem HimpLookup : forall (min' min max max' : LiftOrder key) (i i' ol oh : list (sigTS value)) rt,
    KLsorted _ min i max ->
    KLsorted _ min i' max ->
    KLsorted _ min' ol min ->
    KLsorted _ max oh max' ->
    key_between min tK max ->
    Q i rt i' ==> Q (ol ++ i ++ oh) rt (ol ++ i' ++ oh).
  Proof. clear. 
    intros; unfold Q. intro_pure. subst. 
    repeat rewrite specLookup_append.
    cut (specLookup KOT value_eq tK oh = None); intros. rewrite H4.
    cut (specLookup KOT value_eq tK ol = None); intros. rewrite H5.
    destruct (specLookup KOT value_eq tK i'); sep fail auto.
      eapply specLookup_lt_all; eauto.
      unfold BPlusTreeImplModel.key_between in H3. tauto.
      eapply specLookup_gt_all; eauto.
      unfold BPlusTreeImplModel.key_between in H3. tauto.
  Qed.

  (** Implementation **)
  Require Import BPlusTreeImplLocalComputeHelp.

  Notation "'op'" := (BPlusTreeImplLocalComputeHelp.op key).
  Notation "'repOp'" := (@BPlusTreeImplLocalComputeHelp.repOp SIZE key value KOT).
  Notation "'opModel'" := (@BPlusTreeImplLocalComputeHelp.opModel key value).
  Notation "'as_mapOp'" := (BPlusTreeImplLocalComputeHelp.as_mapOp value).
  Notation "'firstPtrOp'" := (@BPlusTreeImplLocalComputeHelp.firstPtrOp key value).
  
  Definition RES (n : nat) := (RT * sigT (fun o:op => [opModel n o]%type))%type.

  Section lookupFn.

    Lemma firstn_nth_error_expand : forall T i (ls : list T) x,
      nth_error ls i = Some x ->
      firstn (S i) ls = firstn i ls ++ x :: nil.
    Proof. clear.
      induction i. intros; norm list. destruct ls. norm list in H. discriminate.
      norm list in *. inversion H; auto.
      intros. destruct ls. norm list in H. discriminate. norm list in *. f_equal. eauto.
    Qed.

    Lemma length_lt : forall k' v' i x1,
      Some (existTS value k' v') =
      match nth_error x1 (i - 0) with
        | Some v => Some v
        | None => None
      end ->
      S i <= length x1.
    Proof. clear.
      intros. case_eq (nth_error x1 (i - 0)); intros.
      cut (i - 0 < length x1); eauto with norm_list_length.
      rewrite H0 in *; discriminate.
    Qed.
    Lemma specLookup_lt : forall i x1 k' v',
      specLookup KOT value_eq tK (firstn i x1) = None ->
      Some (existTS value k' v') =
      match nth_error x1 (i - 0) with
        | Some v => Some v
        | None => None
      end ->
      k' << tK ->
      specLookup KOT value_eq tK (firstn (S i) x1) = None.
    Proof.
      intros. 
      norm arith in *. case_eq (nth_error x1 i); intros.
      rewrite H2 in *.
      rewrite (firstn_nth_error_expand _ _ H2). rewrite specLookup_append. rewrite H.
      simpl. inversion H0. subst. simpl. destruct (equiv_dec k' tK). rewrite e in *. order.
      auto. rewrite H2 in *. discriminate.
    Qed.

    Require Import Setoid SetoidClass.
    Global Instance proper_value : Proper (equiv ==> eq) (@value).
    Proof. unfold Proper, respectful. auto. Qed.

    Lemma specLookup_eq : forall i x1 k' v' (pf : k' == tK) v, 
      specLookup KOT value_eq tK (firstn i x1) = None ->
      Some (existTS value k' v') =
      match nth_error x1 (i - 0) with
        | Some v => Some v
        | None => None
      end ->
      v = Some match value_eq k' tK pf in (_ = x) return x with
                 | eq_refl => v'
               end ->
      v = specLookup KOT value_eq tK x1.
    Proof.
      intros. norm arith in *. case_eq (nth_error x1 i); intros; rewrite H2 in *; [ | subst; discriminate ].
      rewrite <- (firstn_skipn i x1). rewrite specLookup_append. rewrite H.
      rewrite (nth_error_skipn_cons _ _ H2). simpl.
      inversion H0; subst; simpl. destruct (equiv_dec k' tK); [ | rewrite pf in *; order ].
      clear H H0 H2. generalize dependent v'.
      generalize dependent (value_eq _ _ e).
      generalize dependent (value_eq k' tK pf). clear e. rewrite (value_eq _ _ pf). intros.
      rewrite (UIP_refl _ _ e). rewrite (UIP_refl _ _ e0). auto.
    Qed.
    Hint Resolve specLookup_eq.

    Lemma specLookup_gt : forall i x1 k' v' v x0 x p,
      specLookup KOT value_eq tK (firstn i x1) = None ->
      Some (existTS value k' v') =
      match nth_error x1 (i - 0) with
        | Some v => Some v
        | None => None
      end ->
      inv 0 (p, x1) x0 x ->
      tK << k' ->
      v = None ->
      v = specLookup KOT value_eq tK x1.
    Proof. Opaque skipn.
     intros. norm arith in *. case_eq (nth_error x1 i); intros; rewrite H4 in *; [ | subst; discriminate ].
     rewrite <- (firstn_skipn i x1). rewrite specLookup_append. rewrite H. subst.
     rewrite (nth_error_skipn_cons _ _ H4). simpl. inversion H0; simpl.
     destruct (equiv_dec k' tK). rewrite e in *. order.
     Transparent BPlusTreeImplModel.inv. unfold BPlusTreeImplModel.inv in H1. simpl in H1. Opaque BPlusTreeImplModel.inv.
     rewrite <- (firstn_skipn i x1) in H1.
     destruct (KLsorted_app _ (firstn i x1) (skipn i x1) x x0).
     symmetry. apply H3 in H1. destruct H1. erewrite nth_error_skipn_cons in H7; eauto.
     destruct H7. eapply specLookup_gt_all. eapply H8. inversion H0. simpl. auto.
   Qed.

   Lemma specLookup_end : forall i (x1 : list (sigTS value)) v,
     specLookup KOT value_eq tK (firstn i x1) = None ->
     None =
     match nth_error x1 (i - 0) with
       | Some v => Some v
       | None => None
     end ->
     v = None ->
     v = specLookup KOT value_eq tK x1.
   Proof. clear.
     intros. norm arith in *. case_eq (nth_error x1 i); intros; rewrite H2 in *; [ discriminate | ].
     norm list in H. subst; auto.
   Qed.
   Hint Resolve specLookup_end specLookup_eq specLookup_lt specLookup_gt length_lt.
    

  Definition lookupFn : forall (p : ptr) (ary : array) (nxt : option ptr)
      (ls : [list (sigTS value)]) (min max : [LiftOrder key]),
      STsep (ls ~~ min ~~ max ~~
                p ~~> mkNode 0 ary nxt * repLeaf ary 0 SIZE ls * [KLsorted _ min ls max] *
                [key_between min tK max] * [length ls <= SIZE] * [array_length ary = SIZE] * P)
            (fun r:RES 0 => min ~~ max ~~ ls ~~ m :~~ projT2 (snd r) in
                repOp 0 (projT1 (snd r)) m min max nxt * Q ls (fst r) (as_mapOp _ _ m) *
                [firstPtrOp _ _ m = p]).
    refine (fun p ary nxt ls min max =>
      x <- Fix (fun (i:nat) => min ~~ max ~~ ls ~~ 
                  repLeaf ary 0 SIZE ls *
                  [i <= length ls] * [i <= SIZE] * [length ls <= SIZE] *
                  [specLookup _ value_eq tK (firstn i ls) = None] *
                  [inv 0 (p,ls) min max])
               (fun _ (res:option (value tK)) => ls ~~ min ~~ max ~~ 
                  repLeaf ary 0 SIZE ls * [inv 0 (p,ls) min max] * [length ls <= SIZE] *
                  [res = specLookup _ value_eq tK ls])
               (fun self i =>
                 if le_lt_dec SIZE i then
                   {{ Return None }}
                 else
                   okv <- sub_array ary i _ ;
                   let _ : option (sigTS value) := okv in
                   match okv as okv' return okv = okv' -> _ with 
                     | None => fun pfOkv => {{ Return None }}
                     | Some (existTS k' v') => fun pfOkv => 
                       match ordCompare k' tK with
                         | LT _  => {{ self (S i) }}
                         | EQ pf => {{ Return (Some 
                           match value_eq _ _ pf in _ = x return x with
                             | refl_equal => v'
                           end) }}
                         | GT _ => {{ Return None }}
                       end
                   end (refl_equal _)) 0 <@> _ ;
      {{ Return (x, existT (fun o:op => [opModel 0 o]%type) (Merge key p) (ls ~~~ (p,ls))) }}); 
    try clear self; try rewrite pfOkv in *.
  Proof.
    solve [ sep_unify ].
    solve [ sep2 ltac:(combine_le_le || subst || norm list in *) bpt_elim; sep_unify ].
    solve [ sep2 fail bpt_elim; sep_unify ].  
    solve [ sep_unify ].

    solve [ sep2 fail bpt_elim; sep_unify ].
    solve [ sep2 fail bpt_elim; sep_unify ].
    solve [ sep_unify ].

    solve [ sep2 fail bpt_elim; sep_unify ].
    solve [ sep_unify ].

    sep2 fail bpt_elim.
    solve [ sep2 fail bpt_elim; sep_unify ].
    solve [ sep_unify ].
    
    solve [ sep2 fail bpt_elim; sep_unify ].
    solve [ sep2 fail bpt_elim; sep_unify ].
    solve [ sep_unify ].
    solve [ sep_unify ].

    sep2 fail bpt_elim. unfold BPlusTreeImplLocalComputeHelp.repOp.
      generalize dependent x3.
      rewrite H6 in *; clear H6. simpl. sep2 fail bpt_elim. instantiate_conc ary.
        subst; simpl. unfold Q.
      solve [ sep2 fail bpt_elim; sep_unify ].
  Qed.
  
  End lookupFn.

End BPlusTreeImpl.
  
