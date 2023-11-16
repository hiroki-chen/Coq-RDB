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
Require Import Think ThinkList ThinkArith.
Require Import Even.

Require Import BPlusTreeImplModel.
Require Import BPlusTreeModelFacts.
Require Import BPlusTreeTactics.
Require Import BPlusTreeImplNewFree.
Require Import BPlusTreeImplLocalCompute.
Require Import BPlusTreeImplLookup BPlusTreeImplInsert BPlusTreeImplIterate.

Require Import OrderedTypeNM.
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

  Open Local Scope hprop_scope.
  Open Local Scope stsepi_scope.
  Open Local Scope stsep_scope.

  (** Compute **)

  Definition localCompute := @localCompute SIZE pfMin SIZE_even key value KOT.

  Lemma key_between_all : forall k, key_between MinK k MaxK.
  Proof.
    unfold BPlusTreeImplModel.key_between. split; simpl; auto. 
    left. simpl. auto.
  Qed.
  Lemma repack : forall x x1,
    projT2S x = [x1]%inhabited ->
    x = existTS (fun h :nat => [ptree h]%type) (projT1S x) [x1]%inhabited.
  Proof.
    destruct x; intros; simpl in *; subst; auto.
  Qed.
  Hint Immediate key_between_all repack.

  Definition rep_frame' (p:ptr) (m : [Model]) (v : ptr * sigTS (fun h:nat => [ptree h]%type)) : hprop :=
    tr :~~ projT2S (snd v) in m ~~ 
    [eqlistA (entry_eq KOT value_eq) m (as_map tr)] * [inv _ tr MinK MaxK] *
    rep' (fst v) None tr.

  Require Import Eqdep.
  Lemma specLookup_equiv : forall (a b : Model),
    eqlistA (entry_eq _ value_eq) b a -> forall k, specLookup _ value_eq k a = specLookup _ value_eq k b.
  Proof.
    induction a; destruct b; simpl; inversion 1; auto. subst.
    destruct a; destruct s.  unfold entry_eq in H3; simpl in *.
    intros k.
    destruct (key_eq_dec _ x0 x); intuition.
    destruct (equiv_dec x k); destruct (equiv_dec x0 k).
    rewrite H3.
    generalize (value_eq _ _ e0).
    generalize (value_eq _ _ e1).
    destruct e2. clear. intros.
    generalize (value_eq _ _ e). destruct e1.
    clear.
    rewrite (UIP_refl _ _ e0). simpl. auto.

    elimtype False. elim c. rewrite e. auto.
    elimtype False. elim c. rewrite <- e. auto.

    apply IHa; auto.
  Qed.

  Lemma specInsert_equiv : forall (a b : Model), 
    eqlistA (entry_eq _ value_eq) a b -> forall k (v: value k), eqlistA (entry_eq _ value_eq) (specInsert _ k v a) (specInsert _ k v b).
  Proof.
    induction a; destruct b; simpl; inversion 1; intros; simpl; auto. 
      constructor. unfold entry_eq.  simpl. destruct (key_eq_dec _ k k).
      generalize (value_eq _ _ e). intros.
      rewrite (UIP_refl _ _ e0). unfold eq_rec_r. unfold eq_rec. unfold eq_rect. simpl. auto.
      apply c. reflexivity. auto.

    destruct a; destruct s.  unfold entry_eq in H3; simpl in *.
    subst. destruct (key_eq_dec KOT x0 x1).
    inversion H. subst. 
    destruct (ordCompare x1 k); rewrite <- e in *.
      elim_comp_lt x0 k. constructor; auto.
      elim_comp_eq x0 k. constructor; auto. reflexivity.  
      elim_comp_gt x0 k. constructor; auto. reflexivity.
    destruct H3.
  Qed.

  Hint Resolve specLookup_equiv specInsert_equiv.

  Definition lookup : forall (t : BptMap) (k : key) (m : [Model]),
    STsep (m ~~ rep t m)
          (fun res:option (value k) => m ~~ rep t m * [res = specLookup _ value_eq k m]).
    refine (fun t k m =>
      bpt <- t !! (rep_frame' t m) ;
      res <- @localCompute (option (value k)) __  (@BPlusTreeImplLookup.Q key value KOT value_eq k)
           k 
           (@BPlusTreeImplLookup.HimpLookup key value KOT value_eq k)
           (@BPlusTreeImplLookup.lookupFn SIZE pfMin SIZE_even key value KOT value_eq k)
           (projT1S (snd bpt)) (fst bpt) (projT2S (snd bpt)) <@> _ ;
      t ::= (snd (fst res), snd res) <@> _ ;;
      {{ Return (fst (fst res)) <@> _ }}).
  Proof.
    unfold BPlusTreeImplModel.rep, rep_frame'. sep2 fail bpt_elim. simpl.
      sep2 fail bpt_elim.
      solve [ sep2 fail bpt_elim; sep_unify ].
    solve [ sep_unify ].
    unfold BPlusTreeImplModel.rep, rep_frame'. sep2 fail bpt_elim. sep_unify.
    solve [ sep_unify ].
    solve [ sep2 fail bpt_elim; sep_unify ].
    solve [ sep_unify ].
    solve [ sep_unify ].
    unfold BPlusTreeImplModel.rep. sep2 fail bpt_elim.
      instantiate_conc (snd (fst res)). instantiate_conc (projT1S (snd res)). instantiate_conc x1.
      unfold BPlusTreeImplLookup.Q.
      sep2 fail bpt_elim. rewrite H6 in *; rewrite H7 in *; rewrite H8 in *.
      solve [ sep2 fail bpt_elim; sep_unify ].
  Qed.

  Definition insert : forall (t : BptMap) (k : key) (v : value k) (m : [Model]),
    STsep (m ~~ rep t m)
          (fun res:option (value k) => m ~~ rep t (specInsert _ _ v m) * [res = specLookup _ value_eq k m]).
    refine (fun t k v m =>
      bpt <- t !! (rep_frame' t m) ;
      res <- @localCompute (option (value k)) __  (@BPlusTreeImplInsert.Q key value KOT value_eq k v)
           k 
           (@BPlusTreeImplInsert.HimpInsert key value KOT value_eq k v)
           (@BPlusTreeImplInsert.insertFn SIZE pfMin SIZE_even key value KOT value_eq k v)
           (projT1S (snd bpt)) (fst bpt) (projT2S (snd bpt)) <@> _ ;
      t ::= (snd (fst res), snd res) <@> _ ;;
      {{ Return (fst (fst res)) <@> _ }}).
  Proof.
    unfold BPlusTreeImplModel.rep, rep_frame'. sep2 fail bpt_elim. simpl.
      solve [ sep2 fail bpt_elim; sep_unify ].
    solve [ sep_unify ].
    solve [ unfold BPlusTreeImplModel.rep, rep_frame'; sep2 fail bpt_elim; sep_unify ].
    solve [ sep_unify ].
    solve [ sep2 fail bpt_elim; sep_unify ].
    solve [ sep_unify ].
    solve [ sep_unify ].
    unfold BPlusTreeImplModel.rep. sep2 fail bpt_elim.
      instantiate_conc (snd (fst res)). instantiate_conc (projT1S (snd res)). instantiate_conc x1.
      unfold BPlusTreeImplInsert.Q.
      sep2 fail bpt_elim. rewrite H6 in *; rewrite H7 in *; rewrite H8 in *.
      solve [ sep2 fail bpt_elim; sep_unify ].
  Qed.

End BPlusTreeImpl.

Require Import BPlusTreeImplIterate.

Require Import Even.
Definition BPlusTreeImpl 
  SIZE (SIZE_min : SIZE > 1) (SIZE_even : even SIZE)
  (key : Set) (value : key -> Set) (KOT : OrderedType key) (value_eq : forall k1 k2, k1 == k2 -> value k1 = value k2) : @bpt_map SIZE key value KOT value_eq := mkBpt 
  (@BPlusTreeImplNewFree.new SIZE SIZE_min key value KOT value_eq)
  (@BPlusTreeImplNewFree.free SIZE SIZE_min key value KOT value_eq)
  (@lookup SIZE SIZE_min SIZE_even key value KOT value_eq)
  (@insert SIZE SIZE_min SIZE_even key value KOT value_eq)
  (@BPlusTreeImplIterate.iterate SIZE SIZE_min SIZE_even key value KOT value_eq)
  (@BPlusTreeImplIterate.orderedIterate SIZE SIZE_min SIZE_even key value KOT value_eq).

Print Assumptions BPlusTreeImpl.
