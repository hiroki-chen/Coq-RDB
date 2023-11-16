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
Require Import BPlusTreeModelFacts.
Require Import BPlusTreeTactics.
Require Import ArrayOps.
Require Import BPlusTreeImplNewFree.
Require Import BPlusTreeImplLocalComputeHelp.

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
  Opaque BPlusTreeImplModel.MinK.
  Opaque BPlusTreeImplModel.MaxK.

  Open Local Scope hprop_scope.
  Open Local Scope stsepi_scope.

  Notation "'op'" := (@op key).
  Notation "'opModel'" := (@opModel key value).
  Notation "'as_mapOp'" := (as_mapOp value).
  Notation "'firstPtrOp'" := (firstPtrOp value).
  Notation "'repOp'" := (repOp SIZE value KOT).

  Hint Immediate div2_gt_0.

  (** Compute **)
  Section Compute.
    Hypothesis RT : Type.
    Hypothesis P  : hprop.
    Hypothesis Q  : Model -> RT -> Model -> hprop.
    Hypothesis tK : key.

    Definition RES (n : nat) := (RT * sigT (fun o:op => [opModel n o]%type))%type.

    Hypothesis HimpLocal : forall (min' min max max' : LiftOrder key) (i i' ol oh : list (sigTS value)) rt,
      KLsorted _ min i max ->
      KLsorted _ min i' max ->
      KLsorted _ min' ol min ->
      KLsorted _ max oh max' ->
      key_between min tK max ->
      Q i rt i' ==> Q (ol ++ i ++ oh) rt (ol ++ i' ++ oh).

    Hypothesis Fn : forall (p : ptr) (ary : array) (nxt : option ptr) 
      (ls : [list (sigTS value)]) (min max : [LiftOrder key]),
      STsep (ls ~~ min ~~ max ~~
                p ~~> mkNode 0 ary nxt * repLeaf ary 0 SIZE ls * [KLsorted _ min ls max] * 
                [key_between min tK max] * [length ls <= SIZE] * [array_length ary = SIZE] * P)
            (fun r:RES 0 => min ~~ max ~~ ls ~~ m :~~ projT2 (snd r) in
                repOp 0 (projT1 (snd r)) m min max nxt * Q ls (fst r) (as_mapOp _ _ m) *
                [firstPtrOp _ _ m = p]).

    Definition repOp_facts (h : nat) (o : op) (m : opModel h o) (min max : LiftOrder key) : Prop :=
      match o as o return opModel h o -> Prop with
        | Merge p        => fun m => inv h m min max
        | Split lp kp rp => fun lkr => 
          let l := fst lkr in
          let r := snd lkr in
          inv h l min (Val kp) /\ inv h r (Val kp) max /\
          lp = ptrFor l /\ rp = ptrFor r
      end m.

    Lemma repOp_pure : forall h A B C D E P Q,
      (repOp_facts h A B C D -> repOp h A B C D E * P ==> Q) 
      -> repOp h A B C D E * P ==> Q.
    Proof. clear.
      destruct A; simpl in *; intros; intro_pure; (eapply himp_trans; [ | eapply H ]); sep fail auto.
    Qed.
    Ltac add_opFacts :=
      search_prem ltac:(idtac; 
        match goal with 
          | [ H : @repOp_facts ?H ?O ?M _ _ |- @BPlusTreeImplLocalComputeHelp.repOp _ _ _ _ ?H ?O ?M _ _ _ * _ ==> _ ] => fail 1
          | [ |- @BPlusTreeImplLocalComputeHelp.repOp _ _ _ _ ?H ?O ?M _ _ _ * _ ==> _ ] => simple apply repOp_pure; intro
        end).

(*  Section mergeOpNext. *)
    Lemma merge_inv_preserve : forall h x11 x8 x6 x5 x7 p,
      inv h x8 x6 x5 ->
      contextual h
        (fun (mi : LiftOrder key) (c : BranchCell h) =>
          inv h (projT2S c) mi (Val (projT1S c))) x7 x6 
        x11 ->
      inv (S h) (p, (x11, x8)) x7 x5.
    Proof. Transparent BPlusTreeImplModel.contextual. Transparent BPlusTreeImplModel.inv.
      induction x11; intros.
      simpl in *. split; fold ptree in *; simpl; try reflexivity. rewrite H0. auto.
      simpl in *. destruct H0. generalize (IHx11 _ _ _ _ p H H1); intros. intuition eauto.
    Qed.
    Lemma firstPtr_merge_head : forall h p x11 x8 p',
      firstPtrOp (S h) (Merge key p) (p, (x11, x8)) =
      match head x11 with
        | Some n => firstPtr (projT2S n)
        | None => firstPtrOp h (Merge key p') x8
      end.
    Proof.
      destruct x11; simpl; intros; auto.
    Qed.

    Lemma Q_next1 : forall h rt p' p x8 x0 x6 x5 x7,
      inv h x8 x6 x5 ->
      inv (S h) x0 x7 x5 ->
      x6 = lastKey  (_cont x0) x7 ->
      key_between x6 tK x5 ->
      Q (as_map (_next x0)) rt (as_mapOp h (Merge key p') x8) ==>
      Q (as_map x0) rt (as_mapOp (S h) (Merge key p) (p, (_cont x0, x8))).
    Proof. generalize HimpLocal. clear.
      intros. simpl; fold ptree in *. autorewrite with bpt_rw.
      Change (flat_map (fun x : BranchCell h => as_map (projT2S x)) (_cont x0) ++ as_map x8)
      into (flat_map (fun x : BranchCell h => as_map (projT2S x)) (_cont x0) ++ as_map x8 ++ nil) using (norm list; reflexivity).
      Change (flat_map (fun x : BranchCell h => as_map (projT2S x)) (_cont x0) ++ as_map (_next x0))
      into (flat_map (fun x : BranchCell h => as_map (projT2S x)) (_cont x0) ++ as_map (_next x0) ++ nil) using (norm list; reflexivity).
      destruct x0 as [ ? [ ? ? ] ]; fold ptree in *; autorewrite with bpt_rw in *.
      eapply HimpLocal; try eassumption. eapply inv_KLsorted_map; [ | eauto ].
      simpl in H0; fold ptree in *. intuition. rewrite <- H1 in *. auto.
      eapply inv_KLsorted_map; eauto.
      eapply contextual_KLsorted; eauto. destruct H0. rewrite H1. eapply H0; auto.
      eauto.
    Qed.
    Lemma inv_S_contextual : forall h X x7 x5 x6,
      inv (S h) X x7 x5 ->
      x6 = lastKey (_cont X) x7 ->
      contextual h
      (fun (mi : LiftOrder key) (c : BranchCell h) =>
        inv h (projT2S c) mi (Val (projT1S c))) x7 x6 
      (_cont X).
    Proof. clear; fold ptree in *; intros.
      simpl in H. destruct X as [ ? [ ? ? ] ]. simpl in *. autorewrite with bpt_rw. destruct H.
      rewrite H0 in *. auto.
    Qed.

    Lemma Q_next_split : forall h l k r x11 x2 res x5 x6 x4 res0 x10,
      flat_map (fun x0 : BranchCell h => as_map (projT2S x0)) (_cont x2) ++
      as_map (fst x11) ++ as_map (snd x11) = as_mapOp (S h) res0 x10 ->
      inv h (fst x11) x5 (Val k) -> 
      inv h (snd x11) (Val k) x4 ->
      inv (S h) x2 x6 x4 ->
      key_between x5 tK x4 ->
      x5 = lastKey (_cont x2) x6 ->
      Q (as_map (_next x2)) res (as_mapOp h (Split l k r) x11) ==>
      Q (as_map x2) res (as_mapOp (S h) res0 x10).
    Proof. clear Fn.
      intros. destruct x2 as [ ? [ ? ? ] ]; simpl; fold ptree in *. autorewrite with bpt_rw in *.
      Change (flat_map (fun x : BranchCell h => as_map (projT2S x)) l0 ++ as_map p0)
        into (flat_map (fun x : BranchCell h => as_map (projT2S x)) l0 ++ as_map p0 ++ nil) using (norm list; trivial).
      rewrite <- H. autorewrite with bpt_rw.
      Change (flat_map (fun x0 : BranchCell h => as_map (projT2S x0)) l0 ++ as_map (fst x11) ++ as_map (snd x11))
        into (flat_map (fun x0 : BranchCell h => as_map (projT2S x0)) l0 ++ (as_map (fst x11) ++ as_map (snd x11)) ++ nil) using (norm list; trivial).
      eapply HimpLocal. Focus 5. eassumption.
      destruct H2; fold ptree in *.
      eapply inv_KLsorted_map. rewrite <- H4 in H5. eassumption. auto.

      eapply KLsorted_app_ex; eapply inv_KLsorted_map; eauto.
      destruct H2. eapply contextual_KLsorted. fold ptree in *. rewrite <- H4 in H2. eassumption. eauto.
      eauto.     
    Qed.

    Lemma repBranch_himp2 : forall h ary pos (x1 : list (BranchCell h)) x2 k0 IRR IRR',
      length x1 = pos ->
      repBranch h rep' ary 0 pos x1 (firstPtr x2) ==>
      repBranch h rep' ary 0 pos (x1 ++ existTS (fun _ : key => ptree h) k0 x2 :: IRR) IRR'.
    Proof. clear.
      intros; apply iter_imp; do 2 sep fail auto.
      norm list. case_eq (nth_error x1 i); sep fail auto.
        autorewrite with bpt_rw. simpl. sep fail auto.
    Qed.

    Lemma firstPtr_tauto : forall h (p:ptr) x3 k (x8 : ptree h * ptree h),
      @BPlusTreeImplModel.firstPtr _ _ (S h) (p,(x3 ++ existTS (fun _ : key => ptree h) k (fst x8) :: nil, snd x8)) =
      match head x3 with
        | Some n => firstPtr (projT2S n)
        | None => firstPtr (fst x8)
      end.
    Proof. clear. 
      simpl; intros; autorewrite with bpt_rw. destruct x3; auto.
    Qed.

    Lemma Q_next_merge : forall h l k r x3 x7 x5 x6 x8 p rt full,
      inv (S h) x3 x7 x5 ->
      length (_cont x3) = full ->
      full < SIZE ->
      inv h (fst x8) x6 (Val k) ->
      inv h (snd x8) (Val k) x5 ->
      key_between x6 tK x5 ->
      x6 = lastKey (_cont x3) x7 ->
      Q (as_map (_next x3)) rt (as_mapOp h (Split l k r) x8) ==>
      Q (as_map x3) rt (as_mapOp (S h) (Merge key p) (p, (_cont x3 ++ existTS (fun _ : key => ptree h) k (fst x8) :: nil, snd x8))).
    Proof. clear Fn.
      intros; simpl; fold ptree in *. autorewrite with bpt_rw. norm list. simpl.
      Change (flat_map (fun x : BranchCell h => as_map (projT2S x)) (_cont x3) ++ as_map (fst x8) ++ as_map (snd x8))
        into (flat_map (fun x : BranchCell h => as_map (projT2S x)) (_cont x3) ++ (as_map (fst x8) ++ as_map (snd x8)) ++ nil) using (norm list; trivial).
      Change (flat_map (fun x : BranchCell h => as_map (projT2S x)) (_cont x3) ++ as_map (_next x3))
        into (flat_map (fun x : BranchCell h => as_map (projT2S x)) (_cont x3) ++ as_map (_next x3) ++ nil) using (norm list; trivial).
      destruct x3 as [ ? [ ? ? ] ]; fold ptree in *. destruct H; autorewrite with bpt_rw in *.
      eapply HimpLocal; try eassumption; fold ptree in *.
      Focus 4. eauto.
      eapply inv_KLsorted_map. rewrite H5. eapply H6; eauto. eauto.
      eapply KLsorted_app_ex; eapply inv_KLsorted_map; eauto.
      eapply contextual_KLsorted. rewrite H5. eassumption. auto.
    Qed.
    Lemma inv_next_merge : forall h k x3 x7 x5 x6 x8 p full,
      inv (S h) x3 x7 x5 ->
      length (_cont x3) = full ->
      full < SIZE ->
      inv h (fst x8) x6 (Val k) ->
      inv h (snd x8) (Val k) x5 ->
      key_between x6 tK x5 ->
      x6 = lastKey (_cont x3) x7 ->
      inv (S h)
      (p,(_cont x3 ++ existTS (fun _ : key => ptree h) k (fst x8) :: nil, snd x8)) x7 x5.
    Proof. clear.
      simpl; intuition; simpl in *; destruct H; autorewrite with bpt_rw in *; fold ptree in *.
      Focus 2. rewrite lastKey_last. simpl. auto.
      eapply contextual_append.
        intros. rewrite H7. auto.
        apply H.
      rewrite lastKey_last. simpl. rewrite <- H5; auto. intuition reflexivity.
    Qed.

    Opaque BPlusTreeImplModel.contextual BPlusTreeImplModel.inv.


    Definition mergeOpNext : forall (min mid max : [LiftOrder key]) (h : nat)
      (p : ptr) (ary : array) (optr : [option ptr]) (full : nat) (res' : RES h) (m : [ptree (S h)]),
      full <= SIZE ->
      STsep (min ~~ mid ~~ max ~~ m ~~ optr ~~ opm :~~ projT2 (snd res') in
               let o := projT1 (snd res') in
               let lsM  := _cont m in
               let nxtM := _next m in
               Exists nxt :@ ptr,
               p ~~> mkNode (S h) ary (Some nxt) *
               [length lsM = full] * [array_length ary = SIZE] *
               [mid = lastKey lsM min] *
               [inv (S h) m min max] *
               [key_between mid tK max] *
               repBranch h (rep') ary 0 SIZE lsM (firstPtrOp _ _ opm) *
               repOp h o opm mid max optr * Q (as_map (_next m)) (fst res') (as_mapOp _ _ opm))
            (fun res : RES (S h) => min ~~ max ~~ optr ~~ m ~~ 
               opm :~~ projT2 (snd res) in opm' :~~ projT2 (snd res') in
               repOp (S h) (projT1 (snd res)) opm min max optr * Q (as_map m) (fst res) (as_mapOp _ _ opm) *
               [firstPtrOp _ _ opm = match head (_cont m) return ptr with
                                       | None => firstPtrOp _ _ opm'
                                       | Some n => firstPtr (projT2S n)
                                     end]).
      refine (fun min mid max h p ary optr full res m pfFullSize =>
        let rt := fst res in
        match snd res as OP return snd res = OP -> _ with
          | (existT (Merge p') opm) => fun pf =>
            p ::= mkNode (S h) ary (Some p') ;;
            let rM : [opModel (S h) (Merge key p)] := 
                     m ~~~' opm ~~~ (p, (_cont m, opm)) in
            {{ Return (rt, existT _ (Merge key p) rM) }}
          | (existT (Split l k r) opm) => fun pf => 
            if le_lt_dec SIZE full then
              res <- @splitBranch_atEnd SIZE pfMin SIZE_even key value KOT min mid max h p ary l r optr (opm ~~~ fst opm) k (opm ~~~ snd opm) m <@> _ ;
              {{ Return (rt, res) }}
            else
              (** we can just merge **)
              upd_array ary full (Some (k, l)) <@> _ ;;
              p ::= mkNode (S h) ary (Some r) ;;
              let rM : [opModel (S h) (Merge key p)] := 
                opm ~~~' m ~~~
                  (p, (_cont m ++ ((existTS (fun _ => ptree h) k (fst opm)) :: nil), snd opm)) in
              {{ Return (rt, existT _ (Merge key p) rM) }}
        end (refl_equal _));
      clear Fn.
    Proof. idtac "Starting mergeOpNext".
      (** Merge **)
      solve [ sep2 fail bpt_elim; sep_unify ].
      solve [ sep_unify ].
      solve [ sep_unify ].
      sep2 ltac:(add_opFacts || bpt_elab) bpt_elim. 
        generalize dependent x9. generalize dependent x8. 
        rewrite H14 in *; clear H14. rewrite pf in *; clear pf.
        norm pair in *; simpl projT1 in *; simpl projT2 in *. unfold rM in *; clear rM.
        intros. simpl BPlusTreeImplLocalComputeHelp.repOp. fold ptree in *; sep2 bpt_elab bpt_elim. 
          solve [ rewrite <- H; autorewrite with bpt_rw; auto ].
          solve [ simpl BPlusTreeImplLocalComputeHelp.firstPtrOp;  rewrite <- H; autorewrite with bpt_rw; auto ].
          rewrite <- H in *; clear H. rewrite <- H17 in *; clear H17. unfold rt in *. norm pair in *. autorewrite with bpt_rw in *.
      Hint Resolve Q_next1 firstPtr_merge_head merge_inv_preserve inv_S_contextual.
        solve [ sep2 fail bpt_elim; sep_unify ].

      (** Split **)
      sep2 ltac:(combine_le_le || bpt_elab) bpt_elim. instantiate_conc v.
        generalize dependent x7. rewrite pf in *.
        simpl fst in *; simpl snd in *; simpl projT1 in *; simpl projT2 in *.
        unfold BPlusTreeImplLocalComputeHelp.repOp;
        unfold BPlusTreeImplLocalComputeHelp.firstPtrOp; fold ptree in *.
        Hint Extern 0 (firstPtr ?X = firstPtr ?Y) => f_equal. (** DELETE **)
        rewrite <- H7; rewrite <- H8. sep2 fail bpt_elim. sep_unify.
      solve [ sep_unify ].
      solve [ sep_unify ].
      sep2 ltac:(combine_le_le || bpt_elab) bpt_elim.
        generalize dependent x10; generalize dependent x11.
        rewrite H13 in *; clear H13; rewrite pf in *; clear pf. norm pair. unfold rt.
        sep2 fail bpt_elim. unfold BPlusTreeImplLocalComputeHelp.firstPtrOp.
        rewrite <- H7; rewrite <- H8. sep2 fail bpt_elim.
      Hint Resolve Q_next_split.
        solve [ sep2 fail bpt_elim; sep_unify ].
       
      (** Don't need to split **)
      solve [ sep2 fail bpt_elim; sep_unify ].
      solve [ sep_unify ].
      solve [ sep2 fail bpt_elim; sep_unify ].
      solve [ sep_unify ].
      solve [ sep_unify ].
      sep2 bpt_elab bpt_elim.
        generalize dependent x10; generalize dependent x8.
        rewrite pf in *; clear pf; rewrite H17 in *; clear H17. unfold rM in *; clear rM.
        simpl fst in *; simpl snd in *; simpl projT1 in *; simpl projT2 in *.
        unfold BPlusTreeImplLocalComputeHelp.repOp;
        unfold BPlusTreeImplLocalComputeHelp.firstPtrOp; fold ptree in *. 
        Transparent BPlusTreeImplModel.rep'. simpl BPlusTreeImplModel.rep'. Opaque BPlusTreeImplModel.rep'.
      Hint Resolve repBranch_himp2 : bpt_sep.
      Hint Immediate firstPtr_tauto.
      Hint Immediate Q_next_merge inv_next_merge.
        sep2 add_opFacts bpt_elim.
          rewrite <- H; auto.
          rewrite <- H; autorewrite with bpt_rw.
          eauto with bpt_sep.
          rewrite <- H; autorewrite with bpt_rw. norm list. eauto with bpt_sep.
          norm arith. rewrite <- H. autorewrite with bpt_rw. norm list. rewrite H11. norm arith.
          norm list. norm pair. sep2 fail bpt_elim.
idtac "Ending mergeOpNext".
        solve [ sep2 fail bpt_elim; sep_unify ].
  Qed.
(*  End mergeOpNext. *)

(*  Section mergeOpInternal. *)

    Lemma himp_repBranch_skipn_replacenth : forall h ary pos x2 x0 midH,
      pos < length (_cont x2) ->
      repBranch h rep' ary (S pos) (SIZE - S pos) (skipn (S pos) (_cont x2))
        (firstPtr (_next x2)) ==>
      repBranch h rep' ary (S pos) (SIZE - S pos)
        (skipn (S pos) (replaceNth pos (_cont x2) (existTS (fun _ : key => ptree h) midH x0)))
        (firstPtr (_next x2)).
    Proof.
      intros. rewrite skipn_replaceNth. auto.
    Qed.
    Lemma repBranch_nextPtr_firstn_extra_rw : forall h x3 i optr len irr irr' (X : BranchCell h),
      i < len -> len <= length x3 ->
      optr = firstPtr (projT2S X) ->
      repBranch_nextPtr (firstn len x3) i optr =
      repBranch_nextPtr (firstn len x3 ++ X :: irr) i irr'.
    Proof. clear.
      intros; unfold BPlusTreeImplModel.repBranch_nextPtr.
      destruct (eq_nat_dec (S i) len).
      cut (length (firstn len x3) = len); eauto with norm_list_length; intros; subst.
      norm list. rewrite H2. norm arith. auto.
      rewrite nth_error_firstn_app; eauto. norm list.
      case_eq (nth_error x3 (S i)); auto; intros.
      elimtype False. cut (length x3 <= S i); eauto with norm_list_length.
    Qed.
    Lemma repBranch_firstn_extra_irr : forall h ary st len x3 x8 (X : BranchCell h) optr irr,
      firstPtr (projT2S X) = x8 ->
      len < length x3 ->
      repBranch h rep' ary st len (firstn len x3) x8 ==>
      repBranch h rep' ary st len (firstn len x3 ++ X :: irr) optr.
    Proof. clear.
      intros; apply iter_imp; do 2 sep fail auto.
      norm list.
      rewrite nth_error_firstn_app; eauto. case_eq (nth_error x3 i); sep fail auto.
      erewrite <- repBranch_nextPtr_firstn_extra_rw; eauto.  auto.
    Qed.

    Lemma himp_repBranch_replaceNth : forall h ary pos x2 p' x0 midH,
      pos < length (_cont x2) ->
      repBranch h rep' ary 0 pos (firstn pos (_cont x2)) (firstPtrOp h (Merge key p') x0) ==>
      repBranch h rep' ary 0 pos (replaceNth pos (_cont x2) (existTS (fun _ : key => ptree h) midH x0)) (firstPtr (_next x2)).
    Proof.
      intros. unfold replaceNth. simpl BPlusTreeImplLocalComputeHelp.firstPtrOp. eapply repBranch_firstn_extra_irr; auto.
    Qed.

    Lemma repBranch_nextPtr_replaceNth : forall h pos (x3 : list (BranchCell h)) X irr,
      pos < length x3 ->
      repBranch_nextPtr x3 pos irr =
      repBranch_nextPtr (replaceNth pos x3 X) pos irr.
    Proof. clear.
      unfold BPlusTreeImplModel.repBranch_nextPtr. unfold replaceNth.
      intros. 
      cut (length (firstn pos x3) = pos); eauto with norm_list_length; intros.
      norm list. rewrite H0. norm arith. norm list. norm arith. auto.
    Qed.

    Lemma mergeOpInternal_merge_firstPtr : forall h p (x3 : ptree (S h)) midH (x8 : ptree h) pos p' (X : BranchCell h),
      nth_error (_cont x3) pos = Some X ->
      firstPtrOp h (Merge key p') x8 = firstPtr (projT2S X) ->
      firstPtrOp (S h) (Merge key p)
        (p, (replaceNth pos (_cont x3) (existTS (fun _ : key => ptree h) midH x8), _next x3)) =
      match _cont x3 with
        | nil => firstPtrOp h (Merge key p') x8
        | n :: _ => firstPtr (projT2S n)
      end.
    Proof. clear.
      intros. simpl. unfold replaceNth. destruct (_cont x3). norm list in H; discriminate.
      destruct pos. norm list in *. inversion H. auto. norm list. auto.
    Qed.
    Lemma mergeOpInternal_merge_length : forall T (x3 : list T) X pos,
      pos < length x3 ->
      length x3 <= SIZE ->
      length (replaceNth pos x3 X) <= SIZE.
    Proof.
      intros; rewrite length_replaceNth; auto.
    Qed.

    Lemma mergeOpInternal_merge_inv : forall h (x3 : ptree (S h)) p x5 x8 midH pos x6 x7 v0,
         inv h x8 x6 (Val midH)
      -> inv h (_next x3) (lastKey (_cont x3) (Val midH)) x5
      -> contextual h
           (fun (mi : LiftOrder key) (c : BranchCell h) => inv h (projT2S c) mi (Val (projT1S c))) x7 x6
           (firstn pos (_cont x3))
      -> contextual h
           (fun (mi : LiftOrder key) (c : BranchCell h) => inv h (projT2S c) mi (Val (projT1S c))) 
           (Val midH) (lastKey (_cont x3) (Val midH)) (skipn (S pos) (_cont x3))
      -> nth_error (_cont x3) pos = Some v0
      -> projT1S v0 = midH
      -> inv (S h)
           (p, (replaceNth pos (_cont x3) (existTS (fun _ : key => ptree h) midH x8), _next x3))
           x7 x5.
    Proof. clear. Opaque firstn skipn.
      unfold replaceNth. intros. split; fold ptree in *.
        rewrite lastKey_append. simpl. eapply contextual_append; eauto.
          intros. eapply (@inv_subst key value KOT h (projT2S c) a b (Val (projT1S c)) (Val (projT1S c))); auto. reflexivity.
        split; simpl; auto. rewrite <- (firstn_skipn pos (_cont x3)) in H2 at 1. rewrite lastKey_append in H2. erewrite nth_error_skipn_cons in H2; eauto. simpl in H2.
        rewrite H4 in H2. auto.
      rewrite lastKey_append. simpl. rewrite <- (firstn_skipn pos (_cont x3)) in H0. rewrite lastKey_append in H0.
        erewrite nth_error_skipn_cons in H0; eauto. simpl in H0. rewrite H4 in H0. auto.
    Qed.

    Lemma mergeOpInternal_solve_flatmaps : forall h pos x2 p' p midH x0,
      flat_map (fun x9 : BranchCell h => as_map (projT2S x9))
      (firstn pos (_cont x2)) ++
      as_mapOp h (Merge key p') x0 ++
      flat_map (fun x9 : BranchCell h => as_map (projT2S x9))
      (skipn (S pos) (_cont x2)) ++ as_map (_next x2) =
      as_mapOp (S h) (Merge key p)
      (p, (replaceNth pos (_cont x2) (existTS (fun _ : key => ptree h) midH x0), _next x2)).
    Proof. clear.
      unfold replaceNth. simpl BPlusTreeImplLocalComputeHelp.as_mapOp. intros. autorewrite with bpt_rw. fold ptree in *.
      norm list. simpl. auto.
    Qed.

    Lemma repBranch_nextPtr_as_match_head : forall h pos (x : list (BranchCell h)) x6 x7 X,
      skipn (S pos) x = x6 ->
      X = x7 ->
      repBranch_nextPtr x pos X =
      match head x6 with
        | Some v0 => firstPtr (projT2S v0)
        | None => x7
      end.
    Proof. clear.
      intros; unfold BPlusTreeImplModel.repBranch_nextPtr; subst.
      rewrite head_skipn. auto.
    Qed.
    Lemma bound_length : forall t (x : list t) pos x6,
      length x <= SIZE ->
      skipn (S pos) x = x6 ->
      length x6 <= SIZE - (S pos).
    Proof. clear.
      intros. subst. rewrite length_skipn. omega.
    Qed.

    Lemma repBranch_himp_rw2 : forall h k pos x4 x1 x10 ary x2 irr midH v0,
      pos < length (_cont x4) ->
      pos < SIZE ->
      nth_error (_cont x4) pos = Some v0 ->
      firstPtr (projT2S v0) = firstPtr (fst x2) ->
      (fst x4, (firstn SIZE x1, _next x4)) = x10 ->
      firstn pos (_cont x4) ++ existTS (fun _ : key => ptree h) k (fst x2) :: existTS (fun _ : key => ptree h) midH (snd x2) :: skipn (S pos) (_cont x4) = x1 ->
      repBranch h rep' ary 0 pos (firstn pos (_cont x4)) (firstPtr (fst x2)) ==>
      repBranch h rep' ary 0 pos (_cont x10) irr.
    Proof. clear; fold ptree in *; intros.
      rewrite <- H3. rewrite <- H4. autorewrite with bpt_rw.
      unfold BPlusTreeImplModel.repBranch; apply iter_imp; do 2 sep fail auto.
        repeat rewrite nth_error_firstn by omega. rewrite nth_error_firstn_app by omega.
        case_eq (nth_error (_cont x4)); intros; fold ptree in *; sep fail auto.
        eapply himp_rep'_eq; auto. f_equal. unfold BPlusTreeImplModel.repBranch_nextPtr.
        symmetry. rewrite nth_error_firstn by omega. 
        cut (length (firstn pos (_cont x4)) = pos); eauto with norm_list_length; intros.
        destruct (eq_nat_dec (S i) pos). 
          rewrite e. rewrite nth_error_app_second; eauto with norm_list_length.
          fold ptree in *; rewrite H4. norm arith. rewrite nth_error_red_0. rewrite nth_error_len_rw; eauto.
        rewrite nth_error_app_first.
        case_eq (nth_error (firstn pos (_cont x4)) (S i)); fold ptree in *; intros; rewrite H8; auto.
          elimtype False.
          cut (length (firstn pos (_cont x4)) <= S i); eauto with norm_list_length; intros.
          fold ptree in *. omega. fold ptree in *; rewrite H4. auto.
    Qed.
    Lemma length_correct : forall h (x4 : ptree (S h)) pos x10 x1 X Y,
      pos < length (_cont x4) -> 
      length (skipn (S pos) (_cont x4)) = SIZE - (pos + 1) -> 
      firstn pos (_cont x4) ++ X :: Y :: skipn (S pos) (_cont x4) = x1 ->
      (fst x4, (firstn SIZE x1, _next x4)) = x10 -> 
      length (_cont x10) = SIZE.
    Proof. clear; fold ptree in *; intros.
      subst. autorewrite with bpt_rw.
      cut (SIZE <= length (firstn pos (_cont x4) ++ X :: Y :: skipn (S pos) (_cont x4))); eauto with norm_list_length.
      cut (length (firstn pos (_cont x4)) = pos); eauto with norm_list_length; intros.
      rewrite length_app. simpl. rewrite H1. rewrite length_skipn. rewrite length_skipn in H0. norm arith in *.
      fold ptree in *. omega.
    Qed.
    Lemma full_contextual : forall h k x0 x11 k' x4 pos midH x2 x8 (x1 : list (BranchCell h)) x7,
         contextual h
           (fun (mi : LiftOrder key) (c : BranchCell h) =>
             inv h (projT2S c) mi (Val (projT1S c))) x8 x7
           (firstn pos (_cont x4))
      -> contextual h
          (fun (mi : LiftOrder key) (c : BranchCell h) =>
            inv h (projT2S c) mi (Val (projT1S c))) 
          (Val midH)
          (lastKey (_cont x4) (Val midH))
          (skipn (S pos) (_cont x4))
      -> firstn pos (_cont x4) ++ existTS (fun _ : key => ptree h) k (fst x2)
           :: existTS (fun _ : key => ptree h) midH (snd x2) :: skipn (S pos) (_cont x4) = x1
      -> inv h (fst x2) x7 (Val k)
      -> inv h (snd x2) (Val k) (Val midH)
      -> pos < SIZE
      -> pos < length (_cont x4)
      -> length (_cont x4) <= SIZE
      -> existTS (fun _ : key => ptree h) k' x0 =
           last (skipn (S pos) (_cont x4))
           (existTS (fun _ : key => ptree h) midH (snd x2))
      -> lastKey (firstn SIZE x1) x8 = x11
      -> contextual h
          (fun (mi : LiftOrder key) (c : BranchCell h) =>
            inv h (projT2S c) mi (Val (projT1S c))) 
          x8 (lastKey (_cont x4) (Val midH)) x1.
    Proof. clear; fold ptree in *; intros.
      rewrite <- H1. eapply contextual_append.
        intros. rewrite H9; auto.
        eauto. split. intuition. split; intuition.
    Qed.

      Lemma split_contextual : forall h k x0 x11 k' x4 pos midH x2 x8 (x1 : list (BranchCell h)) x7 x10,
           contextual h
             (fun (mi : LiftOrder key) (c : BranchCell h) =>
               inv h (projT2S c) mi (Val (projT1S c))) x8 x7
             (firstn pos (_cont x4))
        -> contextual h
            (fun (mi : LiftOrder key) (c : BranchCell h) =>
              inv h (projT2S c) mi (Val (projT1S c))) 
            (Val midH)
            (lastKey (_cont x4) (Val midH))
            (skipn (S pos) (_cont x4))
        -> firstn pos (_cont x4) ++ existTS (fun _ : key => ptree h) k (fst x2)
             :: existTS (fun _ : key => ptree h) midH (snd x2) :: skipn (S pos) (_cont x4) = x1
        -> inv h (fst x2) x7 (Val k)
        -> inv h (snd x2) (Val k) (Val midH)
        -> pos < SIZE
        -> pos < length (_cont x4)
        -> length (_cont x4) <= SIZE
        -> existTS (fun _ : key => ptree h) k' x0 =
             last (skipn (S pos) (_cont x4))
             (existTS (fun _ : key => ptree h) midH (snd x2))
        -> lastKey (firstn SIZE x1) x8 = x11
        -> (fst x4, (firstn SIZE x1, _next x4)) = x10
        -> contextual h
            (fun (mi : LiftOrder key) (c : BranchCell h) =>
              inv h (projT2S c) mi (Val (projT1S c))) x8 x11 
            (_cont x10).
      Proof. clear.
        intros. assert (contextual h
            (fun (mi : LiftOrder key) (c : BranchCell h) =>
              inv h (projT2S c) mi (Val (projT1S c))) 
            x8 (lastKey (_cont x4) (Val midH)) x1). eapply full_contextual; eauto.
        rewrite <- H9. autorewrite with bpt_rw in *; fold ptree in *. 
        rewrite <- (firstn_skipn SIZE x1) in H10.
        apply contextual_split in H10. intuition. subst; auto.
        intros. rewrite H11. auto.
      Qed.

      Lemma last_as_nth_error : forall T l (d:T),
        last l d = match nth_error l (length l - 1) with
                     | None => d
                     | Some v => v 
                   end.
      Proof. clear.
        intros. remember (length l) as L. 
        revert HeqL. revert l. revert d. induction L.
          destruct l. simpl. auto.
          intros; simpl in *; discriminate.
          destruct l. simpl; intros; discriminate.
          intros. simpl last. rewrite IHL; eauto. destruct l. norm arith.
          inversion HeqL. subst. norm list. auto.
          inversion HeqL; subst. norm arith. norm list. auto.
      Qed.

      Lemma skipn_firstn_comm : forall T (ls : list T) n n',
        skipn n (firstn n' ls) = firstn (n' - n) (skipn n ls).
      Proof. clear.
        induction ls.
          intros. norm list. auto.
          destruct n. intros. norm list. norm arith. auto.
          destruct n'. norm list. auto.
          norm arith. rewrite firstn_red_S. repeat rewrite skipn_red_S.  auto.
      Qed.
      Lemma split_repBranch : forall h ary pos midH x2 x4 x0 x10 k x1 k',
        (fst x4, (firstn SIZE x1, _next x4)) = x10 ->
        firstn pos (_cont x4) ++ existTS (fun _ : key => ptree h) k (fst x2) :: existTS (fun _ : key => ptree h) midH (snd x2) :: skipn (S pos) (_cont x4) = x1 ->
        length (skipn (S pos) (_cont x4)) = SIZE - (pos + 1) -> 
        pos < SIZE ->
        pos < length (_cont x4) ->
        existTS (fun _ : key => ptree h) k' x0 =
          last (skipn (S pos) (_cont x4)) (existTS (fun _ : key => ptree h) midH (snd x2)) ->
        repBranch h rep' ary (S pos) (SIZE - S pos)
          (existTS (fun _ : key => ptree h) midH (snd x2) :: skipn (S pos) (_cont x4)) (firstPtr x0) ==>
        repBranch h rep' ary (S pos) (SIZE - S pos) (skipn (S pos) (_cont x10)) (firstPtr x0).
      Proof. clear; fold ptree in *; intros.
        subst. autorewrite with bpt_rw.
        rewrite skipn_firstn_comm. cut (length (firstn pos (_cont x4)) = pos); eauto with norm_list_length; fold ptree in *; intros.
        norm list. norm arith. rewrite skipn_red_S. rewrite skipn_red_0.
        apply iter_imp. intros. simpl. sep fail auto. norm list.
        case_eq (nth_error
       (existTS (fun _ : key => ptree h) midH (snd x2)
        :: skipn (S pos) (_cont x4)) i); fold ptree in *; intros; rewrite H7; sep fail auto.
        apply himp_rep'_eq; auto. f_equal. unfold BPlusTreeImplModel.repBranch_nextPtr.
        destruct (eq_nat_dec (SIZE - S pos) (S i)). 
          symmetry. rewrite nth_error_len_rw; eauto with norm_list_length.
          norm arith in *. 

        rewrite last_as_nth_error in H4. fold ptree in *. rewrite H1 in H4.
        rewrite nth_error_red_S. norm list in H4. rewrite e in H4. norm arith in H4.
        norm list. case_eq (nth_error (_cont x4) (S pos + i)); fold ptree in *; intros. 
          rewrite H8 in *. rewrite <- H4. auto.
          rewrite H8 in *. auto.
        rewrite nth_error_firstn; try omega. auto.
      Qed.

      Lemma split_hint_match_conc : forall h P Q pos x1 x4 x2 k midH x10 x9 x0 l k',
        (fst x4, (firstn SIZE x1, _next x4)) = x10 ->
        firstn pos (_cont x4) ++ existTS (fun _ : key => ptree h) k (fst x2) :: existTS (fun _ : key => ptree h) midH (snd x2) :: skipn (S pos) (_cont x4) = x1 ->
        pos < length (_cont x4) ->
        length (_cont x4) <= SIZE ->
        l = ptrFor (fst x2) ->
        existTS (fun _ : key => ptree h) k' x0 = last (skipn (S pos) (_cont x4)) (existTS (fun _ : key => ptree h) midH (snd x2)) ->
        pos < SIZE ->
        (P ==> x9 ~~> Some (k, l) * 
               rep' l (Some (firstPtr (snd x2))) (fst x2) * Q) ->
        P ==> match nth_error (_cont x10) (pos - 0) with
                | Some v' =>
                  x9 ~~> Some (projT1S v', ptrFor (projT2S v')) *
                  rep' (ptrFor (projT2S v')) (Some (repBranch_nextPtr (_cont x10) (pos - 0) (firstPtr x0))) (projT2S v')
                | None => x9 ~~> @None (key * ptr)
              end * Q.
      Proof. clear; fold ptree in *; intros.
        eapply himp_trans; [ eassumption | clear H6 ].
        subst; fold ptree in *. autorewrite with bpt_rw.
        sep fail auto. norm arith. norm list. 
        cut (length (firstn pos (_cont x4)) = pos); eauto with norm_list_length; intros; fold ptree in *. rewrite H. norm arith.
        rewrite nth_error_red_0. simpl. sep fail auto. apply himp_rep'_eq; auto.

        f_equal. unfold BPlusTreeImplModel.repBranch_nextPtr. norm list. rewrite H. norm arith.
        Change (SIZE - pos) into (S (SIZE - S pos)) using omega. rewrite firstn_red_S. rewrite nth_error_red_S.
        destruct (eq_nat_dec SIZE (S pos)).
          rewrite <- e in *. norm arith. norm list. norm list in H4. inversion H4. auto.
          Change (SIZE - S pos) into (S (SIZE - S (S pos))) using omega. norm list. auto.
      Qed.

      Lemma split_ptrFor : forall h x12 nxt (x4 : ptree (S h)),
        _next x4 = x12 -> ptrFor (_next x4) = nxt -> nxt = ptrFor x12.
      Proof. clear.
        intros; subst; auto.
      Qed.
      Lemma split_lastKey : forall h (x10 : ptree (S h)) x8 x11 x1 X Y,
        lastKey (firstn SIZE x1) x8 = x11 ->
        (X, (firstn SIZE x1, Y)) = x10 ->
        x11 = lastKey  (_cont x10) x8.
      Proof. clear.
        intros; subst; auto.
      Qed.
      
      Lemma list_unfold_end : forall T (ls : list T) a,
        a :: ls = firstn (length ls) (a :: ls) ++ (last ls a) :: nil.
      Proof. clear.
        induction ls. simpl. auto.
        intros. simpl length. norm list. f_equal. auto.
      Qed.

      Lemma split_inv_left : forall h k x0 x11 k' x4 pos midH x2 x8 (x1 : list (BranchCell h)) x10 x7,
        firstn pos (_cont x4) ++ existTS (fun _ : key => ptree h) k (fst x2) :: existTS (fun _ : key => ptree h) midH (snd x2) :: skipn (S pos) (_cont x4) = x1 ->
        lastKey (firstn SIZE x1) x8 = x11 ->
        existTS (fun _ : key => ptree h) k' x0 = last (skipn (S pos) (_cont x4)) (existTS (fun _ : key => ptree h) midH (snd x2)) ->
        contextual h
          (fun (mi : LiftOrder key) (c : BranchCell h) =>
           inv h (projT2S c) mi (Val (projT1S c))) 
          (Val midH)
          (lastKey (_cont x4) (Val midH))
          (skipn (S pos) (_cont x4)) ->
        (fst x4, (firstn SIZE x1, _next x4)) = x10 ->
        length (_cont x10) = SIZE ->
        length (skipn (S pos) (_cont x4)) = SIZE - (pos + 1) ->
        pos < SIZE ->
        pos < length (_cont x4) ->
        length (_cont x4) <= SIZE ->
        inv h (snd x2) (Val k) (Val midH) ->
        inv h (fst x2) x7 (Val k) ->
        contextual h
             (fun (mi : LiftOrder key) (c : BranchCell h) =>
               inv h (projT2S c) mi (Val (projT1S c))) x8 x7
             (firstn pos (_cont x4)) ->
        inv h x0 x11 (Val k').
      Proof. clear; fold ptree in *; intros.
        assert (contextual h
            (fun (mi : LiftOrder key) (c : BranchCell h) =>
              inv h (projT2S c) mi (Val (projT1S c))) 
            x8 (lastKey (_cont x4) (Val midH)) x1); fold ptree in *. eapply full_contextual; eauto.
        rewrite <- H in *.  rewrite <- H3 in *. autorewrite with bpt_rw in *.
        cut (length (firstn pos (_cont x4)) = pos); eauto with norm_list_length; intros; fold ptree in *. 
        case_eq (skipn (S pos) (_cont x4)); fold ptree in *; intros; rewrite H14 in *.
          simpl in H1. assert (S pos = SIZE). simpl in H5.  norm arith in H5. omega.
          rewrite <- H15 in H0. rewrite firstn_append in H0. rewrite H13 in *. 
          norm arith in *. norm list in H0. rewrite lastKey_last in H0. 
          eapply contextual_split in H12. simpl in H12. intuition. inversion H1. rewrite <- H0. simpl. auto.
          intros. rewrite H16; auto. omega.

          rewrite (list_unfold_end l s) in H0. norm list in H0. rewrite H13 in *. simpl in H5. norm arith in *.
          rewrite last_cons_red in H1. rewrite (list_unfold_end l s) in H12.  rewrite <- H1 in *.
          apply contextual_split in H12. Transparent BPlusTreeImplModel.contextual.
          simpl in H12. intuition. apply contextual_split in H18. simpl in H18.
          intuition. rewrite <- H0. Change (SIZE - pos) into (S (S (SIZE - S (S pos)))) using omega.
          norm list. rewrite lastKey_append. simpl. assert (length l = SIZE - S (S pos)). omega.
          rewrite <- H19. cut (length (firstn (length l) (s :: l)) = length l); eauto with norm_list_length; intros.
          rewrite H21. norm arith. rewrite firstn_0. rewrite app_nil. auto.
          intros; rewrite H17; auto.
          intros. rewrite H15; auto.
      Qed.
      Lemma split_inv_right : forall h k x0 x11 k' x4 pos midH x2 x8 (x1 : list (BranchCell h)) x10 x7 x6 x12,
        firstn pos (_cont x4) ++ existTS (fun _ : key => ptree h) k (fst x2) :: existTS (fun _ : key => ptree h) midH (snd x2) :: skipn (S pos) (_cont x4) = x1 ->
        lastKey (firstn SIZE x1) x8 = x11 ->
        existTS (fun _ : key => ptree h) k' x0 = last (skipn (S pos) (_cont x4)) (existTS (fun _ : key => ptree h) midH (snd x2)) ->
        contextual h
          (fun (mi : LiftOrder key) (c : BranchCell h) =>
           inv h (projT2S c) mi (Val (projT1S c))) 
          (Val midH)
          (lastKey (_cont x4) (Val midH))
          (skipn (S pos) (_cont x4)) ->
        (fst x4, (firstn SIZE x1, _next x4)) = x10 ->
        length (_cont x10) = SIZE ->
        length (skipn (S pos) (_cont x4)) = SIZE - (pos + 1) ->
        pos < SIZE ->
        pos < length (_cont x4) ->
        length (_cont x4) <= SIZE ->
        inv h (snd x2) (Val k) (Val midH) ->
        inv h (fst x2) x7 (Val k) ->
        contextual h
             (fun (mi : LiftOrder key) (c : BranchCell h) =>
               inv h (projT2S c) mi (Val (projT1S c))) x8 x7
             (firstn pos (_cont x4)) ->
        inv h (_next x4) (lastKey (_cont x4) (Val midH)) x6 ->
        _next x4 = x12 ->
        inv h x12 (Val k') x6.
      Proof. clear; fold ptree in *; intros.
        rewrite <- H13. rewrite <- (firstn_skipn (S pos) (_cont x4)) in H12.
        case_eq (skipn (S pos) (_cont x4)); fold ptree in *; intros; rewrite H14 in *.
          simpl in H1. inversion H1. simpl in H2. rewrite H2. norm list in H12. auto.
          
          rewrite (list_unfold_end l s) in H12. rewrite <- app_ass in H12. rewrite lastKey_last in H12.
          rewrite (list_unfold_end l s) in H1.
          rewrite ThinkList.last_cons in H1.  rewrite <- H1 in *. auto.
      Qed.

      Lemma split_return_firstPtr : forall h k (x4 : ptree (S h)) x1
        (x13 : ptree h * ptree h) resOp (x12 : opModel (S h) resOp) x10 x0 k' midH pos v1,
        nth_error (_cont x4) pos = Some v1 ->
        firstPtr (projT2S v1) = firstPtr (fst x13) ->
        (fst x4, (firstn SIZE x1, _next x4)) = x10 ->
        pos < length (_cont x4) ->
        firstn pos (_cont x4) ++ existTS (fun _ : key => ptree h) k (fst x13) :: existTS (fun _ : key => ptree h) midH (snd x13) :: skipn (S pos) (_cont x4) = x1 ->
        existTS (fun _ : key => ptree h) k' x0 = last (skipn (S pos) (_cont x4)) (existTS (fun _ : key => ptree h) midH (snd x13)) ->
        firstPtrOp (S h) resOp x12 =
        match head (_cont x10) with
          | Some n => firstPtr (projT2S n)
          | None => firstPtr x0
        end ->
        firstPtrOp (S h) resOp x12 =
        match _cont x4 with
          | nil => firstPtr (fst x13)
          | n :: _ => firstPtr (projT2S n)
        end.
      Proof.
        Change SIZE into (S (SIZE - 1)) using omega.
        clear; intros; fold ptree in *.
        rewrite H5; clear H5. rewrite <- match_head_is_list. subst. autorewrite with bpt_rw in *.
        Lemma head_is_nth_error_0 : forall T (l : list T), head l = nth_error l 0.
        Proof. clear. induction l; auto. Qed.
        repeat rewrite head_is_nth_error_0.
        destruct pos.
          norm list. rewrite H. simpl. auto.
          norm list. destruct (_cont x4). norm list in H. discriminate. norm list. auto.
      Qed.
    Lemma split_content : forall h (x4: ptree (S h)) pos resOp x13 x12 x10 (x0 :ptree h) (x11 : ptree h) x1 k midH k',
      _next x4 = x11 ->
      pos < SIZE ->
      pos < length (_cont x4) ->
      length (_cont x4) <= SIZE ->
      length (skipn (S pos) (_cont x4)) = SIZE - (pos + 1) ->
      firstn pos (_cont x4) ++ existTS (fun _ : key => ptree h) k (fst x13) :: existTS (fun _ : key => ptree h) midH (snd x13) :: skipn (S pos) (_cont x4) = x1 ->
      (fst x4, (firstn SIZE x1, _next x4)) = x10 ->
      existTS (fun _ : key => ptree h) k' x0 = last (skipn (S pos) (_cont x4)) (existTS (fun _ : key => ptree h) midH (snd x13)) ->
      flat_map (fun x0 : BranchCell h => as_map (projT2S x0)) (_cont x10) ++ as_map x0 ++ as_map x11 = as_mapOp (S h) resOp x12 ->
      flat_map (fun x14 : BranchCell h => as_map (projT2S x14)) (firstn pos (_cont x4)) ++
        (as_map (fst x13) ++ as_map (snd x13)) ++
        flat_map (fun x14 : BranchCell h => as_map (projT2S x14))
        (skipn (S pos) (_cont x4)) ++ as_map (_next x4) =
      as_mapOp (S h) resOp x12.
    Proof. clear; intros; fold ptree in *.
      rewrite <- H7. subst. autorewrite with bpt_rw in *. norm list.
      cut (length (firstn pos (_cont x4)) = pos); eauto with norm_list_length; intros; fold ptree in *.
      rewrite H. destruct (eq_nat_dec SIZE (S pos)).
         Change (SIZE - pos) into 1 using omega. rewrite e in *. norm arith in *. norm list.
           f_equal. simpl. f_equal. f_equal. norm list in H6. inversion H6. auto.
         Change (SIZE - pos) into (S (S (SIZE - S (S pos)))) using omega. norm arith in *. norm list.
           simpl. f_equal. f_equal. f_equal. case_eq (skipn (S pos) (_cont x4)); fold ptree in *; intros.
             rewrite H4 in *. elimtype False; simpl in *. omega.
             rewrite H4 in *. clear H7. simpl in H3. rewrite (list_unfold_end l s) in *. rewrite ThinkList.last_cons in H6.
             simpl in *. Change (SIZE - S (S pos)) into (length l) using omega. norm list.
             cut (length (firstn (length l) (s :: l)) = length l); fold ptree in *; intros.
             rewrite H5. norm arith. rewrite <- H6. simpl. rewrite firstn_0. auto.
           eauto with norm_list_length.
    Qed.

    Lemma himp_repBranch_merge : forall h k ary pos x10 x11 (x4 : ptree (S h)) p midH (v0 : BranchCell h),
      firstPtr (projT2S v0) = firstPtr (fst x11) ->
      pos < length (_cont x4) ->
      length (_cont x4) <= SIZE ->
      nth_error (_cont x4) pos = Some v0 ->
      (p, (firstn pos (_cont x4) ++ existTS (fun _ : key => ptree h) k (fst x11) :: existTS (fun _ : key => ptree h) midH (snd x11) :: skipn (S pos) (_cont x4), _next x4)) = x10 ->
      repBranch h rep' ary 0 pos (firstn pos (_cont x4)) (firstPtr (fst x11)) ==>
      repBranch h rep' ary 0 pos (_cont x10) (firstPtr (_next x10)).
    Proof. clear; intros; fold ptree in *.
      apply iter_imp; do 2 sep fail auto. autorewrite with bpt_rw.
      cut (length (firstn pos (_cont x4)) = pos); eauto with norm_list_length; intros.
      rewrite nth_error_app_first. case_eq (nth_error (firstn pos (_cont x4))); intros; fold ptree in *.
      sep fail auto. apply himp_rep'_eq; auto. f_equal.
      autorewrite with bpt_rw. simpl. auto. auto.
      fold ptree in *; rewrite H6; auto.
    Qed.
    Lemma himp_repBranch_merge' : forall h k ary pos x10 midH x4 (x11 : ptree h * ptree h) p,
      pos < length (_cont x4) ->
      length (_cont x4) <= SIZE ->
      (p, (firstn pos (_cont x4) ++ existTS (fun _ : key => ptree h) k (fst x11) :: existTS (fun _ : key => ptree h) midH (snd x11) :: skipn (S pos) (_cont x4), _next x4)) = x10 ->
      repBranch h rep' ary (S pos) (SIZE - S pos) (existTS (fun _ : key => ptree h) midH (snd x11) :: skipn (S pos) (_cont x4)) (firstPtr (_next x4)) ==>
      repBranch h rep' ary (S pos) (SIZE - S pos) (skipn (S pos) (_cont x10)) (firstPtr (_next x10)).
    Proof. clear; intros; fold ptree in *.
      apply iter_imp; do 2 sep fail auto. autorewrite with bpt_rw.
      cut (length (firstn pos (_cont x4)) = pos); eauto with norm_list_length; intros.
      rewrite skipn_app'. norm arith. rewrite skipn_red_S; auto. auto. auto.
    Qed.

    Lemma merge_length : forall h x10 x4 p k x11 pos midH,
      pos < length (_cont x4) ->
      length (_cont x4) <= SIZE ->
      (p, (firstn pos (_cont x4) ++ existTS (fun _ : key => ptree h) k (fst x11) :: existTS (fun _ : key => ptree h) midH (snd x11) :: skipn (S pos) (_cont x4), _next x4)) = x10 ->
      length (skipn (S pos) (_cont x4)) < SIZE - (pos + 1) ->
      length (_cont x10) <= SIZE.
    Proof. clear; intros; fold ptree in*.
      subst; autorewrite with bpt_rw.
      rewrite length_app. simpl.
      cut (length (firstn pos (_cont x4)) = pos); eauto with norm_list_length; intros; fold ptree in *.
      rewrite H1. omega.
    Qed.
    Lemma merge_firstPtr : forall h k x4 pos midH p x10 x11 v0,
      nth_error (_cont x4) pos = Some v0 ->
      firstPtr (projT2S v0) = firstPtr (fst x11) ->
      pos < length (_cont x4) ->
      length (_cont x4) <= SIZE ->
      (p, (firstn pos (_cont x4) ++ existTS (fun _ : key => ptree h) k (fst x11) :: existTS (fun _ : key => ptree h) midH (snd x11) :: skipn (S pos) (_cont x4), _next x4)) = x10 ->
      match _cont x10 with
        | nil => firstPtr (_next x10)
        | a :: _ => firstPtr (projT2S a)
      end =
      match _cont x4 with
        | nil => firstPtr (fst x11)
        | n :: _ => firstPtr (projT2S n)
      end.
    Proof. clear; intros; fold ptree in *.
      subst. autorewrite with bpt_rw.
      destruct (_cont x4). norm list in H. discriminate.
      destruct pos. Transparent firstn skipn nth_error. simpl.
        inversion H. auto.
        simpl. auto.
    Qed.
    Lemma merge_flat_maps : forall h k x4 pos midH p x10 x11 v0,
      nth_error (_cont x4) pos = Some v0 ->
      firstPtr (projT2S v0) = firstPtr (fst x11) ->
      pos < length (_cont x4) ->
      length (_cont x4) <= SIZE ->
      (p, (firstn pos (_cont x4) ++ existTS (fun _ : key => ptree h) k (fst x11) :: existTS (fun _ : key => ptree h) midH (snd x11) :: skipn (S pos) (_cont x4), _next x4)) = x10 ->
      flat_map (fun x12 : BranchCell h => as_map (projT2S x12))
          (firstn pos (_cont x4)) ++
        (as_map (fst x11) ++ as_map (snd x11)) ++
        flat_map (fun x12 : BranchCell h => as_map (projT2S x12))
          (skipn (S pos) (_cont x4)) ++ as_map (_next x4) =
        flat_map (fun x12 : BranchCell h => as_map (projT2S x12)) (_cont x10) ++
        as_map (_next x10).
    Proof. clear; intros; fold ptree in *.
      subst; autorewrite with bpt_rw. rewrite flat_map_app. repeat rewrite flat_map_cons.
      Opaque firstn skipn nth_error. simpl.
      repeat rewrite app_ass. auto.
    Qed.
    Lemma merge_inv : forall h k x11 x4 pos midH x8 x7 x6 x10 p v0,
      nth_error (_cont x4) pos = Some v0 ->
      firstPtr (projT2S v0) = firstPtr (fst x11) ->
      pos < length (_cont x4) ->
      length (_cont x4) <= SIZE ->
      (p, (firstn pos (_cont x4) ++ existTS (fun _ : key => ptree h) k (fst x11) :: existTS (fun _ : key => ptree h) midH (snd x11) :: skipn (S pos) (_cont x4), _next x4)) = x10 ->
      contextual h
          (fun (mi : LiftOrder key) (c : BranchCell h) =>
           inv h (projT2S c) mi (Val (projT1S c))) x8 x7
          (firstn pos (_cont x4)) ->
      contextual h
          (fun (mi : LiftOrder key) (c : BranchCell h) =>
           inv h (projT2S c) mi (Val (projT1S c))) 
          (Val midH) (lastKey (_cont x4) (Val midH)) (skipn (S pos) (_cont x4)) ->
      x7 = lastKey (firstn pos (_cont x4)) x8 ->
      Val midH = lastKey (firstn (S pos) (_cont x4)) x8 ->
      inv h (_next x4) (lastKey (_cont x4) (Val midH)) x6 ->
      inv h (fst x11) x7 (Val k) ->
      inv h (snd x11) (Val k) (Val midH) ->
      inv (S h) x10 x8 x6.
    Proof. clear; intros; fold ptree in *.
      subst. split; fold ptree in *. eapply contextual_append.
      intros. eapply (@inv_subst key value KOT h (projT2S c) _ _ (Val (projT1S c)) (Val (projT1S c)) H3).
      reflexivity. auto. eauto. split. intuition. simpl. intuition.
      rewrite lastKey_app. simpl. rewrite <- (firstn_skipn (S pos) (_cont x4)) in H5 at 1.
      rewrite lastKey_app in H5; fold ptree in *. 
      case_eq (skipn (S pos) (_cont x4)); fold ptree in *; intros; rewrite H3 in *. simpl in *.
        reflexivity.
        rewrite (list_unfold_end l s) in *. rewrite lastKey_last in *. auto.
      rewrite <- (firstn_skipn (S pos) (_cont x4)) in H8. rewrite lastKey_append in *. simpl in *.
      case_eq (skipn (S pos) (_cont x4)); fold ptree in *; intros; rewrite H3 in *; simpl in *.
        rewrite <- (firstn_skipn (S pos) (_cont x4)) in H5. rewrite lastKey_append in H5; fold ptree in *. rewrite H3 in *. simpl in *.
        eapply (@inv_subst key value KOT h (_next x4) _ _ x6 x6). eassumption. reflexivity. auto.
        intuition.
    Qed.

    Lemma reduce_match : forall h k P Q pos x10 x9 x11 p x4 midH v0,
      nth_error (_cont x4) pos = Some v0 ->
      pos < length (_cont x4) ->
      length (_cont x4) <= SIZE ->
      (p, (firstn pos (_cont x4) ++ existTS (fun _ : key => ptree h) k (fst x11) :: existTS (fun _ : key => ptree h) midH (snd x11) :: skipn (S pos) (_cont x4), _next x4)) = x10 ->
      (P ==> x9 ~~> Some (k,ptrFor (fst x11)) * rep' (ptrFor (fst x11)) (Some (firstPtr (snd x11))) (fst x11) * Q) ->
      P ==>
      match nth_error (_cont x10) (pos - 0) with
        | Some v' =>
          x9 ~~> Some (projT1S v', ptrFor (projT2S v')) *
          rep' (ptrFor (projT2S v')) (Some (repBranch_nextPtr (_cont x10) (pos - 0) (firstPtr (_next x10)))) (projT2S v')
        | None => x9 ~~> @None (key * ptr)
      end * Q.
    Proof. clear; intros; fold ptree in *.
      eapply himp_trans; [ eassumption | clear H3 ].
      subst. autorewrite with bpt_rw.
      unfold BPlusTreeImplModel.repBranch_nextPtr. norm arith. norm list.
      cut (length (firstn pos (_cont x4)) = pos); eauto with norm_list_length; intros; fold ptree in *.
      rewrite H2; norm arith. Transparent nth_error. simpl. Opaque nth_error. bpt_elab. sep fail auto.
    Qed.

    Opaque skipn firstn nth_error.
    Definition mergeOpInternal : forall (min midL max : [LiftOrder key]) (h : nat)
      (p : ptr) (ary : array) (nxt : ptr) (optr : [option ptr]) (pos : nat) (midH : key) (res' : RES h) (m : [ptree (S h)]),
      STsep (min ~~ midL ~~ max ~~ m ~~ optr ~~ opm :~~ projT2 (snd res') in
               let o := projT1 (snd res') in
               p' :~~ array_plus ary pos in
               [pos < SIZE] *
               p ~~> mkNode (S h) ary (Some nxt) *
               Exists p'' :@ ptr,
               p' ~~> Some (midH, p'') *
               [array_length ary = SIZE] * 
               [pos < length (_cont m)] * [length (_cont m) <= SIZE] *
               [midL = lastKey (firstn pos (_cont m)) min] *
               [Val midH = lastKey (firstn (S pos) (_cont m)) min] *
               [contextual h (fun mi c => inv h (projT2S c) mi (Val (projT1S c))) min midL (firstn pos (_cont m))] *
               [contextual h (fun mi c => inv h (projT2S c) mi (Val (projT1S c))) (Val midH) (lastKey (_cont m) (Val midH)) (skipn (S pos) (_cont m))] *
               [inv h (_next m) (lastKey (_cont m) (Val midH)) max] *
               repBranch h (rep') ary 0 pos (firstn pos (_cont m)) (firstPtrOp _ _ opm) *
               repBranch h (rep') ary (S pos) (SIZE - S pos) (skipn (S pos) (_cont m)) (firstPtr (_next m)) *
               rep' nxt optr (_next m) *
               repOp h o opm midL (Val midH) (Some (repBranch_nextPtr (_cont m) pos (firstPtr (_next m)))) *
               Exists v :@ BranchCell h,
               [nth_error (_cont m) pos = Some v] * [projT1S v = midH] * [firstPtr (projT2S v) = firstPtrOp _ _ opm])
            (fun res : RES (S h) => min ~~ max ~~ optr ~~ m ~~ 
               opm :~~ projT2 (snd res) in opm' :~~ projT2 (snd res') in
               repOp (S h) (projT1 (snd res)) opm min max optr * 
               [firstPtrOp _ _ opm = match _cont m with
                                       | nil    => firstPtrOp _ _ opm' (** JUNK **)
                                       | n :: _ => firstPtr (projT2S n)
                                     end] *
               [fst res = fst res'] *
               [List.flat_map (fun x : BranchCell h => as_map (projT2S x)) (firstn pos (_cont m)) ++ as_mapOp _ _ opm' ++ 
                List.flat_map (fun x : BranchCell h => as_map (projT2S x)) (skipn (S pos) (_cont m)) ++ as_map (_next m) = as_mapOp _ _ opm]).
      refine (fun min midL max h p ary nxt optr pos midH res m =>
        match snd res as OP return snd res = OP -> _ with
          | existT (Merge p') opm => fun pf =>
            upd_array ary pos (Some (midH, p')) <@> _ ;;
            let rM : [opModel (S h) (Merge key p)] :=
              m ~~~' opm ~~~ (p, (replaceNth pos (_cont m) (existTS (fun _ => ptree h) midH opm), _next m)) in
            {{ Return (fst res, existT _ (Merge key p) rM) }}
          | existT (Split l k r) opm => fun pf =>
            ml <- shiftInsert' SIZE value h (pos + 1) ary (midH, r) (opm ~~~ snd opm) (m ~~~ skipn (S pos) (_cont m)) (m ~~~ firstPtr (_next m)) <@> _ ;
            upd_array ary pos (Some (k, l)) <@> _ ;;
            let lsM' := m ~~~' opm ~~~
              firstn pos (_cont m) ++ existTS _ k (fst opm) :: existTS _ midH (snd opm) :: skipn (S pos) (_cont m)
            in
            match ml as ml' return ml = ml' -> _ with
              | (Some (k',v,m''), full) => fun pf' =>
                resOp <- @splitBranch_atEnd SIZE pfMin SIZE_even key value KOT min 
                     (lsM' ~~~' min ~~~ lastKey (firstn SIZE lsM') min) max h p ary v nxt optr m'' k' 
                     (m ~~~ _next m) 
                     (m ~~~' lsM' ~~~ (ptrFor m, (firstn SIZE lsM', _next m))) <@> _ ;
                {{ Return (fst res, resOp) }}
              | (None, _) => fun pf' => 
                (** Return Merge **)
                let rM : [opModel (S h) (Merge key p)] := m ~~~' opm ~~~
                  (p, (firstn pos (_cont m) ++ (existTS (fun _ => ptree h) k (fst opm)) :: (existTS (fun _ => ptree h) midH (snd opm)) :: skipn (S pos) (_cont m), _next m))
                in
                {{ Return (fst res, existT _ (Merge key p) rM) }}
            end (refl_equal _)
        end (refl_equal _)); clear Fn.
    Proof. idtac "Starting mergeOpInternal".
      (** Merge **)
      solve [ sep2 fail bpt_elim; sep_unify ].
      solve [ sep_unify ].
      solve [ sep_unify ].
      
      unfold rM in *; clear rM. rewrite pf in *; clear pf. norm pair in *.
      sep2 bpt_elab bpt_elim.
        generalize dependent x8; rewrite H9 in *; clear H9. intros. norm pair in *. red_prems.
        rewrite <- H7 in *; clear H7. 
        norm pair in *; fold ptree in *. Opaque BPlusTreeImplModel.rep'. unfold BPlusTreeImplLocalComputeHelp.repOp.
      Hint Immediate himp_repBranch_skipn_replacenth himp_repBranch_replaceNth : bpt_sep.
      Hint Resolve repBranch_firstn_extra_irr : bpt_sep.
        sep2 bpt_elab bpt_elim.
          sep2 fail bpt_elim. 
      Hint Rewrite <- repBranch_nextPtr_replaceNth using solve [ eauto with norm_list_length ] : bpt_rw.
          norm arith. rewrite nth_error_replaceNth; eauto.  
      Hint Resolve mergeOpInternal_merge_firstPtr mergeOpInternal_merge_length mergeOpInternal_merge_inv.
      Hint Immediate mergeOpInternal_solve_flatmaps.
        solve [ sep2 fail bpt_elim; sep fail idtac ].

      (** Split **)
      rewrite pf in *; clear pf. simpl projT1 in *; simpl projT2 in *; norm pair; fold ptree in *.
      Hint Resolve bound_length repBranch_nextPtr_as_match_head.
      solve [ sep2 ltac:(norm arith || bpt_elab) bpt_elim; sep_unify ].
      solve [ sep_unify ].
      solve [ sep2 bpt_elab bpt_elim; rewrite <- H8; rewrite <- H9; rewrite <- H7; sep_unify ].
      solve [ sep_unify ].

      (** FULL **)
      sep2 bpt_elab bpt_elim; fold ptree in *. instantiate_conc nxt. 
        unfold lsM' in *; clear lsM'; rewrite pf'. simpl.

      Hint Resolve length_correct split_contextual.
      Hint Immediate split_repBranch repBranch_himp_rw2 : bpt_sep.

      sep2 bpt_elab bpt_elim.
        rewrite H11. auto.
        search_conc ltac:(idtac; match goal with 
                                   | [ |- _ ==> match _ with
                                                  | Some _ => _ 
                                                  | None => _ 
                                                end * _ ] => eapply split_hint_match_conc; eauto
                                 end).

      Hint Immediate split_ptrFor split_lastKey.
      Hint Resolve split_inv_left split_inv_right.
      solve [ sep2 fail bpt_elim; rewrite <- H11; sep_unify ].
      solve [ sep_unify ].
      solve [ sep_unify ].
      sep2 bpt_elab bpt_elim. fold ptree in *.
        generalize dependent x12. rewrite H16 in *. generalize dependent x13. rewrite pf in *.
        norm pair. progress unfold lsM' in *; clear lsM'. simpl.
      Hint Immediate split_content split_return_firstPtr.
        solve [ sep2 fail bpt_elim; sep_unify ].

      (** Don't split **)
      solve [ sep_unify ].
      sep2 bpt_elab bpt_elim.
        generalize dependent x11; generalize dependent x10; rewrite H12 in *; rewrite pf in *.
        simpl; fold ptree in *. rewrite pf'. unfold rM in *; clear rM; unfold lsM' in *; clear lsM'. 
        simpl.
      Transparent BPlusTreeImplModel.rep'. simpl BPlusTreeImplModel.rep'. Opaque BPlusTreeImplModel.rep'.
      Hint Immediate himp_repBranch_merge himp_repBranch_merge' : bpt_sep.
      Hint Immediate merge_inv merge_length merge_flat_maps merge_firstPtr.
        sep2 fail bpt_elim.
      subst; auto.
      search_conc ltac:(eapply reduce_match; eauto).
      sep2 fail bpt_elim.
        rewrite <- H. simpl. autorewrite with bpt_rw.
idtac "Ending mergeOpInternal".
        solve [ sep2 fail bpt_elim; sep_unify ].
  Qed.

(*  End mergeOpInternal. *)

(*  Section localCompute'. *)

    Require Import BPlusTreeImplNewFree.

    Open Local Scope stsep_scope.

    Lemma next_inv' : forall h' x x0 x3 x2 x4 i,
         x = lastKey (firstn i (_cont x0)) x3
      -> length (_cont x0) <= SIZE
      -> length (_cont x0) <= i
      -> _next x0 = x4
      -> inv (S h') x0 x3 x2
      -> inv h' x4 x x2.
    Proof. clear.
      intros. destruct x0 as [ ? [ ? ? ] ]. autorewrite with bpt_rw in *. subst.
      destruct H3. norm list. auto.
    Qed.

    Lemma firstPtrOp_manual : forall h' (v : RES (S h')) x5 (x0 : ptree (S h')) (rr : RES h') x4,
      firstPtrOp h' (projT1 (snd rr)) x4 = firstPtr (_next x0) ->
      firstPtrOp (S h') (projT1 (snd v)) x5 =
      match head (_cont x0) with
        | Some n => firstPtr (projT2S n)
        | None => firstPtrOp h' (projT1 (snd rr)) x4
      end ->
      firstPtrOp (S h') (projT1 (snd v)) x5 = firstPtr x0.
    Proof. clear.
      intros. rewrite H0. destruct x0 as [ ? [ ? ? ] ]. destruct l; simpl in *; think.
    Qed.

    Lemma prove_neighborhood : forall h i i' i'' v (x0 : ptree (S h)),
      i = i' ->
      i = i'' ->
      v =
      match nth_error (_cont x0) i with
        | Some v => Some (projT1S v, ptrFor (projT2S v))
        | None => None
      end ->
      match nth_error (_cont x0) i' with
        | Some v0 =>
          [i' < length (_cont x0)] *
          rep' (ptrFor (projT2S v0))
          (Some (repBranch_nextPtr (_cont x0) i' (firstPtr (_next x0))))
          (projT2S v0)
        | None => [length (_cont x0) <= i']
      end ==>
      match nth_error (_cont x0) i'' with
        | Some v' =>
          [v = Some (projT1S v', ptrFor (projT2S v'))] * [i'' < length (_cont x0)] *
          rep' (ptrFor (projT2S v'))
          (Some (repBranch_nextPtr (_cont x0) i'' (firstPtr (_next x0)))) (projT2S v')
        | None => [v = None] * [length (_cont x0) <= i'']
      end.
    Proof. clear.
      intros. subst. subst. case_eq (nth_error (_cont x0) i''); sep fail auto.
    Qed.

    Lemma pick_okv_Some : forall h okv k' p' (m0 : ptree (S h)) i (P Q : hprop),
      okv = Some (k',p') ->
      ((Exists v' :@ BranchCell h,
        [nth_error (_cont m0) i = Some v'] * [i < length (_cont m0)] *
        [okv = Some (projT1S v', ptrFor (projT2S v'))] *
        rep' (ptrFor (projT2S v'))
        (Some (repBranch_nextPtr (_cont m0) i (firstPtr (_next m0))))
        (projT2S v') * P)%hprop ==> Q) ->
      match nth_error (_cont m0) i with
        | Some v' =>
          [okv = Some (projT1S v', ptrFor (projT2S v'))] *
          [i < length (_cont m0)] *
          rep' (ptrFor (projT2S v'))
          (Some (repBranch_nextPtr (_cont m0) i (firstPtr (_next m0))))
          (projT2S v')
        | None => [okv = None] * [length (_cont m0) <= i]
      end  * P ==> Q.
    Proof. clear.
      intros. eapply himp_trans; [ | eassumption ].
      case_eq (nth_error (_cont m0) i). sep fail auto.
      intros. intro_pure. subst. congruence.
    Qed.

    Lemma lastKey_nth_error_eq : forall h v0 i (x0 : list (BranchCell h)) x3,
      nth_error x0 i = Some v0 ->
      Val (projT1S v0) = lastKey (firstn (S i) x0) x3.
    Proof. clear.
      intros; unfold BPlusTreeImplModel.lastKey.
      cut (length (firstn (S i) x0) = S i); eauto with norm_list_length. intros.
      erewrite firstn_nth_error_expand; try eassumption.
      rewrite (@lastKey_last _ _ (firstn i x0)); auto. (** COQ BUG **)
    Qed.
    Lemma key_between_change_lb : forall x x2 x3 x',
      key_between x3 tK x2 ->
      x' << tK ->
      x' = x ->
      key_between (Val x) tK x2.
    Proof.
      unfold BPlusTreeImplModel.key_between. intros; subst; tauto.
    Qed.

    Lemma simplify_len : forall h (x0 : ptree (S h)) i okv k' p' P Q,
      okv = Some (k',p') ->
      i <= length (_cont x0) ->
      ((Exists v0 :@ BranchCell h,
        [nth_error (_cont x0) i = Some v0] *
        [okv = Some (projT1S v0, ptrFor (projT2S v0))] *
        [i < length (_cont x0)] *
        rep' (ptrFor (projT2S v0))
        (Some (repBranch_nextPtr (_cont x0) i (firstPtr (_next x0)))) (projT2S v0) * P)
      ==> Q) ->
      match nth_error (_cont x0) i with
        | Some v' =>
          [okv = Some (projT1S v', ptrFor (projT2S v'))] *
          [i < length (_cont x0)] *
          rep' (ptrFor (projT2S v'))
          (Some (repBranch_nextPtr (_cont x0) i (firstPtr (_next x0))))
          (projT2S v')
        | None => [okv = None] * [length (_cont x0) <= i]
      end * P ==> Q.
    Proof. clear.
      intros. eapply himp_trans; [ | eassumption ].
      case_eq (nth_error (_cont x0) i).
        sep fail auto.
        intros; intro_pure; congruence.
    Qed.
    Ltac hyp_reducer :=
      repeat match goal with 
               | [ H : Some _ = Some _ |- _ ] => inversion H; clear H
               | [ H : (_,_) = (_,_) |- _ ] => inversion H; clear H
             end; 
      try red_prems;
        repeat match goal with 
                 | [ H : ?X = ?X |- _ ] => clear H
               end.

    Lemma lastKey_firstn_as_nth_error : forall h (l : list (BranchCell h)) x i x3,
      x = lastKey (firstn (S i) l) x3 ->
      S i <= length l ->
      exists z, nth_error l i = Some z /\ Val (projT1S z) = x.
    Proof. clear.
      induction l. simpl in *; think.
      destruct i. intros. norm list in H. simpl in H. subst. exists a. auto.
      intros. norm list in *. simpl in H0. eauto.
    Qed.

    Lemma inv_proof : forall h' x0 x3 x2 x i (v0 : BranchCell h') k' x6 p' okv,
         inv (S h') x0 x3 x2
      -> x = lastKey (firstn i (_cont x0)) x3
      -> i <= length (_cont x0)
      -> okv = Some (projT1S v0, ptrFor (projT2S v0))
      -> projT2S v0 = x6
      -> nth_error (_cont x0) i = Some v0
      -> okv = Some (k',p')
      -> inv h' x6 x (Val k').
    Proof. fold ptree in *. clear.
      intros. rewrite H5 in *; clear H5. 
      destruct x0 as [ ? [ ? ? ] ]. inversion H2. clear H2. destruct H. autorewrite with bpt_rw in *.
      fold ptree in *. clear H2.
      destruct i. norm list in H0. simpl lastKey in H0. subst.
      destruct l. norm list in H4. discriminate. norm list in H4. inversion H4. subst.
        destruct H. auto.
        destruct (lastKey_firstn_as_nth_error _ _ _ H0 H1).
        destruct H2. clear H0. subst.
        eapply contextual_denote_mid; eauto. 
    Qed.
    Lemma key_between_change_ub : forall k' k'' x x2,
      key_between x tK x2 -> tK <<= k'->
      k' = k'' ->
      key_between x tK (Val k'').
    Proof. clear.
      unfold BPlusTreeImplModel.key_between. intuition. rewrite <- H1. destruct H0.
      left; simpl; auto.
      right; simpl; auto.
    Qed.
    Lemma sle_from_eq : forall (a b : key),
      b == a -> a <<= b.
      intuition. right. symmetry; auto.
    Qed.
    Lemma sle_from_lt : forall (a b : key),
      a << b -> a <<= b.
      left; auto.
    Qed.

    Lemma himp_repBranch_19 : forall h ary st len x0 v0 x5,
      nth_error (_cont x0) len = Some v0 ->
      x5 = projT2S v0 ->
      repBranch h rep' ary st len (_cont x0) (firstPtr (_next x0)) ==>
      repBranch h rep' ary st len (firstn len (_cont x0)) (firstPtr x5).
    Proof. clear; fold ptree in *.
      intros; apply iter_imp; do 2 sep fail auto. norm list.
      case_eq (nth_error (_cont x0) i); fold ptree in *; intros.
        rewrite H3. sep fail auto. apply himp_rep'_eq; auto.
        f_equal. unfold BPlusTreeImplModel.repBranch_nextPtr.
        destruct (eq_nat_dec len (S i)).
        subst. rewrite H. cut (length (firstn (S i) (_cont x0)) <= S i); eauto with norm_list_length; intros.
        norm list. auto. norm list.
        case_eq (nth_error (_cont x0) (S i)); fold ptree in *; intros. rewrite H4. auto.
        elimtype False. cut (length (_cont x0) <= S i); eauto with norm_list_length. 
        cut (len < length (_cont x0)); eauto with norm_list_length.
        rewrite H3. auto.
    Qed.
    Lemma inv_contextual_firstn : forall h' i x0 x3 x2 x,
      inv (S h') x0 x3 x2
      -> x = lastKey (firstn i (_cont x0)) x3
      -> contextual h'
        (fun (mi : LiftOrder key) (c : sigTS (fun _ : key => ptree h')) =>
          inv h' (projT2S c) mi (Val (projT1S c)))
        x3 x (firstn i (_cont x0)).
    Proof. clear. Transparent firstn skipn nth_error BPlusTreeImplModel.contextual BPlusTreeImplModel.inv.
      destruct x0. destruct y. simpl. generalize dependent l. generalize dependent p0. 
      induction i; simpl.
        intros; subst; reflexivity.
        fold ptree in *.
        intros; subst. destruct l. simpl. reflexivity.
        simpl in *. intuition eauto. generalize (@IHi p0 l). eauto.
    Qed.
    Lemma inv_contextual_skipn : forall h' i x0 x3 x2 k' v0 irr,
      inv (S h') x0 x3 x2
      -> nth_error (_cont x0) i = Some v0
      -> k' = projT1S v0
      -> contextual h'
      (fun (mi : LiftOrder key) (c : sigTS (fun _ : key => ptree h')) =>
        inv h' (projT2S c) mi (Val (projT1S c))) (Val k')
      (lastKey (_cont x0) irr) (skipn (S i) (_cont x0)).
    Proof. clear.
      destruct x0. destruct y. simpl. generalize dependent l. generalize dependent p0. 
      induction i; simpl.
        destruct l; simpl; intros; try discriminate. inversion H0.
        destruct H. simpl in *. inversion H1. subst. simpl in *. tauto.
        destruct l. simpl. intros; discriminate.
        intros. simpl. fold ptree in *. simpl in *. generalize (@IHi p0 l). subst. 
        intros. eapply H1. intuition eauto; simpl in *; eauto. autorewrite with bpt_rw. eassumption.
      auto.
    Qed.
    Lemma inv_next : forall h' x0 x3 x2 v0 i,
         inv (S h') x0 x3 x2
      -> nth_error (_cont x0) i = Some v0 
      -> inv h' (_next x0) (lastKey (_cont x0) (Val (projT1S v0))) x2.
    Proof. clear; fold ptree in *.
      intros. destruct x0 as [ ? [ ? ? ] ]. destruct H.
      destruct v0. autorewrite with bpt_rw in *. fold ptree in *.
      erewrite lastKey_nth_error. Focus 2. simpl. eauto. Focus 2. eauto. eauto.
    Qed.

    Lemma pick_okv_None : forall h okv (m0 : ptree (S h)) i (P Q : hprop),
      okv = None ->
      ([nth_error (_cont m0) i = None] * [length (_cont m0) <= i] * P ==> Q) ->
      match nth_error (_cont m0) i with
        | Some v' =>
          [okv = Some (projT1S v', ptrFor (projT2S v'))] *
          [i < length (_cont m0)] *
          rep' (ptrFor (projT2S v'))
          (Some (repBranch_nextPtr (_cont m0) i (firstPtr (_next m0))))
          (projT2S v')
        | None => [okv = None] * [length (_cont m0) <= i]
      end * P ==> Q.
    Proof. clear.
      intros. eapply himp_trans; [ | eassumption ].
      case_eq (nth_error (_cont m0) i). intros; intro_pure; subst; congruence.
      sep fail auto.
    Qed.

    Lemma firstPtrOp_manual' : forall h' (v : RES (S h')) x5 (x0 : ptree (S h')) ignore i,
      i < length (_cont x0) ->
      firstPtrOp (S h') (projT1 (snd v)) x5 =
      match _cont x0 with
        | nil => ignore
        | n :: _ => firstPtr (projT2S n)
      end ->
      firstPtrOp (S h') (projT1 (snd v)) x5 = firstPtr x0.
    Proof.
      intros. destruct x0 as [ ? [ ? ? ] ]. destruct l; simpl in *; think.
    Qed.

    Lemma Q_imp1 : forall h' x x0 x3 x2 i k' p' v1 (rr:RES h') x4 (v:RES (S h')) okv x5,
      key_between x tK x2 ->
      inv (S h') x0 x3 x2 ->
      x = lastKey (firstn i (_cont x0)) x3 ->
      tK <<= k' ->
      nth_error (_cont x0) i = Some v1 ->
      okv = Some (projT1S v1, ptrFor (projT2S v1)) ->
      okv = Some (k', p') ->
      fst v = fst rr ->
      flat_map (fun x : BranchCell h' => as_map (projT2S x))
        (firstn i (_cont x0)) ++
        as_mapOp h' (projT1 (snd rr)) x4 ++
        flat_map (fun x : BranchCell h' => as_map (projT2S x))
          (skipn (S i) (_cont x0)) ++ as_map (_next x0) =
      as_mapOp (S h') (projT1 (snd v)) x5 ->
      repOp_facts (S h') (projT1 (snd v)) x5 x3 x2 ->
      repOp_facts h' (projT1 (snd rr)) x4 x (Val k') ->
      Q (as_map (projT2S v1)) (fst rr) (as_mapOp h' (projT1 (snd rr)) x4) ==>
      Q (as_map x0) (fst v) (as_mapOp (S h') (projT1 (snd v)) x5).
    Proof. generalize HimpLocal; clear.
      intros. destruct x0 as [ ? [ ? ? ] ]. simpl; fold ptree in *. autorewrite with bpt_rw in *.
      assert (key_between x tK (Val k')); [ destruct H; split; auto | clear H ].
      destruct rr. norm pair in *. destruct H0; fold ptree in *.
      rewrite (ls_expand i l H3) in H at 2. apply contextual_split in H. destruct H. 
      rewrite (ls_expand i l H3). rewrite <- H7. rewrite H6. norm list. 
      subst. inversion H5. subst.
      destruct H11.
      eapply HimpLocal; [ | | | | eassumption ].
        eapply inv_KLsorted_map; eauto. 
        destruct s; destruct x; simpl in *.
          eapply inv_KLsorted_map; eauto.
          destruct H9; destruct H9; eapply KLsorted_app_ex; eapply inv_KLsorted_map; eauto.
        eapply contextual_KLsorted; eauto.
        eapply KLsorted_app_ex. 
          eapply contextual_KLsorted; eauto. rewrite (ls_expand i l H3) at 1. rewrite lastKey_append. auto.
          eapply inv_KLsorted_map; eauto.

      clear; intros.
        assert (Val (projT1S c) <<= Val (projT1S c)); [ reflexivity | ].
        eapply (inv_subst _ _ _ H H1 H0).
    Qed.

    Definition ordLt_dec : forall (a b : key), {a << b} + {b <<= a}.
      intros; elim (ordCompare a b); intuition. right. rewrite e. reflexivity. right; left; auto.
    Qed.

    Notation "x << y" := (ordLt_dec x y) (at level 70, no associativity).


    Definition localCompute' : forall (h : nat) (min max : [LiftOrder key]) (optr : [option ptr])
      (p : ptr) (m : [ptree h]),
      STsep (min ~~ max ~~ m ~~ optr ~~
               rep' p optr m * [inv h m min max] * [key_between min tK max] * P)
            (fun res : RES h => m ~~ min ~~ max ~~ optr ~~ opm :~~ projT2 (snd res) in
               repOp h (projT1 (snd res)) opm min max optr * Q (as_map m) (fst res) (as_mapOp _ _ opm) *
               [firstPtrOp _ _ opm = firstPtr m]).
      refine (fix localCompute' h min max optr {struct h} : forall (p : ptr) (m : [ptree h]), _ :=
        match h as h return forall (p : ptr) (m : [ptree h]),
          STsep (min ~~ max ~~ m ~~ optr ~~
                   rep' p optr m * [inv h m min max] * [key_between min tK max] * P)
                (fun res : RES h => m ~~ min ~~ max ~~ optr ~~ opm :~~ projT2 (snd res) in
                   repOp h (projT1 (snd res)) opm min max optr * Q (as_map m) (fst res) (as_mapOp _ _ opm) *
                   [firstPtrOp _ _ opm = firstPtr m])
          with
          | 0    => fun p m =>
            nde <- p !! (fun v : nodeType => m ~~ optr ~~ 
              [height v = 0] * [next v = optr] * [array_length (content v) = SIZE] *
              repLeaf (content v) 0 SIZE (snd m) * P ) <@> _ ;
            {{ Fn p (content nde) (next nde) (m ~~~ snd m) min max <@> _ }}
          | S h' => fun p m => 
            nde' <- readBranch pfMin p optr m <@> _ ;
            let ary := fst nde' in
            let nxt := snd nde' in
            pfArySize <- shift (array_length ary = SIZE) <@> _ ;
            {{ Fix3 (fun (i : nat) (min' : [LiftOrder key]) (pfRange : i <= SIZE) =>
                      min ~~ max ~~ min' ~~ optr ~~ m ~~ 
                      let lsM  := _cont m in 
                      let nxtM := _next m in
                      let nxtP := nxt in
                      p ~~> mkNode (S h') ary (Some nxt) *
                      [length lsM <= SIZE] * [inv (S h') m min max] * [i <= length lsM] *
                      [key_between min' tK max] *
                      [min' = lastKey (firstn i lsM) min] * 
                      repBranch h' (rep') ary 0 SIZE lsM (firstPtr nxtM) *
                      rep' nxtP optr nxtM * P)
                    (fun _ _ _ (res : RES (S h')) => m ~~ min ~~ max ~~ optr ~~ opm :~~ projT2 (snd res) in
                      repOp (S h') (projT1 (snd res)) opm min max optr * Q (as_map m) (fst res) (as_mapOp _ _ opm) *
                      [firstPtrOp _ _ opm = firstPtr m])
                    (fun self i min' pfRange =>
                     match le_lt_dec SIZE i with
                       | left pfLe => _
                       | right pfLt =>
                         okv <- sub_array ary i (fun v:option (key * ptr) => m ~~ match nth_error (_cont m) i with
                                                                                    | None => [v = @None (key * ptr)] * [length (_cont m) <= i]
                                                                                    | Some v' => [v = Some (projT1S v', ptrFor (projT2S v'))] * [i < length (_cont m)] * 
                                                                                      rep' (ptrFor (projT2S v')) (Some (repBranch_nextPtr (_cont m) i (firstPtr (_next m)))) (projT2S v')
                                                                                  end) <@> _ ;
                         let _:option (key * ptr) := okv in
                         match okv as okv' return okv = okv' -> _ with
                           | None => fun pfOkv => _
                           | Some (k', p') => fun pfOkv =>
                             match k' << tK with
                               | left _ => {{ self (S i) [Val k']%inhabited (lt_S_le pfLt) }}
                               | right  _ => _
                             end
                         end (refl_equal _)
                     end) 0 min (O_le SIZE) }}
        end); try clear self; try clear Fn.
    Proof. idtac "Starting localCompute'".
      (** Leaf Case **)
      Transparent BPlusTreeImplModel.rep'.
      solve [ sep2 fail bpt_elim; sep_unify ].
      solve [ sep_unify ].
      solve [ sep2 bpt_elab bpt_elim; rewrite <- H3; sep2 fail bpt_elim; sep_unify ].
      solve [ sep2 bpt_elab bpt_elim; rewrite <- H3; rewrite <- H8; rewrite H12; sep2 fail bpt_elim; sep_unify ].
      
      (** Branch Case **)
      solve [ sep2 bpt_elab bpt_elim; sep_unify ].
      solve [ sep_unify ].
      solve [ sep2 bpt_elab bpt_elim; sep_unify ].
      solve [ sep_unify ].

      (** Less-equal **)
      refine (
        rr <- localCompute' h' min' max optr nxt (m ~~~ _next m) <@> _ ;
        {{ @mergeOpNext min min' max h' p ary optr SIZE rr m (eq_le SIZE) <@> _ }}); try clear localCompute'.
      Hint Resolve next_inv'.
      solve [ sep2 ltac:(combine_le_le || bpt_elab) bpt_elim; sep_unify ].
      solve [ sep_unify ].
      sep2 ltac:(combine_le_le || bpt_elab) bpt_elim. instantiate_conc nxt; fold ptree in *.
        rewrite <- H4 in *; clear H4. rewrite firstn_len_le_rw; try omega. solve [ sep2 fail bpt_elim; sep_unify ].
      Hint Resolve firstPtrOp_manual.
      solve [ sep2 ltac:(combine_le_le || bpt_elab) bpt_elim; sep_unify ].

      (** Less-than **)
      Hint Resolve prove_neighborhood.
      solve [ clear localCompute'; sep2 bpt_elab bpt_elim; norm arith; sep2 fail bpt_elim; sep_unify ].
      solve [ clear localCompute'; sep_unify ].
      clear localCompute'; sep2 bpt_elab bpt_elim. fold ptree in *. norm arith. sep2 fail bpt_elim.
      search_prem ltac:(simple eapply pick_okv_Some; eauto).
        sep2 bpt_elab bpt_elim. fold ptree in *. rewrite H15 in *. rewrite pfOkv in *; inversion H17.
      Hint Immediate key_between_change_lb lastKey_nth_error_eq.
        solve [ sep2 fail bpt_elim; sep_unify ].
      solve [ clear localCompute'; sep2 fail bpt_elim; sep_unify ].
      
      (** Branch -- Greater or Equal **)
      refine (
          rr <- localCompute' h' min' [Val k']%inhabited
                    (m ~~~ Some (repBranch_nextPtr (_cont m) i (firstPtr (_next m))))
                    p' 
                    (m ~~~ match nth_error (_cont m) i with
                             | None => _next m (** junk **)
                             | Some m' => projT2S m'
                           end) <@> _ ;
          {{ @mergeOpInternal min min' max h' p ary nxt optr i k' rr m <@> _ <@> 
                (min' ~~ (opm :~~ projT2 (snd rr) in [repOp_facts h' (projT1 (snd rr)) opm min' (Val k')])) }}); clear localCompute'.
      sep2 bpt_elab bpt_elim.
      search_prem ltac:(eapply simplify_len; eauto). sep2 hyp_reducer bpt_elim.
      Hint Resolve sle_from_eq sle_from_lt.
      Hint Resolve key_between_change_ub inv_proof.
        subst. inversion H18; auto.
        solve [ sep2 fail bpt_elim; sep_unify ].
      solve [ sep_unify ].
      fold ptree in *.
      sep2 ltac:(add_opFacts || bpt_elab) bpt_elim. instantiate_conc p'.
      Hint Resolve himp_repBranch_19 : bpt_sep.
        sep2 fail bpt_elim.
        rewrite H11; eauto with bpt_sep. instantiate_conc v0. sep2 fail bpt_elim.
        rewrite <- H7. rewrite <- H6. rewrite <- H5.
      Hint Resolve inv_contextual_firstn inv_contextual_skipn inv_next.
        rewrite pfOkv in H13. inversion H13. rewrite <- H6 in H21. rewrite H26 in H21.
        solve [ sep2 fail bpt_elim; sep_unify ].

      Hint Resolve firstPtrOp_manual' Q_imp1.
      solve [ sep2 add_opFacts bpt_elim; sep_unify ].

      (** okv = None **)
      refine (
        rr <- localCompute' h' min' max optr nxt (m ~~~ _next m) <@> _ ;
        {{ @mergeOpNext min min' max h' p ary optr i rr m _ <@> _ }}); try clear localCompute'; auto.
      sep2 ltac:(combine_le_le || bpt_elab) bpt_elim. 
        fold ptree in *.
        search_prem ltac:(simple eapply pick_okv_None; [ eassumption | ]).
        solve [ sep2 combine_le_le bpt_elim; sep_unify ].
      solve [ try clear localCompute'; sep_unify ].
      sep2 ltac:(combine_le_le || bpt_elab) bpt_elim. search_conc ltac:(simple apply himp_ex_conc; exists nxt).
        rewrite H16. fold ptree in *. rewrite <- H5 in *.
        sep2 ltac:(combine_le_le || bpt_elab) bpt_elim. norm arith. rewrite H16.
        norm list in H15. sep2 fail bpt_elim. sep_unify.
        solve [ sep2 fail bpt_elim; sep_unify ].
      
      solve [ clear localCompute'; sep2 bpt_elab bpt_elim; sep_unify ].
idtac "Ending localCompute'".
      solve [ clear localCompute'; sep2 bpt_elab bpt_elim; sep_unify ].
    Qed.

(*  End localCompute'. *)

(*  Section toplevel. *)

    Definition localCompute : forall (h : nat) (p : ptr) (m : [ptree h]),
      STsep (m ~~
              rep' p None m * [inv h m MinK MaxK] * [key_between MinK tK MaxK] * P)
            (fun res : (RT * ptr * sigTS (fun h:nat => [ptree h]%type)) => m ~~ opm :~~ projT2S (snd res) in
              rep' (snd (fst res)) None opm * Q (as_map m) (fst (fst res)) (as_map opm) *
              [inv _ opm MinK MaxK] * [firstPtr opm = firstPtr m]).
    refine (fun h p m =>
      res <- @localCompute' h [MinK]%inhabited [MaxK]%inhabited [None]%inhabited p m <@> _ ;
      let oper := projT1 (snd res) in
      let operM := projT2 (snd res) in
      {{ match oper as oper return forall (m' : [opModel h oper]%type),
        STsep (m ~~ m' ~~ 
                repOp h oper m' MinK MaxK None * Q (as_map m) (fst res) (as_mapOp _ _ m') *
                [firstPtrOp _ _  m' = firstPtr m])
              (fun res : (RT * ptr * sigTS (fun h:nat => [ptree h]%type)) => m ~~ opm :~~ projT2S (snd res) in
                rep' (snd (fst res)) None opm * Q (as_map m) (fst (fst res)) (as_map opm) *
                [inv _ opm MinK MaxK] * [firstPtr opm = firstPtr m]) with
        | Merge p     => fun m => {{ Return (fst res, p, existTS _ h m) <@> _ }}
        | Split l k r => fun m =>
          ary <- new_constant_array SIZE (@None (key * ptr)) <@> _ ;
          upd_array ary 0 (Some (k, l)) <@> _ ;;
          p' <- New (mkNode (S h) ary (Some r)) <@> _ ;
          {{ Return (fst res, p', existTS (fun h:nat => [ptree h]%type) (S h) (m ~~~ (p', (existTS (fun _:key => ptree h) k (fst m) :: nil, snd m)))) <@> _ }}
      end operM }}); clear Fn HimpLocal.
    Proof.
      solve [ sep2 fail bpt_elim; sep_unify ].
      solve [ sep_unify ].

      solve [ sep_unify ].
      intros; inhabiter. add_opFacts. simpl in H1. sep2 fail bpt_elim.
        generalize dependent x1. rewrite H4. simpl. sep2 fail bpt_elim; sep_unify.

      solve [ sep_unify ].
      solve [ sep_unify ].
      solve [ sep2 fail bpt_elim; norm arith; sep_unify ].
      solve [ sep_unify ].
      solve [ sep_unify ].
      solve [ sep_unify ].
      solve [ sep_unify ].
      sep2 fail bpt_elim.
        generalize dependent x2; rewrite H3 in *; clear H3; simpl in *; fold ptree in *.
        sep2 fail bpt_elim; rewrite <- H2 in *; autorewrite with bpt_rw in *; auto.
        norm arith; norm list. simpl projT2S; simpl projT1S. norm pair. sep2 fail bpt_elim.
        Transparent BPlusTreeImplModel.contextual. simpl. cut_pure; try sep_unify. intuition.

      solve [ sep2 add_opFacts bpt_elim; sep fail auto ].
      solve [ sep2 fail bpt_elim; sep_unify ].
    Qed.
(*  End toplevel. *)

End Compute.

End BPlusTreeImpl.
  
