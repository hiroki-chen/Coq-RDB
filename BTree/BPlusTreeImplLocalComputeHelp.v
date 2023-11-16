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

Require Import OrderedTypeNM LiftOrder.

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
  Notation "'tH'" := (tH value).

  Notation repBranchExcept h ary st i len ls optr := 
    (@BPlusTreeImplModel.repBranch key value h (rep') ary st i ls optr *
     @BPlusTreeImplModel.repBranch key value h (rep') ary (S i + st) (len - S i) (skipn (S i) ls) optr)%hprop.

  Opaque BPlusTreeImplModel.inv.
  Opaque BPlusTreeImplModel.MinK.
  Opaque BPlusTreeImplModel.MaxK.

  Open Local Scope hprop_scope.
  Open Local Scope stsepi_scope.

  Inductive op : Set :=
  | Merge   : ptr -> op
  | Split   : ptr -> key -> ptr -> op.
(*  | Splice  : ptr -> op. *)

  Definition opModel (h : nat) (m : op) : Set :=
    match m with
      | Merge _ => ptree h
      | Split _ _ _ => ptree h * ptree h
(*      | Splice _ => ptree h *)
    end%type.

  Definition as_mapOp (h : nat) (m : op) : opModel h m -> Model :=
    match m as m return opModel h m -> Model with
      | Merge _     => fun opm => as_map opm
      | Split _ _ _ => fun opm => (as_map (fst opm)) ++ (as_map (snd opm))
(*      | Splice _    => fun opm => as_map h opm *)
    end.

  Definition firstPtrOp (h : nat) (m : op) : opModel h m -> ptr :=
    match m as m return opModel h m -> ptr with
      | Merge _ => fun m => firstPtr m
      | Split _ _ _ => fun m => firstPtr (fst m)
(*      | Splice _ => fun m => firstPtr _ m *)
    end.

  Definition repOp (h : nat) (o : op) (m : opModel h o) (min max : LiftOrder key) 
    (optr : option ptr) : hprop :=
    match o as o return opModel h o -> hprop with
      | Merge p        => fun m => [inv h m min max] * rep' p optr m
      | Split lp kp rp => fun lkr => 
        let l := fst lkr in
        let r := snd lkr in
        [inv h l min (Val kp)] * [inv h r (Val kp) max] * 
        [lp = ptrFor l] * [rp = ptrFor r] *
        rep' lp (Some (firstPtr r)) l * rep' rp optr r
(**   | Splice p       => 
        [p = ptrForm m] *
        Exists ary :@ array, 
        match h as h return opModel h (Splice p) -> hprop with
          | 0   => fun m => p ~~> mkNode 0 ary optr *
            repLeaf ary 0 SIZE (snd m) * [length (snd m) < div2 SIZE]
          | S h => fun m => p ~~> mkNode (S h) ary None *
            repBranch ary 
[inv h m min max] * rep' h p optr m
        end
*)
    end m.

  Lemma div2_mag : forall x,
    1 < x -> x - div2 x >= 1.
  Proof.
    clear. intros.
    assert (0 < x); think. generalize (lt_div2 _ H0). omega.
  Qed.
  Lemma half_list_not_nil : forall T (l:list T),
    1 < length l -> skipn (div2 (length l)) l = nil -> False.
  Proof.
    clear. intros. generalize (firstn_skipn (div2 (length l)) l). intros.
    generalize (div2_mag H). assert (length l = length l); think. rewrite <- H1 in H2 at 2. rewrite H2 in H3.
    assert (length (firstn (div2 (length l)) l) = div2 (length l)).
      generalize (Min.min_dec (div2 (length l)) (length l)). intros. destruct H4. 
      Focus 2. generalize (Min.le_min_l (div2  (length l)) (length l)). rewrite e.
      intros. elimtype False.         
      generalize (lt_div2 (length l)). cut (0 < length l); think.
          
      rewrite <- e. rewrite List.firstn_length. rewrite <- Min.min_assoc.
      cut (Min.min (length l) (length l) = length l). intros. rewrite H4. auto.
      clear. induction (length l); think.
      rewrite app_length in *. rewrite H4 in *. rewrite H0 in *. simpl in *. norm arith in *. norm list in *.
      generalize H2. generalize H. clear. generalize (length l). clear.
      intros. assert (0 < n); think. generalize (lt_div2 _ H0). think.
  Qed.

  Definition splitContent : forall (h : nat) (lsM : list (BranchCell h))
    (pf : length lsM = SIZE),
    (list (BranchCell h) * ptree h * key * list (BranchCell h)).
    refine (fun h lsM pf =>
      match skipn (div2 SIZE) lsM as LL return skipn (div2 SIZE) lsM = LL -> _ with
        | nil => fun _ => False_rec _ _
        | (existTS k v) :: rr => fun _ => 
          (firstn (div2 SIZE) lsM, v, k, rr)
      end (refl_equal _)).
  Proof.
    Hint Resolve half_list_not_nil.
    subst. eauto.
  Defined.

  Lemma div2_SIZE_lt_SIZE : div2 SIZE < SIZE.
  Proof.
    destruct SIZE. think. destruct n; think.
  Qed.

  Lemma div2_gt_0 : div2 SIZE > 0.
    destruct SIZE using ind_0_1_SS; simpl; think.
  Qed.
  Hint Immediate div2_gt_0.

  Lemma pred_div2_SIZE_lt_div2_SIZE : pred (div2 SIZE) < div2 SIZE.
  Proof.
    destruct SIZE; think. destruct n; think.
  Qed.
  
  (** Compute **)
    Lemma div2_pred : forall i, i < div2 SIZE -> div2 SIZE + i < SIZE.
    Proof.
      intros. rewrite <- (twice_half SIZE) at 2; auto. 
    Qed.      
    Hint Resolve div2_pred.
    Lemma pred_div2_SIZE_lt_SIZE : pred (div2 SIZE) < SIZE.
    Proof.
      generalize div2_SIZE_lt_SIZE; think.
    Qed.
    Hint Immediate pred_div2_SIZE_lt_SIZE.

    Lemma half_plus_less_lt : forall L i,
      L = SIZE ->
      i < div2 SIZE ->
      div2 SIZE + i < L. intros.
      rewrite <- (twice_half SIZE) in H; auto.
    Qed.
    Hint Resolve half_plus_less_lt.

    Lemma minus_gt_0 : forall b, 
      b < div2 SIZE -> SIZE - pred b > 0.
    Proof.
      intros. rewrite <- (twice_half SIZE); eauto. omega.
    Qed.
    Lemma plus_lt : forall a b,
      b > 0 -> a < a + b.
    Proof.
      intros; omega.
    Qed.
    Hint Resolve minus_gt_0 plus_lt.

    Lemma match_skipns : forall T (LS : list T) N LS',
      N < length LS ->
      match LS with
        | nil => nil
        | _ :: l0 => skipn N l0
      end ++ LS' = skipn 1 (skipn N LS ++ LS').
    Proof.
      induction LS.
      simpl; think.
      simpl; intros. destruct N. think. simpl. rewrite IHLS. simpl. auto. auto.
    Qed.

    Lemma size_half_plus_minus : SIZE - pred (div2 SIZE) = div2 SIZE + 1.
      rewrite <- (twice_half SIZE) at 1; eauto. 
      cut (div2 SIZE > 0); eauto. omega.
    Qed.
    Hint Immediate size_half_plus_minus.

    Lemma zzz_rw : SIZE - pred (div2 SIZE) = S (div2 SIZE).
      rewrite <- (twice_half SIZE) at 1; auto.
      cut (0 < div2 SIZE); intros; auto. omega.
    Qed.
    Hint Resolve zzz_rw.


    Lemma yyy : forall h (x1 : ptree (S h)) i P Q x0 k x2 (x : ptree h),
      (P ==> x2 ~~> match nth_error (_cont x1) (i + div2 SIZE) with
                      | Some v0 => Some (projT1S v0, ptrFor (projT2S v0))
                      | None => None
                    end * Q) ->
      
      match nth_error (_cont x1) (i + div2 SIZE) with
        | Some v0 =>
          [i + div2 SIZE < length (firstn (S i + div2 SIZE) (_cont x1))] *
          rep' (ptrFor (projT2S v0))
          (Some
            (repBranch_nextPtr (firstn (S i + div2 SIZE) (_cont x1))
              (i + div2 SIZE)
              (repBranch_nextPtr (_cont x1) (i + div2 SIZE) (firstPtr x0))))
          (projT2S v0)
        | None =>
          [length (firstn (S i + div2 SIZE) (_cont x1)) <= i + div2 SIZE]
      end * P
      ==>
      match nth_error (_cont x1) (i + div2 SIZE) with
        | Some v' =>
          x2 ~~> Some (projT1S v', ptrFor (projT2S v')) *
          rep' (ptrFor (projT2S v'))
          (Some
            (repBranch_nextPtr
              (skipn (i + div2 SIZE) (_cont x1) ++ existTS (fun _ : key => ptree h) k x0 :: nil) 0 
              (firstPtr x))) (projT2S v')
        | None => x2 ~~> @None (key * ptr)
      end * Q.
    Proof. clear. intros. 
      search_prem ltac:(apply (himp_subst H); clear H).
      Opaque skipn firstn nth_error.
      case_eq (nth_error (_cont x1) (i + div2 SIZE)); sep fail auto.
      apply himp_rep'_eq; auto. f_equal. 
      rewrite repBranch_nextPtr_choose_default; eauto with norm_list_length.
      rewrite <- repBranch_nextPtr_eq2; eauto with norm_list_length.
      simpl. erewrite repBranch_nextPtr_eq3_l; [ | trivial ]. auto.
      cut (i + div2 SIZE < length (_cont x1)); eauto with norm_list_length; intros.
      rewrite length_skipn. omega.
    Qed.

    Lemma repBranch_hint : forall h (ls : list (BranchCell h)) len slen plen ary st x0,
      len < slen ->
      plen = pred len ->
      repBranch h rep' ary st len (firstn slen ls) (repBranch_nextPtr ls len x0) ==>
      repBranch h rep' ary st len (firstn len ls) (repBranch_nextPtr ls plen x0).
    Proof. clear.
      intros; apply iter_imp; do 2 sep fail auto.
      norm list.
      destruct (nth_error ls i); sep fail auto.
      apply himp_rep'_eq; auto; f_equal.
      unfold BPlusTreeImplModel.repBranch_nextPtr.
      case_eq (nth_error ls (S i)); intros; norm list.
        rewrite H3. norm arith.
        destruct (eq_nat_dec len (S i)); subst; norm list; rewrite H3; auto.
        cut (length ls <= len); try omega; intros.
        norm list; auto.
        cut (length ls <= S i); eauto with norm_list_length.
    Qed.
    Hint Resolve repBranch_hint.

    Definition moveBranch_nextOp : forall {h} ary aryR (m : [ptree (S h)]) k (lM rM : [ptree h]),
      STsep (lM ~~ rM ~~ m ~~
               [length (_cont m) = SIZE] *
               repBranch h (rep') ary 0 SIZE (_cont m) (firstPtr lM) *
               {@ p :~~ array_plus aryR j in p ~~> @None (key * ptr) | j <- 0 + (div2 SIZE - 1)} *
               repBranch h (rep') aryR (div2 SIZE - 1) (div2 SIZE + 1) 
                 (existTS (fun _:key => ptree h) k lM :: nil) (firstPtr rM))
            (fun _:unit => lM ~~ rM ~~ m ~~
               repBranch h (rep') ary 0 SIZE (firstn (div2 SIZE + 1) (_cont m))
                 (repBranch_nextPtr (_cont m) (div2 SIZE)
                   (firstPtr lM)) *
               repBranch h (rep') aryR 0 SIZE 
                 (skipn (div2 SIZE + 1) (_cont m) ++ (existTS (fun _:key => ptree h)) k lM :: nil)
                 (firstPtr rM)).
      refine (fun h ary aryR m k lM rM =>
        {{ Fix2 (fun (i : nat) (_ : i < div2 SIZE) => lM ~~ rM ~~ m ~~
                  [length (_cont m) = SIZE] *
                  repBranch h (rep') ary 0 SIZE (firstn (i + 1 + div2 SIZE) (_cont m))
                  (repBranch_nextPtr (_cont m) (i + div2 SIZE)
                    (firstPtr lM)) *
                  {@ p :~~ array_plus aryR j in p ~~> @None (key * ptr) | j <- 0 + i} *
                  repBranch h (rep') aryR i (SIZE - i)
                    (skipn (i + 1 + div2 SIZE) (_cont m) ++ (existTS (fun _:key => ptree h)) k lM :: nil)
                    (firstPtr rM))
                (fun _ _ (_:unit) => lM ~~ rM ~~ m ~~
                  repBranch h (rep') ary 0 SIZE (firstn (div2 SIZE + 1) (_cont m))
                    (repBranch_nextPtr (_cont m) (div2 SIZE)
                      (firstPtr lM)) *
                  repBranch h (rep') aryR 0 SIZE 
                    (skipn (div2 SIZE + 1) (_cont m) ++ (existTS (fun _:key => ptree h)) k lM :: nil)
                    (firstPtr rM))
                (fun self i pfI =>
                  match eq_nat_dec i 0 with
                    | left pfEq => {{ Return tt }}
                    | right pfNeq => 
                      v <- sub_array ary (div2 SIZE + i) (fun v' : option (key * ptr) => _) ;
                      upd_array aryR (pred i) v <@> _ ;;
                      upd_array ary (div2 SIZE + i) (@None (key * ptr)) <@> _ ;;
                      {{ self (pred i) (pred_le _ _ pfI) }}
                  end)
                (pred (div2 SIZE)) pred_div2_SIZE_lt_div2_SIZE }}); 
        try clear self; 
        (try (rewrite pfEq; clear pfEq)).
      Proof.
        solve [ sep_unify ].
        solve [ sep2 ltac:(norm arith; norm list) bpt_elim; sep_unify ].

        solve [ sep2 fail bpt_elim; clear H4; sep fail idtac ].
        solve [ sep_unify ].

        solve [ sep2 fail bpt_elim; sep_unify ].
        solve [ sep_unify ].

        solve [ sep2 fail bpt_elim; sep_unify ].
        solve [ sep_unify ].

        Lemma repBranch_hint_1 : forall h aryR i x1 k x0 x,
          i < div2 SIZE ->
          i <> 0 ->
          length (_cont x1) = SIZE ->
          repBranch h rep' aryR i (SIZE - i)
            (skipn (S i + div2 SIZE) (_cont x1) ++ existTS (fun _ : key => ptree h) k x0 :: nil) x ==>
          repBranch h rep' aryR i (SIZE - i)
            (skipn 1 (skipn (i + div2 SIZE) (_cont x1) ++ existTS (fun _ : key => ptree h) k x0 :: nil)) x.
        Proof.
          intros. cut (i + div2 SIZE < length (_cont x1)); [ | rewrite comm_plus; auto ]; intros.
          cut (1 <= length (skipn (i + div2 SIZE) (_cont x1))); intros.
          rewrite skipn_combine_app. simpl. eauto with bpt_sep. omega. rewrite length_skipn. auto.
        Qed.
        Hint Resolve repBranch_hint_1.
        sep2 fail bpt_elim.
          norm list in *. norm arith in *. fold ptree in *.
          generalize (@nth_error_len_rw (i + div2 SIZE) _ (firstn (i + div2 SIZE) (_cont x1))); intro.
          fold ptree in *. rewrite H6.

          norm list. rewrite nth_error_skipn_app; [ | subst; apply div2_plus_lt_div2'; eauto ].

          search_prem ltac:(search_conc ltac:(simple eapply yyy; auto with norm_list_length)).
          sep2 fail bpt_elim. sep fail idtac.
          auto with norm_list_length.

        solve [ intros; auto ].
        sep2 fail bpt_elim.
          intros. rewrite repBranch_nextPtr_choose_default; eauto with norm_list_length.
          Lemma S_pred_div2 : forall X, X = SIZE -> X <= S (pred (div2 SIZE) + div2 SIZE).
            intros; subst. cut (S (pred (div2 SIZE) + div2 SIZE) = SIZE); try omega.
            rewrite <- (twice_half SIZE) at 3; eauto. cut (div2 SIZE > 0); eauto; omega.
          Qed.
          Hint Resolve S_pred_div2. eauto.
          norm arith.
          sep2 fail bpt_elim. sep fail auto.
        solve [ intros; auto ].
    Qed.

    Opaque BPlusTreeImplModel.inv.

    Lemma lastKey_nth_error : forall h i v' k' LS x6 x3,
      Val k' = x6
      -> nth_error LS i = Some (existTS (fun _:key => ptree h) k' v')
      -> lastKey LS x6 = lastKey LS x3.
    Proof. clear.
      induction LS.
        intros. norm list in *. discriminate.
        intros. simpl. auto.
    Qed.

    Lemma lastKey_firstn_nth_error : forall h i LS k' x9 x3,
      nth_error LS i = Some (existTS (fun _ : key => ptree h) k' x9)
      -> Val k' = lastKey (firstn (S i) LS) x3.
    Proof. clear.
      induction i; destruct LS; intros; norm list in *.
        discriminate.
        simpl; inversion H; auto.
        discriminate.
        simpl; eauto.
    Qed.

    Lemma inv_contextual_firstn : forall h' i x0 x3 x2 x,
      inv (S h') x0 x3 x2
      -> x = lastKey (firstn i (fst (snd x0))) x3
      -> contextual h'
      (fun (mi : LiftOrder key) (c : sigTS (fun _ : key => ptree h')) =>
        inv h' (projT2S c) mi (Val (projT1S c)))
      x3 x (firstn i (fst (snd x0))).
    Proof. clear; fold ptree in *.
      destruct x0. destruct y. simpl. generalize dependent l. generalize dependent p0. 
      induction i; simpl.
        intros; subst. norm list. simpl. reflexivity. 
        fold ptree in *.
        intros; subst. destruct l. simpl in *. norm list. simpl. reflexivity.
          Transparent BPlusTreeImplModel.inv. simpl BPlusTreeImplModel.inv in *. Opaque BPlusTreeImplModel.inv. destruct H. destruct H.
          split; try tauto. eapply IHi. split. auto. eauto. eauto.
    Qed.

    Lemma inv_contextual_skipn : forall h' i x0 x3 x2 k' x6 x9,
      inv (S h') x0 x3 x2
      -> Val k' = x6
      -> nth_error (fst (snd x0)) i = Some (existTS (fun _ : key => ptree h') k' x9)
      -> contextual h'
      (fun (mi : LiftOrder key) (c : sigTS (fun _ : key => ptree h')) =>
        inv h' (projT2S c) mi (Val (projT1S c))) x6
      (lastKey (fst (snd x0)) x3) (skipn (S i) (fst (snd x0))).
    Proof. clear.
      destruct x0. destruct y. simpl. generalize dependent l. generalize dependent p0.
      fold ptree in *.
      induction i; simpl.
        destruct l; simpl; intros; try discriminate. Transparent skipn nth_error. simpl in *.
        inversion H1. simpl.
        destruct H. fold ptree in *. simpl in *.
        inversion H1. subst. simpl in *. tauto.

        destruct l. simpl. intros; discriminate.
        intros. simpl. eapply IHi. Focus 2. eauto. Focus 2. eauto. 
        Transparent BPlusTreeImplModel.inv. simpl in *. think. Opaque BPlusTreeImplModel.inv. eapply H2.
    Qed.

    Lemma destruct_head : forall h (LS : list (sigTS (fun _:key => ptree h ))) Z X Y,
      length LS >= 1->
      Z >= 1 ->
      match firstn Z LS with
        | nil => X
        | a :: _ => firstPtr (projT2S a)
      end =
      match head LS with
        | Some n => firstPtr (projT2S n)
        | None => Y
      end.
    Proof.
      destruct LS; intros; simpl in *; firstorder. elimtype False; omega.
      destruct Z. elimtype False; omega. simpl. auto.
    Qed.
    Hint Resolve destruct_head.

    Lemma x_minus_div2_x : forall x, even x -> x - div2 x = div2 x.
      intros. rewrite <- (twice_half x) at 1; auto.
    Qed.

    Definition splitContent' {h} k (lptr rptr: ptr)
      (lsM : list (BranchCell h)) (lM rM : ptree h) :
      (ptree (S h) * ptree (S h)) :=
      match skipn (div2 SIZE) lsM with
        | nil => ((lptr, (nil, lM)), (rptr, (nil, rM)))
        | (existTS _ v) :: rr => 
          ((lptr, (firstn (div2 SIZE) lsM, v)),
           (rptr, (rr ++ existTS (fun _:key => ptree h) k lM :: nil, rM)))
      end.

    Lemma inv_contextual_firstn' : forall h' i ls x3 x,
      contextual h'
        (fun (mi : LiftOrder key) (c : BranchCell h') =>
          inv h' (projT2S c) mi (Val (projT1S c))) x3 
        (lastKey ls x3) ls
      -> x = lastKey (firstn i ls) x3
      -> contextual h'
      (fun (mi : LiftOrder key) (c : sigTS (fun _ : key => ptree h')) =>
        inv h' (projT2S c) mi (Val (projT1S c)))
      x3 x (firstn i ls).
    Proof. clear.
      induction i; simpl.
        intros; subst. norm list. simpl. reflexivity.
        intros; subst. destruct ls. simpl in *. norm list. simpl. reflexivity.
          simpl  in H.
          split; try tauto. eapply IHi. auto. tauto. simpl. auto.
    Qed.

    Lemma inv_contextual_skipn' : forall h' i ls x3 k' x6 x9,
      contextual h'
      (fun (mi : LiftOrder key) (c : BranchCell h') =>
          inv h' (projT2S c) mi (Val (projT1S c))) x3 
        (lastKey ls x3) ls
      -> Val k' = x6
      -> nth_error ls i = Some (existTS (fun _ : key => ptree h') k' x9)
      -> contextual h'
      (fun (mi : LiftOrder key) (c : sigTS (fun _ : key => ptree h')) =>
        inv h' (projT2S c) mi (Val (projT1S c))) x6
      (lastKey ls x3) (skipn (S i) ls).
    Proof. clear.
      fold ptree in *.
      induction i; simpl.
        destruct ls; simpl; intros; try discriminate. inversion H0.
        destruct H. Transparent skipn. Transparent nth_error. simpl in *.
        inversion H1. subst. simpl in *. tauto.

        destruct ls. simpl. intros; discriminate.
        intros. simpl. eapply IHi. Focus 2. eauto. Focus 2. eauto. 
        Transparent BPlusTreeImplModel.inv. simpl in *. think. Opaque BPlusTreeImplModel.inv.
    Qed.

    Lemma contextual_nth_inv : forall h x2 x0 N x5 p4 x6,
      contextual h
        (fun (mi : LiftOrder key) (c : BranchCell h) =>
         inv h (projT2S c) mi (Val (projT1S c))) x6 
        (lastKey x0 x6) x0
      -> nth_error x0 N = Some (existTS (fun _ : key => ptree h) x5 p4)
      -> x2 = lastKey (firstn N x0) x6
      -> inv h p4 x2 (Val x5).
    Proof. clear.
      intros. subst. generalize dependent x6. generalize dependent N. generalize dependent x0. 
      induction x0; simpl; intros.
        norm list in *. discriminate.
        destruct N. simpl in *. inversion H0. subst. simpl in *. tauto.
        simpl. norm list. apply IHx0. tauto. simpl in H0. tauto.
    Qed.

    Lemma split_inv_firstn : forall h x0 x5 p4 p2 x6,
      contextual h
        (fun (mi : LiftOrder key) (c : BranchCell h) =>
          inv h (projT2S c) mi (Val (projT1S c))) x6
        (lastKey x0 x6) x0
      -> nth_error x0 (div2 SIZE) =
         Some (existTS (fun _ : key => ptree h) x5 p4)
      -> inv (S h) (p2, (firstn (div2 SIZE) x0, p4)) x6 (Val x5).
    Proof. clear.
      Hint Resolve inv_contextual_firstn.
      Transparent BPlusTreeImplModel.inv. simpl BPlusTreeImplModel.inv. firstorder.
      generalize inv_contextual_firstn'. firstorder.
      Hint Resolve contextual_nth_inv.
      eauto.
    Qed.

    Lemma nth_error_lastKey : forall h LS N p4 x5 x6,
      nth_error LS N = Some (existTS (fun _ : key => ptree h) x5 p4)
      -> Val x5 = lastKey (firstn (S N) LS) x6.
    Proof. clear.
      induction LS.
        intros. norm list in H. discriminate.
        destruct N. intros; simpl. norm list in *.  inversion H. auto.
        intros; simpl. norm list in *. simpl. eauto.
    Qed.
    Hint Resolve nth_error_lastKey.

    Lemma split_inv_skipn : forall h (x0:ptree (S h)) x5 p4 x4 p3 p x1 x9 k x6,
      contextual h
        (fun (mi : LiftOrder key) (c : BranchCell h) =>
          inv h (projT2S c) mi (Val (projT1S c))) x6
        (lastKey (fst (snd x0)) x6) (fst (snd x0))
      -> inv h (fst x9) (lastKey (fst (snd x0)) x6) (Val k)
      -> inv h (snd x9) (Val k) x4
      -> nth_error (fst (snd x0)) (div2 SIZE) =
         Some (existTS (fun _ : key => ptree h) x5 p4)
      -> nth_error (fst (snd x0)) (S (div2 SIZE)) =
         Some (existTS (fun _ : key => ptree h) x1 p)
      -> inv (S h)
         (p3,
           (existTS (fun _ : key => ptree h) x1 p
             :: skipn (S (S (div2 SIZE))) (fst (snd x0)) ++
             existTS (fun _ : key => ptree h) k (fst x9) :: nil, 
             snd x9)) (Val x5) x4.
    Proof. Opaque skipn firstn nth_error. clear.
      intros. split; fold ptree in *.
        destruct x0 as [ ? [ ? ? ] ]; fold ptree in *; simpl in *.
        rewrite <- (firstn_skipn (div2 SIZE) l) in H.
        erewrite nth_error_skipn_cons in H; eauto. rewrite lastKey_app in H. simpl in H.
        erewrite nth_error_skipn_cons in H; eauto. simpl in *. rewrite lastKey_last. simpl.
        eapply contextual_split in H. destruct H. 
        destruct H4. destruct H5. simpl in *. intuition.
        eapply contextual_append; eauto. intros. rewrite H7. auto. simpl. intuition try reflexivity.
        rewrite <- (firstn_skipn (S (div2 SIZE)) l) in H0. erewrite nth_error_skipn_cons in H0; eauto.
        rewrite lastKey_app in H0. simpl in H0. auto.
        intros. rewrite H4. auto.
        
        simpl. rewrite lastKey_last. simpl. auto.
    Qed.

    Lemma SIZE_is_two : {SIZE = 2} + {S (div2 SIZE) < SIZE}.
    Proof.
      destruct (lt_eq_lt_dec SIZE 2). destruct s.
      elimtype False. omega. firstorder.
      right. rewrite <- (twice_half SIZE) at 2; eauto.  cut (1 < div2 SIZE). omega.
      induction SIZE using ind_0_1_SS; try solve [ elimtype False; omega ].
      induction n using ind_0_1_SS; try solve [ elimtype False; omega ]. inversion SIZE_even. inversion H0. inversion H2. inversion H4.
      simpl. omega.
    Qed.

    Lemma split_merge_single : forall h p0 x7 k x5 p2 p3,
      inv h p0 x7 (Val k)
      -> inv h p3 (Val k) x5
      -> inv (S h) (p2, (existTS (fun _ : key => ptree h) k p0 :: nil, p3)) x7 x5.
    Proof. clear. Transparent BPlusTreeImplModel.inv.
      intros; firstorder; fold ptree in *.
        unfold BPlusTreeImplModel.lastKey. simpl. norm list. simpl. reflexivity.
      Opaque BPlusTreeImplModel.inv.
    Qed.
    Hint Resolve split_merge_single.
    
    Theorem odd_merge : forall h ary ll n  k p0 l OPTR',
      ll = length l ->
      repBranch h (rep') ary n ll l (firstPtr p0) ==>
      repBranch h (rep') ary n ll
      (l ++ existTS (fun _ : key => ptree h) k p0 :: nil) 
      OPTR'.
    Proof. clear.
      intros; apply iter_imp; do 2 sep fail auto.
      norm list. case_eq (nth_error l i); sep fail auto.
      autorewrite with bpt_rw. simpl. sep fail idtac.
    Qed.
    Hint Resolve odd_merge.

    Lemma inv_S_unfold : forall h x2 p0 x9 x5 x7,
      contextual h (fun (mi : LiftOrder key) (c : BranchCell h) => inv h (projT2S c) mi (Val (projT1S c))) x7
      (lastKey x9 x7) x9
      -> inv h x2 (lastKey x9 x7) x5
      -> inv (S h) (p0, (x9, x2)) x7 x5.
    Proof.
      Transparent BPlusTreeImplModel.inv.
      intros. simpl. auto.
      Opaque BPlusTreeImplModel.inv.
    Qed.
    Hint Resolve inv_S_unfold.

    Lemma QQQ : forall h (x : ptree (S h)) x7 k p pR x1 x0 kM nxtL0 nxtL,
      x7 = splitContent' k p pR (_cont x) x1 x0 ->
      nxtL = Some (kM, nxtL0) ->
      nxtL =
      match nth_error (_cont x) (div2 SIZE) with
        | Some v => Some (projT1S v, ptrFor (projT2S v))
        | None => None
      end ->
      nxtL0 = ptrFor (_next (fst x7)).
    Proof.
      intros. unfold splitContent' in *.
      case_eq (nth_error (_cont x) (div2 SIZE)); intros.
      erewrite nth_error_skipn_cons in *; eauto. simpl in *. fold ptree in *.
      rewrite H2 in *. destruct s. simpl in *. subst. simpl.
      inversion H1. compute; auto.
      rewrite H2 in *.  subst. inversion H1.
    Qed.
    Lemma QQQ' : forall h (x : ptree (S h)) x7 k r p pR x1 x0,
      x7 = splitContent' k p pR (_cont x) x1 x0 ->
      r = ptrFor x0 ->
      r = ptrFor (_next (snd x7)).
    Proof.
      intros. unfold splitContent' in *.
      case_eq (nth_error (_cont x) (div2 SIZE)); intros; fold ptree in *.
        erewrite nth_error_skipn_cons in *; eauto. destruct s. subst. compute; auto.
        norm list in H. subst. simpl. auto.
    Qed.
    Hint Resolve QQQ' QQQ.

    Opaque skipn firstn nth_error.

    Lemma repBranch_nextPtr_eq7 : forall h (x : ptree (S h)) k x1 l0 x0,
      skipn (S (div2 SIZE)) (_cont x) = l0 ->
      repBranch_nextPtr (_cont x) (div2 SIZE) (firstPtr x1) =
      match l0 ++ existTS (fun _ : key => ptree h) k x1 :: nil with
        | nil => x0
        | a :: _ => firstPtr (projT2S a)
      end.
    Proof.
      unfold BPlusTreeImplModel.repBranch_nextPtr. intros.
      rewrite <- H.
      case_eq (nth_error (_cont x) (S (div2 SIZE))); intros; fold ptree in *.
      rewrite H0. norm list. auto.
      rewrite H0. norm list. simpl. auto.
    Qed.
    Hint Resolve repBranch_nextPtr_eq7.
    Hint Resolve skipn_S_cons.
    Theorem repBranch_firstn_extra'' : forall h ary LEN x0 st X' X SLEN PLEN ZZZ,
      SLEN = S LEN ->
      PLEN = pred LEN ->
      LEN > 0 ->
      LEN < length x0 ->
      nth_error x0 LEN = Some X' ->
      X = projT2S X' ->
      repBranch h (rep') ary st LEN (firstn SLEN x0) ZZZ ==>
      repBranch h (rep') ary st LEN (firstn LEN x0) (firstPtr X).
    Proof. clear.
      intros; subst.
      unfold BPlusTreeImplModel.repBranch_nextPtr.
      norm arith.
      apply iter_imp; intros; do 2 sep fail auto.
      norm list. sep fail auto.
      case_eq (nth_error x0 i); sep fail auto.
      apply himp_rep'_eq; eauto. f_equal.
      rewrite repBranch_nextPtr_elim_firstn; auto.
      unfold BPlusTreeImplModel.repBranch_nextPtr.
      destruct (eq_nat_dec LEN (S i)).
        subst. apply nth_error_ex in H2. destruct H2. rewrite H2. norm list.
        rewrite H3 in H2. inversion H2. auto.
        cut (S i < LEN); try omega; intros. norm list.
        case_eq (nth_error x0 (S i)); intros; auto.
          elimtype False. assert (length x0 <= S i); eauto with norm_list_length.
    Qed.
    Hint Resolve repBranch_firstn_extra'' : bpt_sep.

    Lemma flat_maps_solve : forall h i (x : ptree (S h)) x1 (x0 : ptree i) p1 l0 k x8,
      skipn (div2 SIZE) (_cont x) = existTS (fun _ : key => ptree h) x8 p1 :: l0 ->
      flat_map (fun x9 : BranchCell h => as_map (projT2S x9)) (_cont x) ++
      as_map x1 ++ as_map x0 =
      flat_map (fun x9 : BranchCell h => as_map (projT2S x9)) (firstn (div2 SIZE) (_cont x)) ++
      as_map p1 ++
      flat_map (fun x9 : BranchCell h => as_map (projT2S x9)) (l0 ++ existTS (fun _ : key => ptree h) k x1 :: nil) ++ as_map x0.
    Proof. clear.
      intros. norm list. simpl.
      repeat rewrite <- app_ass. f_equal. f_equal. repeat rewrite app_ass.
      rewrite <- (firstn_skipn (div2 SIZE) (_cont x)) at 1. rewrite H. norm list.
      auto.
    Qed.
    Hint  Resolve flat_maps_solve.
    Lemma length_app : forall t (a b : list t), 
      length (a ++ b) = length a + length b.
    Proof.
      induction a; simpl in *; auto.
    Qed.
    Lemma aaa' : forall t (l0 : list t) w x y,
      length w = SIZE ->
      skipn (div2 SIZE) w = y :: l0 ->
      length (l0 ++ x :: nil) <= SIZE.
    Proof.
      intros; rewrite length_app. simpl.
      cut (length l0 = length w - div2 SIZE - 1); intros.
      cut (div2 SIZE > 0); auto. rewrite <- length_skipn. rewrite H0. simpl. auto.
    Qed.
    Hint Resolve aaa'.

    Lemma left_proof : forall h x kM p1 x8 x5 p nxtL nxtL0 x4,
      nth_error (_cont x) (div2 SIZE) = Some (existTS (fun _ : key => ptree h) x8 p1) ->
      contextual h
      (fun (mi : LiftOrder key) (c : BranchCell h) =>
        inv h (projT2S c) mi (Val (projT1S c))) x5 x4 
      (_cont x) ->
      nxtL = Some (x8, ptrFor p1) ->
      nxtL = Some (kM, nxtL0) ->
      inv (S h) (p, (firstn (div2 SIZE) (_cont x), p1)) x5 (Val kM).
    Proof. clear.
      intros. subst. inversion H2. subst.
      destruct x as [ ? [ ? ? ] ]; autorewrite with bpt_rw in *; fold ptree in *.
      rewrite <- (firstn_skipn (div2 SIZE) l) in H0. apply contextual_split in H0.
      destruct H0. erewrite nth_error_skipn_cons in H1; eauto. destruct H1.
      split; fold ptree in *; eauto.
      intros. rewrite H1 in *. auto.
    Qed.
    Lemma right_proof : forall h x1  x0 k x3 x8 p1 b kM pR x x5 x4 nxtL nxtL0,
      inv h x1 x4 (Val k) ->
      inv h x0 (Val k) x3 ->
      nxtL = Some (kM, nxtL0) ->
      nxtL = match nth_error (firstn (S (div2 SIZE)) (_cont x)) (div2 SIZE) with
               | Some v => Some (projT1S v, ptrFor (projT2S v))
               | None => None
             end ->
      skipn (div2 SIZE) (_cont x) = existTS (fun _ : key => ptree h) x8 p1 :: b ->
      contextual h
        (fun (mi : LiftOrder key) (c : BranchCell h) =>
          inv h (projT2S c) mi (Val (projT1S c))) x5 x4 
        (_cont x) ->
      inv (S h) (pR, (b ++ existTS (fun _ : key => ptree h) k x1 :: nil, x0)) (Val kM) x3.
    Proof. clear.
      intros; subst. 
      case_eq (nth_error (firstn (S (div2 SIZE)) (_cont x)) (div2 SIZE)); fold ptree in *; intros; rewrite H1 in *; [ | discriminate ].
      inversion H2. subst. clear H2.
      destruct x as [ ? [ ? ? ] ]; fold ptree in *; autorewrite with bpt_rw in *.
      rewrite <- (firstn_skipn (div2 SIZE) l) in H4. apply contextual_split in H4. 
      destruct H4. split; fold ptree in *. rewrite lastKey_last. simpl projT1S.
      eapply contextual_append; eauto. intros.
      apply (@inv_subst key value KOT h (projT2S c) a b0 (Val (projT1S c)) (Val (projT1S c)) H5). reflexivity. auto.
      rewrite H3 in H4. destruct H4. simpl in H5.
      norm list in H1. specialize (skipn_nth_error _ _ H3); intros. rewrite H6 in H1. inversion H1. simpl.
      eassumption. simpl; intuition.
      rewrite lastKey_last. simpl. auto. intros. rewrite H2. auto.
    Qed.
    Hint Resolve left_proof right_proof.
    Lemma false_elim : forall h (x : ptree (S h)) nxtL,
      nxtL = None ->
      nxtL = match nth_error (firstn (div2 SIZE + 1) (_cont x)) (div2 SIZE - 0) with
               | Some v => Some (projT1S v, ptrFor (projT2S v))
               | None => None
             end ->
      length (_cont x) = SIZE ->  
      False.
    Proof.
      intros; norm arith in *; norm list in *.
      case_eq (nth_error (_cont x) (div2 SIZE)); intros.
      rewrite H2 in *. subst. inversion H0.
      cut (length (_cont x) <= div2 SIZE); eauto with norm_list_length; intros.
      fold ptree in *.
      rewrite <- (twice_half SIZE) in H1. cut (0 < div2 SIZE); eauto. intros; omega. auto.
    Qed.

    Lemma repBranch_nextPtr_ignore_default_gen : forall h a b i j (LS LS' : list (BranchCell h)),
      S i < length LS ->
      nth_error LS (S i) = nth_error LS' (S j) ->
      repBranch_nextPtr LS i a = repBranch_nextPtr LS' j b.
    Proof.
      intros; unfold BPlusTreeImplModel.repBranch_nextPtr. 
      rewrite <- H0. case_eq (nth_error LS (S i)); intros.
      auto. elimtype False. cut (length LS <= S i); try omega; eauto with norm_list_length.
    Qed.
    Lemma repBranch_nextPtr_eq_6 : forall h len i (ls : list (BranchCell h)) k p1 X,
      i < len ->
      len < length ls -> 
      nth_error ls len = Some (existTS (fun _ : key => ptree h) k p1) ->
      repBranch_nextPtr (firstn (S len) ls) i X =
      repBranch_nextPtr (firstn len ls) i (firstPtr p1).
    Proof.
      intros; unfold BPlusTreeImplModel.repBranch_nextPtr.
      cut (S len <= length ls); eauto with norm_list_length; intros.
      norm list.
      destruct (eq_nat_dec (S i) len).
      rewrite <- e in *.
      assert (nth_error (firstn (S i) ls) (S i) = None); eauto with norm_list_length.
      rewrite H3.  rewrite H1. simpl. auto.
      norm list. case_eq (nth_error ls (S i)); intros; auto.
      elimtype False.
      cut (length ls <= S i); eauto with norm_list_length.
    Qed.
    Lemma repBranch_imp_a : forall h ary st len (ls : list (BranchCell h)) k p1 X,
      len < length ls ->
      nth_error ls len = Some (existTS _ k p1) ->
      repBranch h rep' ary st len (firstn (S len) ls) X ==>
      repBranch h rep' ary st len (firstn len ls) (firstPtr p1).
    Proof.
      intros; apply iter_imp; intros; do 2 sep fail auto; norm list.
      case_eq (nth_error ls i); intros; sep fail auto.
      apply himp_rep'_eq; eauto. f_equal.

      eapply repBranch_nextPtr_eq_6; eauto.
    Qed.

    Lemma flat_maps_normed_solve : forall h i (x : ptree (S h)) x1 (x0 : ptree i) p1 k x8 b,
      skipn (div2 SIZE) (_cont x) = existTS (fun _ : key => ptree h) x8 p1 :: b ->
      flat_map (fun x9 : BranchCell h => as_map (projT2S x9)) (_cont x) ++
      as_map x1 ++ as_map x0 =
      flat_map (fun x9 : BranchCell h => as_map (projT2S x9))
      (firstn (div2 SIZE) (_cont x)) ++
      as_map p1 ++
      flat_map (fun x9 : BranchCell h => as_map (projT2S x9)) b ++
      as_map (projT2S (existTS (fun _ : key => ptree h) k x1)) ++ as_map x0.
    Proof. clear.
      intros. norm list. simpl.
      repeat rewrite <- app_ass. f_equal. f_equal. repeat rewrite app_ass.
      rewrite <- (firstn_skipn (div2 SIZE) (_cont x)) at 1. rewrite H. norm list.
      auto.
    Qed.
    Hint Resolve flat_maps_normed_solve.

    Lemma learn_split : forall h (x : ptree (S h)) nxtL P Q p,
      length (_cont x) = SIZE ->
      nxtL = Some p ->
      (forall a b, skipn (div2 SIZE) (_cont x) = a :: b ->
        [nxtL =
          match nth_error (firstn (div2 SIZE + 1) (_cont x)) (div2 SIZE - 0) with
            | Some v0 => Some (projT1S v0, ptrFor (projT2S v0))
            | None => @None (key * ptr)
          end] * P ==> Q) ->
      [nxtL =
        match nth_error (firstn (div2 SIZE + 1) (_cont x)) (div2 SIZE - 0) with
          | Some v0 => Some (projT1S v0, ptrFor (projT2S v0))
          | None => @None (key * ptr)
        end] * P ==> Q.
    Proof.
      intros. intro_pure.
      case_eq (skipn (div2 SIZE) (_cont x)); intros.
        norm list in H2. norm arith in *.  norm list in H2. subst. congruence.
        eapply H1. eassumption.
    Qed.
    Ltac g := idtac;
      match goal with
        | [ H : skipn _ _ = _ :: _ |- _ ] => fail 1
        | _ => search_prem ltac:(eapply learn_split; [ solve [ eauto ] | solve [ eauto ] | intros ])
      end.

    Definition splitBranch_atEnd : forall (min mid max : [LiftOrder key]) (h : nat)
      (p : ptr) (ary : array) l r (optr : [option ptr]) (lM : [ptree h]) k (rM : [ptree h]) (m : [ptree (S h)]),
      STsep (m ~~ optr ~~ max ~~ mid ~~ min ~~ lM ~~ rM ~~
              Exists p0 :@ ptr,
              [inv h lM mid (Val k)] *
              [inv h rM (Val k) max] *
              [l = ptrFor lM] * 
              [r = ptrFor rM] *
              rep' l (Some (firstPtr rM)) lM *
              rep' r optr rM *
              repBranch h (rep') ary 0 SIZE (_cont m) (firstPtr lM) *
              p ~~> mkNode (S h) ary (Some p0) *
              [length (_cont m) = SIZE] *
              [array_length ary = SIZE] *
              [mid = lastKey (_cont m) min] *
              [contextual h
                (fun (mi : LiftOrder key) (c : BranchCell h) =>
                  inv h (projT2S c) mi (Val (projT1S c))) min mid
                (_cont m)])
            (fun res : sigT (fun o : op => [opModel (S h) o])%type =>
              resM :~~ projT2 res in min ~~ max ~~ optr ~~ m ~~ lM ~~ rM ~~
              repOp (S h) (projT1 res) resM min max optr *
              [firstPtrOp (S h) (projT1 res) resM =
                match head (_cont m) with
                  | Some n => firstPtr (projT2S n)
                  | None => firstPtr lM                    
                end] *
              [flat_map (fun x0 : BranchCell h => as_map (projT2S x0))
                (_cont m) ++
                as_map lM ++ as_map rM =
                as_mapOp (S h) (projT1 res) resM]).
      refine (fun min mid max h p ary l r optr lM k rM m =>
        aryR <- new_constant_array SIZE (@None (key * ptr)) <@> _ ;

        (** put (k,l) in aryR at SIZE / 2 **)
        upd_array aryR (pred (div2 SIZE)) (Some (k,l)) <@> _ ;;

        (** copy indicies [SIZE / 2, SIZE) into aryR (write None to the rest) **)
        moveBranch_nextOp ary aryR m k lM rM <@> _ ;;

        (** **)
        pR <- New (mkNode (S h) aryR (Some r)) ;
        nxtL <- sub_array ary (div2 SIZE) (fun v : option (key * ptr) => _ ) ;
        match nxtL as nxtL' return nxtL = nxtL' -> _ with 
          | None           => fun _ => {{ !!! }}
          | Some (kM,nxtL) => fun _ =>
            (** write None to ary[SIZE/2] **)
            upd_array ary (div2 SIZE) (@None (key * ptr)) <@> _ ;;
            p ::= mkNode (S h) ary (Some nxtL) ;;
            {{ Return (existT (fun o => [opModel (S h) o]%type) (Split p kM pR)
              (lM ~~~' rM ~~~' inhabit_unpack m (fun pM =>
                splitContent' k p pR (_cont pM) lM rM))) }}
        end (refl_equal _)).
    Proof.
      solve [ sep2 fail bpt_elim; sep_unify ].
      solve [ sep_unify ].

      solve [ sep2 fail bpt_elim; sep_unify ].
      solve [ sep_unify ].

      sep2 fail bpt_elim.
        fold ptree in *; norm arith. 
          rewrite nth_error_red_0. rewrite skipn_red_S. rewrite skipn_nil.
          simpl projT1S. simpl projT2S.
        sep2 fail bpt_elim. sep_unify.
      solve [ sep_unify ].
      solve [ sep_unify ].
      solve [ sep_unify ].
      
      solve [ sep2 fail bpt_elim; clear H17; sep_unify ].
      solve [ sep_unify ].

      solve [ sep2 fail bpt_elim; sep_unify ].
      solve [ sep_unify ].
      
      solve [ sep2 fail bpt_elim; sep_unify ].
      solve [ sep_unify ].
      solve [ sep_unify ].

      sep2 g bpt_elim.
        generalize dependent x7. rewrite H18 in *.
        simpl; intros; fold ptree in *; norm arith.

        sep2 bpt_elab bpt_elim.
        norm list in H20. norm arith in *.
        unfold splitContent' in H7. rewrite H19 in H7. destruct a. rewrite <- H7. simpl.
        autorewrite with bpt_rw. rewrite (skipn_nth_error _ _ H19) in *. subst. inversion H20. auto.
        norm arith in *. norm list in H20. rewrite (skipn_nth_error _ _ H19) in *. 
        unfold splitContent' in H7. rewrite H19 in H7. destruct a. rewrite <- H7. simpl.
        autorewrite with bpt_rw. auto.

        intro.
        norm arith in *. norm list in H20. rewrite (skipn_nth_error _ _ H19) in *. 
        unfold splitContent' in H7. rewrite H19 in H7. destruct a. rewrite <- H7. simpl.
        autorewrite with bpt_rw. rewrite (skipn_S_cons _ _ H19). sep fail auto.
        
        norm arith in *. norm list in H20. rewrite (skipn_nth_error _ _ H19) in *. 
        unfold splitContent' in H7. rewrite H19 in H7. destruct a. rewrite <- H7. simpl.
        autorewrite with bpt_rw. norm list.

        sep2 fail bpt_elim.
        intro. 
        eapply repBranch_imp_a; eauto with norm_list_length. rewrite H12; eauto.
          eapply skipn_nth_error. eauto.
        Hint Resolve skipn_nth_error.
        sep2 fail bpt_elim.
        fold ptree in *.
        cut (length (firstn (div2 SIZE) (_cont x)) <= div2 SIZE); eauto with norm_list_length; intros.
        fold ptree in *; rewrite (nth_error_len_rw _ H25).

        rewrite (skipn_nth_error _ _ H19).
        sep2 fail bpt_elim.
        assert (length (firstn (div2 SIZE) (_cont x)) <= SIZE); eauto with norm_list_length. 
        solve [ sep2 fail bpt_elim; sep_unify ].

        sep2 fail bpt_elim. 
          elimtype False. eapply false_elim; eauto.
        sep fail idtac.
   Qed.


    Lemma lastKey_append : forall h (LS LS' : list (BranchCell h)) DEF,
      lastKey (LS ++ LS') DEF = lastKey LS' (lastKey LS DEF).
    Proof. clear.
      induction LS; simpl; auto.
    Qed.
    Lemma lastKey_move : forall h n (ls : list (BranchCell h)) X,
      lastKey ls X = lastKey (skipn n ls) (lastKey (firstn n ls) X).
    Proof. clear.
      induction n. Transparent skipn firstn.
      simpl. auto.
      destruct ls; auto. simpl. auto.
    Qed.
    Lemma inv_replace : forall h pos x5 x6 x8 x7 x10 x3 midH,
      pos < length (fst x3)
      -> Val midH = lastKey (firstn (S pos) (fst x3)) x7
      -> contextual h
          (fun (mi : LiftOrder key) (c : BranchCell h) =>
            inv h (projT2S c) mi (Val (projT1S c))) 
          (Val midH)
          (lastKey (fst x3) (Val midH))
          (skipn (S pos) (fst x3))
      -> contextual h
          (fun (mi : LiftOrder key) (c : BranchCell h) =>
            inv h (projT2S c) mi (Val (projT1S c))) x7 x6
          (firstn pos (fst x3))
      -> inv h x8 x6 (Val midH)
      -> inv h (snd x3) (lastKey (fst x3) (Val midH)) x5
      -> inv (S h)
           (x10,
             (firstn pos (fst x3) ++
               existTS (fun _ : key => ptree h) midH x8
               :: skipn (S pos) (fst x3), snd x3)) x7 x5.
    Proof. clear.
      intros. Transparent BPlusTreeImplModel.inv. Opaque skipn. simpl. fold ptree in *. Opaque BPlusTreeImplModel.inv.
      split. eapply contextual_append. intros. rewrite H5. auto. eauto.

      simpl. intuition eauto. rewrite (lastKey_move _ (S pos)) in H1.
      generalize dependent (firstn (S pos) (fst x3)). destruct l; intros.
       rewrite lastKey_app. simpl. auto. rewrite lastKey_app.
       simpl in *. rewrite <- H0 in H1. auto.

      rewrite lastKey_app. simpl. rewrite (lastKey_move _ (S pos)) in H4.
      generalize dependent (firstn (S pos) (fst x3)). destruct l; intros.
        auto. simpl in *. rewrite <- H0 in H4. auto.
    Qed.
    
    Hint Resolve inv_replace.

    Lemma lt_0_diff : forall a b,
      a < b -> 0 < b - a.
      intros; omega.
    Qed.
    
    Lemma skipping_one_len : forall T (LS : list T) i,
      i < length LS ->
      S (length (firstn i LS ++ skipn (S i) LS)) = length LS.
    Proof. clear.
      induction LS.
        simpl; intros; norm list. elimtype False; omega.
        simpl; intros; norm list. Transparent skipn. simpl skipn.
        destruct i. simpl. norm list. auto. Opaque skipn.
        Transparent firstn. norm list. simpl. eauto.
        Opaque firstn.
    Qed.

    Lemma list_length_contra : forall T x (x1 : list T) i,
      i < length (firstn i (x :: x1) ++ skipn (S i) (x :: x1))
      -> length x1 < S i
      -> S (length (firstn i (x :: x1) ++ skipn (S i) (x :: x1))) = length (x :: x1)
      -> False.
    Proof. 
      clear; intros; simpl in *; omega.
    Qed.
    Hint Resolve skipping_one_len list_length_contra.

    Lemma nth_error_firstn_skipn : forall T i (LS : list T) j k,
      j <= length LS ->
      j <= i ->
      nth_error (firstn j LS ++ skipn k LS) i = nth_error LS (k + i - j).
    Proof. clear. Transparent firstn nth_error skipn.
      induction i. intros. cut (j = 0); try omega; intros; subst. norm list;  norm arith. auto.
        destruct j; intros. norm list. norm arith. auto. 
        destruct k. norm arith. rewrite nth_error_app; auto. norm list. norm arith.
        cut (length (firstn (S j) LS) = S j); auto.
        rewrite firstn_length_l; auto.
        destruct LS. norm list; simpl; auto. 
        rewrite firstn_length_l; auto.
        Change (S k + S i - S j) into (S (k + i - j)) using omega. simpl. destruct LS; auto. simpl. apply IHi; auto. simpl in *; auto.
    Qed.

    Lemma nth_error_shift_next : forall T i (x : T) x1 idx,
      i <= length (x :: x1) ->
      nth_error (skipn (S i) (x :: x1)) (i + idx - (idx + i))
      =
      nth_error (firstn i (x :: x1) ++ skipn (S i) (x :: x1)) i.
    Proof. clear.
      intros. Change (i + idx - (idx + i)) into 0 using omega.
      rewrite nth_error_firstn_skipn; eauto.
      norm arith.
      Change 0 into (S i - S i) using omega.
      rewrite nth_error_skipn; eauto.
    Qed.
    Hint Resolve nth_error_shift_next.

    Lemma skipn_ELIM : forall T (x : T) x1 i,
      (skipn 1 (skipn (S i) (x :: x1))) = (skipn (S (S i)) (x :: x1)).
      intros. rewrite skipn_combine. eauto.
    Qed.
    Hint Resolve skipn_ELIM.

    Lemma getting_next : forall T i (LS : list T) X,
      nth_error (firstn i LS ++ skipn (S i) LS) i = Some X
      -> Some X = nth_error LS (S i).
    Proof. clear. Transparent nth_error skipn firstn.
      induction i. simpl; intros. destruct LS; try discriminate. destruct LS; auto.
      intros. destruct LS. simpl in *. discriminate. apply IHi; auto.
    Qed.
    Hint Resolve getting_next.
    Lemma next_leq : forall T i (x : T) x1 X,
      nth_error (firstn i (x :: x1) ++ skipn (S i) (x :: x1)) i = Some X
      -> S i <= length x1.
    Proof. clear.
      induction i. simpl; intros. destruct x1; try discriminate; auto. simpl. auto.
      intros. destruct x1. simpl in *. norm list in *. discriminate. simpl in *.
      Hint Resolve Le.le_n_S. eauto.
    Qed.
    Hint Resolve next_leq.

    Lemma choice_HOW : forall T i (x : T) x1 X v0,
      i <= length x1
      -> Some v0 = nth_error (x :: x1) i
      -> nth_error (firstn i (x :: x1) ++ skipn (S i) (x :: x1)) i = Some X
      -> skipn i (x :: firstn i x1) = v0 :: nil.
    Proof. clear. Transparent skipn firstn nth_error.
      induction i. simpl; intros. destruct x1. discriminate. inversion H0; auto.
      intros. destruct x1. simpl in *. elimtype False; omega. simpl in *.
      eauto.
    Qed.
    Hint Resolve choice_HOW.
    Lemma another_HOW : forall T i (x : T) x1 X,
      nth_error (firstn i (x :: x1) ++ skipn (S i) (x :: x1)) i = Some X
      -> nth_error (skipn (S i) (x :: x1)) 0 = Some X.
    Proof. clear. Transparent skipn firstn nth_error.
      induction i. auto.
      destruct x1; simpl in *; intros. norm list in *. discriminate.
      eauto.
    Qed.

    Lemma better_way_to_write : forall h i x x1 p x4 x0,
      nth_error (firstn i (x :: x1) ++ skipn (S i) (x :: x1)) i =
        Some (existTS (fun _ : key => ptree h) x4 p)
      -> repBranch_nextPtr (x :: x1) i x0 = firstPtr p.
    Proof. clear. unfold BPlusTreeImplModel.repBranch_nextPtr.
      induction i. destruct x1; simpl; intros; try discriminate. inversion H; auto.
      destruct x1; simpl; intros. norm list in *. discriminate. eapply IHi. eauto.
    Qed.
    Hint Resolve better_way_to_write.

    Lemma repBranch_nextPtr_skipn : forall h i (LS : list (BranchCell h)) x0,
      repBranch_nextPtr (skipn (S i) LS) 0 x0 = repBranch_nextPtr LS (S i) x0.
    Proof. clear. Transparent skipn firstn nth_error.
      unfold BPlusTreeImplModel.repBranch_nextPtr.
      induction i; destruct LS; intros; simpl in *; norm list in *; try discriminate; auto.
      Opaque skipn firstn nth_error.
    Qed.
    Hint Resolve repBranch_nextPtr_skipn.

    Lemma derive_length_HOW : forall T i (x : T) x1,
      i <= length x1
      -> nth_error (firstn i (x :: x1) ++ skipn (S i) (x :: x1)) i = None
      -> i = length x1.
    Proof. clear. Transparent firstn skipn nth_error.
      induction i. simpl; intros. destruct x1; auto; discriminate.
      destruct x1; simpl in *; intros. elimtype False; omega. eauto.
      Opaque firstn skipn nth_error.
    Qed.
    Hint Resolve derive_length_HOW.
    Lemma get_case_None : forall (T:Set) U (V : T -> Set) (X : option (sigTS V)) F,
      @None U =
      match X with
        | Some (existTS a b) => Some (F a b)
        | None => None
      end
      -> X = None.
    Proof. clear.      
      destruct X; auto; intros. destruct s. discriminate.
    Qed.
    (** Coq can't unify this for some reason **)
    Lemma manual_combine_WHY : forall h i (x:BranchCell h) x1,
      i <= length x1
      -> None =
      match nth_error (firstn i (x :: x1) ++ skipn (S i) (x :: x1)) i with
        | Some (existTS a b) => Some (a, ptrFor b)
        | None => None
      end
      -> i = length x1.
    Proof. clear.
      intros. eapply derive_length_HOW; eauto. 
      case_eq (nth_error (firstn i (x :: x1) ++ skipn (S i) (x :: x1)) i); intros.
      rewrite H1 in *; destruct s; discriminate. eassumption.
    Qed.
    Hint Resolve manual_combine_WHY.
    
    Lemma repBranch_firstn_prefix2 : forall h ary i (LS : list (BranchCell h)) idx XXX YYY v1,
      i <= length LS ->
      Some v1 = nth_error LS i ->
      YYY = firstPtr (projT2S v1) ->
      repBranch h (rep') ary idx i (firstn i LS) YYY
      ==>
      repBranch h (rep') ary idx i LS XXX.
    Proof. clear. Transparent nth_error firstn.
      intros; eapply iter_imp; intros; do 2 sep fail auto.
      norm list. case_eq (nth_error LS i0); intros; sep fail auto.
      apply himp_rep'_eq; eauto. f_equal.
      unfold BPlusTreeImplModel.repBranch_nextPtr.
      destruct (eq_nat_dec (S i0) i). subst. 
      cut (length (firstn (S i0) LS) <= S i0); eauto with norm_list_length; intros.
      norm list. rewrite <- H0. auto.
      norm list. destruct (@nth_error_ex _ (S i0) LS); try omega. rewrite H5; auto.
    Qed.
    Hint Resolve repBranch_firstn_prefix2.
    Lemma norm_list_should_get_this_ELIM : forall T i x1 (x : T) v1,
      i = length x1
      -> Some v1 = nth_error (x :: x1) i
      -> skipn i (x :: x1) = v1 :: nil.
    Proof. clear. Transparent skipn.
      induction i; destruct x1; simpl in *; intros; try inversion H0; try discriminate; eauto.
      Opaque skipn.
    Qed.
    
    Lemma coq_should_get_this_ELIM : forall T (x : T) x1 i,
      i = length x1 -> S i >= length (x :: x1).
      simpl; intros; omega.
    Qed.
    Hint Resolve coq_should_get_this_ELIM.

    Lemma last_nth_error : forall T i (LS : list T) def,
      i = length LS ->
      nth_error (def :: LS) i = Some (last LS def).
    Proof. clear.
      induction i; destruct LS; intros; try solve [ simpl in *; discriminate ]; auto.
      simpl in H. cut (i = length LS); try omega; intros. simpl nth_error.
      erewrite IHi. rewrite last_cons_red. auto. auto.
    Qed.

    Lemma last_nth_error_hint : forall t (x : t) x1 i v1,
      Some v1 = nth_error (x :: x1) i ->
      length x1 = i ->
      v1 = last x1 x.
    Proof. intros. 
      rewrite last_nth_error in H; auto. inversion H; auto.
    Qed.

    Lemma repBranch_with_end : forall h ary i idx x x1 OPTR v1,
      i = length x1 ->
      v1 = last x1 x ->
      repBranch h (rep') ary idx i (firstn i (x :: x1)) (firstPtr (projT2S v1)) ==>
      repBranch h (rep') ary idx i (x :: x1) OPTR.
    Proof. clear.
      intros; apply iter_imp; intros; do 2 sep fail auto.        
      norm list. case_eq (nth_error (x :: x1) i0); sep fail auto.
      apply himp_rep'_eq; eauto.
      f_equal. unfold BPlusTreeImplModel.repBranch_nextPtr.
      destruct (eq_nat_dec (S i0) (length x1)).
      norm list. case_eq (nth_error x1 i0); intros. 
      eapply (last_nth_error _ x) in e. norm list in e. rewrite H3 in e. inversion e. auto.
      cut (length x1 <= i0); eauto with norm_list_length; intros; elimtype False; omega.
      norm list. case_eq (nth_error x1 i0); auto; intros.
      elimtype False. cut (length x1 <= i0); eauto with norm_list_length.
    Qed.

    Lemma repBranch_nextPtr_0_cons_skipn : forall h (s : BranchCell h) i x1 x0,
      repBranch_nextPtr (s :: skipn (S i) x1) 0 x0 = repBranch_nextPtr x1 i x0. 
    Proof. clear.
      intros; unfold BPlusTreeImplModel.repBranch_nextPtr.
      norm list. norm arith. auto.
    Qed.

    Lemma nth_error_through_firstn : forall t i j (ls : list t) x,
      nth_error ls i = x -> i < j -> nth_error (firstn j ls) i = x.
    Proof. clear.
      induction i; intros. destruct j. think. destruct ls. simpl in *. auto. norm list in *; auto.
      destruct j. think. destruct ls. think. think.
    Qed.

    Lemma repBranch_nextPtr_eq10 : forall h i (x : BranchCell h) x1 i0 v0 s,
      i0 < i ->
      Some v0 = nth_error (x :: x1) i ->
      repBranch_nextPtr (firstn i (x :: x1)) i0 (firstPtr (projT2S v0)) =
      repBranch_nextPtr (x :: firstn i x1) i0 s.
    Proof. clear.
      intros; unfold BPlusTreeImplModel.repBranch_nextPtr;
        change (x :: firstn i x1) with (firstn (S i) (x :: x1)).
      case_eq (nth_error (x :: x1) (S i0)); intros.
      destruct (eq_nat_dec (S i0) i).
      norm list. rewrite <- e in *. norm list in H0. rewrite <- H0. auto.
      repeat erewrite nth_error_through_firstn by eauto. auto.
      cut (length (x :: x1) <= S i0); eauto with norm_list_length; intros.
      elimtype False.
      assert (i < length (x :: x1)). eauto with norm_list_length. omega.
    Qed.

    Lemma repBranch_eq9 : forall h ary idx i x x1 v0 s,
      Some v0 = nth_error (x :: x1) i ->
      repBranch h rep' ary idx i (firstn i (x :: x1)) (firstPtr (projT2S v0)) ==>
      repBranch h rep' ary idx i (x :: firstn i x1) s.
    Proof. clear.
      intros; apply iter_imp; do 2 sep fail auto.
      change (x :: firstn i x1) with (firstn (S i) (x :: x1)).
      case_eq (nth_error (x :: x1) i0); intros;
        repeat erewrite nth_error_through_firstn by eauto; sep fail auto.
      apply himp_rep'_eq; auto. f_equal.
      Hint Resolve repBranch_nextPtr_eq10.
      eauto with bpt_sep.
    Qed.

    Lemma xxxx : forall t i (x1 : list t),
      0 < length (skipn i x1) -> S i <= length x1.
    Proof. clear.
      intros. rewrite length_skipn in H. omega.
    Qed.

    Lemma repBranch_nextPtr_eq11 : forall h (x : BranchCell h) x1 i x0 s,
      nth_error (x :: x1) (S i) = Some s ->
      repBranch_nextPtr (x :: x1) i x0 = 
      repBranch_nextPtr (x :: firstn i x1) i (firstPtr (projT2S s)).
    Proof. clear.
      intros; unfold BPlusTreeImplModel.repBranch_nextPtr.
      norm list in *. rewrite H.
      cut (length (firstn i x1) <= i); eauto with norm_list_length. norm list. auto.
    Qed.

    Lemma elab_length : forall h i (x1 : list (BranchCell h)) P Q x,
      i <= length x1 ->
      (i = length x1 -> P ==> Q) ->
      [None =
        match nth_error x1 (i + (i - length (firstn i (x :: x1)))) with
          | Some v3 => Some (projT1S v3, ptrFor (projT2S v3))
          | None => None
        end] * P ==> Q.
    Proof. clear.
      intros. intro_pure. cut (i = length x1); intros. sep fail auto. clear H0.
      case_eq (nth_error x1 (i + (i - length (firstn i (x :: x1))))); intros; rewrite H0 in *.
        congruence.
        cut (length x1 <= i + (i - length (firstn i (x :: x1)))); eauto with norm_list_length; intros.
        cut (length (firstn i (x :: x1)) = i); eauto with norm_list_length; intros.
        cut (i <= S (length x1)); eauto; intros.
        change (S (length x1)) with (length (x :: x1)) in *. eauto with norm_list_length.
    Qed.


    Definition shiftInsert' : forall (h : nat) (idx : nat) (ary : array)
      (val : key * ptr) (modM : [ptree h])
      (lsM : [list (BranchCell h)]) (nxtP : [ptr]),
      STsep (lsM ~~ nxtP ~~ modM ~~
              repBranch h (rep') ary idx (SIZE - idx) lsM nxtP *
              rep' (snd val) (Some match head lsM with
                                       | None   => nxtP
                                       | Some v => firstPtr (projT2S v)
                                     end) modM *
             [length lsM <= SIZE - idx])
            (fun res:option ((key * ptr) * [ptree h]) * nat => lsM ~~ nxtP ~~ modM ~~
              [length (existTS (fun _:key => ptree h) (fst val) modM :: lsM) = snd res] *
              match fst res with
                | None => 
                  repBranch h (rep') ary idx (SIZE - idx)
                  (existTS (fun _:key => ptree h) (fst val) modM :: lsM) nxtP *
                  [length lsM < SIZE - idx]
                | Some ((k,p),tm) => tm ~~
                  repBranch h (rep') ary idx (SIZE - idx)
                    (existTS (fun _:key => ptree h) (fst val) modM :: lsM) (firstPtr tm) *
                  rep' p (Some nxtP) tm *
                  [existTS _ k tm = last lsM (existTS (fun _:key => ptree h) (fst val) modM)] *
                  [length lsM = SIZE - idx]
              end).
      clear. refine (fun h idx ary val modM lsM nxtP =>
          let modM' := modM ~~~ (existTS (fun _:key => ptree h) (fst val) modM) in
          {{ Fix2 (fun i v => lsM ~~ nxtP ~~ modM' ~~
                    Exists m :@ BranchCell h,
                    repBranch h (rep') ary idx i
                      (firstn i (modM' :: lsM)) (firstPtr (projT2S m)) *
                    repBranch h (rep') ary (idx + i) (SIZE - idx - i) 
                      (skipn (S i) (modM' :: lsM)) nxtP *
                    rep' (snd v) (Some (repBranch_nextPtr (modM' :: lsM) i nxtP)) (projT2S m) *
                    [Some m = nth_error (modM' :: lsM) i] *
                    [fst v = projT1S m] * [snd v = ptrFor (projT2S m)] *
                    [length lsM <= SIZE - idx] * [i <= length lsM])
                  (fun _ _ (res:option ((key * ptr) * [ptree h]) * nat) => lsM ~~ nxtP ~~ modM' ~~
                    [length (modM' :: lsM) = snd res] *
                    match fst res with
                      | None => 
                        repBranch h (rep') ary idx (SIZE - idx) (modM' :: lsM) nxtP *
                        [length lsM < SIZE - idx]
                      | Some ((k,p),tm) => tm ~~
                        repBranch h (rep') ary idx (SIZE - idx)
                        (modM' :: lsM) (firstPtr tm) *
                        rep' p (Some nxtP) tm *
                        [existTS _ k tm = last lsM modM'] *
                        [length lsM = SIZE - idx]
                    end)
                  (fun self i v =>
                    match le_lt_dec (SIZE - idx) i with
                      | right _ => 
                        cur <- sub_array ary (i + idx) (fun v : option (key * ptr) => lsM ~~ modM' ~~
                          [v = match nth_error (firstn i (modM' :: lsM) ++ skipn (S i) (modM' :: lsM)) i with
                                 | None => @None (key * ptr)
                                 | Some v => Some (projT1S v, ptrFor (projT2S v))
                               end] * _);
                        upd_array ary (i + idx) (Some v) <@> _ ;;
                        match cur as v' return cur = v' -> _ with
                          | None => fun pfEq => 
                            {{ Return (None, S i) }}
                          | Some v' => fun pfEq =>
                            {{ self (S i) v' }}
                            
                        end (refl_equal _)
                      | left pf =>
                        {{ Return (Some (v, (lsM ~~~' modM' ~~~ projT2S (last lsM modM'))), S i) }}
                    end)
             0 val }});
        try (rewrite pfEq in * ); try clear self.
    Proof.
      (** Full Case **)
      solve [ sep_unify ].
      sep2 fail bpt_elim.
        rewrite H9 in *; clear H9. norm pair. do 2 sep2 fail bpt_elim.
        Hint Resolve last_nth_error_hint. 
        Hint Extern 1 (projT2S ?X = projT2S ?Y) => f_equal.
        f_equal; simple eapply last_nth_error_hint; eauto. eauto.
          cut (length (x :: x1) <= S i); intros. autorewrite with bpt_rw; auto.
          simpl; auto with norm_list_length.
        Hint Resolve repBranch_with_end.
        intros; eapply repBranch_with_end; eauto. eapply last_nth_error_hint; eauto. eauto.
        simpl.
        sep fail auto.
          assert (existTS (fun _ : key => ptree h) (fst v) (projT2S (last x1 x)) = last x1 x).          
          rewrite last_nth_error in H4; eauto. inversion H4. destruct v1. rewrite <- H17. simpl in *. rewrite <- H12; auto.
          sep fail auto.

      (** **)
      sep2 fail bpt_elim.
        Change (i + idx - (idx + i)) into 0 using omega.
        rewrite nth_error_firstn_skipn; eauto with norm_list_length. norm arith. 
        rewrite nth_error_skipn. norm arith.
        solve [ sep2 fail bpt_elim; sep_unify ].
      solve [ sep_unify ].
      solve [ sep2 fail bpt_elim; sep_unify ].
      solve [ sep_unify ].
      sep2 fail bpt_elim. 
        rewrite nth_error_firstn_skipn in *; eauto with norm_list_length. norm arith in *.
        case_eq (nth_error (x :: x1) (S i)); intros; [ | rewrite H13 in *; congruence ].
        search_conc ltac:(simple eapply himp_ex_conc; exists s). sep2 fail bpt_elim.
          inversion H12; auto.
          Hint Rewrite repBranch_nextPtr_0_cons_skipn : bpt_rw.
          autorewrite with bpt_rw. eauto with bpt_sep.
          Hint Resolve repBranch_eq9 : bpt_sep.
          eauto with bpt_sep.

          norm arith. erewrite nth_error_through_firstn by eauto. rewrite <- H7.
            inversion H12.
            Hint Resolve xxxx.
            sep2 fail bpt_elim.

            Hint Resolve repBranch_nextPtr_eq11.
            eauto with bpt_sep.
            destruct v; auto.
            solve [ sep fail idtac ].

      solve [ sep2 fail bpt_elim; sep fail idtac ].
      solve [ sep_unify ].
      
      sep2 fail bpt_elim.
        rewrite H6 in *. norm pair. norm list in *.
        sep2 ltac:(search_prem ltac:(idtac;match goal with
                                             | [ H : i = length x1 |- _ ] => fail 1
                                             | _ => simple eapply elab_length; [ eauto | intros ]
                                           end)) bpt_elim.
          norm arith. rewrite <- H8. sep2 fail bpt_elim.
            destruct v; eauto.
            norm list. rewrite H15. solve [ sep fail auto ].

      (** Enter Loop **)
      sep2 bpt_elab bpt_elim.
      unfold modM' in *.
      search_conc ltac:(eapply himp_ex_conc; exists x).
      sep2 fail bpt_elim.
        rewrite <- H; auto.
        rewrite <- H; sep fail auto.
    
      (** Exit Loop **)
      sep2 fail bpt_elim.
      unfold modM' in *. sep fail auto.
    Qed.

    Definition shiftInsert : forall (h : nat) (idx : nat) (ary : array)
      (val : key * ptr) (modM : [ptree h])
      (lsM : [list (BranchCell h)]) (nxtP : [ptr]),
      STsep (lsM ~~ nxtP ~~ modM ~~
              repBranch h (rep') ary idx (SIZE - idx) lsM nxtP *
              rep' (snd val) (Some match head lsM with
                                     | None    => nxtP
                                     | Some v => firstPtr (projT2S v)
                                   end) modM *
              [length lsM < SIZE - idx])
            (fun _:unit => lsM ~~ nxtP ~~ modM ~~
              repBranch h (rep') ary idx (SIZE - idx)
              (existTS (fun _:key => ptree h) (fst val) modM :: lsM) nxtP).
      clear.
      refine (fun h idx ary val modM lsM nxtP =>
          res <- @shiftInsert' h idx ary val modM lsM nxtP <@> _ ;
          {{ Return tt }}).
    Proof.
      solve [ sep2 fail bpt_elim; sep_unify ].
      solve [ sep_unify ].
      solve [ sep_unify ].
      sep2 fail bpt_elim.
        destruct (fst res). destruct p. destruct p. inhabiter. intro_pure. elimtype False; omega.
        sep2 fail bpt_elim. sep_unify.
    Qed.

End BPlusTreeImpl.
