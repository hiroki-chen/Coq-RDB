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
Require Import Eqdep.
Require Import Think ThinkList ThinkArith.

Require Import BPlusTreeImplModel.
Require Import BPlusTreeModelFacts.
Require Import BPlusTreeTactics.
Require Import BPlusTreeImplNewFree.

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

  Fixpoint leaves {h} : ptree h -> list (ptree 0) :=
    match h as h return ptree h -> list (ptree 0) with
      | 0 => fun pt => pt :: nil
      | S h' => fun pt =>
        flat_map (fun x:BranchCell h' => leaves (projT2S x)) (_cont pt) ++ leaves (_next pt)
    end.

  Fixpoint rep'_spine {n : nat} (p : ptr) (op_next : option ptr) {struct n} :
    ptree n -> hprop :=
    match n as n return (ptree n -> hprop) with
      | 0 => fun m => [p = ptrFor m]
      | S n' => fun m =>
          [p = ptrFor m] *
          (Exists ary :@ array,
            p ~~> mkNode n ary (Some (ptrFor (_next m))) *
            [array_length ary = SIZE] * [length (_cont m) <= SIZE] *
            repBranch n' (rep'_spine) ary 0 SIZE (_cont m)
            (firstPtr (_next m)) *
            rep'_spine (ptrFor (_next m)) op_next (_next m))
    end.

  Definition firstPtrLeaves (pts : list (ptree 0)) (i : nat) (fin_at : option ptr) : option ptr :=
    match nth_error pts i with
      | None => fin_at
      | Some v => Some (ptrFor v)
    end.

  Fixpoint repLeaves (p : option ptr) (pts : list (ptree 0)) (fin_at : option ptr) : hprop :=
    match pts with
      | nil => [p = fin_at]
      | a :: rr =>
        let ls := snd a in
        let nxt := firstPtrLeaves rr 0 fin_at in
        Exists ary :@ array,
        [p = Some (ptrFor a)] *
        (ptrFor a) ~~> mkNode 0 ary nxt * [array_length ary = SIZE] *
        [length ls <= SIZE] * repLeaf ary 0 SIZE ls *
        repLeaves nxt rr fin_at
    end.

  Lemma repLeaves_append : forall a b p optr optr',
    optr' = firstPtrLeaves b 0 optr ->
    repLeaves p a optr' * repLeaves optr' b optr ==> repLeaves p (a ++ b) optr.
  Proof.
    induction a; intros; norm list.
      simpl. sep fail auto.
      simpl. inhabiter. search_conc ltac:(simple apply himp_ex_conc; exists v). intro_pure; canceler.
        unfold firstPtrLeaves in *. destruct a0. norm list. auto. auto.
        search_conc ltac:(eapply himp_rsubst; [ eapply IHa | ]).
        eauto. canceler. destruct a0. unfold firstPtrLeaves. norm list. sep fail auto.
        unfold firstPtrLeaves. norm list. auto.    
  Qed.
  
  Lemma leaves_not_nil : forall h (l : ptree h),
    exists a, exists b, leaves l = a :: b.
  Proof.
    induction h; intros.
    simpl; eauto.
    destruct l as [ ? [ ? ? ] ]. simpl. fold ptree in *.
    autorewrite with bpt_rw. case_eq l; intros; simpl.
    eauto.
    destruct (IHh (projT2S s)). destruct H0. 
    exists x. exists (x0 ++ flat_map (fun x1 : BranchCell h => leaves (projT2S x1)) l0 ++ leaves p0).
    rewrite H0. norm list. auto.
  Qed.

  Lemma firstPtr_firstPtrLeaves : forall h (m : ptree h) optr,
    firstPtrLeaves (leaves m) 0 optr = Some (firstPtr m).
  Proof. clear.
    induction h; intros.
    simpl. unfold firstPtrLeaves. norm list. auto.
    simpl. destruct m as [ ? [ ? ? ] ]. simpl. autorewrite with bpt_rw.
    destruct l. rewrite <- (IHh _ optr). auto.
    rewrite <- (IHh _ optr). simpl.
    destruct (leaves_not_nil _ (projT2S s)). destruct H. fold ptree in *. rewrite H.
    simpl. unfold firstPtrLeaves. norm list. auto.
  Qed.

  Lemma rep'_to_rep'_spine_lem : forall h len optr v st (l : list (BranchCell h)) (p0 : ptr) (p1 : ptree h),
    (forall (p : ptr) (optr : option ptr) (m : ptree h), 
      rep' p optr m ==>
      rep'_spine p optr m * repLeaves (Some (firstPtr m)) (leaves m) optr) ->
    length l <= len ->
    repBranch h rep' v st len l (firstPtr p1) ==>
    repLeaves (Some (@BPlusTreeImplModel.firstPtr _ _ (S h) (p0, (l, p1))))
      (flat_map (fun x : BranchCell h => leaves (projT2S x)) l)
      (firstPtrLeaves (leaves p1) 0 optr) * repBranch h rep'_spine v st len l (firstPtr p1).
  Proof.
    induction len; intros.
      destruct l; [ | simpl in *; elimtype False; omega ].
        simpl. rewrite firstPtr_firstPtrLeaves. unfold BPlusTreeImplModel.repBranch. sep fail auto.
      destruct l.
        simpl; autorewrite with bpt_rw in *. rewrite firstPtr_firstPtrLeaves. canceler. sep fail auto.
        apply iter_imp; sep fail auto; norm list. auto.

        unfold BPlusTreeImplModel.repBranch. simpl iter_sep. sep fail auto.
          search_prem ltac:(eapply himp_subst; [ eapply H; eauto | ]). canceler.
          search_conc ltac:(eapply himp_rsubst; [ eapply repLeaves_append; eauto | ]).
          rewrite firstPtr_firstPtrLeaves. 
          assert ((firstPtrLeaves
         (flat_map (fun x0 : BranchCell h => leaves (projT2S x0)) l) 0
         (Some (firstPtr p1))) = Some (repBranch_nextPtr (s :: l) 0 (firstPtr p1))).
            unfold BPlusTreeImplModel.repBranch_nextPtr. norm list. unfold firstPtrLeaves.
            destruct l. auto. simpl. destruct (leaves_not_nil _ (projT2S s0)). destruct H2.
            rewrite H2. simpl. rewrite <- (firstPtr_firstPtrLeaves _ _ optr). rewrite H2.
            unfold firstPtrLeaves. simpl. auto.
          unfold BPlusTreeImplModel.ptree in *. rewrite H2. fold ptree in *. canceler.
          cut (length l <= len); try omega; intros.
          generalize (IHlen optr v (S st) l p0 p1 H H3); intros.
          eapply himp_trans. eapply himp_trans. Focus 2. eapply H4.
          apply iter_shift; intros. norm arith.
          Change (st + S i) into (S st + i) using omega. sep fail auto.
          autorewrite with bpt_rw. unfold BPlusTreeImplModel.repBranch.
          apply himp_split. unfold BPlusTreeImplModel.repBranch_nextPtr. norm list.
          rewrite firstPtr_firstPtrLeaves. 
          destruct l; sep fail auto.
          apply iter_shift; intros. norm arith. Change (st + S i) into (S st + i) using omega.
          sep fail auto.
  Qed.

  Lemma rep'_to_rep'_spine : forall h (p : ptr) (optr : option ptr) (m : ptree h),
    rep' p optr m ==> rep'_spine p optr m * repLeaves (Some (firstPtr m)) (leaves m) optr.
  Proof.
    induction h.
      sep fail auto.
      intros. simpl @leaves. search_conc ltac:(eapply himp_rsubst; [ eapply repLeaves_append | ]). auto.
      simpl @rep'_spine. simpl BPlusTreeImplModel.rep'. inhabiter. 
      instantiate_conc v. intro_pure. canceler. search_prem ltac:(eapply himp_subst; [ eapply IHh | ]). canceler.
    clear H. destruct m as [ ? [ ? ? ] ]; autorewrite with bpt_rw in *; fold ptree in *.
      rewrite firstPtr_firstPtrLeaves. canceler.
    eapply himp_trans. eapply (@rep'_to_rep'_spine_lem h SIZE optr v 0 l p0 p1 IHh); auto.
    rewrite firstPtr_firstPtrLeaves. auto.
  Qed.

  Lemma repLeaves_append' : forall a b p optr optr',
    optr' = firstPtrLeaves b 0 optr ->
    repLeaves p (a ++ b) optr ==> repLeaves p a optr' * repLeaves optr' b optr.
  Proof.
    induction a; intros; norm list.
      simpl. subst. destruct b. simpl. intro_pure. subst. unfold firstPtrLeaves. norm list. sep fail auto.
         sep fail auto.

      simpl. inhabiter. instantiate_conc v. intro_pure; canceler.
        unfold firstPtrLeaves in *. destruct a0. norm list. auto. auto.
        search_conc ltac:(eapply himp_rsubst; [ eapply IHa | ]).
        eauto. canceler. destruct a0. unfold firstPtrLeaves. norm list. sep fail auto.
        unfold firstPtrLeaves. norm list. auto.    
  Qed.

  Lemma rep'_spine_to_rep'_lem : forall h len v st (m : ptree (S h)) p,
    (forall (p : ptr) (optr : option ptr) (m : ptree h),
      rep'_spine p optr m * repLeaves (Some (firstPtr m)) (leaves m) optr ==>
      rep' p optr m) ->
    p = fst m ->
    length (_cont m) <= len ->
    repLeaves (Some (firstPtr m))
      (flat_map (fun x : BranchCell h => leaves (projT2S x)) (_cont m))
      (Some (firstPtr (_next m))) *
      repBranch h rep'_spine v st len (_cont m) (firstPtr (_next m)) ==>
    repBranch h rep' v st len (_cont m) (firstPtr (_next m)).
  Proof.
    induction len; destruct m as [ ? [ ? ? ] ]; intros.
      autorewrite with bpt_rw in *. destruct l; [ | simpl in *; elimtype False; omega ]. sep fail auto.
      autorewrite with bpt_rw in *. destruct l.
        simpl. sep fail auto. apply iter_imp; do 2 sep fail auto. norm list. sep fail auto.
        simpl. search_prem ltac:(eapply himp_subst; [ eapply repLeaves_append' | ]); auto.
          unfold BPlusTreeImplModel.repBranch. simpl. norm arith. sep fail auto.
          search_conc ltac:(eapply himp_rsubst; [ eapply H | ]). canceler.
          assert (Some (repBranch_nextPtr (s :: l) 0 (firstPtr p0)) = firstPtrLeaves
         (flat_map (fun x0 : BranchCell h => leaves (projT2S x0)) l) 0
         (Some (firstPtr p0))).
            unfold BPlusTreeImplModel.repBranch_nextPtr. norm list.
            destruct l. unfold firstPtrLeaves; simpl; norm list. auto.
            unfold firstPtrLeaves; simpl; norm list. destruct (leaves_not_nil _ (projT2S s0)).
            destruct H0. unfold BPlusTreeImplModel.ptree in *. rewrite H0. fold ptree in *. simpl.
            rewrite <- (firstPtr_firstPtrLeaves _ _ None). rewrite H0. unfold firstPtrLeaves. norm list. auto.
          unfold BPlusTreeImplModel.ptree in *. rewrite <- H0. fold ptree in *. canceler.
        generalize (IHlen v (S st) (p, (l, p0)) p H); intros.
        eapply himp_trans; [ | eapply himp_trans ].  Focus 2.  eapply H3; simpl in *; auto. autorewrite with bpt_rw. auto.
      autorewrite with bpt_rw. apply himp_split.
        unfold BPlusTreeImplModel.repBranch_nextPtr. norm list.
        destruct l; norm list; auto.
      apply iter_shift; intros. norm arith.
        Change (st + S i) into (S st + i) using omega.
        do 2 sep fail auto.
      apply iter_shift; intros; norm arith.
        Change (st + S i) into (S st + i) using omega.
        do 2 sep fail auto.
  Qed.

  Lemma rep'_spine_to_rep' : forall h (p : ptr) (optr : option ptr) (m : ptree h),
    rep'_spine p optr m * repLeaves (Some (firstPtr m)) (leaves m) optr ==> rep' p optr m.
  Proof.
    induction h.
      sep fail auto.
      intros. simpl @leaves. search_prem ltac:(eapply himp_subst; [ eapply repLeaves_append' | ]). auto.
      simpl @rep'_spine. simpl BPlusTreeImplModel.rep'. inhabiter. 
      instantiate_conc v. intro_pure. canceler. search_conc ltac:(eapply himp_rsubst; [ eapply IHh | ]). canceler.
      rewrite firstPtr_firstPtrLeaves. canceler. 
      eapply rep'_spine_to_rep'_lem; auto.
  Qed.

  Section getLeaves.

    Lemma read_Some_contra : forall h k p2 (p5 : ptree (S h)) P Q,
      Some (k, p2) =
      match nth_error (_cont p5) 0 with
        | Some v => Some (projT1S v, ptrFor (projT2S v))
        | None => None
      end ->
      ((Exists v :@ BranchCell h, 
        [nth_error (_cont p5) 0 = Some v] *
        [k = projT1S v] * [p2 = ptrFor (projT2S v)] *
        [0 < length (_cont p5)] *
        rep' p2 (Some (repBranch_nextPtr (_cont p5) 0 (firstPtr (_next p5)))) (projT2S v)) * P ==> Q) ->
      (match nth_error (_cont p5) 0 with
         | Some v =>
           [0 < length (_cont p5)] *
           rep' (ptrFor (projT2S v))
           (Some
             (repBranch_nextPtr (_cont p5) 0 (firstPtr (_next p5))))
           (projT2S v)
         | None => [length (_cont p5) <= 0]
       end * P ==> Q).
    Proof. clear.
      intros. eapply himp_trans; [ | eassumption ]. 
      case_eq (nth_error (_cont p5) 0); intros; rewrite H1 in *.
        search_conc ltac:(simple apply himp_ex_conc; exists s); fold ptree in *. 
          destruct s. inversion H. sep fail auto.
        congruence.
    Qed.
    Lemma read_None_contra : forall h (p5 : ptree (S h)) P Q,
      None =
      match nth_error (_cont p5) 0 with
        | Some v => Some (projT1S v, ptrFor (projT2S v))
        | None => None
      end ->
      ([nth_error (_cont p5) 0 = None] * [length (_cont p5) = 0] * P ==> Q) ->
      (match nth_error (_cont p5) 0 with
         | Some v =>
           [0 < length (_cont p5)] *
           rep' (ptrFor (projT2S v))
           (Some
             (repBranch_nextPtr (_cont p5) 0 (firstPtr (_next p5))))
           (projT2S v)
         | None => [length (_cont p5) <= 0]
       end * P ==> Q).
    Proof. clear.
      intros. eapply himp_trans; [ | eassumption ]. 
      case_eq (nth_error (_cont p5) 0); intros; rewrite H1 in *.
        congruence.
        sep fail auto.
    Qed.
    Lemma rep'_combine2 : forall h p (pt : ptree (S h)) optr P Q,
      P ==> ([p = ptrFor pt] * Exists ary :@ array,
             p ~~> mkNode (S h) ary (Some (ptrFor (_next pt))) * 
             [array_length ary = SIZE] * [length (_cont pt) <= SIZE] *
             repBranch h (rep') ary 0 SIZE (_cont pt) (firstPtr (_next pt)) *
             rep' (ptrFor (_next pt)) optr (_next pt))%hprop * Q ->
      P ==> @BPlusTreeImplModel.rep' SIZE key value (S h) p optr pt * Q.
    Proof.
      intros. eapply himp_trans; [ eassumption | ]; clear H.
      Transparent BPlusTreeImplModel.rep'.
      sep fail idtac.
      Opaque BPlusTreeImplModel.rep'.
    Qed.

    Lemma first_ptr : forall h v (x0 : ptree (S h)) (v1 : BranchCell h) x4,
      v = firstPtr x4 ->
      nth_error (_cont x0) 0 = Some v1 ->
      projT2S v1 = x4 ->
      v = firstPtr x0.
    Proof.
      intros; subst. destruct x0 as [ ? [ ? ? ] ]. autorewrite with bpt_rw in *. simpl.
      destruct l. norm list in H0; congruence. norm list in H0. inversion H0. auto.
    Qed.
    Hint Immediate first_ptr.

    Lemma firstPtr_empty_list : forall h v (x0 : ptree (S h)) (x3 : ptree h),
      v = firstPtr x3 ->
      _next x0 = x3 ->
      nth_error (_cont x0) 0 = None ->
      v = firstPtr x0.
    Proof. clear.
      intros; subst. destruct x0 as [ ? [ ? ? ] ]. autorewrite with bpt_rw in *.
      destruct l; auto. Transparent nth_error. simpl in H1. discriminate. Opaque nth_error.
    Qed.
    Hint Immediate firstPtr_empty_list.

    Fixpoint buildDummy_ptree (h : nat) (p : ptr) : ptree h:=
      match h as h return ptree h with
        | 0 => (p, nil)
        | S n => (p, (@nil (sigTS (fun _:key => ptree n)), buildDummy_ptree n p))
      end.

    Opaque firstn skipn nth_error.
    Opaque BPlusTreeImplModel.rep' BPlusTreeImplModel.repBranch. 
  Definition getLeaves : forall h p (m : [ptree h]), 
    STsep (m ~~ rep' p None m)
          (fun res : ptr => m ~~
            rep'_spine p None m * repLeaves (Some (firstPtr m)) (leaves m) None *
            [res = firstPtr m]).
    refine (fun h p m => 
      {{ (fix getLeaves h : forall (p : ptr) (m :  [ptree h]) (optr : [option ptr]),
            STsep (m ~~ optr ~~ rep' p optr m)
                  (fun res : ptr => optr ~~ m ~~ rep' p optr m * [res = firstPtr m]) := 
            match h as h return forall (p : ptr) (m :  [ptree h]) (optr : [option ptr]),
              STsep (m ~~ optr ~~ rep' p optr m)
                    (fun res : ptr => optr ~~ m ~~ rep' p optr m * [res = firstPtr m]) 
              with 
              | 0    => fun p m optr => {{ Return p }}
              | S h' => fun p m optr =>
                br <- readBranch pfMin p optr m <@> _ ;
                let ary := fst br in
                let nxt := snd br in
                f <- sub_array ary 0 _ ;
                let _ : option (key * ptr) := f in
                match f as f' return f = f' -> _ with
                  | None       => fun pf => {{ getLeaves h' nxt (m ~~~ _next m) optr <@> _ }}
                  | Some (_,p) => fun pf => 
                    {{ getLeaves h' p (m ~~~ match nth_error (_cont m) 0 with
                                               | None => buildDummy_ptree h' p (** junk **)
                                               | Some v => projT2S v
                                             end)
                                      (m ~~~ Some (repBranch_nextPtr (_cont m) 0 (firstPtr (_next m)))) <@> _ }}
                end (refl_equal _)
            end) h p m [None]%inhabited }}); try clear getLeaves; try (rewrite pf in *; clear pf).
  Proof.
    solve [ sep_unify ].
    solve [ sep2 bpt_elab bpt_elim; sep_unify ].
    solve [ sep2 bpt_elab bpt_elim; sep_unify ].
    solve [ sep_unify ].
    solve [ sep2 ltac:(bpt_elab || norm arith) bpt_elim; sep_unify ].
    solve [ sep_unify ].
    sep2 bpt_elab bpt_elim. search_prem ltac:(simple eapply read_Some_contra; [ eassumption | ]).
      solve [ sep2 bpt_elab bpt_elim; sep_unify ].

    sep2 bpt_elab bpt_elim. search_conc ltac:(eapply rep'_combine2). sep2 bpt_elab bpt_elim.
      norm arith in *. fold ptree in *. rewrite H11. sep2 bpt_elab bpt_elim. sep_unify.
      
    solve [ sep2 bpt_elab bpt_elim; sep_unify ].
    sep2 bpt_elab bpt_elim. search_prem ltac:(simple eapply read_None_contra; [ eassumption | ]).
      search_conc ltac:(eapply rep'_combine2). sep2 bpt_elab bpt_elim.
      unfold nxt in *; subst; auto.
      unfold nxt in *; subst; auto.
      norm arith; fold ptree in *. rewrite H10. sep2 fail bpt_elim.

    sep2 fail bpt_elim. sep_unify.
    sep2 fail bpt_elim; sep_unify.
    sep2 fail bpt_elim. eapply himp_subst; [ eapply rep'_to_rep'_spine | ]. subst. sep fail auto.
  Qed.

  End getLeaves.

  Section iterate_leaves.
    Lemma repLeaves_NoneNone : forall x P Q,
      (x = nil -> repLeaves None x None * P ==> Q) ->
      repLeaves None x None * P ==> Q.
    Proof. clear.
      intros; case_eq x; intros; subst; auto.
      simpl repLeaves. inhabiter. intro_pure. discriminate.
    Qed.

    Ltac bpt_elab_leaves := 
      search_prem ltac:(idtac;
        match goal with 
          | [ H : ?X = nil 
            |- repLeaves None ?X None * _ ==> _ ] => fail 1
          | [ |- repLeaves None ?X None * _ ==> _ ] => simple apply repLeaves_NoneNone; intro
        end).

    Lemma unfold_repLeaves : forall p (x : list (ptree 0)) P Q,
      (let nxt := firstPtrLeaves x 1 None in
       (Exists f :@ ptree 0, [Some f = head x] *
        let ls := snd f in [p = fst f] *
        Exists ary :@ array, Exists nde :@ nodeType,
        p ~~> nde * [nde = mkNode 0 ary nxt] * [array_length ary = SIZE] *
        [length ls <= SIZE] * repLeaf ary 0 SIZE ls) *
       repLeaves nxt (tail x) None * P ==> Q) ->
      repLeaves (Some p) x None * P ==> Q.
    Proof. clear.
      intros. destruct x; simpl in *.
        intro_pure. discriminate.
        eapply himp_trans; [ | eassumption ]. sep fail auto. 
          inversion H1. sep fail auto.
    Qed.
    Lemma end_of_loop : forall T (I : T -> Model -> hprop) (v0 : ptree 0) i x0 acc,
      length (snd v0) <= i ->
      I acc (flat_map (fun x2 : ptree 0 => as_map x2) x0 ++ firstn i (as_map v0)) ==>
      I acc (flat_map (fun x2 : ptree 0 => as_map x2) (x0 ++ v0 :: nil)).
    Proof. clear.
      intros. norm list. auto.
    Qed.
    Hint Resolve end_of_loop.

    Lemma option_exn : forall t (v : list t) i,
      exc2opt (nth_error v i) = nth_error v i.
    Proof.
      intros; case_eq (nth_error v i); auto.
    Qed.
    Hint Immediate option_exn. 

    Lemma firstn_extend_end : forall T i (kv : T) v0,
      Some kv = nth_error v0 i ->
      firstn (S i) v0 = (firstn i v0) ++ kv :: nil.
    Proof. clear.
      induction i; destruct v0; intros; norm list in H; try discriminate.
        inversion H. norm list. auto.
        norm list. f_equal. eauto.
    Qed.

    Lemma invariant_next : forall T (I : T -> Model -> hprop) x3 kv (v0 : ptree 0) acc' x0 i,
      Some kv = nth_error (snd v0) i ->
      flat_map (fun x : ptr * list (sigTS value) => snd x) x0 ++ firstn i (snd v0) = x3 ->
      I acc' (x3 ++ existTS value (projT1S kv) (projT2S kv) :: nil) ==>
      I acc' (flat_map (fun x4 : ptree 0 => as_map x4) x0 ++ firstn (S i) (as_map v0)).
    Proof. clear.
      intros. Opaque firstn. simpl.
      rewrite (firstn_extend_end _ _ H). norm list.
      cutrewrite (x3 ++ existTS value (projT1S kv) (projT2S kv) :: nil = flat_map (fun x4 : ptr * list (sigTS value) => snd x4) x0 ++
        firstn i (snd v0) ++ kv :: nil); auto.
      rewrite <- H0. norm list. destruct kv; auto.
    Qed.
    Hint Resolve invariant_next.

    Lemma next_pf : forall t (ls : list t) kv i, 
      Some kv = nth_error ls i ->
      S i <= length ls.
    Proof. 
      intros. cut (i < length ls); eauto with norm_list_length.
    Qed.
    Hint Resolve next_pf.

    Lemma aaa : forall T (I : T -> Model -> hprop) i (v1 : ptree 0) x0 acc,
      None = nth_error (snd v1) i ->
      I acc (flat_map (fun x3 : ptree 0 => as_map x3) x0 ++ firstn i (as_map v1)) ==>
      I acc (flat_map (fun x3 : ptree 0 => as_map x3) (x0 ++ v1 :: nil)).
    Proof.
      intros.
      cut (length (snd v1) <= i); eauto with norm_list_length.
    Qed.
    Hint Immediate aaa.

    Lemma himp_f_eq_2 : forall A B (f : A -> B -> hprop) a b a' b',
      a = a' -> b = b' -> f a b ==> f a' b'.
      intros; subst; auto.
    Qed.
    Hint Resolve himp_f_eq_2.

    Ltac bpt_ext x := 
         (progress unfold BPlusTreeImplModel.repLeaf)
      || bpt_elim
      || match goal with
           | [ |- ?F _ _ * _ ==> ?F _ _ * _ ] => idtac;
             match F with
               | hprop_sep => fail 1
               | _ => apply himp_split; [ apply himp_f_eq_2; eauto | ]
             end
         end.
    Ltac bpt_elab_ext := 
         search_prem ltac:(eapply unfold_repLeaves)
      || bpt_elab.

    Lemma eq_app_firstn0 : forall T (X : list T) L,        
      X = X ++ firstn 0 L.
      intros; norm list; auto.
    Qed.
    Hint Immediate eq_app_firstn0.

  Definition iterate_leaves : forall (T : Type) 
    (I : T -> Model -> hprop)
    (fn : forall (k : key) (v:value k) (acc: T) lm,
         STsep (lm ~~ I acc lm) (fun a:T => lm ~~ I a (lm ++ existTS _ _ v :: nil)))
    (acc : T) p (m : [list (ptree 0)]),
    STsep (m ~~ repLeaves p m None * I acc nil)
          (fun res:T => m ~~ repLeaves p m None *
             I res (flat_map (fun x => as_map x) m)).
    refine (fun T I fn acc p m =>
      {{ Fix4 (fun (p : option ptr) (acc:T) (b a : [list (ptree 0)]) =>
                b ~~ a ~~ repLeaves p a None * I acc (flat_map (fun x => as_map x) b))
              (fun p _ b a (res:T) => 
                b ~~ a ~~ repLeaves p a None * I res (flat_map (fun x => as_map x) (b ++ a)))
              (fun self p acc b a =>
                IfNull p Then 
                  {{ Return acc }}
                Else
                  nde <- ! p ;
                  cr <- Fix2 (fun (i : nat) (acc : T) => a ~~ b ~~
                               Exists c :@ ptree 0, [head a = Some c] *
                               [i <= length (snd c)] * [length (snd c) <= SIZE] *
                               repLeaf (content nde) 0 SIZE (snd c) *
                               I acc (flat_map (fun x => as_map x) b ++ (firstn i (as_map c))))
                             (fun _ _ (res : T) => a ~~ b ~~ 
                               Exists c :@ ptree 0, [head a = Some c] *
                               repLeaf (content nde) 0 SIZE (snd c) *
                               I res (flat_map (fun x => as_map x) (b ++ c :: nil)))
                             (fun self i acc => 
                               if le_lt_dec SIZE i then
                                 {{ Return acc }}
                               else
                                 v <- sub_array (content nde) i 
                                      (fun v : option (sigTS value) => 
                                        a ~~ Exists c :@ ptree 0, [head a = Some c] * 
                                        [v = nth_error (snd c) i] *
                                        {@ p2 :~~ array_plus (content nde) j in
                                          p2 ~~> exc2opt (nth_error (snd c) (j - 0)) | j <- 0 + i} *
                                        {@ p2 :~~ array_plus (content nde) j in
                                          p2 ~~> exc2opt (nth_error (snd c) (j - 0)) | j <- (S i) + (SIZE - S i)}) <@> _ ;

                                 match v as v' return v = v' -> _ with 
                                   | None    => fun pf => {{ Return acc }}
                                   | Some kv => fun pf => 
                                     acc' <- fn (projT1S kv) (projT2S kv) acc 
                                             (b ~~~' a ~~~ flat_map (fun x => as_map x) b ++
                                               match head a with 
                                                 | None   => nil
                                                 | Some c => firstn i (as_map c)
                                               end) <@> _ ;
                                     {{ self (S i) acc' }}
                                 end (refl_equal _)) 0 acc <@> _ ;
                  {{ self (next nde) cr (b ~~~' a ~~~  match head a with 
                                                         | None => b 
                                                         | Some v => b ++ v :: nil
                                                       end)
                                        (a ~~~ tail a) <@> _ }})
              p acc [nil]%inhabited m }}); try (rewrite _H in *; clear _H); try (rewrite pf in *; clear pf).
  Proof.
    solve [ sep_unify ].
    solve [ sep2 bpt_elab_leaves bpt_elim; subst; norm list; sep fail auto ].

    solve [ sep2 bpt_elab_ext bpt_elim; unfold nxt; sep_unify ].    
    solve [ sep_unify ].
    
    (** inner-most loop **)
    solve [ sep_unify ].
    solve [ sep2 fail bpt_elim; instantiate_conc v0; sep2 fail bpt_elim; sep_unify ].
    
    (** i < SIZE **)
    sep2 fail bpt_ext. 
      sep2 fail bpt_elim. norm arith. instantiate_conc v.
      solve [ sep2 fail bpt_elim; sep_unify ].
    solve [ sep_unify ].

    (** Some **)
    sep2 fail bpt_elim. unfold BPlusTreeImplModel.ptree in *. rewrite H6 in H8. inversion H8. red_prems. clear H5 H8.
      rewrite <- H3. sep2 fail bpt_elim. sep_unify.

    solve [ sep_unify ].
    sep2 fail bpt_elim. instantiate_conc v0. sep2 fail bpt_elim.
      unfold BPlusTreeImplModel.repLeaf. sep2 fail bpt_elim. norm arith. rewrite <- H6. 
      Lemma iter_implication : forall T a b (v0 : list T) nde,
        {@hprop_unpack (array_plus (content nde) j)
          (fun p2 : ptr => p2 ~~> exc2opt (nth_error v0 (j - 0))) | j <-
         a + b} ==>
        {@hprop_unpack (array_plus (content nde) i0)
          (fun p2 : ptr =>
            p2 ~~> exc2opt (nth_error (skipn a v0) (i0 - a))) | i0 <-
          a + b}.
      Proof.
        intros; apply iter_imp; intros; norm list. norm arith.
          Change (a + (i - a)) into i using omega.
        auto.
      Qed.
      Hint Immediate iter_implication.
      solve [ sep2 fail bpt_elim; sep_unify ].
        
    solve [ auto ].
    solve [ sep_unify ].
    
    sep2 fail bpt_elim. instantiate_conc v1. unfold BPlusTreeImplModel.repLeaf.
      fold ptree in *. rewrite H5 in H8. inversion H8. rewrite H11 in *; clear H11 H4.
      sep2 fail bpt_elim. norm arith. rewrite <- H6. symmetry. auto.
      solve [ sep_unify ].

    sep2 fail bpt_ext. instantiate_conc v. sep2 fail bpt_ext.
      unfold BPlusTreeImplModel.Model; auto.
      assert (v0 = content nde). subst; auto.
      rewrite H9. simpl content. solve [ sep2 fail bpt_elim; sep_unify ].

    solve [ sep_unify ].
    sep2 fail bpt_elim.
      rewrite H6 in H8. inversion H8. clear H5 H8.
      Lemma subst_help : forall t (x : list t) x0 x2 v0,
        match head x with
          | Some v => x0 ++ v :: nil
          | None => x0
        end = x2 ->
        head x = Some v0 ->
        x0 ++ v0 :: nil = x2.
      Proof. 
        intros; subst. rewrite H0. auto.
      Qed.
      Hint Immediate subst_help. unfold BPlusTreeImplModel.Model.
      Hint Extern 0 (flat_map ?X ?Y = flat_map ?X ?B) => f_equal.
      cutrewrite (next nde = firstPtrLeaves x 1 None); [ | rewrite H10; auto ].
      solve [ sep2 fail bpt_ext; sep_unify ].

    Lemma shift_cons : forall t (x : list t) x3 x2 x0 v0,
      match head x with
        | Some v => x0 ++ v :: nil
        | None => x0
      end = x2 ->
      tail x = x3 ->
      Some v0 = head x ->
      x2 ++ x3 = x0 ++ x.
    Proof.
      intros; subst. rewrite <- H1. destruct x. simpl in *; discriminate.
      simpl in *. norm list.  inversion H1. auto.
    Qed.
    Hint Immediate shift_cons.
    Lemma repLeaves_combine : forall p (x : list (ptree 0)) P Q,
      (let nxt := firstPtrLeaves x 1 None in
       P ==> 
        Exists f :@ ptree 0, [Some f = head x] *
        let ls := snd f in [p = fst f] *
        Exists ary :@ array, Exists nde :@ nodeType,
        p ~~> nde * [nde = mkNode 0 ary nxt] * [array_length ary = SIZE] *
        [length ls <= SIZE] * repLeaf ary 0 SIZE ls *
        repLeaves nxt (tail x) None * Q) ->
      P ==> repLeaves (Some p) x None * Q.
    Proof. clear.
      intros. eapply himp_trans; [ eassumption | ].
       destruct x. sep fail auto. discriminate.
       inhabiter. intro_pure. simpl in *. inversion H7.
       sep fail auto.
    Qed.
    Lemma repLeaves_elab : forall (x3 : list (ptree 0)) pp P Q,
      (x3 = nil -> pp = None -> P ==> Q) ->
      (forall a b, x3 = a :: b -> pp = Some (ptrFor a) ->
        repLeaves (Some (ptrFor a)) (a :: b) None * P ==> Q) ->
      repLeaves pp x3 None * P ==> Q.
    Proof. clear.
      intros. case_eq x3; intros; simpl.
        sep fail auto. 
        sep fail auto. eapply himp_trans; [ | eapply (H0 p l); auto ].
          sep fail auto.
    Qed.
    sep2 bpt_elab_ext bpt_ext; search_conc ltac:(simple apply repLeaves_combine); search_prem ltac:(eapply repLeaves_elab); sep2 bpt_elab_ext bpt_ext;
      instantiate_conc v0; instantiate_conc (content nde); instantiate_conc nde; sep2 fail bpt_elim.
      unfold BPlusTreeImplModel.Model in *. rewrite H11 in *; simpl in *. rewrite H3. simpl.
        Lemma tail_nil_second_ptr : forall x A,
          tail x = nil -> firstPtrLeaves x 1 A = A.
        Proof.
          destruct x. firstorder. simpl. firstorder. subst. auto.
        Qed.
        Hint Immediate tail_nil_second_ptr.
        sep fail auto.
      unfold BPlusTreeImplModel.ptree in *. rewrite H3. rewrite H11. simpl.
      instantiate_conc v2. sep2 fail bpt_ext. inversion H22.
        Lemma tail_cons_second_ptr : forall x x3 a0 b0,
          tail x = x3 ->
          x3 = a0 :: b0 ->
          firstPtrLeaves x 1 None = Some (fst a0).
        Proof. clear.
          intros; subst. destruct x; simpl in *. discriminate. subst.
          unfold firstPtrLeaves. norm list. auto.
        Qed.
        Hint Immediate tail_cons_second_ptr.
        solve [ sep2 fail bpt_elim; sep_unify ].
    
    solve [ sep2 fail bpt_elim; sep_unify ].
    solve [ sep2 fail bpt_elim; subst; norm list; auto ].
   Qed.
  End iterate_leaves.

  Open Local Scope stsep_scope.

  Lemma control_rw : forall rec (x0 : ptree (projT1S (snd rec))) x1 pLeaves (v:ptr) v0 v1,
    inhabit_unpack (projT2S (snd rec)) (fun m : ptree (projT1S (snd rec)) => m) = [x0]%inhabited ->
    inhabit_unpack (projT2S (snd rec)) (fun m : ptree (projT1S (snd rec)) => leaves m) = [x1]%inhabited ->
    pLeaves = firstPtr x0 ->
    rec = (v, existTS (fun h : nat => [ptree h]%type) v0 [v1]%inhabited) ->
    repLeaves (Some (firstPtr x0)) (leaves x0) None ==>
    repLeaves (Some pLeaves) x1 None.
  Proof.
    intros. generalize dependent x0. rewrite H2. simpl. sep fail auto.
  Qed.
  Lemma leaves_are_tree : forall h (x : ptree h) x1,
    leaves x = x1 ->
    flat_map (fun x2 : ptree 0 => as_map x2) x1 = as_map x.
  Proof. clear.
    induction h; intros.
      simpl in *. subst. simpl. norm list. auto.
      simpl in *. destruct x as [ ? [ ? ? ] ]. autorewrite with bpt_rw in *.
        simpl in *. fold ptree in *. rewrite <- H.
        norm list. f_equal; eauto. generalize dependent IHh. clear.
        induction l; auto.
          intros. simpl. norm list. f_equal; eauto.
  Qed.

  Definition orderedIterate : forall (T : Type) (t : BptMap)
    (I : T -> Model -> hprop)
    (tm : [Model])
    (fn : forall (k : key) (v:value k) (acc: T) lm,
         STsep (lm ~~ I acc lm)
               (fun a:T => lm ~~ I a (lm ++ existTS _ _ v :: nil)))
    (acc : T),
    STsep (tm ~~ rep t tm * I acc nil)
          (fun res:T => tm ~~ Exists tm' :@ Model, 
            [eqlistA (entry_eq KOT value_eq) tm tm'] *
            rep t tm * I res tm').
    refine (fun T t I tm fn acc =>
      rec <- t !! (rep_frame _ _ value_eq t tm) <@> _ ;
      pLeaves <- getLeaves (projT1S (snd rec) ) (fst rec) (inhabit_unpack (projT2S (snd rec)) (fun m => m)) <@> _ ;
      {{ iterate_leaves I fn acc (Some pLeaves) (inhabit_unpack (projT2S (snd rec)) (fun m => leaves m)) <@> _ }}).
  Proof.
    unfold BPlusTreeImplModel.rep, BPlusTreeImplModel.rep_frame. sep2 bpt_elab bpt_elim. 
      instantiate_conc v. instantiate_conc v0. instantiate_conc v1. sep2 fail bpt_elim. instantiate (2 := SIZE).
      solve [ sep2 fail bpt_elim; sep_unify ].
    solve [ sep_unify ].
    unfold BPlusTreeImplModel.rep_frame. sep2 fail bpt_elim.
      generalize dependent x0. rewrite H6; simpl; fold ptree in *.
      sep2 fail bpt_elim.
      instantiate (1 := tm ~~ Exists p :@ ptr, Exists h :@ nat, Exists tr :@ ptree h,
        t ~~> (p, existTS (fun h:nat => [ptree h]%type) _ [tr]%inhabited) *
        I acc nil * [inv h tr MinK MaxK] * [eqlistA (entry_eq KOT value_eq) tm (as_map tr)] *
        [rec = (p, existTS (fun h : nat => [ptree h]%type) h [tr]%inhabited)]).
      sep fail auto.
    solve [ sep_unify ].  
    Hint Immediate control_rw.
    solve [ sep2 fail bpt_elim; sep_unify ].

    Hint Immediate leaves_are_tree.      
    unfold BPlusTreeImplModel.rep. sep2 bpt_elab bpt_elim. instantiate_conc (as_map v2).
      sep fail auto.
      erewrite leaves_are_tree; eauto. sep fail auto. apply himp_comm_prem.
      eapply rep'_spine_to_rep'.
  Qed.

  Lemma perm_refl : forall x v0,
    eqlistA (@entry_eq key value KOT value_eq) x v0 ->
    Permutation_eq KOT value_eq x v0.
  Proof.
    induction x; inversion 1. eapply perm_nil.
    eapply perm_skip; auto.
  Qed.
  Hint Resolve perm_refl.

  Definition iterate : forall (T : Type) (t : BptMap)
    (I : T -> Model -> hprop)
    (tm : [Model])
    (fn : forall (k : key) (v:value k) (acc: T) lm,
         STsep (lm ~~ I acc lm)
               (fun a:T => lm ~~ I a (lm ++ existTS _ _ v :: nil)))
    (acc : T),
    STsep (tm ~~ rep t tm * I acc nil)
          (fun res:T => tm ~~ Exists tm' :@ Model, 
            [Permutation_eq _ value_eq tm tm'] *
            rep t tm * I res tm').
    refine (fun T t I tm fn acc =>
      {{ @orderedIterate T t I tm fn acc }}); sep fail auto.
  Qed.

End BPlusTreeImpl.
  
