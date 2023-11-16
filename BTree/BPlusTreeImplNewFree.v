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
Require Import Think ThinkList ThinkArith.

Require Import BPlusTreeImplModel.
Require Import BPlusTreeModelFacts.
Require Import BPlusTreeTactics.

Require Import OrderedTypeNM LiftOrder.
Require Import ArrayOps.

Require Eqdep.
Module EqdepTheory := EqdepFacts.EqdepTheory(Eqdep.Eq_rect_eq).

Set Implicit Arguments.

Section BPlusTreeImpl.

  Variable SIZE : nat.
  Variable pfMin : SIZE > 1.

  Variable key : Set.
  Variable value : key -> Set.

  (** Ordering on Keys **)
  Variable KOT : OrderedType key.
  Variable value_eq : forall k1 k2 : key, k1 == k2 -> value k1 = value k2.

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
  Notation "'MinK'" := (@MinK key).
  Notation "'MaxK'" := (@MaxK key).
  Notation "'BptMap'" := BptMap.
  Notation "'tH'" := (tH value).

  Notation repBranchExcept h ary st i len ls optr := 
    (@BPlusTreeImplModel.repBranch key value h (rep') ary st i ls (@BPlusTreeImplModel.repBranch_nextPtr key value h ls i optr) *
     @BPlusTreeImplModel.repBranch key value h (rep') ary (S i) (len - S i) (skipn (S i) ls) optr)%hprop.

  (** Case Analysis on trees **)
  Open Local Scope stsepi_scope.
  Open Local Scope hprop_scope.

  Definition checkLeaf : forall (h : nat) (m : [sigTS ptree]), [h]%inhabited = (m ~~~ projT1S m) -> h = 0 -> [list (sigTS value)].
  refine (fun h m pf1 pf2 =>
    match m as m' return m = m' -> _ with
      | inhabits x => fun pf => [ _ ]%inhabited
    end (refl_equal _)).
    subst; simpl in *. destruct x. generalize p. simpl in pf1. rewrite <- (pack_injective pf1). simpl. intros. destruct p0. assumption.
  Defined.

  Definition checkBranch (h h' : nat) (m : [sigTS ptree]) :
    [h]%inhabited = (m ~~~ projT1S m) -> h = S h' -> [ptree (S h')].
    refine (fun h h' m pf1 pf2 =>
      match m as m' return m = m' -> _ with
        | inhabits x => fun pf => [ _ ]%inhabited
      end (refl_equal _)).
    case_eq x. intros. rewrite pf in pf1. rewrite H in pf1. simpl in pf1. rewrite pf2 in pf1.
    generalize dependent p. rewrite <- (pack_injective pf1) in *. intros.
    apply p.
  Defined.

  Lemma fst_hint : forall A B (a:A) (b:B) x,
    x = (a, b) -> a = fst x. 
  Proof.
    destruct x; simpl in *; intros; inversion H; firstorder.
  Qed.
  Lemma snd_hint : forall A B (a:A) (b:B) x,
    x = (a, b) -> b = snd x. 
  Proof.
    destruct x; simpl in *; intros; inversion H; firstorder.
  Qed.
  Hint Resolve fst_hint snd_hint nodeType_eta.

  Definition readBranch : forall (p : ptr) (optr: [option ptr]) (h : nat) (m : [ptree (S h)]), 
    STsep (m ~~ optr ~~ rep' p optr m)
          (fun res : (array * ptr) => m ~~ optr ~~
            let ary := fst res in
            let nxtP := snd res in
            let lsM := _cont m in
            let nxtM := _next m in
            p ~~> mkNode (S h) ary (Some nxtP) * [ptrFor m = p] *
            [array_length ary = SIZE] * [length lsM <= SIZE] *
            repBranch h (rep') ary 0 SIZE lsM (firstPtr nxtM) *
            rep' nxtP optr nxtM).
    refine (fun p optr h m => 
      nde <- ! p ;
      match next nde as nxt return next nde = nxt -> _ with
        | None   => fun pf => {{ !!! }}
        | Some p => fun pf => {{ Return (content nde, p) }}
      end (refl_equal _)); try rewrite pf in *.
  Proof.
    instantiate (1 := fun v => m ~~ optr ~~ [next v = Some (ptrFor (_next m))] * [height v = S h] *
      [array_length (content v) = SIZE] * [length (_cont m) <= SIZE] * [p = ptrFor m] *
      repBranch h (rep') (content v) 0 SIZE (_cont m) (firstPtr (_next m)) *
      rep' (ptrFor (_next m)) optr (_next m)).
    solve [ sep2 bpt_elab bpt_elim; sep_unify ].
    solve [ sep_unify ].
    solve [ sep_unify ].
    sep2 bpt_elab bpt_elim; rewrite pf in *.
      inversion H1; subst; auto.
      apply nodeType_eta; eauto. subst; auto.
      sep fail auto.
    sep2 bpt_elab ltac:(fun _ => fail); rewrite pf in *; discriminate.
    solve [ sep fail idtac ].
  Qed.

  Open Local Scope stsep_scope.

  Section HideEq.

  Lemma bpt_case_Branch : forall (P : hprop) (p : ptr)
    (m : [sigTS ptree]) (op : [option ptr]) (nde : nodeType)
    (pfCorrespond : [height nde]%inhabited = (m ~~~ projT1S m))
    (h' : nat) (pf : height nde = S h') (nn : ptr),
    next nde = Some nn ->
    hprop_unpack m
     (fun m0 : sigTS ptree =>
      hprop_unpack op
        (fun op0 : option ptr =>
         [height nde = projT1S m0] * p ~~> nde *
         match m0 with
         | existTS x m1 =>
             match x as x0 return (ptree x0 -> hprop) with
             | 0 =>
                 fun m2 : ptree 0 =>
                 [height nde = 0] * [array_length (content nde) = SIZE] *
                 [length (snd m2) <= SIZE] * [next nde = op0] *
                 [p = ptrFor m2] *
                 repLeaf (content nde) 0 SIZE (snd m2)
             | S n' =>
                 fun m2 : ptree (S n') =>
                 let ls := _cont m2 in
                 let nxt := _next m2 in
                 [height nde = S n'] * [array_length (content nde) = SIZE] *
                 [length ls <= SIZE] * [p = ptrFor m2] *
                 [next nde = Some (ptrFor nxt)] *
                 repBranch n' rep' (content nde) 0 SIZE ls (firstPtr nxt) *
                 rep' (ptrFor nxt) op0 nxt
             end m1
         end * P)) ==>
   hprop_unpack m
     (fun m0 : sigTS ptree =>
      hprop_unpack (checkBranch m pfCorrespond pf)
        (fun m' : ptree (S h') =>
         hprop_unpack op
           (fun op0 : option ptr =>
            [m0 = existTS ptree (S h') m'] *
            p ~~> mkNode (S h') (content nde) (Some nn) *
            [array_length (content nde) = SIZE] * [length (_cont m') <= SIZE] *
            [p = ptrFor m'] * [nn = ptrFor (_next m')] *
            repBranch h' rep' (content nde) 0 SIZE 
              (_cont m') (firstPtr (_next m')) * rep' nn op0 (_next m') * P))).
  Proof.
    sep fail auto.
    destruct x0. simpl in H0. generalize dependent pfCorrespond. generalize dependent p0. rewrite pf in H0. rewrite <- H0.
      simpl. unfold eq_rec. unfold eq_rect. intros.
      generalize (pack_injective
        (eq_ind (height nde)
          (fun h : nat => [h]%inhabited = [S h']%inhabited)
          pfCorrespond (S h') pf)). intro.
      rewrite (EqdepTheory.UIP_refl _ _ e). 
      canceler. sep fail auto. rewrite H in H0. inversion H0. sep fail auto.
  Qed.

  Definition bpt_case : forall (T : Type) (Q : T -> hprop) (P:hprop)
    (p:ptr) (m : [sigTS ptree]) (op : [option ptr]),
    (forall (ary : array) (nxt : option ptr) (ls : [list (sigTS value)]),
     STsep (ls ~~ op ~~ m ~~ 
              [m = existTS ptree 0 (p, ls)] * 
              p ~~> mkNode 0 ary nxt * [array_length ary = SIZE] * [length ls <= SIZE] *
              [p = ptrFor (projT2S m)] *
              repLeaf ary 0 SIZE ls * [nxt = op] * P)
           (fun res:T => Q res)) ->
    (forall (h' : nat) (ary : array) (nxt : ptr) (m' : [ptree (S h')]),
     STsep (m ~~ m' ~~ op ~~ 
             [m = existTS ptree (S h') m'] *
             p ~~> mkNode (S h') ary (Some nxt) * [array_length ary = SIZE] * [length (_cont m') <= SIZE] * 
             [p = ptrFor m'] * [nxt = ptrFor (_next m')] *
             repBranch h' (rep') ary 0 SIZE (_cont m') (firstPtr (_next m')) *
             rep' nxt op (_next m') * P)
           (fun res:T => Q res)) ->
    STsep (m ~~ op ~~ [p = ptrFor (projT2S m)] * rep' p op (projT2S m) * P)
          (fun res:T => Q res).
  refine (fun T Q P p m op CLeaf CBranch => 
    nde <- p !! (fun v:nodeType => [[height v]%inhabited = (m ~~~ projT1S m)] *
      (m ~~ op ~~ [p = ptrFor (projT2S m)] *
      match m with 
        | existTS 0 ls =>
          [height v = 0] * [array_length (content v) = SIZE] * [length (snd ls) <= SIZE] *
          [next v = op] * [p = ptrFor ls] *
          repLeaf (content v) 0 SIZE (snd ls)

        | existTS (S n') m =>
          let ls  := _cont m in
          let nxt := _next m in
          [height v = S n'] * [array_length (content v) = SIZE] *
          [length ls <= SIZE] * [p = ptrFor m] * [next v = Some (ptrFor nxt)] *
          repBranch n' (rep') (content v) 0 SIZE ls (firstPtr nxt) * rep' (ptrFor nxt) op nxt
      end * P)) ;
    pfCorrespond <- shift' ([height nde]%inhabited = (m ~~~ projT1S m)) <@> _ ;
    match height nde as h 
      return height nde = h ->
        STsep (m ~~ op ~~ [height nde = projT1S m] * p ~~> nde *
               match m with 
                 | existTS 0 ls => 
                   [height nde = 0] * [array_length (content nde) = SIZE] * [length (snd ls) <= SIZE] *
                   [next nde = op] * [p = ptrFor ls] *
                   repLeaf (content nde) 0 SIZE (snd ls)
                   
                 | existTS (S n') m =>
                   let ls  := _cont m in
                   let nxt := _next m in
                   [height nde = S n'] * [array_length (content nde) = SIZE] *
                   [length ls <= SIZE] * [p = ptrFor m] * [next nde = Some (ptrFor nxt)] *
                   repBranch n' (rep') (content nde) 0 SIZE ls (firstPtr nxt) * rep' (ptrFor nxt) op nxt
               end * P)
        (fun res:T => Q res)
      with
      | 0 => fun pf =>
        {{ CLeaf (content nde) (next nde) (@checkLeaf (height nde) m pfCorrespond pf) }}
      | S h' => fun pf =>
        (** Can probably clean this up with readBranch **)
        match next nde as nn return next nde = nn -> _ with
          | None => fun _ => {{ !!! }}
          | Some nn => fun pfNxt =>
            {{ CBranch h' (content nde) nn (@checkBranch (height nde) h' m pfCorrespond pf) }}
        end (refl_equal _)
    end (refl_equal _)); try clear CLeaf CBranch.
  Proof.
    solve [ inhabiter; destruct x0; destruct x0; sep fail auto ].
    solve [ sep_unify ].
    solve [ sep2 fail bpt_elim'; sep_unify ].
    solve [ sep2 fail bpt_elim'; sep fail idtac ].
  
    (** Leaf Case **)
    sep fail auto.
      destruct x0. destruct x0.
      unfold eq_rec_r. unfold eq_rec. unfold eq_rect.
      generalize (sym_eq (refl_equal [existTS ptree 0 p0]%inhabited)). intro e. rewrite (EqdepTheory.UIP_refl _ _ e). clear e.
      generalize (sym_eq pf). intro e. generalize e. generalize dependent H. generalize dependent pf. generalize dependent pfCorrespond.
       rewrite <- e. clear e. intros. rewrite (EqdepTheory.UIP_refl _ _ e).
       Require ThinkEq.
       ThinkEq.eqdep. 
       sep fail auto.
      sep fail auto. congruence.
    solve [ sep fail auto ].

    (** Branch Case **)
    solve [ eapply bpt_case_Branch; eauto ].
    solve [ sep fail auto ].
    sep fail auto. destruct x0.
      destruct x0. simpl in *. congruence.
      simpl in *. sep fail auto. congruence.
    sep fail auto.
  Qed.
  End HideEq.

  (** Implementation **)

  (** NEW **)
  (*********)
  Definition emptyTree (p:ptr) : ptree 0 := (p, nil).
  Definition emptyTreeInv : forall p:ptr, inv 0 (emptyTree p) MinK MaxK.
    simpl; auto; intros. unfold BPlusTreeImplModel.MinK, BPlusTreeImplModel.MaxK. unfold BPlusTreeImplModel.KLsorted. simpl. left.
    unfold ordLt. destruct KOT. simpl; auto.
  Qed.
  Hint Resolve emptyTreeInv.

  Lemma sorted_nil : forall V a, KLsorted V a (@nil (sigTS V)) a.
  Proof. 
    unfold BPlusTreeImplModel.KLsorted. simpl. right. apply LO_eq_refl.
  Qed.
  Lemma sorted_nil_lt : forall V a b,
    a << b -> KLsorted V a (@nil (sigTS V)) b.
  Proof.
    unfold BPlusTreeImplModel.KLsorted. simpl. left. auto.
  Qed.

  Lemma min_lt_max : MinK << MaxK.
  Proof. 
    unfold ordLt. destruct KOT. simpl; auto.
  Qed.
    
  Hint Immediate sorted_nil.
  Hint Resolve sorted_nil_lt min_lt_max.

  Definition new :
    STsep (__)
          (fun t : BptMap => rep t nil).
    refine (ary <- new_constant_array SIZE (@None (sigTS value)) ;
            res <- New (mkNode 0 ary None) <@> [array_length ary = SIZE] * _ ;
            ind <- New (res, existTS (fun h:nat => [ptree h]%type) 0 [emptyTree res]%inhabited) <@> _ ;
            {{ Return ind <@> _ }}).
  Proof.
    solve [ sep fail idtac ].
    solve [ sep fail idtac ].
    solve [ sep2 fail ltac:(fun _ => fail); sep fail idtac ].
    solve [ sep fail idtac ].
    solve [ sep fail idtac ].
    solve [ sep fail idtac ].
    solve [ sep fail auto ].
    unfold BPlusTreeImplModel.rep in *. sep fail auto; auto.
    unfold BPlusTreeImplModel.repLeaf. apply iter_sep_inj. intros; norm arith; norm list; do 2 sep fail auto.
  Qed.

  (** FREE **)
  (**********)

  Lemma repLeaf_iter : forall len (T:Set) ary (ls:list T) s,
    length ls <= len ->
    repLeaf ary s len ls ==> {@hprop_unpack (array_plus ary i) (fun p0 : ptr => p0 ~~>?) | i <- s + len}.
  Proof.
    intros. eapply iter_shift. intros; norm arith. unfold ptsto_any; sep fail auto.
  Qed.

  Definition free_leaf : forall (p : ptr) (ary : array)
    (nxt : option ptr) (ls : [list (sigTS value)]),
    STsep (ls ~~ p ~~> mkNode 0 ary nxt * [array_length ary = SIZE] * [length ls <= SIZE] *
             repLeaf ary 0 SIZE ls)
          (fun res:unit => __).
    refine (fun p ary nxt ls =>
      free_array ary <@> (p ~~> mkNode 0 ary nxt) ;;
      Free p <@> _ ;;
      {{ Return tt }});
    sep fail auto; eapply repLeaf_iter; eauto.
  Qed.

  Lemma iter_fb : forall n (x1 x0 : ptr) s ary (T:Set) (v:T),
    array_plus ary s = [x1]%inhabited ->
    array_plus ary (s + n) = [x0]%inhabited ->
    {@hprop_unpack (array_plus ary i) (fun p4 : ptr => p4 ~~>?) | i <- s + n} * x0 ~~> v ==>
    {@hprop_unpack (array_plus ary i) (fun p0 : ptr => p0 ~~>?) | i <- (S s) + n} * x1 ~~>?.
  Proof.
    clear. induction n.
      simpl; intros. norm arith in *. rewrite H in H0. rewrite (pack_injective H0). unfold ptsto_any. sep fail auto.
      simpl; intros. rewrite H. sep fail auto. eapply himp_trans. eapply IHn. eassumption. assert (s + S n = S s + n). omega. rewrite H1 in *. eassumption.
      sep fail auto.
  Qed.

  Lemma pred_SIZE_lt_SIZE : pred SIZE < SIZE.
    omega.
  Qed.
  Lemma lt_S : forall a b c, a = S c -> a < b -> c < b.
    intros; omega.
  Qed.

  Lemma aaa : forall h n (x0 : ptree (S h)) P Q P',
    n < length (_cont x0) ->
    (forall v, nth_error (skipn n (_cont x0)) 0 = Some v ->
      [0 < length (skipn n (_cont x0))] *
      rep' (ptrFor (projT2S v))
      (Some (repBranch_nextPtr (skipn n (_cont x0)) 0 (firstPtr (_next x0))))
      (projT2S v) * P ==> Q)
    -> 
    match nth_error (skipn n (_cont x0)) 0 with
      | Some v =>
        [0 < length (skipn n (_cont x0))] *
        rep' (ptrFor (projT2S v))
        (Some (repBranch_nextPtr (skipn n (_cont x0)) 0 (firstPtr (_next x0)))) (projT2S v)
      | None => P'
    end * P ==> Q.
  Proof. clear. intros.
    case_eq (nth_error (skipn n (_cont x0)) 0); intros.
    apply H0 in H1. destruct s. auto. elimtype False.
    clear H0. apply nth_error_None_length in H1. 
    case_eq (skipn n (_cont x0)); intros. Focus 2. rewrite H0 in *. simpl in *. omega.
    apply len_skipn_nil in H0. omega.
  Qed.
  Lemma bbb : forall T n (x0 : list T) v (l : n < length x0),
    nth_error (skipn n x0) 0 = Some v ->
    v = nthDep x0 l.
  Proof. clear.
    intros. erewrite nthDep_nth_error. eauto.
    erewrite nth_error_skipn in H. norm arith in *. auto.
  Qed.
  Hint Resolve bbb.
  Lemma ccc : forall h (x0 : ptree (S h)) n (l : n < length (_cont x0)) v,
    nth_error (skipn n (_cont x0)) 0 = Some v ->
    match nth_error (skipn n (_cont x0)) 0 with
      | Some v => Some (projT1S v, ptrFor (projT2S v))
      | None => None
    end =
    Some (projT1S (nthDep (_cont x0) l), ptrFor (projT2S (nthDep (_cont x0) l))).
  Proof. clear.
    intros. rewrite H.
    cut (nthDep (_cont x0) l = v); intros. rewrite H0. destruct v. auto.
    eapply nthDep_nth_error. erewrite nth_error_skipn in H. norm arith in *. auto.
  Qed.
  Hint Resolve ccc.

  Lemma ddd : forall h (x0 : ptree (S h)) n,
    match nth_error (_cont x0) n with
      | Some v =>
        [0 < length (skipn n (_cont x0))] *
        rep' (ptrFor (projT2S v))
        (Some (repBranch_nextPtr (skipn n (_cont x0)) 0 (firstPtr (_next x0)))) (projT2S v)
      | None => [length (skipn n (_cont x0)) <= 0]
    end ==>
    match le_lt_dec (length (_cont x0)) n with
      | left _ =>
        [length (_cont x0) <= n] *
        [match nth_error (_cont x0) n with
           | Some v => Some (projT1S v, ptrFor (projT2S v))
           | None => None
         end = None]
      | right pf' =>
        [match nth_error (_cont x0) n with
           | Some v => Some (projT1S v, ptrFor (projT2S v))
           | None => None
         end =
           Some (projT1S (nthDep (_cont x0) pf'),
             ptrFor (projT2S (nthDep (_cont x0) pf')))] *
        rep' (ptrFor (projT2S (nthDep (_cont x0) pf')))
        (Some
          (repBranch_nextPtr (skipn n (_cont x0)) 0 (firstPtr (_next x0))))
        (projT2S (nthDep (_cont x0) pf'))
    end.
  Proof.
    intros.
    destruct (le_lt_dec (length (_cont x0)) n). 
    solve [ sep2 fail bpt_elim; norm list; sep fail idtac ].
    norm arith. generalize (nth_error_len_lt _ l); intros. destruct H. rewrite H. destruct x.
    erewrite nthDep_nth_error; try eassumption. fold ptree in *. simpl. 
    solve [ sep2 fail bpt_elim; sep fail auto ].
  Qed.
  Hint Immediate ddd.

  Lemma repBranch_nextPtr_skipn : forall h n a (LS : list (sigTS (fun _:key => ptree h))) N,
    repBranch_nextPtr (skipn n LS) a N = repBranch_nextPtr LS (a + n) N.
  Proof. clear. unfold BPlusTreeImplModel.repBranch_nextPtr.
    intros; norm list. Change (n + S a) into (S (a + n)) using omega. reflexivity.
  Qed.
  Hint Resolve repBranch_nextPtr_skipn.


  Definition free_branch : forall (p : ptr) (h : nat) (ary : array) (nxt : ptr) (m : [ptree (S h)]) (op : [option ptr]),
    (forall (p : ptr) (m : [sigTS ptree]) (op: [option ptr]),
       STsep (m ~~ op ~~ rep' p op (projT2S m))
             (fun _:unit => __)) ->
     STsep (m ~~ op ~~
              p ~~> mkNode (S h) ary (Some nxt) * [array_length ary = SIZE] * [length ((_cont m)) <= SIZE] *
              [nxt = ptrFor (_next m)] *
              repBranch h (rep') ary 0 SIZE ((_cont m)) (firstPtr (_next m)) * rep' nxt op (_next m))
           (fun _:unit => __).
     refine (fun p h ary nxt m op rec =>
       Free p ;;
       rec nxt (m ~~~ existTS ptree h (_next m)) op <@> _ ;;
       {{ Fix2 (fun (n:nat) (pf:n <= SIZE) => m ~~ op ~~
                      let lsM := _cont m in
                      let nxtM := _next m in 
                      [length lsM <= SIZE] * [array_length ary = SIZE] *
                      {@ p0 :~~ array_plus ary i in p0 ~~>? | i <- 0 + n} *
                      repBranch h (rep') ary n (SIZE - n) (skipn n lsM) (firstPtr nxtM))
               (fun _ _ (_:unit)    => __)
               (fun self n pf =>
                 match le_lt_dec SIZE n with
                   | left _  => 
                     {{ free_array ary }}
                   | right pfSn =>
                     kv <- sub_array ary n 
                     (fun cp:option (key * ptr) => m ~~ op ~~ 
                       let lsM := _cont m in
                       let nxtM := _next m in
                       {@ p0 :~~ array_plus ary i in p0 ~~>? | i <- 0 + n} *
                       [array_length ary = SIZE] * [length lsM <= SIZE] *
                       repBranch h (rep') ary (S n) (SIZE - S n) (skipn (S n) lsM) (firstPtr nxtM) *
                       match le_lt_dec (length lsM) n with
                         | right pf' => 
                           let m'  := @nthDep _ lsM n pf' in
                           let p'' := ptrFor (projT2S (@nthDep _ lsM n pf')) in
                           [cp = Some (projT1S m', p'')] * 
                           rep' p'' (Some (repBranch_nextPtr (skipn n lsM) 0 (firstPtr nxtM))) (projT2S m')
                         | left _ =>
                           [length lsM <= n] * [cp = None]
                       end) ;
                     match kv as kv' return kv = kv' -> _ with
                       | None => fun pf' => {{ self (S n) (lt_S_le pfSn) }}
                       | Some (k,p) => fun pf' =>
                         zz <- rec p (m ~~~ match nth_error (_cont m) n with
                                              | None => existTS ptree (S h) m (** Junk **) 
                                              | Some v => existTS ptree h (projT2S v)
                                            end) (m ~~~ Some (repBranch_nextPtr (_cont m) n (firstPtr (_next m)))) <@> 
                                     (x1 :~~ array_plus ary n in op ~~ m ~~ 
                                       repBranch h (rep') ary (S n) (SIZE - S n) (skipn (S n) (_cont m)) (firstPtr (_next m)) *
                                       {@hprop_unpack (array_plus ary i) (fun p2 : ptr => p2 ~~>?) | i <- 0 + n} *
                                       [array_length ary = SIZE] * [length (_cont m) <= SIZE] *
                                       x1 ~~> Some (k, p)) ;
                         {{ self (S n) (lt_S_le pfSn) }}
                     end (refl_equal _)
                 end) 0 (O_le SIZE) }}); clear rec; try clear self.
   Proof.
     solve [ sep2 fail bpt_elim; sep fail idtac ].
     solve [ sep fail idtac ].
     solve [ sep2 fail bpt_elim; rewrite <- H1; simpl; sep2 fail bpt_elim; sep_unify ].
     solve [ sep_unify ].
     solve [ sep2 fail bpt_elim; sep fail idtac ].
     solve [ sep fail idtac ].

     sep2 fail bpt_elim. eauto with bpt_sep. rewrite H5. norm arith; norm list; norm arith. sep2 fail bpt_elim. sep fail idtac.
     solve [ sep_unify ].

     sep2 fail bpt_elim. destruct (le_lt_dec (length (_cont x0)) n); [ intro_pure; congruence | ].
     rewrite pf' in *.  intro_pure. inversion H6. rewrite <- H3. generalize (nth_error_ex _ l); intros.
     destruct H7. rewrite H7 in *. apply (nthDep_nth_error _ l) in H7.
     rewrite H7 in *. sep2 fail bpt_elim. rewrite <- H2. simpl.
     repeat search_prem ltac:(apply himp_inj_prem; intros XX; clear XX). apply himp_rep'_eq; auto.
       f_equal. apply repBranch_nextPtr_eq3_l; auto.
     solve [ sep_unify ].

     sep2 fail bpt_elim. unpack_conc.
     solve [ sep2 fail bpt_elim; sep fail idtac ].
     solve [ sep fail idtac ].
     
     sep2 fail bpt_elim.
     destruct (le_lt_dec (length (_cont x0)) n). sep fail auto. intro_pure. congruence.
     solve [ sep fail idtac ].
     sep2 fail bpt_elim. eauto with bpt_sep.
     search_conc ltac:(apply himp_iter_sep_0_conc; [ solve [ trivial ] | ]). sep fail idtac.
     solve [ sep fail idtac ].
  Qed.

  Definition free_rec : forall (p : ptr) (m : [sigTS ptree]) (op : [option ptr]),
    STsep (m ~~ op ~~ rep' p op (projT2S m))
          (fun r:unit => __).
    refine
      (Fix3 (fun p m op => m ~~ op ~~ rep' p op (projT2S m))
            (fun _ _ _ (r:unit) => __)
            (fun self p m op =>
              {{ @bpt_case (unit) (fun _ => __) (__) p m op
                  (fun a n l => {{ free_leaf p a n l }})
                  (fun h a n m => {{ @free_branch p h a n m op self }}) }})); try clear self;
    solve [ sep2 bpt_elab bpt_elim; sep fail idtac ].
  Qed.

  Open Local Scope stsep_scope.

  Definition free (t : BptMap) (m : [Model]) :
    STsep (m ~~ rep t m)
          (fun _:unit => __).
    refine (fun t m =>
      rec <- t !! (rep_frame _ _ value_eq t m) ;
      Free t ;;
      {{ @free_rec (fst rec) (inhabit_unpack (projT2S (snd rec)) (fun m => existTS (ptree) _ m)) [None] }});
    (try unfold BPlusTreeImplModel.rep_frame; try unfold BPlusTreeImplModel.rep); solve [ sep_unify | sep2 fail bpt_elim; sep_unify | sep fail auto ].
  Qed.

End BPlusTreeImpl.
