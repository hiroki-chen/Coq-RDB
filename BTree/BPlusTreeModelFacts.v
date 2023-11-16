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
Require Import BPlusTreeImplModel.

Hint Resolve SIZE_S.
Hint Resolve nodeType_eta.
Hint Resolve sorted_nil.
Hint Resolve sorted_nil_lt.

Require Import Ynot.
Require Import Think ThinkList ThinkArith.
Require Import Array.
Require Import OrderedTypeNM.

Open Local Scope hprop_scope.
Open Local Scope stsepi_scope.

Section BPlusTreeModelFacts.

  Variable SIZE : nat.
  Variable pfMin : SIZE > 1.
  Definition SIZE_S := SIZE_S pfMin.

  Variable key : Set.
  Variable value : key -> Set.

  (** Ordering on Keys **)
  Variable KOT : OrderedType key.

  Notation "'ptree' n" := (ptree value n) (at level 50).
  Notation "'rep''"    := (rep' SIZE value) (at level 50).
  Notation "'repBranch'" := (repBranch value) (at level 50).
  Notation "'repBranch_nextPtr'" := (repBranch_nextPtr value).
  Notation "'key_between'" := (key_between KOT) (at level 50).
  Notation "'KLsorted'" := (KLsorted KOT) (at level 50).
  Notation "'contextual'" := (contextual value KOT) (at level 50).
  Notation "'lastKey'" := (lastKey).
  Notation "'inv'" := (inv value KOT).
  Notation "'Model'" := (Model value).
  Notation "'as_map'" := (as_map value).
  Notation "'repLeaf'" := repLeaf.
  Notation "'lastPtr'" := (lastPtr value).
  Notation "'firstPtr'" := (firstPtr value).
  Notation "'ptrFor'" := (ptrFor value).
  Notation "'rep'" := (@rep SIZE key value KOT).
  Notation "'BranchCell' h" := (sigTS (fun _:key => ptree h)) (at level 50).
  Notation "'MinK'" := (@MinK key).
  Notation "'MaxK'" := (@MaxK key).
  Notation "'BptMap'" := (BptMap value).
  Notation "'tH'" := (tH value).

Require Import Compare_dec Peano_dec.

(** Theorems are given as hints to auto **)

Opaque nth_error skipn firstn.

(** _cont and _next **)
Lemma _cont_red : forall h (a : ptr) (b: list (BranchCell h)) (c : ptree h), 
  _cont (a,(b,c)) = b.
Proof.
  unfold BPlusTreeImplModel._cont. auto.
Qed.

Lemma _next_red : forall h (a : ptr) (b: list (BranchCell h)) (c : ptree h), 
  _next (a,(b,c)) = c.
Proof.
  unfold BPlusTreeImplModel._next. auto.
Qed.

Lemma ptrFor_red0 : forall (a : ptr) (b: list (sigTS value)),
  @BPlusTreeImplModel.ptrFor key value 0 (a, b) = a.
Proof.
  unfold BPlusTreeImplModel.ptrFor. auto.
Qed.

Lemma ptrFor_redS : forall h (a : ptr) (b: list (BranchCell h)) (c : ptree h),
  @BPlusTreeImplModel.ptrFor key value (S h) (a, (b,c)) = a.
Proof.
  unfold BPlusTreeImplModel.ptrFor. auto.
Qed.

(** repBranch_nextPtr **)
Theorem repBranch_nextPtr_ignore_default : forall h i (LS : list (BranchCell h)) a b,
  S i < length LS ->
  repBranch_nextPtr LS i a = repBranch_nextPtr LS i b.
Proof.
  unfold BPlusTreeImplModel.repBranch_nextPtr.
  intros. apply nth_error_len_lt in H. destruct H. rewrite H. auto.
Qed.
Hint Resolve repBranch_nextPtr_ignore_default.

Theorem repBranch_nextPtr_eq2 : forall h i (X : BranchCell h) (XS LS : list (BranchCell h)) PTR,
  i < length LS ->
  repBranch_nextPtr LS i (firstPtr (projT2S X)) =
  repBranch_nextPtr (LS ++ X :: XS) i PTR.
Proof.
  intros; unfold BPlusTreeImplModel.repBranch_nextPtr.
  destruct (eq_nat_dec (S i) (length LS)).
    norm list. rewrite <- e; norm arith. norm list. auto.
    rewrite nth_error_app_first; auto.
    cut (S i < length LS); try omega; intros.
    apply nth_error_len_lt in H0. destruct H0; rewrite H0; auto.
Qed.
Hint Resolve repBranch_nextPtr_eq2.

Theorem repBranch_nextPtr_eq3_l : forall h i s (ls : list (BranchCell h)) x0 X,
  X = i + s ->
  repBranch_nextPtr (skipn i ls) s x0 = repBranch_nextPtr ls X x0.
Proof. clear.
  intros; unfold BPlusTreeImplModel.repBranch_nextPtr. subst.
  norm list; norm arith; auto.
  Change (i + S s) into (S (i + s)) using omega. auto.
Qed.
Hint Resolve repBranch_nextPtr_eq3_l.
Theorem repBranch_nextPtr_eq3_r : forall h i s (ls : list (BranchCell h)) x0 X,
  X = i + s ->
  repBranch_nextPtr ls X x0 = repBranch_nextPtr (skipn i ls) s x0.
Proof.
  intros; symmetry; auto. (** auto should really get this it seems **)
Qed.
Hint Resolve repBranch_nextPtr_eq3_r.

Theorem repBranch_nextPtr_choose_default : forall h i (LS : list (BranchCell h)) x0,
  length LS <= S i ->
  repBranch_nextPtr LS i x0 = x0.
Proof. clear. unfold BPlusTreeImplModel.repBranch_nextPtr.
  intros; norm list; auto.
Qed.
Hint Resolve repBranch_nextPtr_choose_default.

Theorem repBranch_nextPtr_eq4 : forall h (ls : list (BranchCell h)) A B C D p,
  A + B = C + D ->
  repBranch_nextPtr (skipn A ls) B p = repBranch_nextPtr (skipn C ls) D p.
Proof.
  intros; unfold BPlusTreeImplModel.repBranch_nextPtr.
  norm list.
  Change (A + S B) into (C + S D) using omega. auto.
Qed.
Hint Resolve repBranch_nextPtr_eq4.

Theorem repBranch_nextPtr_eq5 : forall h (a0 : list (BranchCell h)) i optr idx,
  i <= idx ->
  length a0 <= idx ->
  repBranch_nextPtr a0 i optr =
  repBranch_nextPtr a0 i (repBranch_nextPtr a0 idx optr).
Proof.
  intros; unfold BPlusTreeImplModel.repBranch_nextPtr.
  case_eq (nth_error a0 (S i)); sep fail auto.
  norm list. auto.
Qed.
Hint Resolve repBranch_nextPtr_eq5.

Theorem repBranch_nextPtr_firstn_rw : forall h (v0 : BranchCell h) i i0 (LS : list (BranchCell h)),
  i0 < i ->
  nth_error LS i = Some v0 ->
  repBranch_nextPtr (firstn (S i) LS) i0 (firstPtr (projT2S v0)) =
  repBranch_nextPtr (firstn i LS) i0 (firstPtr (projT2S v0)).
Proof.
  intros; subst; unfold BPlusTreeImplModel.repBranch_nextPtr.
    destruct (le_lt_dec (length LS) i). 
    norm list; auto.
    destruct (le_lt_dec i (S i0)).
    subst; norm list; auto. assert (i = S i0); try omega.
    subst; rewrite H0; norm list; auto.
    norm list; auto.
Qed.
Hint Resolve repBranch_nextPtr_firstn_rw.

Theorem repBranch_nextPtr_elim_firstn : forall h (x0 : list (BranchCell h)) i n OPTR,
  S i < n ->
  repBranch_nextPtr (firstn n x0) i OPTR = repBranch_nextPtr x0 i OPTR.
Proof.
  intros; unfold BPlusTreeImplModel.repBranch_nextPtr; norm list; auto.
Qed.

Lemma repBranch_nextPtr_XXX : forall h (ls : list (BranchCell h)) len len' i optr optr',
  len < len' ->
  len < length ls ->
  i < len ->
  repBranch_nextPtr (firstn len' ls) i optr =
  repBranch_nextPtr (firstn len ls) i (repBranch_nextPtr ls (len - 1) optr').
Proof.
  unfold BPlusTreeImplModel.repBranch_nextPtr.
  intros. norm arith.
  destruct (eq_nat_dec len (S i)); norm list.
  symmetry. norm list. subst.
  apply nth_error_ex in H0. destruct H0. rewrite H0. auto.
  subst. eauto with norm_list.
  
  cut (S i < length ls); try omega; intros; norm list.
  apply nth_error_ex in H2; destruct H2; rewrite H2. auto.
Qed.
Hint Resolve repBranch_nextPtr_XXX.

(** array **)
Theorem himp_iter_sep_eq : forall F a b a' b',
  a = a' -> b = b' ->
  {@ F i | i <- a + b} ==> {@ F i | i <- a' + b'}.
Proof. 
  intros; subst; sep fail auto.
Qed.
Hint Resolve himp_iter_sep_eq.

(** rep' **)
Theorem himp_rep'_eq : forall h b c (d : ptree h) b' c' d',
  b = b' -> d = d' -> c = c' -> 
  rep' b c d ==> rep' b' c' d'.
Proof. sep fail auto. Qed.
Hint Resolve himp_rep'_eq.

Lemma rep'_expand : forall h p p' (lsM : list (BranchCell h)) nxtM optr P Q,
  ([p = p'] * Exists ary :@ array,
   p ~~> mkNode (S h) ary (Some (ptrFor nxtM)) * 
   [array_length ary = SIZE] * [length lsM <= SIZE] *
   repBranch h (rep') ary 0 SIZE lsM (firstPtr nxtM) *
   rep' (ptrFor nxtM) optr nxtM)%hprop * P ==> Q ->
  @BPlusTreeImplModel.rep' SIZE key value (S h) p optr (p', (lsM, nxtM)) * P ==> Q.
Proof.
  intros; eapply himp_trans; [ | eassumption ]; clear H.
  sep fail idtac.
Qed.

Lemma rep'_combine : forall h p p' (lsM : list (BranchCell h)) nxtM optr P Q,
  P ==> ([p = p'] * Exists ary :@ array,
         p ~~> mkNode (S h) ary (Some (ptrFor nxtM)) * 
         [array_length ary = SIZE] * [length lsM <= SIZE] *
         repBranch h (rep') ary 0 SIZE lsM (firstPtr nxtM) *
         rep' (ptrFor nxtM) optr nxtM)%hprop * Q ->
  P ==> @BPlusTreeImplModel.rep' SIZE key value (S h) p optr (p', (lsM, nxtM)) * Q.
Proof.
  intros. eapply himp_trans; [ eassumption | ]; clear H.
  sep fail idtac.
Qed.

Lemma rep'_combine2 : forall h p (pt : ptree (S h)) optr P Q,
  P ==> ([p = ptrFor pt] * Exists ary :@ array,
         p ~~> mkNode (S h) ary (Some (ptrFor (_next pt))) * 
         [array_length ary = SIZE] * [length (_cont pt) <= SIZE] *
         repBranch h (rep') ary 0 SIZE (_cont pt) (firstPtr (_next pt)) *
         rep' (ptrFor (_next pt)) optr (_next pt))%hprop * Q ->
  P ==> @BPlusTreeImplModel.rep' SIZE key value (S h) p optr pt * Q.
Proof.
  intros. eapply himp_trans; [ eassumption | ]; clear H. sep fail idtac.
Qed.

(** repLeaf **)
Theorem himp_repLeaf_eq : forall h a b c d a' b' c' d',
  a = a' -> b = b' -> c = c' -> d = d' ->
  @BPlusTreeImplModel.repLeaf h a b c d ==> @BPlusTreeImplModel.repLeaf h a' b' c' d'.
Proof. sep fail auto. Qed.
Hint Resolve himp_repLeaf_eq.

(** repBranch **)
Theorem himp_repBranch_eq : forall h a b c d e a' b' c' d' e',
  a = a' -> b = b' -> c = c' -> d = d' -> e = e' ->
  repBranch h (rep') a b c d e ==> repBranch h (rep') a' b' c' d' e'.
Proof. sep fail auto. Qed.
Hint Resolve himp_repBranch_eq.

Theorem himp_repBranch_0_prem : forall a b c d e f g P Q,
  e = 0 ->
  P ==> Q ->
  repBranch a b c d e f g * P ==> Q.
Proof.
  intros; subst; unfold BPlusTreeImplModel.repBranch; sep fail auto.
Qed.

Theorem himp_repBranch_0_conc : forall a b c d e f g P Q,
  e = 0 ->
  P ==> Q ->
  P ==> repBranch a b c d e f g * Q.
Proof.
  intros; subst; unfold BPlusTreeImplModel.repBranch; sep fail auto.
Qed.

Theorem repBranch_ignore_end : forall h ARY i s LS a b,
  i < length LS
  -> repBranch h (rep') ARY s i LS a ==> repBranch h (rep') ARY s i LS b.
Proof. clear. Opaque nth_error.
  intros. unfold BPlusTreeImplModel.repBranch.
  apply iter_imp; intros. norm arith in *. sep fail auto.
  cut (i0 < length LS); try omega; intros.
  apply nth_error_len_lt in H3. destruct H3. rewrite H3. sep fail auto.
Qed.
Hint Resolve repBranch_ignore_end.

Theorem repBranch_prefix : forall h ary pos LS (X : sigTS (fun _:key => @BPlusTreeImplModel.ptree key value h)) XS PTR n,
  pos <= length LS ->
  repBranch h (rep') ary n pos LS (firstPtr (projT2S X)) ==> repBranch h (rep') ary n pos (LS ++ X :: XS) PTR.
Proof.
  intros; unfold BPlusTreeImplModel.repBranch.
  apply iter_imp; intros. norm arith in *. sep fail auto. norm list.
  cut (i < length LS); try omega; intros.
  apply nth_error_len_lt in H3; destruct H3. rewrite H3. sep fail auto.
Qed.
Hint Resolve repBranch_prefix.

Theorem repBranch_nil_ignore : forall a c e d f g,
  repBranch a (rep') c d e nil f ==> repBranch a (rep') c d e nil g.
Proof.
  intros; unfold BPlusTreeImplModel.repBranch.
  apply iter_imp. sep fail auto. norm list. sep fail auto.
Qed.
Hint Resolve repBranch_nil_ignore.

Theorem repBranch_ending : forall h ary idx ST a0 optr,
  length a0 <= idx ->
  (repBranch) h (rep') ary ST idx a0 optr ==>
  (repBranch) h (rep') ary ST idx a0 (repBranch_nextPtr a0 idx optr).
Proof. clear.
  intros; unfold BPlusTreeImplModel.repBranch.
  apply iter_imp; intros. sep fail auto.
  destruct (nth_error a0 i); sep fail auto.
Qed.
Hint Resolve repBranch_ending.

Theorem repBranch_nil' : forall h p ary LEN ST LEN' ST',
  LEN = LEN' -> ST = ST' ->      
  {@ p :~~ array_plus ary i in p ~~> @None (key * ptr) | i <- ST + LEN }
  ==>
  repBranch h (rep') ary ST' LEN' nil p.
Proof.
  intros; subst; unfold BPlusTreeImplModel.repBranch; apply iter_shift; intros.
  norm arith; norm list; sep fail auto.
Qed.

Theorem repBranch_nil : forall h p ary LEN ST LEN' ST',
  LEN = LEN' -> ST = ST' ->      
  repBranch h (rep') ary ST LEN nil p
  ==> 
  {@ p :~~ array_plus ary i in p ~~> @None (key * ptr) | i <- ST' + LEN' }.
Proof.
  intros; subst; unfold BPlusTreeImplModel.repBranch; apply iter_shift; intros.
  norm arith; norm list; sep fail auto.
Qed.
Hint Resolve repBranch_nil repBranch_nil'.


Lemma repBranch_firstn_prefix : forall h ary i (LS LS' : list (BranchCell h)) v0 idx XXX YYY,
  LS' = firstn (S i) LS ->
  nth_error LS i = Some v0 ->
  XXX = firstPtr (projT2S v0) ->
  YYY = firstPtr (projT2S v0) ->
  repBranch h (rep') ary idx i (firstn i LS) XXX 
  ==>
  repBranch h (rep') ary idx i LS' YYY.
Proof. clear. 
  intros; subst; unfold BPlusTreeImplModel.repBranch; apply iter_imp; intros.
  sep fail auto. norm list. destruct (nth_error LS i0); sep fail auto.
  apply himp_rep'_eq; auto. f_equal. symmetry; apply repBranch_nextPtr_firstn_rw; auto. (** I thought Coq did symmetry **)
Qed.
Hint Resolve repBranch_firstn_prefix.

Theorem repBranch_firstn_extra : forall h ary LEN x0 st X SLEN PLEN Z,
  SLEN = S LEN ->
  PLEN = pred LEN ->
  LEN > 0 ->
  LEN < length x0 ->
  repBranch h (rep') ary st LEN (firstn SLEN x0) Z ==>
  repBranch h (rep') ary st LEN (firstn LEN x0) (repBranch_nextPtr x0 (PLEN) X).
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
    subst. apply nth_error_ex in H2. destruct H2. rewrite H2. norm list. auto.
    cut (S i < LEN); try omega; intros. norm list.
    case_eq (nth_error x0 (S i)); intros; auto.
      elimtype False. assert (length x0 <= S i); eauto with norm_list_length.
Qed.
Hint Resolve repBranch_firstn_extra.

Lemma repBranch_reduce : forall h ary len len' st (ls : list (BranchCell h)) optr optr' lenm1,
  len < len' ->
  lenm1 = len - 1 ->
  len < length ls ->
  repBranch h (rep') ary st len (firstn len' ls) optr ==>
  repBranch h (rep') ary st len (firstn len ls) (repBranch_nextPtr ls lenm1 optr').
Proof.
  intros; apply iter_imp; intros; do 2 sep fail auto.
  norm list; case_eq (nth_error ls i); sep fail auto.
Qed.

(**
Theorem repBranch_prefix' : forall h ary pos LS (X : sigTS (fun _:key => @BPlusTreeImplModel.ptree key value h)) XS PTR n,
  pos <= length LS ->
  repBranch h (rep') ary n pos LS (firstPtr (projT2S X))
  ==>
  repBranch h (rep') ary n pos (LS ++ X :: XS) PTR.
Proof. clear.
  induction pos. sep fail auto.
    simpl; destruct LS; sep fail auto. elimtype False; omega. elimtype False; omega.
    destruct LS. simpl in *. destruct pos; try solve [ elimtype False; omega ]. sep fail auto.
    simpl. simpl. sep fail auto. 
    Change (s0 :: LS ++ X :: XS) into ((s0 :: LS) ++ X :: XS) using eauto.
    eapply IHpos; simpl; eauto.
Qed.
Hint Resolve repBranch_prefix'.

Theorem repBranch_prefix_shift' : forall OPTR OPTR' h ary X LS ST,
  X < length LS ->
  repBranch h (rep') ary ST X (firstn (X + 1) LS) OPTR
  ==>
  repBranch h (rep') ary ST X (firstn X LS) 
  match nth_error LS X with
    | None => OPTR'
    | Some v => firstPtr (projT2S v)
  end.
Proof. clear. Opaque skipn nth_error firstn.
  induction X; [ sep fail auto | ]. intros; simpl BPlusTreeImplModel.repBranch.
  destruct LS. norm list. Focus 2. Transparent firstn. simpl firstn. Opaque firstn.
  simpl. sep fail auto. Transparent nth_error. simpl nth_error. Opaque nth_error.
  
  Transparent skipn nth_error firstn.
  destruct LS. simpl in *. elimtype False. omega.
  search_prem ltac:(search_conc ltac:(eapply himp_split; [ apply IHX; omega | ])).
  
  destruct X. simpl. destruct s0. sep fail auto.
  simpl. sep fail auto.
  
  sep fail auto.
Qed.
Hint Resolve repBranch_prefix_shift'.

Lemma repBranch_prefix_shift : forall P Q OPTR OPTR' OPTR'' h ary X (LS : list (BranchCell h)),
  X < length LS ->
  OPTR' = match nth_error LS X with
            | None => OPTR''
            | Some v => firstPtr (projT2S v)
          end ->
  P ==> Q ->
  repBranch h (rep') ary 0 X (firstn (X + 1) LS) OPTR * P
  ==>
  repBranch h (rep') ary 0 X (firstn X LS) OPTR' * Q.
Proof. clear. 
  intros. apply himp_split; try auto. rewrite H0. apply repBranch_prefix_shift'; auto.
Qed.
**)




(** Reading Lemmas **)
Lemma repBranch_splitPrem : forall h ary s i ls x0 e P Q,
  i < e
  -> (repBranch h (rep') ary s i ls x0 *
     repBranch h (rep') ary (s + i) (e - i) (skipn i ls) x0 * P)%hprop ==> Q
  -> repBranch h (rep') ary s e ls x0 * P ==> Q.
Proof. clear.
  intros; unfold BPlusTreeImplModel.repBranch in *.
  eapply himp_trans; [ | eapply H0 ]; clear H0.
  search_prem ltac:(eapply sp_index_hyp; try eassumption).
  norm arith. sep fail auto.
  Change (e - i) into (S (pred (e - i))) using omega. do 2 sep fail auto.
  apply himp_comm_prem. apply himp_split. norm list. norm arith in *.
    rewrite H0 in H1; rewrite (pack_injective H1).
    case_eq (nth_error ls i); intros; sep fail auto.

  apply iter_shift; intros.
  sep fail auto. norm list.
  Change (i + S i0) into (S (i + i0)) using omega.
  Change (s + S (i + i0)) into (s + i + S i0) using omega. rewrite H3 in H4. rewrite (pack_injective H4).
  sep fail auto.
  destruct (nth_error ls (S (i + i0))); sep fail auto.
Qed.

Lemma repLeaf_read : forall P idx ary ST LEN a0 Q x,
  array_plus ary idx = [x]%inhabited ->
  ST <= idx ->
  idx < ST + LEN ->
  (repLeaf ary ST (idx - ST) a0 *
  (repLeaf ary (S idx) (LEN + ST - S idx) (skipn (S (idx - ST)) a0) *
    Exists v :@ option (sigTS value),
    x ~~> v *
    [v = match nth_error a0 (idx - ST) with
           | None => @None (sigTS value)
           | Some v => Some v
         end])%hprop * P ==> Q)%hprop
  -> repLeaf ary ST LEN a0 * P ==> Q.
Proof. clear.
  intros; unfold BPlusTreeImplModel.repLeaf in *.
  eapply himp_trans; [ | eapply H2 ]; clear H2.
  assert (idx - ST < LEN); try omega.
  search_prem ltac:(eapply sp_index_hyp; try eassumption).
  Change (ST + (idx - ST)) into idx using omega.
  Change (1 + ST + (idx - ST)) into (S idx) using omega.
  Change (LEN - (idx - ST) - 1) into (LEN + ST - S idx) using omega.
  sep fail auto. eapply iter_imp; intros. sep fail auto. norm list.
  f_equal; f_equal. omega.
Qed.


Lemma repBranch_read : forall P idx ary h ST LEN a0 x0 Q x,
  array_plus ary idx = [x]%inhabited ->
  ST <= idx ->
  idx < ST + LEN ->
  (repBranch h (rep') ary ST (idx - ST) a0 x0 *
  (repBranch h (rep') ary (S idx) (LEN + ST - S idx) (skipn (S (idx - ST)) a0) x0 *
    Exists v :@ option (key * ptr),
    x ~~> v *
    [v = match nth_error a0 (idx - ST) with
           | None => @None (key * ptr)
           | Some v => Some (projT1S v, ptrFor (projT2S v))
         end] * 
   match nth_error a0 (idx - ST) with
     | None => [length a0 <= idx - ST]
     | Some v => [idx - ST < length a0] *
       rep' (ptrFor (projT2S v)) (Some (repBranch_nextPtr a0 (idx - ST) x0)) (projT2S v)
   end)%hprop * P ==> Q)%hprop
  -> repBranch h (rep') ary ST LEN a0 x0 * P ==> Q.
Proof. clear. Opaque skipn nth_error firstn.
  intros. eapply repBranch_splitPrem. instantiate (1 := idx - ST); omega.
  eapply himp_trans; [ | eapply H2 ]; clear H2. canceler.
 
  unfold BPlusTreeImplModel.repBranch.
  search_prem ltac:(eapply sp_index_hyp). instantiate (1 := 0); omega.
  sep fail auto.
  Change (LEN - (idx - ST) - 0 - 1) into (LEN + ST - S idx) using omega2.
  search_prem ltac:(search_conc ltac:(apply himp_split; [ apply iter_shift; intros | ])).

  
  sep fail auto. norm list.    
    Change (idx - ST + S i) into (S (idx - ST) + i) using omega.
    Change (ST + (idx - ST) + S i) into (S (idx + i)) using omega.
    rewrite H4 in H5; rewrite (pack_injective H5) in *.
    destruct (nth_error a0 (S (idx - ST) + i)); sep fail auto.

  norm list. norm arith.
    Change (ST + (idx - ST) + 0) into idx using omega.
    rewrite H in H2; rewrite (pack_injective H2).
    case_eq (nth_error a0 (idx - ST)); sep fail ltac:(eauto with norm_list). 
Qed.

(**
Lemma repBranch_elimPart : forall h ary st st' len len' ls ls' nxt nxt' P Q,
  0 < len' ->
  len' < len ->
  st <= st' ->
  st' + len' <= st + len ->

  (repBranch h (rep') ary st' len' (skipn (st' - st) ls) nxt
   ==>
   repBranch h (rep') ary st' len' ls' nxt') ->

  ((repBranch h (rep') ary st (st' - st) ls nxt *
   repBranch h (rep') ary (st' + len') (len - len' - (st' - st)) (skipn (len' + (st' - st)) ls) nxt * P)%hprop
   ==> Q) ->

  repBranch h (rep') ary st len ls nxt * P ==> repBranch h (rep') ary st' len' ls' nxt' * Q.
Proof.
  intros.
  destruct (eq_nat_dec st st').
    subst. norm arith in *. norm list in *.
    search_prem ltac:(eapply repBranch_splitPrem). instantiate (1 := len'); omega.
    search_prem ltac:(apply himp_split; [ assumption | ]).
    eapply himp_trans; [ | eassumption ].
    search_conc ltac:(apply himp_repBranch_0_conc; [ omega | ]). sep fail auto.

  destruct (eq_nat_dec (st' + len') (st + len)).
    subst.
    search_prem ltac:(eapply repBranch_splitPrem). instantiate (1 := len - len'); omega.
    Change (len - (len - len')) into len' using omega. 
    Change (len - len' - (st' - st)) into 0 using omega.
    Change (len - len') into (st' - st) using omega.
    Change (st + (st' - st)) into st' using omega. 
    search_prem ltac:(search_conc ltac:(apply himp_split; [ assumption | ])).
    eapply himp_trans; [ | eassumption ]. sep fail auto.

  search_prem ltac:(eapply repBranch_splitPrem). instantiate (1 := st' - st); omega.
    Change (st + (st' - st)) into st' using omega.
    assert (len' < len - (st' - st)); try omega.
    search_prem ltac:(eapply repBranch_splitPrem; [ eassumption | ]).
    search_prem ltac:(search_conc ltac:(apply himp_split; [ assumption | ])).
    eapply himp_trans; [ | eassumption ]. sep fail auto.
Qed.
**)

Notation repBranchExcept h ary st i len ls optr := 
  (@BPlusTreeImplModel.repBranch key value h (rep') ary st i ls optr *
   @BPlusTreeImplModel.repBranch key value h (rep') ary (S i + st) (len - S i) (skipn (S i) ls) optr)%hprop.

(**
Lemma repBranch_readArray : forall h ary len st idx ls p F P Q,
  st <= idx -> idx < st + len ->

  (forall p' v, array_plus ary idx = [p']%inhabited ->
    repBranchExcept h ary st (idx - st) len ls p *
    p' ~~> v *
    [v = match nth_error ls (idx - st) with
           | None => @None (key * ptr)
           | Some v' => Some (projT1S v', ptrFor (projT2S v'))
         end] *
    match nth_error ls (idx - st) with
      | None => __
      | Some v' => rep' (ptrFor (projT2S v')) (Some (repBranch_nextPtr ls (idx - st) p)) (projT2S v')
    end * P ==> F p' * Q) ->
  repBranch h (rep') ary st len ls p * P ==> hprop_unpack (array_plus ary idx) F * Q.
Proof.
  intros; inhabiter. eapply himp_unpack_conc; [ eassumption | ].
  case_eq (nth_error ls (idx - st)); intros;
    (eapply himp_trans; [ | eapply H1 ]; auto);
    (eapply repBranch_read; try eassumption).
    rewrite H3; sep fail auto.
    rewrite H3; sep fail auto.
Qed.
**)

(** Combining Lemmas **)
Lemma repLeaf_combine : forall P idx ary ST LEN a0 Q x,
  array_plus ary idx = [x]%inhabited ->
  ST <= idx ->
  idx < ST + LEN ->
  (P ==> repLeaf ary ST (idx - ST) a0 *
         repLeaf ary (S idx) (LEN + ST - S idx) (skipn (S (idx - ST)) a0) *
         Exists v :@ option (sigTS value),
         x ~~> v *
         [v = match nth_error a0 (idx - ST) with
                | None => @None (sigTS value)
                | Some v => Some v
              end] * Q)%hprop
  -> P ==> repLeaf ary ST LEN a0 * Q.
Proof. clear.
  intros; unfold BPlusTreeImplModel.repLeaf in *.
  eapply himp_trans; [ eapply H2 | clear H2 ].
  assert (idx - ST < LEN); try omega.
  search_conc ltac:(eapply sp_index_conc; try eassumption).
  Change (ST + (idx - ST)) into idx using omega.
  Change (1 + ST + (idx - ST)) into (S idx) using omega.
  Change (LEN - (idx - ST) - 1) into (LEN + ST - S idx) using omega.
  sep fail auto. eapply iter_imp; sep fail auto.
  norm list. f_equal; f_equal; omega.
Qed.

Lemma repBranch_combine : forall h ary s i ls x0 e P Q,
  i < e
  -> P ==> repBranch h (rep') ary s i ls x0 *
           (repBranch h (rep') ary (s + i) (e - i) (skipn i ls) x0 * Q)%hprop
  -> P ==> repBranch h (rep') ary s e ls x0 * Q.
Proof. clear.
  intros; unfold BPlusTreeImplModel.repBranch in *.
  eapply himp_trans; [ eapply H0 | ]; clear H0.
  search_conc ltac:(eapply sp_index_conc; try eassumption).
  norm arith. sep fail auto.
  Change (e - i) into (S (pred (e - i))) using omega. do 2 sep fail auto.
  apply himp_split. norm list. norm arith in *.
    rewrite H0 in H1; rewrite (pack_injective H1).
    case_eq (nth_error ls i); intros; sep fail auto.

  apply iter_shift; intros.
  sep fail auto. norm list.
  Change (i + S i0) into (S (i + i0)) using omega.
  Change (s + S (i + i0)) into (s + i + S i0) using omega. rewrite H3 in H4. rewrite (pack_injective H4).
  sep fail auto.
  destruct (nth_error ls (S (i + i0))); sep fail auto.
Qed.

Lemma repBranch_combineRead : forall h ary len st idx ls p x P Q,
  array_plus ary idx = [x]%inhabited ->
  st <= idx -> idx < st + len ->

  P ==> repBranchExcept h ary st (idx - st) len ls p *
        match nth_error ls (idx - st) with
          | None => x ~~> (@None (key * ptr))
          | Some v' => x ~~> Some (projT1S v', ptrFor (projT2S v')) *
            rep' (ptrFor (projT2S v')) (Some (repBranch_nextPtr ls (idx - st) p)) (projT2S v')
        end * Q ->
  P ==> repBranch h (rep') ary st len ls p * Q.
Proof.
  intros. search_prem ltac:(apply (himp_subst H2); clear H2).
  search_conc ltac:(eapply repBranch_combine). instantiate (1 := idx - st); omega.
  Change (st + (idx - st)) into idx using omega.
  sep fail auto.
  Change (S (idx - st + st)) into (S idx) using omega.
  unfold BPlusTreeImplModel.repBranch.
  
  search_conc ltac:(eapply sp_index_conc). instantiate (1 := 0); omega.
  norm arith. sep fail auto.
  apply himp_comm_conc. apply himp_split. norm list. norm arith.
    destruct (nth_error ls (idx - st)); sep fail auto.
  Change (pred (len - (idx - st))) into (len - S (idx - st)) using omega.
  apply iter_shift. intros. norm arith. norm list.
    Change (idx + S i) into (S (idx + i)) using omega.
    sep fail auto.
    Change (idx - st + S i) into (S (idx - st + i)) using omega.
    destruct (nth_error ls (S (idx - st + i))); sep fail auto.
Qed.

(**
Lemma repBranch_combineArray : forall h ary len st idx ls p x (v : option (key * ptr)) P Q,
  array_plus ary idx = [x]%inhabited ->
  st <= idx -> idx < st + len ->

  P ==> repBranchExcept h ary st (idx - st) len ls p *
        [v = match nth_error ls (idx - st) with
               | None => @None (key * ptr)
               | Some v' => Some (projT1S v', ptrFor (projT2S v'))
             end] *
        match nth_error ls (idx - st) with
          | None => __
          | Some v' => rep' (ptrFor (projT2S v')) (Some (repBranch_nextPtr ls (idx - st) p)) (projT2S v')
        end * Q ->
  x ~~> v * P ==> repBranch h (rep') ary st len ls p * Q.
Proof.
  intros; search_prem ltac:(apply (himp_subst H2); clear H2).
  eapply repBranch_combine; try eassumption. canceler. instantiate (1 := idx - st); omega.
  Change (st + (idx - st)) into idx using omega.
  destruct (nth_error ls (idx - st)); sep fail auto.
      
Qed.
**)


(** Breaking based on the branch isn't really possible since the branch doesn't tell
 ** you where to split, but you shouldn't be able to read the branch anyways, so it
 ** shouldn't be a problem
 **)

Theorem himp_rep'_frame : forall h b c (d d' : ptree h) b' c' P Q,
  b = b' -> d = d' -> c = c' ->
  P ==> Q ->
  rep' b c d * P ==> rep' b' c' d' * Q.
Proof. 
  intros; subst; apply himp_split; sep fail auto.
Qed.

Theorem himp_repLeaf_frame : forall h a b c d a' b' c' d' P Q,
  a = a' -> b = b' -> c = c' -> d = d' ->
  P ==> Q ->
  @BPlusTreeImplModel.repLeaf h a b c d * P ==> @BPlusTreeImplModel.repLeaf h a' b' c' d' * Q.
Proof. sep fail auto. Qed.
Hint Resolve himp_repLeaf_frame.

(** repBranch **)
Theorem himp_repBranch_frame : forall h a b c d e a' b' c' d' e' P Q,
  a = a' -> b = b' -> c = c' ->
  repBranch h (rep') a b c d e ==> repBranch h (rep') a b c d' e' ->
  P ==> Q ->
  repBranch h (rep') a b c d e * P ==> repBranch h (rep') a' b' c' d' e' * Q.
Proof.
  intros; subst; apply himp_split; sep fail auto.
Qed.

End BPlusTreeModelFacts.
