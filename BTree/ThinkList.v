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

Require Import List.
Require Import Omega.
Require Import Think ThinkArith.

Set Implicit Arguments.

Create HintDb norm_list discriminated.
Create HintDb norm_list_rw discriminated.
Create HintDb norm_list_length discriminated.
Hint Opaque app rev map fold_left fold_right skipn firstn nth_error nth nth_ok : norm_list.

Hint Extern 1 (@eq nat ?X ?Y) => omega2 : norm_list.
Hint Extern 1 (?X < ?Y)  => omega2 : norm_list.
Hint Extern 1 (?X <= ?Y) => omega2 : norm_list.
Hint Extern 1 (?X >= ?Y) => omega2 : norm_list.
Hint Extern 1 (?X > ?Y)  => omega2 : norm_list.

Ltac solve_length := 
  solve [ (eauto with norm_list_length)
        | repeat (rewrite app_length || simpl length); eauto with norm_list_length ].

(** List Rewriting **)
(** append **)
Lemma nil_app : forall T (l : list T), nil ++ l = l.
  auto.
Qed.
Lemma app_nil : forall T (l : list T), l ++ nil = l.
  induction l; firstorder.
Qed.
Hint Rewrite nil_app app_nil app_ass : norm_list_rw.
Hint Rewrite <- app_comm_cons : norm_list_rw.
Hint Immediate nil_app app_nil app_ass app_comm_cons : norm_list.

(** map **)
Lemma map_nil : forall (T U : Type) (f : T -> U), map f nil = nil.
  reflexivity.
Qed.
Lemma map_cons : forall (T U : Type) (f : T -> U) (t : T) (r : list T), map f (t :: r) = (f t) :: map f r.
  reflexivity.
Qed.
Lemma map_app : forall (T U : Type) (f : T -> U) (t r : list T), map f (t ++ r) = (map f t) ++ map f r.
  induction t; simpl; firstorder.
Qed.
Hint Rewrite map_nil map_cons map_app : norm_list_rw.
Hint Immediate map_nil map_cons map_app : norm_list.

(** skipn **)
Lemma skipn_nil : forall T n,
  skipn n (@nil T) = @nil T.
  destruct n; auto.
Qed.
Lemma skipn_red_0 : forall T (ls :list T), 
  skipn 0 ls = ls.
  reflexivity.
Qed.
Lemma skipn_red_S : forall T n (x : T) xs,
  skipn (S n) (x :: xs) = skipn n xs.
  reflexivity.
Qed.
Hint Rewrite skipn_nil skipn_red_0 skipn_red_S : norm_list_rw.
Hint Immediate skipn_nil skipn_red_0 skipn_red_S : norm_list.

Lemma skipn_len_rw : forall n (T : Type) (l : list T),
  length l <= n -> skipn n l = nil.
Proof.
  induction n; simpl; firstorder. destruct l; firstorder. simpl in *; elimtype False; omega. destruct l; firstorder.
Qed.
Hint Rewrite skipn_len_rw using solve [ solve_length ] : norm_list_rw.
Hint Resolve skipn_len_rw : norm_list.

Lemma skipn_combine : forall T m n (LS : list T),
  skipn n (skipn m LS) = skipn (n + m) LS.
Proof.
  induction m. intros; simpl. norm arith. auto.
  intros; simpl. destruct LS. autorewrite with norm_list_rw. auto.
  Change (n + S m) into (S (n + m)) using omega. simpl. auto.
Qed.

Lemma skipn_combine_app : forall T LS' (LS : list T) m n,
  n + m <= length LS -> skipn n (skipn m LS ++ LS') = skipn (n + m) LS ++ LS'.
Proof.
  induction LS.
    simpl; intros; cut (n = 0); try omega; cut (m = 0); try omega; intros; subst. simpl. auto.
    intros. destruct m. simpl. destruct n. simpl. auto. simpl. rewrite <- IHLS; auto.
    simpl in *; omega.
    Change (n + S m) into (S (n + m)) using omega. simpl. apply IHLS. simpl in *; omega.
Qed.

Hint Rewrite skipn_combine skipn_combine_app using solve [ eauto with norm_list_length ] : norm_list_rw.
Hint Immediate skipn_combine skipn_combine_app : norm_list.

(** firstn **)
Lemma firstn_nil : forall T n,
  firstn n (@nil T) = @nil T.
  destruct n; auto.
Qed.
Lemma firstn_0 : forall T (ls : list T),
  firstn 0 ls = nil.
  auto.
Qed.
Lemma firstn_red_S : forall T n (x : T) xs,
  firstn (S n) (x :: xs) = x :: firstn n xs.
  reflexivity.
Qed.
Hint Rewrite firstn_nil firstn_0 firstn_red_S : norm_list_rw.
Hint Immediate firstn_nil firstn_0 firstn_red_S : norm_list.

Lemma firstn_len_le_rw : forall (n : nat) T (ls : list T), 
  length ls <= n -> firstn n ls = ls.
Proof.
  induction n; simpl; intros; destruct ls; firstorder.
Qed.
Lemma firstn_length : forall T (LS: list T) i,
  length LS <= i -> firstn i LS = LS.
Proof.
  induction LS; simpl in *; intros; auto with norm_list.
  destruct i. elimtype False; omega. simpl. f_equal. apply IHLS. omega.
Qed.

Lemma firstn_append : forall T (ls ls' : list T) a,
  length ls <= a ->
  firstn a (ls ++ ls') = ls ++ firstn (a - length ls) ls'.
Proof. 
  induction ls. intros. norm arith. simpl. auto.
  destruct a0; simpl; intros. elimtype False; omega.
  f_equal. simpl in *. eauto. 
Qed.

Lemma firstn_cons : forall T a x (ls : list T),
  0 < a ->
  firstn a (x :: ls) = x :: firstn (a - 1) ls.
Proof.
  induction a. intros. norm arith. elimtype False; omega.
  destruct ls. intros; autorewrite with norm_list_rw. auto.
  intros; autorewrite with norm_list_rw. f_equal. simpl in *. norm arith. auto.
Qed. 

Hint Rewrite firstn_len_le_rw firstn_length firstn_append using solve [ solve_length ] : norm_list_rw.
Hint Resolve firstn_len_le_rw firstn_length firstn_append : norm_list.

(** nth_error **)
Lemma nth_error_nil : forall T n, 
  nth_error (@nil T) n = None.
  destruct n; auto.
Qed.
Lemma nth_error_red_S : forall T n (x : T) xs,
  nth_error (x :: xs) (S n) = nth_error xs n.
  reflexivity.
Qed.
Lemma nth_error_red_0 : forall T (x : T) xs,
  nth_error (x :: xs) 0 = Some x.
  reflexivity.
Qed.
Hint Rewrite nth_error_nil nth_error_red_S nth_error_red_0 : norm_list_rw.
Hint Immediate nth_error_nil nth_error_red_S nth_error_red_0 : norm_list.

Lemma nth_error_len_rw : forall i T (x:list T), 
  length x <= i -> nth_error x i = None.
Proof.
  induction i; destruct x; simpl in *; firstorder. elimtype False. omega.
Qed.
Lemma nth_error_app_first : forall T n (x y : list T),
  n < length x ->
  nth_error (x ++ y) n = nth_error x n.
Proof. clear. 
  induction n; destruct x; simpl in *; intros; try (elimtype False; omega); try discriminate; auto.
Qed.
Lemma nth_error_app_second : forall T n (x y : list T),
  length x <= n ->
  nth_error (x ++ y) n = nth_error y (n - length x).
Proof. clear. 
  induction n; destruct x; simpl in *; intros; try (elimtype False; omega); try discriminate; auto.
Qed.
Hint Rewrite nth_error_len_rw nth_error_app_first nth_error_app_second using solve [ solve_length ] : norm_list_rw.
Hint Immediate nth_error_len_rw nth_error_app_first nth_error_app_second.

(** last **)
Lemma last_cons : forall T ls (x y : T),
  last (ls ++ x :: nil) y = x.
  induction ls; simpl in *; firstorder.
  generalize (IHls x y). intros. rewrite <- H at 1.
  destruct ls. auto. simpl. auto.
Qed.
Lemma last_nil : forall T (y : T),
  last nil y = y.
  auto.
Qed.

Lemma last_cons_red : forall T (ls : list T) x y,
  last (x :: ls) y = last ls x.
Proof.
  induction ls; auto; destruct ls; auto.
Qed.

Lemma last_nth_error : forall T i (ls : list T) x y,
  S i = length ls ->
  nth_error ls i = Some x ->
  last ls y = x.
Proof. 
  induction i. intros; autorewrite with norm_list_rw in *. destruct ls. simpl in *; discriminate.
    destruct ls. simpl in *. autorewrite with norm_list_rw in *. inversion H0. auto.
    simpl in *; discriminate.
    destruct ls. simpl; intros; discriminate.
    intros. autorewrite with norm_list_rw in *. rewrite last_cons_red. auto.
Qed.
Lemma last_nth_error' : forall T i (ls : list T) x y,
  S i = length ls ->
  last ls y = x ->
  nth_error ls i = Some x.
Proof. clear.
  induction i. intros; autorewrite with norm_list_rw in *. destruct ls. simpl in *; discriminate.
    destruct ls. simpl in *. autorewrite with norm_list_rw in *. inversion H0. auto.
    simpl in *; discriminate.
    destruct ls. simpl; intros; discriminate.
    intros. autorewrite with norm_list_rw in *. 
    simpl in H. rewrite last_cons_red in H0. eauto.
Qed.

Hint Rewrite last_cons last_nil last_cons_red : norm_list_rw.
Hint Immediate last_cons last_nil last_cons_red : norm_list.

Lemma nth_nil : forall T n (d:T),
  nth n nil d = d.
  destruct n; auto.
Qed.
Lemma nth_ok_nil : forall T n (d:T),
  nth_ok n nil d = false.
  destruct n; auto.
Qed.
Hint Rewrite nth_nil nth_ok_nil : norm_list_rw.
Hint Immediate nth_nil nth_ok_nil : norm_list.

(** flat map **)
Lemma flat_map_cons : forall (T S : Type) (F:T -> list S) a b,
  flat_map F (a :: b) = (F a) ++ (flat_map F b).
Proof.
  auto.
Qed.
Lemma flat_map_app : forall (T S : Type) (F:T -> list S) a b,
  flat_map F (a ++ b) = (flat_map F a) ++ (flat_map F b).
Proof.
  induction a; auto. simpl. intros; rewrite app_ass. rewrite IHa. auto.
Qed.
Hint Rewrite flat_map_app flat_map_cons : norm_list_rw.
Hint Immediate flat_map_app flat_map_cons : norm_list.

(** Extras **)
Lemma rev_app : forall T (a b : list T), rev (a ++ b) = (rev b) ++ (rev a).
  induction a; intros; simpl;
    [ rewrite  <- app_nil_end; trivial
    | rewrite (IHa b); rewrite app_ass; trivial ].
Qed.
Lemma foldr_cons : forall (T U:Type) (f: U -> T -> T) a b v, fold_right f v (a :: b) = f a (fold_right f v b).
  reflexivity.
Qed.
Hint Rewrite rev_app foldr_cons : norm_list_rw.
Hint Immediate rev_app foldr_cons : norm_list.

(** TODO : continue fixing this file **)

Lemma nth_error_firstn : forall T a (ls : list T) b,
  b < a -> nth_error (firstn a ls) b = nth_error ls b.
Proof. 
  induction a; destruct ls; simpl; intros; firstorder. elimtype False; omega.
  destruct b; auto. simpl. apply IHa. omega.
Qed.

Lemma nth_error_firstn_app : forall T a (ls : list T) b irr,
  b < a -> b < length ls -> nth_error (firstn a ls ++ irr) b = nth_error ls b.
Proof.
  induction a; destruct ls; simpl; intros; autorewrite with norm_list_rw in *; auto.
  destruct b. simpl. auto. simpl. auto.
Qed.

Lemma nth_error_skipn : forall T s n (ls : list T), 
  nth_error (skipn s ls) n = nth_error ls (s + n).
Proof.
  induction s. auto.
  simpl; intros. destruct ls. rewrite nth_error_nil. auto. auto.
Qed.

Lemma nth_error_skipn_app : forall T len (LS LS' : list T),
  len < length LS ->
  nth_error (skipn len LS ++ LS') 0 = nth_error LS len.
Proof. 
  induction len; intros; auto.
  destruct LS. autorewrite with norm_list_rw. simpl in *; elimtype False; omega.
  simpl in *; eauto.
Qed.

Lemma skipn_S_cons : forall T N LS XS (X : T),
  skipn N LS = X :: XS -> skipn (S N) LS = XS.
Proof.
  induction N; intros; subst. autorewrite with norm_list_rw in *; subst; auto.
  destruct LS; autorewrite with norm_list_rw in *; try discriminate. erewrite <- IHN; simpl; eauto.
Qed.

Lemma skipn_app_eq : forall T (ls ls' : list T) N,
  N = length ls -> skipn N (ls ++ ls') = ls'.
Proof.
  induction ls; simpl in *; intros; subst; firstorder.
Qed.

Lemma head_app : forall T (a b : list T),
  0 < length a -> head (a ++ b) = head a.
Proof.
  induction a; simpl; firstorder. elimtype False; omega.
Qed.

Lemma head_skipn : forall t i (ls : list t),
  head (skipn i ls) = nth_error ls i.
Proof. clear.
  induction i; destruct ls; simpl in *; auto.
Qed.
Hint Rewrite head_skipn : norm_list_rw.

Lemma skipn_nth_error : forall T idx (x:T) a0 x1,
  skipn idx a0 = x :: x1
  -> nth_error a0 idx = Some x.
Proof.
  induction idx; destruct a0; simpl in *; intros; try discriminate.
  inversion H; auto. eapply IHidx; eauto.
Qed.

Lemma skipn_shift : forall (T : Type) n b d (a:T) c,
  skipn n (a :: b) = c :: d -> skipn n b = d.
Proof.
  induction n; simpl in *; firstorder; inversion H; auto.
  destruct b; firstorder. autorewrite with norm_list_rw in *. discriminate. eauto.
Qed.

Lemma skipn_nil' : forall T i (ls : list T),
  length ls <= i -> skipn i ls = nil.
Proof.
  induction i; destruct ls; simpl in *; intros; auto; 
    try discriminate. elimtype False; omega. 
Qed.

(** To integrate **)

Lemma skipn_app' : forall T i j (LS LS' : list T),
  j <= i ->
  j <= length LS ->
  skipn i (firstn j LS ++ LS') = skipn (i - j) LS'.
Proof.
  induction i. simpl; intros. cut (j = 0); try omega; intros; subst; auto.
  intros. destruct j. norm arith. auto. norm arith.
  destruct LS. simpl in *; elimtype False; omega.
  simpl in *. apply IHi. omega. omega.
Qed.

Lemma skipn_firstn : forall T n n' (LS : list T), 
  n' <= n -> skipn n (firstn n' LS) = nil.
Proof. clear.
  induction n; simpl; intros.
  cut (n' = 0); try omega; intros; subst; auto.
  destruct n'; destruct LS; simpl; auto.
Qed.

Lemma skipn_firstn_skipn : forall T (LS : list T) i j k,
  j <= length LS ->
  j <= i ->
  skipn i (firstn j LS ++ skipn k LS) = skipn (k + i - j) LS.
Proof.
  induction LS. simpl; intros. cut (j = 0); try omega; intros. subst. autorewrite with norm_list_rw. auto.
  simpl; intros. destruct i. cut (j = 0); try omega; intros. subst. autorewrite with norm_list_rw. norm arith. auto.
  destruct j. autorewrite with norm_list_rw. norm arith. f_equal.
  simpl.
  destruct k. autorewrite with norm_list_rw. norm arith.
  Focus 2. simpl. Change (k + S i - j) into (S (k + i - j)) using omega. simpl.
  apply IHLS; omega.
  apply skipn_app'; omega.
Qed.

(** Match rewrites **)
Lemma match_skipn_ignore_tail : forall T S N (LS : list T) (NC:S) CC,
  match skipn N LS with
    | nil    => NC
    | a :: _ => CC a
  end =
  match nth_error LS N with
    | None => NC
    | Some a => CC a
  end.
Proof.
  induction N; simpl; intros; destruct LS; auto.
Qed.
Lemma match_head_is_list : forall T S (LS : list T) (NC:S) CC,
  match head LS with
    | None => NC
    | Some a => CC a
  end = 
  match LS with
    | nil    => NC
    | a :: _ => CC a
  end.
Proof.
  destruct LS; auto.
Qed.

Lemma nth_error_skipn_cons : forall T i LS (x : T),
  nth_error LS i = Some x -> skipn i LS = x :: skipn (S i) LS.
Proof.
  induction i; destruct LS; simpl in *; firstorder; inversion H; auto.
Qed.


(** Tactics
 ** - autorewrite has problems with existentials, so we have to code it
 **   manually
 **)
Ltac list_norm_goal :=
  repeat match goal with 
           | [ H : skipn ?I _ = _ :: _
             |- context [ nth_error ?LS ?I ] ] =>
             rewrite (@skipn_nth_error _ _ _ _ _ H)
           | [ H : nth_error ?LS ?i = Some _
             |- context [ skipn ?i ?LS ] ] =>
             rewrite (@nth_error_skipn_cons _ _ _ _ H)
           | [ H : skipn ?I (_ :: ?L) = _ :: _ 
             |- context [ skipn ?I ?L ] ] =>
             rewrite (@skipn_shift _ _ _ _ _ _ H)
           | [ H : skipn ?I (_ :: ?L) = _ :: _ 
             |- context [ skipn (S ?I) ?L ] ] =>
             rewrite (@skipn_S_cons _ _ _ _ _ H)
         end;
  autorewrite with norm_list_rw.

Hint Rewrite nth_error_skipn_cons skipn_app' skipn_firstn_skipn skipn_combine using solve [ solve_length ] : norm_list_rw.
Hint Rewrite skipn_nth_error skipn_shift skipn_nil' skipn_app_eq head_app firstn_length using solve [ solve_length ] : norm_list_rw.
Hint Rewrite nth_error_firstn nth_error_skipn skipn_len_rw firstn_len_le_rw nth_error_len_rw using solve [ solve_length ] : norm_list_rw.
Hint Rewrite skipn_firstn using solve [ solve_length ] : norm_list_rw.

Hint Resolve skipn_S_cons : norm_list.


Tactic Notation "norm" "list" := 
  list_norm_goal. (** ; list_grw_goal ltac:(simpl_length; eauto). **)
Tactic Notation "norm" "list" "in" constr(H) := 
  autorewrite with norm_list_rw in H.  (** ; list_grw_hyp H ltac:(simpl_length; eauto). **)
Tactic Notation "norm" "list" "in" "*" :=
  repeat match goal with 
           | [ H : skipn ?I _ = _ :: _
             |- context [ nth_error ?LS ?I ] ] =>
             rewrite (@skipn_nth_error _ I _ LS H)
           | [ H : nth_error ?LS ?i = Some _
             |- context [ skipn ?i ?LS ] ] =>
             rewrite (@nth_error_skipn_cons _ _ _ _ H)
         end;
  autorewrite with norm_list_rw in *.
(**
  list_grw_star ltac:(simpl_length; eauto); 
  list_norm_goal.
**)

(** Stronger "in" for when domain is decidable **)

Theorem decideable_in : forall T (dec : forall a b : T, {a = b} + {a <> b}) (a x : T) b,
  In x (a :: b) -> a = x \/ (x <> a /\ In x b).
Proof.
  intros. destruct (dec x a); auto. 
  right. destruct H. congruence. auto.
Qed.

(** List Length Theorems
 ** - Most of the rewriting lemmas work based on list length, so we include different
 **   ways for determining the length of a list; these should be combined with
 **   omega and auto to be completely useful
 **)
Lemma app_length_le : forall t (ls ls' : list t) x,
  length ls + length ls' <= x -> length (ls ++ ls') <= x.
Proof. intros; 
  rewrite app_length; auto.
Qed.
Lemma app_length_lt : forall t (ls ls' : list t) x,
  length ls + length ls' < x -> length (ls ++ ls') < x.
Proof. intros; 
  rewrite app_length; auto.
Qed.
Lemma app_length_eq : forall t (ls ls' : list t) x,
  length ls + length ls' = x -> length (ls ++ ls') = x.
Proof. intros; 
  rewrite app_length; auto.
Qed.
Lemma app_length_le' : forall t (ls ls' : list t) x,
  x <= length ls + length ls' -> x <= length (ls ++ ls').
Proof. intros; 
  rewrite app_length; auto.
Qed.
Lemma app_length_lt' : forall t (ls ls' : list t) x,
  x < length ls + length ls' -> x < length (ls ++ ls').
Proof. intros; 
  rewrite app_length; auto.
Qed.
Lemma app_length_eq' : forall t (ls ls' : list t) x,
  x = length ls + length ls' -> x = length (ls ++ ls').
Proof. intros; 
  rewrite app_length; auto.
Qed.
Hint Resolve app_length_le app_length_lt app_length_eq.
Hint Resolve app_length_le' app_length_lt' app_length_eq'.


Theorem nth_error_None_length : forall i T (x:list T), 
  nth_error x i = None -> length x <= i.
Proof.
  induction i; destruct x; simpl in *; firstorder. discriminate. 
Qed.

Theorem firstn_len_len : forall T n (ls : list T) x,
  n <= x -> length (firstn n ls) <= x.
Proof.
  induction n; destruct ls; firstorder. simpl; destruct x. 
  elimtype False; omega. firstorder.
Qed.

Theorem firstn_len_list : forall T n (ls : list T) x,
  length ls <= x -> length (firstn n ls) <= x.
Proof.
  induction n; destruct ls; firstorder; simpl; destruct x; simpl in *; eauto; firstorder.
Qed.

Theorem length_firstn : forall T n (ls : list T),
  length (firstn n ls) <= n.
Proof. clear.
  induction n; destruct ls; simpl; intros; try omega; try discriminate.
  generalize (IHn ls). omega.
Qed.

Theorem length_firstn_le : forall T n (ls : list T),
  length (firstn n ls) <= length ls.
Proof.
  induction n; destruct ls; simpl; intros; try omega; auto.
  generalize (IHn ls); omega.
Qed.

Theorem firstn_len_le : forall (n : nat) T (ls : list T), 
  firstn n ls = ls -> length ls <= n.
Proof.
  induction n; simpl; intros. subst; auto. destruct ls. simpl; omega. simpl in *. inversion H. 
  apply IHn in H1. inversion H. repeat rewrite H2. omega.
Qed.

Theorem len_skipn_nil : forall T (l : list T) i,
  skipn i l = nil -> length l <= i.
Proof.
  induction l; intros; norm list in *. firstorder. destruct i; simpl in *. discriminate. auto with arith.
Qed.

Theorem nth_error_len' : forall T i ls (x : T),
  nth_error ls i = Some x -> i < length ls.
Proof.
  induction i; destruct ls; simpl in *; firstorder; discriminate.
Qed.
Theorem skipn_length_cons : forall T idx LS (X Y : T),
  skipn idx (Y :: LS) = X :: nil -> length LS = idx.
Proof.
  induction idx; simpl in *; intros; subst; eauto. inversion H. auto.
  destruct LS; simpl; norm list in *; try discriminate. apply IHidx in H; eauto.
Qed.

Lemma nth_error_app : forall T (LS LS' : list T) N,
  length LS <= N ->
  nth_error (LS ++ LS') N = nth_error LS' (N - length LS).
Proof.
  induction LS; simpl in *; intros; norm arith; auto.
  Transparent nth_error.
  destruct N; simpl in *; auto. elimtype False; omega.
Qed.
    
Lemma firstn_length_l : forall T N (LS : list T), 
  N <= length LS -> length (firstn N LS) = N.
Proof.
  induction N; destruct LS; norm list; simpl; think.
Qed.

Lemma firstn_length_r : forall t X (LS : list t), length (firstn X LS) <= X.
Proof.
  induction X; destruct LS; norm list; simpl in *; eauto.
  generalize (IHX LS); auto.
Qed.
Hint Resolve firstn_length_r : norm_list_length.

Hint Resolve nth_error_app firstn_length_l : norm_list_length. 

Hint Resolve nth_error_None_length firstn_len_len firstn_len_list length_firstn : norm_list_length.
Hint Resolve length_firstn_le firstn_len_le len_skipn_nil : norm_list_length.
Hint Resolve nth_error_len' skipn_length_cons : norm_list_length.

Hint Resolve nth_error_app firstn_length_l : norm_list. 
Hint Resolve nth_error_None_length firstn_len_len firstn_len_list length_firstn : norm_list.
Hint Resolve length_firstn_le firstn_len_le len_skipn_nil : norm_list.
Hint Resolve nth_error_len' skipn_length_cons : norm_list.

(** Existentials 
 ** - Existentials can be difficult to work with, so we don't rewrite or apply
 **   then by default
 **)
Lemma skipn_len_ne : forall (T : Type) n (ls : list T), 
  n < length ls -> exists f, exists r, skipn n ls = f :: r.
Proof.
  induction n; destruct ls; simpl in *; intros; try (elimtype False; omega); eauto.
Qed.

Lemma nth_error_len_lt : forall T (ls:list T) i,
  i < length ls -> exists v, nth_error ls i = Some v.
Proof.
  induction ls; simpl. intros; elimtype False; omega.
  simpl. destruct i; simpl; intros; eauto. 
Qed.

Lemma nth_error_skipn_ex : forall T i (LS : list T) t,
  nth_error LS i = Some t
  -> exists LS', skipn i LS = t :: LS'.
Proof.
  induction i. simpl. destruct LS; intros. discriminate. exists LS. inversion H; auto.
  intros. destruct LS. norm list in *. discriminate. simpl in *. firstorder.
Qed.

Lemma nth_error_ex : forall T i (LS : list T),
  i < length LS -> exists t, nth_error LS i = Some t.
Proof.
  induction i; destruct LS; simpl; intros; try solve [ elimtype False; omega ]; eauto.
Qed.

Lemma length_skipn : forall T n (ls:list T),
  length (skipn n ls) = length ls - n.
Proof. clear.
  induction n; simpl; intros. omega.
  destruct ls. simpl. omega.
  simpl in *. auto.
Qed.

Lemma firstn_nth_error_expand : forall T i (ls : list T) x,
  nth_error ls i = Some x ->
  firstn (S i) ls = firstn i ls ++ x :: nil.
Proof. clear.
  induction i. intros; norm list. destruct ls. norm list in H. discriminate.
  norm list in *. inversion H; auto.
  intros. destruct ls. norm list in H. discriminate. norm list in *. f_equal. eauto.
Qed.

Lemma ls_expand : forall T i LS (V:T), 
  nth_error LS i = Some V
  -> LS = (firstn i LS) ++ V :: (skipn (S i) LS).
Proof.
  intros. rewrite <- (firstn_skipn i LS) at 1. f_equal.
  norm list; auto.
Qed.

Hint Resolve length_firstn_le length_firstn : norm_list.
Hint Resolve nth_error_len' nth_error_None_length : norm_list.
Hint Resolve length_skipn : norm_list.

(** Test Cases **)
(****************)


Section TestCases.
Variable T : Type.
Variable LS : list T.

Lemma test_1 : forall x, skipn x (firstn x LS) = nil.
  intros; norm list; apply refl_equal.
Qed.
Lemma test_2 : forall x y, skipn (x + y) (firstn (y + x) LS) = nil.
  intros; norm list; apply refl_equal.
Qed.
Lemma test_3 : forall x y, 
  skipn (x + y) (firstn (y + x) LS) = nil /\ skipn (x + y) (firstn (y + x + 1) LS) = skipn (x + y) (firstn (y + x + 1) LS).
  intros; norm list. split; apply refl_equal.
Qed.
Lemma test_4 : forall SIZE N,
  0 < SIZE ->
  N < SIZE ->
  length LS = SIZE ->
  nth_error (firstn (N + 1) LS) N = nth_error LS N.
  intros; norm list; apply refl_equal.
Qed.
Lemma test_5 : forall T xs (y x : T),
  skipn (S (length (y :: xs))) ((y :: xs) ++ x :: nil) = nil.
  intros; norm list; apply refl_equal. 
Qed.
Lemma test_6 : forall T (LS LS' : list T),
  skipn (length LS') (LS' ++ LS) = LS.
  intros; norm list; apply refl_equal.
Qed.
Lemma test_7 : forall T X (LS : list T),
  skipn 1 (X :: LS) = LS.
  intros; norm list; apply refl_equal.
Qed.
(**
Lemma test_8 : forall T (x : T) s a0 x0 idx,
  skipn idx (s :: a0) = x :: x0
  -> nth_error (s :: a0) idx = Some x.
  intros; norm list. 
Qed.
**)
Lemma test_9 : forall T (x : T) s a0 idx,
  skipn idx (s :: a0) = x :: nil
  -> skipn idx a0 = nil.
  intros; norm list; apply refl_equal.
Qed.
Lemma test_10 : forall T (X : T) s a0 idx,
  skipn idx (s :: a0) = X :: nil
  -> nth_error (s :: a0) (S idx) = None.
  intros. rewrite nth_error_len_rw. eauto.
  apply skipn_length_cons in H. simpl in *; omega.
Qed.

(*  
Lemma test_11 : forall T (X X' : T) (LS LS' : list T),
  skipn (length (X :: X' :: LS')) (X :: LS' ++ X' :: LS) = LS.
 intros; norm list. simpl.
*)
  

Definition Hide := T.
Lemma test_hidden : forall n,
  @skipn Hide n (@firstn T n LS) = nil.
  intros. norm list. auto.
Qed.

End TestCases.

(** Replace nth **)
Definition replaceNth T (idx : nat) (ls : list T) (nv : T) : list T :=
  firstn idx ls ++ nv :: skipn (S idx) ls.

Lemma length_replaceNth : forall T (ls : list T) (x : T) idx,
  idx < length ls -> length (replaceNth idx ls x) = length ls.
Proof. clear. Opaque skipn nth_error.
  unfold replaceNth. intros. rewrite app_length; simpl.
  rewrite List.firstn_length; eauto. rewrite length_skipn.
  rewrite Min.min_l; eauto.
Qed.
Lemma nth_error_replaceNth : forall T pos LS (X : T),
  pos < length LS ->
  nth_error (replaceNth pos LS X) pos = Some X.
Proof. clear.
  unfold replaceNth. induction pos.
  intros; norm list; auto.
  intros. destruct LS.
    simpl in *; elimtype False; omega.
    erewrite <- IHpos; [ | simpl in *; instantiate (1 := LS); omega ].
    norm list. simpl length. norm arith. auto.
Qed.
Lemma skipn_replaceNth : forall T pos LS (X : T),
  skipn (S pos) (replaceNth pos LS X) = skipn (S pos) LS.
Proof. clear. 
  unfold replaceNth.
  induction pos. simpl; intros; auto.
  destruct LS. auto.
  intros; simpl in *. norm list. auto.
Qed.
Transparent skipn nth_error.


(** Dependent nth **)
Definition nthDep {T : Type} (ls : list T) (n : nat) : n < length ls -> T.
  intro T. clear.
  refine (fix nthDep (ls:list T) (n:nat) (pf: n < length ls) {struct ls} : T :=
    match ls as ls, n as n return n < length ls -> T with
      | nil, 0      => fun pf => False_rect _ _
      | nil, S n    => fun pf => False_rect _ _
      | f :: _, 0   => fun _  => f
      | _ :: r, S n => fun pf => nthDep r n _
    end pf);
  simpl in *; omega. 
Defined.

Lemma nthDep_pf_irrel (T:Type) b n pf1 pf2 :
  @nthDep T b n pf1 = @nthDep T b n pf2.
Proof. 
  induction b; simpl.
    inversion pf1.
    destruct n; intuition.
Qed.

Lemma skipn_nthDep : forall (T : Type) n b (c:T) d pf, 
  skipn n b = c :: d -> @nthDep T b n pf = c.
Proof.
  induction n. simpl. think. destruct b. discriminate. simpl. inversion H; auto.
  intros. destruct b. simpl in H. destruct n; think.
  assert (n < length b). simpl in *; think.
  pose (IHn _ _ _ H0 H). rewrite <- e. 
  simpl. destruct n; apply nthDep_pf_irrel.
Qed.
  
Lemma nth_error_nthDep : forall (T:Type) (n : nat) (l : list T) pf x,
  @nthDep T l n pf = x -> nth_error l n = Some x.
Proof.
  induction n; destruct l; simpl; try inversion pf.
      subst; auto.
      eapply IHn; eauto.
      eapply IHn; eauto.
Qed.

Lemma nthDep_nth_error : forall (T:Type) (n : nat) (l : list T) pf x,
  nth_error l n = Some x -> @nthDep T l n pf = x.
Proof.
  induction n; destruct l; simpl; try inversion pf.
    intros. inversion H. auto.
    intros; eapply IHn; auto.
    intros; eapply IHn; auto.
Qed.

Opaque nthDep.

Require Export List.
