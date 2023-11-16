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
Require Import Think ThinkList ThinkArith.

Require Import BPlusTreeImplModel.
Require Import BPlusTreeTactics.

Set Implicit Arguments.

Lemma minus_le : forall m n, n <= m -> n - m = 0.
Proof.
  auto.
Qed.

Lemma lt_S_le : forall n m, n < m -> S n <= m.
Proof.
  auto.
Qed.
Lemma O_le : forall n, 0 <= n.
  auto.
Qed.

Section ArrayStuff.
Open Local Scope stsepi_scope.
Open Local Scope hprop_scope.

Lemma array_split_imp : forall (T:Type) (v : T) ary n s, n < s -> 
  {@hprop_unpack (array_plus ary i) (fun p : ptr => p ~~> v) | i <- 0 + n} *
  {@hprop_unpack (array_plus ary i) (fun p : ptr => p ~~>?) | i <- n + (s - n)} ==>
  {@hprop_unpack (array_plus ary i) (fun p : ptr => p ~~> v) | i <- 0 + n} *
  {@hprop_unpack (array_plus ary i) (fun p : ptr => p ~~>?) | i <- (S n) + (s - (S n))} *
   hprop_unpack (array_plus ary n)
    (fun p : ptr => Exists B :@ Set, (Exists w :@ B, p ~~> w)).
Proof. clear.
  induction n. simpl. destruct s; intros; try solve [ elimtype False; omega ]. simpl. norm arith. unfold ptsto_any; sep fail auto.
  intros. simpl. destruct n. simpl. remember (s - 1) as ZZZ. destruct ZZZ. elimtype False. omega.
    simpl. assert (ZZZ = s - 2). omega. rewrite <- H0. unfold ptsto_any; sep fail auto.
    simpl. rewrite (minus_lt _ _ H). simpl. unfold ptsto_any; sep fail auto.
Qed.

(**
Definition array_fill : forall (T : Set) ary st len (val : T),
  STsep ({@ p :~~ array_plus ary i in p ~~>? | i <- st + len}) 
        (fun _:unit => {@ p :~~ array_plus ary i in p ~~> val | i <- st + len}).
Proof. 
  refine (fun T ary st len val => 
    Fix2 (fun (n:nat) (pf:n <= len) => 
           {@ p :~~ array_plus ary i in p ~~> val | i <- st + n } *
           {@ p :~~ array_plus ary i in p ~~>?    | i <- (st + n) + (len - (st + n)) })
         (fun (n:nat) (pf:n <= len) (_:unit) =>
           {@ p :~~ array_plus ary i in p ~~> val | i <- st + len })
         (fun self n pf =>
           match le_lt_dec len n with
             | left _ => {{ Return tt }}
             | right pf' =>
               upd_array ary (st + n) val <@> 
               ({@ p :~~ array_plus ary i in p ~~> val | i <- st + n} *
                {@ p :~~ array_plus ary i in p ~~>? | i <- (st + S n) + (len - (st + S n))}) ;;
               {{ self (S n) (lt_S_le pf') }}
           end) 0 (O_le len) <@> _ ;;
         {{ Return tt }}).
  solve [ sep fail auto ].
  cut (n = len); try omega; intros; subst. 
  Change (len - (st + len)) into 0 using omega. sep fail auto.

  unfold iter_sep. sep fail auto. 
  pose (array_split_imp val ary pf'). simpl in *. apply h.
  sep fail auto.
  canceler. search_conc ltac:(eapply sp_index_conc). instantiate (1 := n); think. norm arith. sep fail auto.
  sep fail auto.
  rewrite <- minus_n_O. simpl. instantiate (1 := [array_length ary = s]). sep fail auto.
  sep fail auto.
  sep fail auto.
  sep fail auto.
Qed.
**)

Definition new_constant_array : forall (T : Set) s (val : T),
  STsep __
        (fun r:array => {@hprop_unpack (array_plus r i) (fun p : ptr => p ~~> val) | i <- 0 + s} * 
          [array_length r = s]).
Proof. 
  refine (fun T s val => 
    ary <- new_array s ;
    Fix2 (fun (n:nat) (pf:n <= s) => 
           {@ hprop_unpack (array_plus ary i) (fun p : ptr => p ~~> val) | i <- 0 + n } *
           {@ hprop_unpack (array_plus ary i) (fun p : ptr => p ~~>?) | i <- n + (s - n) })
         (fun (n:nat) (pf:n <= s) (_:unit) =>
           {@ hprop_unpack (array_plus ary i) (fun p : ptr => p ~~> val) | i <- 0 + s })
         (fun self n pf =>
           match le_lt_dec s n with
             | left _ => {{ Return tt }}
             | right pf' =>
               upd_array ary n val <@> _ ;;
               {{ self (S n) (lt_S_le pf') }}
           end) 0 (O_le s) <@> _ ;;
         {{ Return ary }});
  solve [ sep2 fail bpt_elim; sep_unify ].
Qed.

Ltac pg := idtac;
  combine_le_le ||
  match goal with
    | [ H : ?X = ?Y |- context [ match ?X with 
                                   | None => _
                                   | Some _ => _ 
                                 end ] ] => rewrite H
    | [ |- ?G ] => idtac G
  end.

Definition array_shiftInsert : forall (T U : Set) ary st len (val : U) (valM : [T]) (F : T -> U) (ls : [list T]),
  STsep (ls ~~ valM ~~
              {@ p :~~ array_plus ary i in
                 p ~~> match nth_error ls (i - st) return option U with
                         | None => None
                         | Some v => Some (F v)
                       end | i <- st + len} *
               [val = F valM])
        (fun r:option U => valM ~~ ls ~~ 
          {@ p :~~ array_plus ary i in 
            p ~~> match nth_error (valM :: ls) (i - st) with
                    | None => None
                    | Some v => Some (F v)
                  end | i <- st + len} *
          match r with
            | None => [length (valM :: ls) <= len]
            | Some v' => [Some v' = match nth_error (valM :: ls) len with
                                      | Some v => Some (F v)
                                      | None => None 
                                    end]
          end).
  refine (fun T U ary st len val valM F ls => 
    {{ Fix3 (fun (n:nat) (pf:n <= len) (v : U) => ls ~~ valM ~~
              {@ p :~~ array_plus ary i in
                p ~~> match nth_error ls (i - st) return option U with
                        | None => None
                        | Some v => Some (F v)
                      end | i <- (st + n) + (len - n)} *
              {@ p :~~ array_plus ary i in 
                p ~~> match nth_error (valM :: ls) (i - st) return option U with
                        | None => None
                        | Some v => Some (F v)
                      end | i <- st + n} *
              [Some v = match nth_error (valM :: ls) n with
                          | None => None
                          | Some v => Some (F v)
                        end])
            (fun _ _ _ (r:option U) => ls ~~ valM ~~
              {@ p :~~ array_plus ary i in 
                p ~~> match nth_error (valM :: ls) (i - st) with
                        | None => None
                        | Some v => Some (F v)
                      end | i <- st + len} *
              match r with
                | None => [length (valM :: ls) <= len]
                | Some v' => [Some v' = match nth_error (valM :: ls) len with
                                          | None => None
                                          | Some v => Some (F v)
                                        end]
              end)
         (fun self n pf v =>
           match le_lt_dec len n with
             | left _ => {{ Return (Some v) }}
             | right pf' =>
               v' <- sub_array ary (st + n) 
                  (fun v:option U => ls ~~ valM ~~
                    {@ p :~~ array_plus ary i in
                      p ~~> match nth_error (valM :: ls) (i - st) with
                              | Some v => Some (F v)
                              | None => None
                            end | i <- st + n } *
                    {@ p :~~ array_plus ary i in
                      p ~~> match nth_error ls (i - st) with
                              | Some v => Some (F v)
                              | None => None
                            end | i <- (S (st + n)) + (len - S n) } *
                    [v = match nth_error ls n with
                           | None => None
                           | Some v => Some (F v)
                         end]) <@> _ ;
               upd_array ary (st + n) (Some v) <@> _ ;;
               match v' as v'' return v' = v'' -> _ with
                 | None    => fun pf => {{ Return None }}
                 | Some v' => fun pf => {{ self (S n) (lt_S_le pf') v' }}
               end (refl_equal _)                   
           end) 0 (O_le len) val }}); try clear self.
Proof.
  solve [ sep2 fail bpt_elim; sep_unify ].
  sep2 pg bpt_elim. sep_unify.
  sep2 pg bpt_elim. sep_unify.
  sep2 pg bpt_elim. sep_unify.
  sep2 pg bpt_elim. sep_unify.
  sep2 pg bpt_elim. sep_unify.
  sep2 pg bpt_elim. norm arith. auto. norm list. rewrite pf0 in *. sep2 fail bpt_elim. sep_unify.
  sep2 pg bpt_elim. sep_unify.
  sep2 pg bpt_elim. sep_unify.
  sep2 pg bpt_elim. norm arith. auto. Change (S (st + n) - st) into (S n) using omega.
    subst. simpl length. case_eq (nth_error x n); intros; rewrite H in *; try discriminate.
    cut (length x <= n); eauto with norm_list_length. sep2 fail bpt_elim.
    repeat search_prem ltac:(apply himp_inj_prem; intro XX; clear XX).
    apply iter_imp; intros; norm list; auto.
  sep2 pg bpt_elim. norm list. sep2 fail bpt_elim. sep_unify.
  sep2 pg bpt_elim. sep_unify.
Qed.

Require Import Div2 Even.

Definition array_move : forall (T U : Set) src trg ssrc strg len (F : T -> U) (ls : [list T]),
  STsep (ls ~~ 
          {@ p :~~ array_plus src i in
            p ~~> match nth_error ls (i - ssrc) return option U with
                    | None => None
                    | Some v => Some (F v)
                  end | i <- ssrc + len} *
          {@ p :~~ array_plus trg i in p ~~>? | i <- strg + len})
        (fun _ : unit => ls ~~ 
          {@ p :~~ array_plus src i in p ~~> @None U | i <- ssrc + len} *
          {@ p :~~ array_plus trg i in
            p ~~> match nth_error ls (i - strg) return option U with
                    | None => None
                    | Some v => Some (F v)
                  end | i <- strg + len}).
  refine (fun T U src trg ssrc strg len F ls =>
    {{ Fix (fun n => ls ~~ 
             {@ p :~~ array_plus src i in
               p ~~> match nth_error ls (i - ssrc) return option U with
                       | None => None
                       | Some v => Some (F v)
                     end | i <- (ssrc + n) + (len - n)} *
             {@ p :~~ array_plus trg i in p ~~>? | i <- (strg + n) + (len - n)})
           (fun n (res:unit) => ls ~~
             {@ p :~~ array_plus src i in p ~~> @None U | i <- (ssrc + n) + (len - n)} *
             {@ p :~~ array_plus trg i in
               p ~~> match nth_error ls (i - strg) return option U with
                       | None => None
                       | Some v => Some (F v)
                     end | i <- (strg + n) + (len - n)})
           (fun self n =>
             if le_lt_dec len n then
               {{ Return tt }}
             else
               v <- sub_array src (ssrc + n) (fun v : option U => ls ~~
                 [v = match nth_error ls n with 
                        | None => None
                        | Some v => Some (F v)
                      end]) <@> _ ;
               upd_array src (ssrc + n) (@None U) <@> _ ;;
               upd_array trg (strg + n) v <@> _ ;;
               {{ self (S n) <@> _ }}) 0 }}).
Proof.
  solve [ sep_unify ].
  solve [ sep2 fail bpt_elim; sep_unify ].
  
  solve [ sep2 fail bpt_elim; sep_unify ].
  solve [ sep_unify ].

  solve [ sep2 fail bpt_elim; sep_unify ].
  solve [ sep_unify ].

  solve [ sep2 fail bpt_elim; sep_unify ].
  solve [ sep_unify ].
  
  solve [ sep2 fail bpt_elim; sep_unify ].

  sep2 fail bpt_elim; [ Change (strg + n - strg) into n using omega | sep_unify ]. auto.
  
  solve [ sep2 fail bpt_elim; sep_unify ].
  solve [ sep2 fail bpt_elim; sep_unify ].
Qed.

Opaque skipn firstn nth_error.

Lemma split_array_half : forall (U:Set) clen plen P Q aryR,
  clen < plen ->
  {@hprop_unpack (array_plus aryR i) (fun p : ptr => p ~~> @None U) | i <-
    clen + plen - clen} * P ==> Q ->
  {@hprop_unpack (array_plus aryR i) (fun p : ptr => p ~~> @None U) | i <-
    0 + plen} * P ==>
  {@hprop_unpack (array_plus aryR i) (fun p : ptr => p ~~>?) | i <- 
    0 + clen} * Q.
Proof.
  intros. search_prem ltac:(eapply sp_index_hyp; [ eassumption | ]).
  search_conc ltac:(eapply himp_rsubst; [ eassumption | ]). sep2 fail bpt_elim.
  apply iter_imp; unfold ptsto_any; sep fail auto.
Qed.

Lemma split_array_half_2 : forall (T U : Set) len P Q ary x1 x (F : T -> U),
  div2 len < len ->
  even len ->
  skipn (S (div2 len)) x = x1 ->
  ({@hprop_unpack (array_plus ary i)
    (fun p : ptr =>
      p ~~>
      match nth_error x i with
        | Some v => Some (F v)
        | None => None
      end) | i <- 0 + S (div2 len)} * P ==> Q) ->    
  {@hprop_unpack (array_plus ary i)
    (fun p : ptr =>
      p ~~>
      match nth_error x i with
        | Some v => Some (F v)
        | None => None
        end) | i <- (0) + len} * P ==>
  {@hprop_unpack (array_plus ary i)
    (fun p : ptr =>
      p ~~>
      match nth_error x1 (i - S (div2 len)) with
        | Some v => Some (F v)
        | None => None
      end) | i <- (S (div2 len)) + pred (div2 len)} * Q.
Proof.
  intros. search_conc ltac:(eapply himp_rsubst; [ eassumption | ]).
  search_prem ltac:(eapply sp_index_hyp). eassumption. norm arith.
  sep2 fail bpt_elim. cut (len - div2 len = div2 len); intros. 
  apply iter_imp; intros; subst. norm list. Change (S (div2 len) + (i - S (div2 len))) into i using omega.
  sep fail auto. rewrite <- (twice_half len) at 1; auto.
Qed.


Definition array_splitEnd : forall (T U : Set) ary len (val : U) (valM : [T]) (F : T -> U) (ls : [list T]),
  1 <= len ->
  even len ->
  STsep (ls ~~ valM ~~ 
          [length ls = len] *
          {@ p :~~ array_plus ary i in
            p ~~> match nth_error ls i return option U with
                    | None => None
                    | Some v => Some (F v)
                  end | i <- 0 + len} *
          [val = F valM])
        (fun aryR : array => ls ~~ valM ~~
          {@ p :~~ array_plus ary i in
            p ~~> match nth_error (firstn (S (div2 len)) ls) i return option U with
                    | None => None
                    | Some v => Some (F v)
                  end | i <- 0 + len} *
          {@ p :~~ array_plus aryR i in
            p ~~> match nth_error (skipn (S (div2 len)) (ls ++ valM :: nil)) i return option U with
                    | None => None
                    | Some v => Some (F v)
                  end | i <- 0 + len } *
          [array_length aryR = len]).
  refine (fun T U ary len val valM F ls pfMin pfEven =>
    aryR <- new_constant_array len (@None U) <@> _ ;

    (** copy indicies [SIZE / 2, SIZE) into aryR (write None to the rest) **)
    @array_move T U ary aryR (S (div2 len)) 0 (pred (div2 len)) F (ls ~~~ skipn (S (div2 len)) ls) <@> _ ;;

    (** put val in aryR at SIZE / 2 **)
    upd_array aryR (pred (div2 len)) (Some val) <@> _ ;;

    {{ Return aryR }}).
Proof.
  solve [ sep_unify ].
  solve [ sep_unify ].
  
  sep2 fail bpt_elim.
  search_prem ltac:(search_conc ltac:(eapply split_array_half)).
    rewrite <- (twice_half len) at 2; auto.
    cut (div2 len > 0); intros. omega.
    destruct len using ind_0_1_SS. elimtype False; omega. inversion pfEven. inversion H6. simpl; omega.
  search_prem ltac:(apply split_array_half_2); auto. sep_unify.

  solve [ sep_unify ].
  cut (len - pred (div2 len) = S (div2 len)); intros.
    sep2 fail bpt_elim. rewrite <- H2. norm arith. sep_unify.
    rewrite <- (twice_half len) at 1; auto. 
    cut (div2 len > 0); intros. omega. destruct len using ind_0_1_SS. elimtype False; omega. inversion pfEven. inversion H0. simpl; omega.
    
  solve [ sep_unify ].
  solve [ sep_unify ].
    
  sep2 fail bpt_elim. 
  destruct (eq_nat_dec len 2).
    rewrite e in *; simpl. sep2 fail bpt_elim.
      norm list. auto. norm list. rewrite H3; norm arith. norm list. auto. destruct x; auto. destruct x; norm list; auto. sep_unify.
      assert (div2 len > 1); intros. destruct len using ind_0_1_SS. elimtype False; omega. inversion pfEven. inversion H6. simpl.
        destruct len using ind_0_1_SS. elimtype False; omega. inversion pfEven. inversion H6. inversion H8. inversion H10. simpl; auto.
      assert (S (div2 len) < len). rewrite <- (twice_half len) at 2; auto. omega.
    norm arith. sep2 fail bpt_elim.
      norm list. cut (S (div2 len) + pred (div2 len) = len); intros. rewrite H7. norm list. rewrite H3. norm arith. norm list. auto.
        rewrite <- (twice_half len) at 3; auto. omega.
      norm arith. assert (pred (len - pred (div2 len)) = div2 len).
        rewrite <- (twice_half len) at 1; auto. omega. rewrite H7.
        search_prem ltac:(search_conc ltac:(apply himp_split; [ apply iter_imp | ])).
          intros. norm arith in *. sep fail auto. norm list. auto.
        search_prem ltac:(search_conc ltac:(apply himp_split; [ apply iter_imp | ])).
          intros. sep fail auto. norm list. auto.
        eapply himp_trans; [ | eapply join_sep ]. 
          instantiate (1 := S (div2 len)). norm arith.
        search_prem ltac:(search_conc ltac:(apply himp_split; [ apply iter_imp | ])).
          intros. sep fail auto. norm list. auto.
        Change (len - S (div2 len)) into (pred (div2 len)) using omega.
        search_prem ltac:(search_conc ltac:(apply himp_split; [ apply iter_imp | ])).
          intros. sep fail auto. norm list. auto.
        sep_unify.
        omega.
Qed.

End ArrayStuff.
