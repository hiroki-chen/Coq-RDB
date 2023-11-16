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

Create HintDb norm_pair_rw discriminated.

(** Pair "normalization" **)
Lemma simpl_fst : forall (T U : Type) (a : T) (b : U), fst (a,b) = a.
  auto.
Qed.
Lemma simpl_snd : forall (T U : Type) (a : T) (b : U), snd (a,b) = b.
  auto.
Qed.

Ltac norm_prod :=
  repeat (progress (simpl snd || simpl fst || simpl projT1 || simpl projT2) ||
          autorewrite with norm_pair_rw).
Ltac norm_prod_hyp H :=
  repeat (progress (simpl projT1 in H || simpl projT2 in H || simpl projT1 in H || simpl projT2 in H) ||
          autorewrite with norm_pair_rw in H).

Tactic Notation "norm" "pair" := norm_prod.
Tactic Notation "norm" "pair" "in" constr(H) := norm_prod_hyp H.
Tactic Notation "norm" "pair" "in" "*" :=
  let rw := (rewrite simpl_fst in * || rewrite simpl_snd in *)
  in repeat (rw || (progress (simpl projT1 in * || simpl projT2 in *))).

(** Basic stuff **)
Theorem S_inj : forall a b, a = b -> S a = S b.
  auto.
Qed.

Theorem cons_inj : forall T (a:T) b c d, a = c -> b = d -> a :: b = c :: d.
  intros; subst; auto.
Qed.

Theorem Pair_inj : forall T U (a:T) (b:U) c d,
  a = c -> b = d -> (a,b) = (c,d).
  intros; subst; auto.
Qed.

Theorem Some_inj : forall T (a b : T),
  a = b -> Some a = Some b.
  intros; subst; auto.
Qed.

Theorem match_option_eq : forall T U (a:option T) b f f' (g g' : U),
  a = b ->
  (forall x, a = Some x -> b = Some x -> f x = f' x) ->
  (a = None -> b = None -> g = g') ->
  match a with
    | Some x => f x
    | None => g
  end =
  match b with 
    | Some x => f' x
    | None => g
  end.
  intros; case_eq a; intros; subst; subst; auto.
Qed.

Hint Resolve S_inj Pair_inj Some_inj cons_inj.
Hint Resolve match_option_eq.

Ltac red_goal cont :=
     (split; cont)
  || f_equal
  || match goal with
       | [ |- context [ (match ?X with 
                           | existT _ _ => _
                         end) ] ] => let H := fresh in remember X as H; destruct H 
       | [ |- context [ (match ?X with 
                           | (_,_) => _
                         end) ] ] => let H := fresh in remember X as H; destruct H 
       | [ |- context [ match ?X with 
                          | left _ => _
                          | right _ => _
                        end ] ] => let H := fresh in remember X as H; destruct H 
     end
  || match goal with
       | [ |- _ \/ _ ] => (left; cont) || (right; cont)
     end
  || congruence
  || discriminate
  || tauto
  || (progress firstorder)
  || omega
  || solve [ elimtype False; omega ].

Ltac red_hyps :=
  match goal with
    | [ H : _ /\ _ |- _ ] => destruct H
    | [ H : exists x, _ |- _ ] => destruct H
  end.
  
Ltac think := 
  let rec th reducer  := 
    repeat (red_hyps || red_goal idtac); 
    try solve [ progress (simpl in *; reducer); th ]
  in th ltac:(simpl in *).


Ltac change_using F R T :=
  let H := fresh in
  assert (H : F = R); [ solve [ T ] | rewrite H in *; clear H ].

Tactic Notation "Change" constr(X) "into" constr(Y) "using" tactic(T) := (change_using X Y T).

Hint Extern 1 (Some ?X = Some ?Y) => f_equal.
Hint Extern 1 (fst ?X = fst ?Y) => f_equal.
Hint Extern 1 (snd ?X = snd ?Y) => f_equal.
Hint Extern 1 (?A :: ?B = ?C :: ?D) => f_equal.
