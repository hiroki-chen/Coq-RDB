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

Require Import OrderedTypeNM.
Require Export Setoid.
Require Export SetoidClass.

Module OT := OrderedTypeNM. 

Set Implicit Arguments.  Unset Strict Implicit.

Inductive LiftOrder (t : Set) : Set := 
| Min : LiftOrder t
| Val : t -> LiftOrder t
| Max : LiftOrder t.

Definition LO_eq (t : Set) (pf : Setoid t) (x y : LiftOrder t) :=
  match x, y with
    | Min,Min => True
    | Max,Max => True
    | Val a, Val b => equiv a b
    | _,_ => False
  end.

Lemma LO_eq_refl (t : Set) (pf : Setoid t) : Reflexive (LO_eq pf).
 unfold Reflexive; intros; destruct x; auto; simpl; trivial; reflexivity.
Qed.
Lemma LO_eq_sym (t : Set) (pf : Setoid t) : Symmetric (LO_eq pf). 
 unfold Symmetric; intros; destruct x; destruct y; auto; simpl in *; symmetry; auto.
Qed.
Lemma LO_eq_trans (t : Set) (pf : Setoid t) : Transitive (LO_eq pf). 
 unfold Transitive; intros; destruct x; destruct y; destruct z; simpl in *; 
  try trivial; try contradiction. setoid_rewrite H . assumption.
Qed.

Global Instance LiftEq (t:Set) {pf:Setoid t} : Equivalence (LO_eq pf).
Proof.
  split; [apply LO_eq_refl | apply LO_eq_sym | apply LO_eq_trans].
Qed.

Global Instance LiftSetoid (t: Set) (pf: Setoid t) : Setoid (LiftOrder t) :=
  { equiv := LO_eq pf
  ; setoid_equiv := LiftEq t
  }.

Definition LO_lt (t : Set) (pf : OrderedType t) (x y : LiftOrder t) :=
  match x, y with
    | Min,Max => True
    | Min, Val _ => True
    | Val _, Max => True
    | Val a, Val b => ordLt a b
    | _,_ => False
  end.

Lemma ordLt_trans (t : Set) (pf : OrderedType t) : Transitive (LO_lt pf).
  solve [ unfold Transitive; intros ? ? x y z; destruct x; destruct y; destruct z; simpl in *; intros; auto; try contradiction; rewrite H; assumption ].
Qed.

Lemma ordLt_not_eq_LO (t : Set) (pf : OrderedType t) : forall x y : LiftOrder t, LO_lt pf x y -> x =/= y.
  intros; destruct x; destruct y; simpl in *; try contradiction; unfold complement; intros; simpl in *; try congruence.
    eapply ordLt_not_eq; eassumption.
Qed.

Definition LO_Compare (t : Set) (pf : OrderedType t) : forall x y : LiftOrder t, Compare (LO_lt pf) equiv x y.
  refine (fun t pf x y =>
    match x as x, y as y return Compare _ equiv x y with
      | Min,Min   => EQ _ _ 
      | Min,Val b => LT _ _
      | Min,Max   => LT _ _
      | Val a,Min => GT _ _
      | Val a,Val b => match ordCompare a b as z return z = ordCompare a b -> _ with
                         | EQ pf => fun _ => EQ _ _
                         | LT pf => fun _ => LT _ _
                         | GT pf => fun _ => GT _ _
                       end (refl_equal _)
      | Val a,Max => LT _ _
      | Max,Min   => GT _ _
      | Max,Val b => GT _ _
      | Max,Max   => EQ _ _
    end); simpl; try trivial; reflexivity.
Qed.


Global Instance LiftOrderIsOrder t (pf: OrderedType t) : OrderedType (LiftOrder t) :=
   { ordEq := LiftSetoid ordEq
   ; ordLt := LO_lt pf
   ; ordLt_trans := @ordLt_trans _ pf 
   ; ordLt_not_eq := @ordLt_not_eq_LO _ pf
   ; ordCompare := @LO_Compare _ pf
   }.

Global Instance proper_Val {A:Set} {s:Setoid A} :
  Proper (equiv ==> equiv) (@Val A). 
Proof.
  unfold Proper, respectful; auto.
Qed.

(** Option **)
Definition OP_eq (t : Set) (pf : Setoid t) (x y : option t) :=
  match x, y with
    | None,None => True
    | Some a, Some b => equiv a b
    | _,_ => False
  end.

Lemma OP_eq_refl (t : Set) (pf : Setoid t) : Reflexive (OP_eq pf).
 unfold Reflexive; intros; destruct x; auto; simpl; trivial; reflexivity.
Qed.
Lemma OP_eq_sym (t : Set) (pf : Setoid t) : Symmetric (OP_eq pf). 
 unfold Symmetric; intros; destruct x; destruct y; auto; simpl in *; symmetry; auto.
Qed.
Lemma OP_eq_trans (t : Set) (pf : Setoid t) : Transitive (OP_eq pf). 
 unfold Transitive; intros; destruct x; destruct y; destruct z; simpl in *; 
  try trivial; try contradiction. setoid_rewrite H . assumption.
Qed.

Global Instance OP_Eq (t:Set) {pf:Setoid t} : Equivalence (OP_eq pf).
Proof.
  split; [apply OP_eq_refl | apply OP_eq_sym | apply OP_eq_trans].
Qed.

Global Instance OptionSetoid (t: Set) (pf: Setoid t) : Setoid (option t) :=
  { equiv := OP_eq pf
  ; setoid_equiv := OP_Eq t
  }.
