(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id: FSetList.v 11867 2009-01-28 19:12:26Z letouzey $ *)

(** * Finite sets library *)

(** This file proposes an implementation of the non-dependant 
    interface [FSetInterface.S] using strictly ordered list. *)

Require Import OrderedTypeNM.

Require Import FSetInterfaceNM.
Require Import SetoidList.
(** * Functions over lists

   First, we provide sets as lists which are not necessarily sorted.
   The specs are proved under the additional condition of being sorted. 
   And the functions returning sets are proved to preserve this invariant. *)

Section Raw.
 Variable elt : Set.
 Context {X: OrderedType elt}.
 
 Definition t := list elt.

  Definition empty : t := nil.

  Definition is_empty (l : t) : bool := if l then true else false.

  Definition ordCmp := @ordCompare elt X.

  (** ** The set operations. *)

  Fixpoint mem (x : elt) (s : t) {struct s} : bool :=
    match s with
    | nil => false
    | y :: l =>
        match ordCmp x y with
        | LT _ => false
        | EQ _ => true
        | GT _ => mem x l
        end
    end.

  Fixpoint add (x : elt) (s : t) {struct s} : t :=
    match s with
    | nil => x :: nil
    | y :: l =>
        match ordCmp x y with
        | LT _ => x :: s
        | EQ _ => s
        | GT _ => y :: add x l
        end
    end.

  Definition singleton (x : elt) : t := x :: nil. 

  Fixpoint remove (x : elt) (s : t) {struct s} : t :=
    match s with
    | nil => nil
    | y :: l =>
        match ordCmp x y with
        | LT _ => s
        | EQ _ => l
        | GT _ => y :: remove x l
        end
    end.  
  
  Fixpoint union (s : t) : t -> t :=
    match s with
    | nil => fun s' => s'
    | x :: l =>
        (fix union_aux (s' : t) : t :=
           match s' with
           | nil => s
           | x' :: l' =>
               match ordCmp x x' with
               | LT _ => x :: union l s'
               | EQ _ => x :: union l l'
               | GT _ => x' :: union_aux l'
               end
           end)
    end.      

  Fixpoint inter (s : t) : t -> t :=
    match s with
    | nil => fun _ => nil
    | x :: l =>
        (fix inter_aux (s' : t) : t :=
           match s' with
           | nil => nil
           | x' :: l' =>
               match ordCmp x x' with
               | LT _ => inter l s'
               | EQ _ => x :: inter l l'
               | GT _ => inter_aux l'
               end
           end)
    end.  
  
  Fixpoint diff (s : t) : t -> t :=
    match s with
    | nil => fun _ => nil
    | x :: l =>
        (fix diff_aux (s' : t) : t :=
           match s' with
           | nil => s
           | x' :: l' =>
               match ordCmp x x' with
               | LT _ => x :: diff l s'
               | EQ _ => diff l l'
               | GT _ => diff_aux l'
               end
           end)
    end.  
   
  Fixpoint equal (s : t) : t -> bool :=
    fun s' : t =>
    match s, s' with
    | nil, nil => true
    | x :: l, x' :: l' =>
        match ordCmp x x' with
        | EQ _ => equal l l'
        | _ => false
        end
    | _, _ => false
    end.

  Fixpoint subset (s s' : t) {struct s'} : bool :=
    match s, s' with
    | nil, _ => true
    | x :: l, x' :: l' =>
        match ordCmp x x' with
        | LT _ => false
        | EQ _ => subset l l'
        | GT _ => subset s l'
        end
    | _, _ => false
    end.

  Fixpoint fold (B : Type) (f : elt -> B -> B) (s : t) {struct s} : 
   B -> B := fun i => match s with
                      | nil => i
                      | x :: l => fold B f l (f x i)
                      end.  


  Fixpoint for_all (f : elt -> bool) (s : t) {struct s} : bool :=
    match s with
    | nil => true
    | x :: l => if f x then for_all f l else false
    end.  
 
  Fixpoint exists_ (f : elt -> bool) (s : t) {struct s} : bool :=
    match s with
    | nil => false
    | x :: l => if f x then true else exists_ f l
    end.

  Fixpoint partition (f : elt -> bool) (s : t) {struct s} : 
   t * t :=
    match s with
    | nil => (nil, nil)
    | x :: l =>
        let (s1, s2) := partition f l in
        if f x then (x :: s1, s2) else (s1, x :: s2)
    end.

  Definition cardinal (s : t) : nat := length s.

  Definition elements (x : t) : list elt := x.

  Definition min_elt (s : t) : option elt :=
    match s with
    | nil => None
    | x :: _ => Some x
    end.

  Fixpoint max_elt (s : t) : option elt :=
    match s with
    | nil => None
    | x :: nil => Some x
    | _ :: l => max_elt l
    end.

  Definition choose := min_elt.

  (** ** Proofs of set operation specifications. *)

  Section ForNotations.

Require Import Decidable.
Require Export SetoidClass.
Require Export SetoidDec.
Require Export Functions.
Require Export Morphisms.
Require Export Relations.
Require Import Program.

Set Implicit Arguments. Unset Strict Implicit.

  Notation Sort := (sort (@ordLt elt X)).
  Notation Inf := (lelistA ordLt).

  Notation In := (@InA elt 
    (@equiv elt (@ordEq elt X))).

  Definition Equal s s' := forall a : elt, In a s <-> In a s'.
  Definition Subset s s' := forall a : elt, In a s -> In a s'.
  Definition Empty s := forall a : elt, ~ In a s.
  Definition For_all (P : elt -> Prop) s := forall x, In x s -> P x.
  Definition Exists (P : elt -> Prop) (s : t) := exists x, In x s /\ P x.

  Lemma mem_1 :
   forall (s : t) (Hs : Sort s) (x : elt), In x s -> mem x s = true. 
  Proof.
  simple induction s; intros.
  inversion H.
  inversion_clear Hs.
  inversion_clear H0.
  unfold mem.
  destruct (ordCmp x a). rewrite H3 in o. order.
  reflexivity. rewrite H3 in o. order.
  
  unfold mem in *.
  destruct (ordCmp x a). pose (Sort_Inf_In H1 H2 H3). order.
  reflexivity.
  apply H; assumption.
  Qed. 

  Lemma mem_2 : forall (s : t) (x : elt), mem x s = true -> In x s.
  Proof.
  simple induction s.
  intros; inversion H.
  intros a l Hrec x.
  simpl.
  case (ordCmp x a); intros; try discriminate; auto.
  Qed.

  Lemma add_Inf :
   forall (s : t) (x a : elt), Inf a s -> ordLt a x -> Inf a (add x s).
  Proof.
  simple induction s.  
  simpl; intuition.
  simpl; intros; case (ordCmp x a); intuition; inversion H0;
   intuition.
  Qed.
  Hint Resolve add_Inf.
  
  Lemma add_sort : forall (s : t) (Hs : Sort s) (x : elt), Sort (add x s).
  Proof.
  simple induction s.
  simpl; intuition.
  simpl; intros; case (ordCmp x a); intuition; inversion_clear Hs;
   auto.
  Qed. 

  Lemma add_1 :
   forall (s : t) (Hs : Sort s) (x y : elt), equiv x y -> In y (add x s).
  Proof.
  simple induction s. 
  simpl; intuition.
  simpl; intros; case (ordCmp x a); inversion_clear Hs; auto.
  constructor. symmetry. assumption. intros.
  constructor. rewrite <- H0. assumption. 
  Qed.

  Lemma add_2 :
   forall (s : t) (Hs : Sort s) (x y : elt), In y s -> In y (add x s).
  Proof.
  simple induction s. 
  simpl; intuition.
  simpl; intros; case (ordCmp x a); intuition.
  inversion_clear Hs; inversion_clear H0; auto.
  Qed.

  Lemma add_3 :
   forall (s : t) (Hs : Sort s) (x y : elt),
   ~ equiv x  y -> In y (add x s) -> In y s.
  Proof.
  simple induction s. 
  simpl. intros. inversion H0. rewrite H2 in H. elim H. reflexivity.
  inversion H2.
  simpl; intros a l Hrec Hs x y; case (ordCmp x a); intros;
   inversion_clear H0; inversion_clear Hs; auto.
  rewrite H1 in H. elim H. reflexivity.
  constructor 2. apply Hrec with x. auto. auto. auto.
Qed.

Lemma Inf_lt : forall l x y, ordLt x y -> Inf y l -> Inf x l.
Proof.
 intros. eapply Inf_lt. eauto. assumption.
Qed.

  Lemma remove_Inf :
   forall (s : t) (Hs : Sort s) (x a : elt), Inf a s -> Inf a (remove x s).
  Proof.
  simple induction s.  
  simpl; intuition.
  simpl; intros; case (ordCmp x a); intuition; inversion_clear H0; auto.
  inversion_clear Hs. apply Inf_lt with a; auto.
  Qed.
  Hint Resolve remove_Inf.

  Lemma remove_sort :
   forall (s : t) (Hs : Sort s) (x : elt), Sort (remove x s).
  Proof.
  simple induction s.
  simpl; intuition.
  simpl; intros; case (ordCmp x a); intuition; inversion_clear Hs; auto.
  Qed. 

 Lemma  Sort_Inf_In : forall l x a, Sort l -> Inf a l -> In x l -> ordLt a x.
 Proof.
  intros. eapply Sort_Inf_In; eauto.
 Qed.

  Lemma remove_1 :
   forall (s : t) (Hs : Sort s) (x y : elt),  x == y -> ~ In y (remove x s).
  Proof.
  simple induction s. 
  simpl; red; intros; inversion H0.
  simpl; intros; case (ordCmp x a); intuition; inversion_clear Hs. 
  inversion_clear H1. order.
  generalize (Sort_Inf_In H2 H3 H4). order.
  generalize (Sort_Inf_In H2 H3 H1). 
  rewrite <- H0. rewrite <- e. intros. order.
  inversion_clear H1.
  order.
  apply (H H2 _ _ H0 H4).
  Qed.

  Lemma remove_2 :
   forall (s : t) (Hs : Sort s) (x y : elt),
   ~ x == y -> In y s -> In y (remove x s).
  Proof.
  simple induction s. 
  simpl; intuition.
  simpl; intros; case (ordCmp x a); intuition; inversion_clear Hs;
   inversion_clear H1; auto. 
  destruct H0. rewrite e. symmetry. assumption.
  Qed.

  Lemma remove_3 :
   forall (s : t) (Hs : Sort s) (x y : elt), In y (remove x s) -> In y s.
  Proof.
  simple induction s. 
  simpl; intuition.
  simpl; intros a l Hrec Hs x y; case (ordCmp x a); intuition.
  inversion_clear Hs; inversion_clear H; auto.
  constructor 2; apply Hrec with x; auto.
  Qed.
  
  Lemma singleton_sort : forall x : elt, Sort (singleton x).
  Proof.
  unfold singleton; simpl; auto.
  Qed.

  Lemma singleton_1 : forall x y : elt, In y (singleton x) -> x == y.
  Proof.
  unfold singleton; simpl; intuition.
  inversion_clear H; auto. symmetry. assumption.
  inversion H0.
  Qed. 

  Lemma singleton_2 : forall x y : elt, x == y -> In y (singleton x).
  Proof.
  unfold singleton; intros; simpl; auto. constructor. symmetry. assumption.
  Qed. 

  Ltac DoubleInd :=
    simple induction s;
     [ simpl; auto; try solve [ intros; inversion H ]
     | intros x l Hrec; simple induction s';
        [ simpl; auto; try solve [ intros; inversion H ]
        | intros x' l' Hrec' Hs Hs'; inversion Hs; inversion Hs'; subst;
           simpl ] ].

  Lemma union_Inf :
   forall (s s' : t) (Hs : Sort s) (Hs' : Sort s') (a : elt),
   Inf a s -> Inf a s' -> Inf a (union s s').
  Proof.
  DoubleInd.
  intros i His His'; inversion_clear His; inversion_clear His'.
  case (ordCmp x x'); auto.
  Qed.
  Hint Resolve union_Inf.

  Lemma union_sort :
   forall (s s' : t) (Hs : Sort s) (Hs' : Sort s'), Sort (union s s').
  Proof.
  DoubleInd; case (ordCmp x x'); intuition; constructor; auto.
  apply Inf_eq with x'; trivial. apply union_Inf; trivial; apply Inf_eq with x; auto.
  symmetry. assumption. 
  change (Inf x' (union (x :: l) l')); auto.
  Qed.  
  
  Lemma union_1 :
   forall (s s' : t) (Hs : Sort s) (Hs' : Sort s') (x : elt),
   In x (union s s') -> In x s \/ In x s'.
  Proof.
  DoubleInd; case (ordCmp x x'); intuition; inversion_clear H; intuition.
  elim (Hrec (x' :: l') H1 Hs' x0); intuition.
  elim (Hrec l' H1 H5 x0); intuition.
  elim (H0 x0); intuition.
  Qed.

  Lemma union_2 :
   forall (s s' : t) (Hs : Sort s) (Hs' : Sort s') (x : elt),
   In x s -> In x (union s s').
  Proof.
  DoubleInd. 
  intros i Hi; case (ordCmp x x'); intuition; inversion_clear Hi; auto.
  Qed.

  Lemma union_3 :
   forall (s s' : t) (Hs : Sort s) (Hs' : Sort s') (x : elt),
   In x s' -> In x (union s s').
  Proof.
  DoubleInd. 
  intros i Hi; case (ordCmp x x'); inversion_clear Hi; intuition.
  constructor. rewrite H. symmetry. assumption.  
  Qed.
    
  Lemma inter_Inf :
   forall (s s' : t) (Hs : Sort s) (Hs' : Sort s') (a : elt),
   Inf a s -> Inf a s' -> Inf a (inter s s').
  Proof.
  DoubleInd.
  intros i His His'; inversion His; inversion His'; subst.
  case (ordCmp x x'); intuition. 
  apply Inf_lt with x; auto.
  apply H3; auto.
  apply Inf_lt with x'; auto.
  Qed.
  Hint Resolve inter_Inf. 

  Lemma inter_sort :
   forall (s s' : t) (Hs : Sort s) (Hs' : Sort s'), Sort (inter s s').
  Proof.
  DoubleInd; case (ordCmp x x'); auto.
  constructor; auto.
  apply Inf_eq with x'; trivial; apply inter_Inf; trivial; apply Inf_eq with x; auto.
  symmetry. assumption.
  Qed.  
  
  Lemma inter_1 :
   forall (s s' : t) (Hs : Sort s) (Hs' : Sort s') (x : elt),
   In x (inter s s') -> In x s.
  Proof.
  DoubleInd; case (ordCmp x x'); intuition.
  constructor 2; apply Hrec with (x'::l'); auto.
  inversion_clear H; auto.
  constructor 2; apply Hrec with l'; auto.
  Qed.

  Lemma inter_2 :
   forall (s s' : t) (Hs : Sort s) (Hs' : Sort s') (x : elt),
   In x (inter s s') -> In x s'.
  Proof.
  DoubleInd; case (ordCmp x x'); intuition; inversion_clear H.
  constructor 1. rewrite H3. assumption.
  constructor 2. apply Hrec; assumption.
  Qed.

  Lemma inter_3 :
   forall (s s' : t) (Hs : Sort s) (Hs' : Sort s') (x : elt),
   In x s -> In x s' -> In x (inter s s').
  Proof.
  DoubleInd.
  intros i His His'; elim (ordCmp x x'); intuition.

  inversion_clear His; auto.
  generalize (Sort_Inf_In Hs' (cons_leA _ _ _ _ l0) His'). order.

  inversion_clear His; auto; inversion_clear His'; auto.
  constructor. rewrite e. assumption.

  change (In i (inter (x :: l) l')). 
  inversion_clear His'; auto.
  generalize (Sort_Inf_In Hs (cons_leA _ _ _ _ l0) His). order.
  Qed.

  Lemma diff_Inf :
   forall (s s' : t) (Hs : Sort s) (Hs' : Sort s') (a : elt),
   Inf a s -> Inf a s' -> Inf a (diff s s').
  Proof.
  DoubleInd.
  intros i His His'; inversion His; inversion His'.
  case (ordCmp x x'); intuition.
  apply Hrec; trivial.
  apply Inf_lt with x; auto.
  apply Inf_lt with x'; auto.
  apply H10; trivial.
  apply Inf_lt with x'; auto.
  Qed.
  Hint Resolve diff_Inf. 

  Lemma diff_sort :
   forall (s s' : t) (Hs : Sort s) (Hs' : Sort s'), Sort (diff s s').
  Proof.
  DoubleInd; case (ordCmp x x'); auto.
  Qed.  
  
  Lemma diff_1 :
   forall (s s' : t) (Hs : Sort s) (Hs' : Sort s') (x : elt),
   In x (diff s s') -> In x s.
  Proof.
  DoubleInd; case (ordCmp x x'); intuition.
  inversion_clear H; auto.
  constructor 2; apply Hrec with (x'::l'); auto.
  constructor 2; apply Hrec with l'; auto.
  Qed.

  Lemma diff_2 :
   forall (s s' : t) (Hs : Sort s) (Hs' : Sort s') (x : elt),
   In x (diff s s') -> ~ In x s'.
  Proof.
    DoubleInd.
  intros; intro Abs; inversion Abs. 
  case (ordCmp x x'); intuition. 

  inversion_clear H.
  
  generalize (Sort_Inf_In Hs' (cons_leA ordLt _ _ _ o ) H3). order.
  apply Hrec with (x'::l') x0; auto.
  
  inversion_clear H3.
  generalize (Sort_Inf_In H1 H2 (diff_1 H1 H5 H)). rewrite H4. rewrite e. order.
  apply Hrec with l' x0; auto.
  
  inversion_clear H3. 
  generalize (Sort_Inf_In Hs (cons_leA ordLt _ _ l o) (diff_1 Hs H5 H)); order.
  apply H0 with x0; auto.
Qed.

  Lemma diff_3 :
   forall (s s' : t) (Hs : Sort s) (Hs' : Sort s') (x : elt),
   In x s -> ~ In x s' -> In x (diff s s').
  Proof.
  DoubleInd.
  intros i His His'; elim (ordCmp x x'); intuition; inversion_clear His; auto.
  elim His'; constructor. rewrite <- e. assumption.
  Qed.  

  Lemma equal_1 :
   forall (s s' : t) (Hs : Sort s) (Hs' : Sort s'),
   Equal s s' -> equal s s' = true.
  Proof.
  simple induction s; unfold Equal.
  intro s'; case s'; auto.
  simpl; intuition.
  elim (H e); intros; assert (A : In e nil). apply H1. 
  constructor. reflexivity. inversion A.
  intros x l Hrec s'.
  case s'.
  intros; elim (H x); intros; assert (A : In x nil). apply H0. 
  constructor. reflexivity. inversion A.
  intros x' l' Hs Hs'; inversion Hs; inversion Hs'; subst.
  simpl. case (ordCmp x x'); intros; auto.

  elim (H x); intros.
  assert (A : In x (x' :: l')). apply H0. constructor. reflexivity. inversion_clear A.
  rewrite H4 in o. order.
  generalize (Sort_Inf_In H5 H6 H4). order.
  
  apply Hrec; intuition; elim (H a); intros.
  assert (A : In a (x' :: l')); auto; inversion_clear A; auto.
  generalize (Sort_Inf_In H1 H2 H0). rewrite e. rewrite <- H7. order.
  assert (A : In a (x :: l)); auto; inversion_clear A; auto.
  generalize (Sort_Inf_In H5 H6 H0). order.

  elim (H x'); intros.
  assert (A : In x' (x :: l)). apply H3. constructor. reflexivity. inversion_clear A.
  rewrite H4 in o. order.
  generalize (Sort_Inf_In H1 H2 H4). order.
  Qed.

  Lemma equal_2 : forall s s' : t, equal s s' = true -> Equal s s'.
  Proof.
  simple induction s; unfold Equal.
  intro s'; case s'; intros.
  intuition.
  simpl in H; discriminate H.
  intros x l Hrec s'.
  case s'.
  intros; simpl in H; discriminate.
  intros x' l'; simpl; case (ordCmp x x'); intros; auto; try discriminate.
  elim (Hrec l' H a); intuition; inversion_clear H2; auto.
  constructor. rewrite H3. assumption.
  constructor. rewrite H3. symmetry. assumption.
  Qed.  
  
  Lemma subset_1 :
   forall (s s' : t) (Hs : Sort s) (Hs' : Sort s'),
   Subset s s' -> subset s s' = true.
  Proof.
  intros s s'; generalize s' s; clear s s'.
  simple induction s'; unfold Subset.
  intro s; case s; auto.
  intros; elim (H e); intros; assert (A : In e nil).
    apply H; constructor. reflexivity. inversion A.
    apply H. constructor. reflexivity. inversion A.
    apply H; constructor. reflexivity. inversion A.
  
  intros x' l' Hrec s; case s.
  simpl; auto.
  intros x l Hs Hs'; inversion Hs; inversion Hs'; subst.
  simpl; case (ordCmp x x'); intros; auto.

  assert (A : In x (x' :: l')). apply H. constructor. reflexivity. inversion_clear A.
  rewrite H0 in o. order.
  generalize (Sort_Inf_In H5 H6 H0). order.
  
  apply Hrec; intuition.
  assert (A : In a (x' :: l')); auto; inversion_clear A; auto.
  generalize (Sort_Inf_In H1 H2 H0). rewrite e. rewrite <- H3. order. 

  apply Hrec; intuition.
  assert (A : In a (x' :: l')); auto; inversion_clear A; auto.
  inversion_clear H0. rewrite <- H3 in o. rewrite <- H4 in o. order.
  generalize (Sort_Inf_In H1 H2 H4). order.
  Qed.

  Lemma subset_2 : forall s s' : t, subset s s' = true -> Subset s s'.
  Proof.
  intros s s'; generalize s' s; clear s s'.
  simple induction s'; unfold Subset.
  intro s; case s; auto.
  simpl; intros; discriminate H.
  intros x' l' Hrec s; case s.
  intros; inversion H0.
  intros x l; simpl; case (ordCmp x x'); intros; auto.
  discriminate H.  
  inversion_clear H0.
  constructor. rewrite H1. assumption.
  constructor 2; apply Hrec with l; auto.
  constructor 2; apply Hrec with (x::l); auto.
  Qed.  
  
  Lemma empty_sort : Sort empty.
  Proof.
  unfold empty; constructor.
  Qed.

  Lemma empty_1 : Empty empty.
  Proof.
  unfold Empty, empty; intuition; inversion H.
  Qed. 

  Lemma is_empty_1 : forall s : t, Empty s -> is_empty s = true.
  Proof.
  unfold Empty; intro s; case s; simpl; intuition.
  elim (H e); auto. constructor. reflexivity.
  Qed.
  
  Lemma is_empty_2 : forall s : t, is_empty s = true -> Empty s. 
  Proof.
  unfold Empty; intro s; case s; simpl; intuition;
   inversion H0.
  Qed.

  Lemma elements_1 : forall (s : t) (x : elt), In x s -> In x (elements s).
  Proof.
  unfold elements; auto.
  Qed.

  Lemma elements_2 : forall (s : t) (x : elt), In x (elements s) -> In x s.
  Proof. 
  unfold elements; auto.
  Qed.
 
  Lemma elements_3 : forall (s : t) (Hs : Sort s), Sort (elements s).  
  Proof. 
  unfold elements; auto.
  Qed.
(*
  Lemma elements_3w : forall (s : t) (Hs : Sort s), NoDupA equiv(elements s).  
  Proof. 
  unfold elements. intros. elim Hs. constructor. constructor. auto.
  Qed.
*)
  Lemma min_elt_1 : forall (s : t) (x : elt), min_elt s = Some x -> In x s. 
  Proof.
  intro s; case s; simpl; intros; inversion H; auto. constructor. reflexivity.
  Qed.  

  Lemma min_elt_2 :
   forall (s : t) (Hs : Sort s) (x y : elt),
   min_elt s = Some x -> In y s -> ~ ordLt y x. 
  Proof.
  simple induction s; simpl.
  intros; inversion H.
  intros a l; case l; intros; inversion H0; inversion_clear H1; subst. 
  order.
  inversion H2.
  order.
  inversion_clear Hs.
  inversion_clear H3.
  generalize (H H1 e y (refl_equal (Some e)) H2). order.
  Qed. 

  Lemma min_elt_3 : forall s : t, min_elt s = None -> Empty s.
  Proof.
  unfold Empty; intro s; case s; simpl; intuition;
   inversion H; inversion H0.
  Qed.

  Lemma max_elt_1 : forall (s : t) (x : elt), max_elt s = Some x -> In x s. 
  Proof. 
  simple induction s; simpl.
  intros; inversion H.
  intros x l; case l; simpl.
  intuition.
  inversion H0. constructor. reflexivity.
  intros.
  constructor 2. apply (H _ H0).
  Qed.
 
  Lemma max_elt_2 :
   forall (s : t) (Hs : Sort s) (x y : elt),
   max_elt s = Some x -> In y s -> ~ ordLt x y. 
  Proof.
  simple induction s; simpl.
  intros; inversion H.
  intros x l; case l; simpl.
  intuition.
  inversion H0; subst.
  inversion_clear H1.
  order.
  inversion H3.
  intros; inversion_clear Hs; inversion_clear H3; inversion_clear H1.
  assert (In e (e::l0)). constructor. reflexivity.
  generalize (H H2 x0 e H0 H1). order.
  generalize (H H2 x0 y H0 H3). order.
  Qed. 

  Lemma max_elt_3 : forall s : t, max_elt s = None -> Empty s.
  Proof.
  unfold Empty; simple induction s; simpl.
  red; intros; inversion H0.
  intros x l; case l; simpl; intros.
  inversion H0.
  elim (H H0 e); auto. constructor. reflexivity.
  Qed.

  Definition choose_1 :
    forall (s : t) (x : elt), choose s = Some x -> In x s := min_elt_1.

  Definition choose_2 : forall s : t, choose s = None -> Empty s := min_elt_3.

  Lemma choose_3: forall s s', Sort s -> Sort s' -> forall x x',
   choose s = Some x -> choose s' = Some x' -> Equal s s' -> x == x'.
  Proof.
   unfold choose, Equal; intros s s' Hs Hs' x x' Hx Hx' H.
   assert (~ordLt x x').
    apply min_elt_2 with s'; auto.
    rewrite <-H; auto using min_elt_1.
   assert (~ordLt x' x).
    apply min_elt_2 with s; auto.
    rewrite H; auto using min_elt_1.
   destruct (ordCmp x x'); intuition.
  Qed.
   
  Lemma fold_1 :
   forall (s : t) (Hs : Sort s) (A : Type) (i : A) (f : elt -> A -> A),
   fold _ f s i = fold_left (fun a e => f e a) (elements s) i.
  Proof.
  induction s.
  simpl; trivial.
  intros.
  inversion_clear Hs.
  simpl; auto.
  Qed.

  Lemma cardinal_1 :
   forall (s : t) (Hs : Sort s),
   cardinal s = length (elements s).
  Proof.
  auto.
  Qed.

  Lemma filter_Inf :
   forall (s : t) (Hs : Sort s) (x : elt) (f : elt -> bool),
   Inf x s -> Inf x (List.filter f s).
  Proof.
  simple induction s; simpl.
  intuition.  
  intros x l Hrec Hs a f Ha; inversion_clear Hs; inversion_clear Ha.
  case (f x). 
  constructor; auto.
  apply Hrec; auto.
  apply Inf_lt with x; auto.
  Qed.

  Lemma filter_sort :
   forall (s : t) (Hs : Sort s) (f : elt -> bool), Sort (List.filter f s).
  Proof.
  simple induction s; simpl.
  auto.
  intros x l Hrec Hs f; inversion_clear Hs.
  case (f x); auto.
  constructor; auto.
  apply filter_Inf; auto. 
  Qed.

  Lemma filter_1 :
   forall (s : t) (x : elt) (f : elt -> bool),
   compat_bool equiv f -> In x (List.filter f s) -> In x s.
  Proof.
  simple induction s; simpl.
  intros; inversion H0.
  intros x l Hrec a f Hf.
  case (f x); simpl.
  inversion_clear 1.
  constructor; auto.
  constructor 2; apply (Hrec a f Hf); trivial.
  constructor 2; apply (Hrec a f Hf); trivial.
  Qed.

   Lemma filter_2 :
    forall (s : t) (x : elt) (f : elt -> bool),
    compat_bool equiv f -> In x (List.filter f s) -> f x = true.   
   Proof.
  simple induction s; simpl.
  intros; inversion H0.
  intros x l Hrec a f Hf.
  generalize (Hf x); case (f x); simpl; auto.
  inversion_clear 2; auto.
  symmetry; auto. apply H. symmetry. assumption.
  Qed.
 
  Lemma filter_3 :
   forall (s : t) (x : elt) (f : elt -> bool),
   compat_bool equiv f -> In x s -> f x = true -> In x (List.filter f s).     
  Proof.
  simple induction s; simpl.
  intros; inversion H0.
  intros x l Hrec a f Hf.
  generalize (Hf x); case (f x); simpl.
  inversion_clear 2; auto.
  inversion_clear 2; auto.
  symmetry in H1.
  rewrite <- (H a ( H1)); intros; discriminate.
  Qed.

  Lemma for_all_1 :
   forall (s : t) (f : elt -> bool),
   compat_bool equiv f ->
   For_all (fun x => f x = true) s -> for_all f s = true.
  Proof. 
  simple induction s; simpl; auto; unfold For_all.
  intros x l Hrec f Hf. 
  generalize (Hf x); case (f x); simpl.
  auto.
  intros; rewrite (H x); auto. rewrite H0. trivial. constructor. reflexivity. reflexivity.
  Qed.

  Lemma for_all_2 :
   forall (s : t) (f : elt -> bool),
   compat_bool equiv f ->
   for_all f s = true -> For_all (fun x => f x = true) s.
  Proof. 
  simple induction s; simpl; auto; unfold For_all.
  intros; inversion H1.
  intros x l Hrec f Hf. 
  intros A a; intros. 
  assert (f x = true).
   generalize A; case (f x); auto.
  rewrite H0 in A; simpl in A.
  inversion_clear H; auto.
  rewrite (Hf a x); auto.
  Qed.

  Lemma exists_1 :
   forall (s : t) (f : elt -> bool),
   compat_bool equiv f -> Exists (fun x => f x = true) s -> exists_ f s = true.
  Proof.
  simple induction s; simpl; auto; unfold Exists.
  intros.
  elim H0; intuition. 
  inversion H2.
  intros x l Hrec f Hf. 
  generalize (Hf x); case (f x); simpl.
  auto.
  destruct 2 as [a (A1,A2)].
  inversion_clear A1. symmetry in H0.
  rewrite <- (H a (H0)) in A2; discriminate.
  apply Hrec; auto.
  exists a; auto.
  Qed.

  Lemma exists_2 :
   forall (s : t) (f : elt -> bool),
   compat_bool equiv f -> exists_ f s = true -> Exists (fun x => f x = true) s.
  Proof. 
  simple induction s; simpl; auto; unfold Exists.
  intros; discriminate.
  intros x l Hrec f Hf.
  case_eq (f x); intros.
  exists x; auto. split. constructor. reflexivity. assumption.
  destruct (Hrec f Hf H0) as [a (A1,A2)].
  exists a; auto.
  Qed.

  Lemma partition_Inf_1 :
   forall (s : t) (Hs : Sort s) (f : elt -> bool) (x : elt),
   Inf x s -> Inf x (fst (partition f s)).
  Proof.
  simple induction s; simpl.
  intuition.  
  intros x l Hrec Hs f a Ha; inversion_clear Hs; inversion_clear Ha.
  generalize (Hrec H f a).
  case (f x); case (partition f l); simpl.
  auto.
  intros; apply H2; apply Inf_lt with x; auto.
  Qed.

  Lemma partition_Inf_2 :
   forall (s : t) (Hs : Sort s) (f : elt -> bool) (x : elt),
   Inf x s -> Inf x (snd (partition f s)).
  Proof.
  simple induction s; simpl.
  intuition.  
  intros x l Hrec Hs f a Ha; inversion_clear Hs; inversion_clear Ha.
  generalize (Hrec H f a).
  case (f x); case (partition f l); simpl.
  intros; apply H2; apply Inf_lt with x; auto.
  auto.
  Qed.

  Lemma partition_sort_1 :
   forall (s : t) (Hs : Sort s) (f : elt -> bool), Sort (fst (partition f s)).
  Proof.
  simple induction s; simpl.
  auto.
  intros x l Hrec Hs f; inversion_clear Hs.
  generalize (Hrec H f); generalize (partition_Inf_1 H f).
  case (f x); case (partition f l); simpl; auto.
  Qed.
  
  Lemma partition_sort_2 :
   forall (s : t) (Hs : Sort s) (f : elt -> bool), Sort (snd (partition f s)).
  Proof.
  simple induction s; simpl.
  auto.
  intros x l Hrec Hs f; inversion_clear Hs.
  generalize (Hrec H f); generalize (partition_Inf_2 H f).
  case (f x); case (partition f l); simpl; auto.
  Qed.

  Lemma partition_1 :
   forall (s : t) (f : elt -> bool),
   compat_bool equiv f -> Equal (fst (partition f s)) (List.filter f s).
  Proof.
  simple induction s; simpl; auto; unfold Equal.
  split; auto.
  intros x l Hrec f Hf.
  generalize (Hrec f Hf); clear Hrec.
  destruct (partition f l) as [s1 s2]; simpl; intros.
  case (f x); simpl; auto.
  split; inversion_clear 1; auto.
  constructor 2; rewrite <- H; auto.
  constructor 2; rewrite H; auto.
  Qed.
   
  Lemma partition_2 :
   forall (s : t) (f : elt -> bool),
   compat_bool equiv f ->
   Equal (snd (partition f s)) (List.filter (fun x => negb (f x)) s).
  Proof.
  simple induction s; simpl; auto; unfold Equal.
  split; auto.
  intros x l Hrec f Hf. 
  generalize (Hrec f Hf); clear Hrec.
  destruct (partition f l) as [s1 s2]; simpl; intros.
  case (f x); simpl; auto.
  split; inversion_clear 1; auto.
  constructor 2; rewrite <- H; auto.
  constructor 2; rewrite H; auto.
  Qed.
 
  Definition eq : t -> t -> Prop := Equal.

  Lemma eq_refl : forall s : t, eq s s. 
  Proof. 
  unfold eq, Equal; intuition.
  Qed.

  Lemma eq_sym : forall s s' : t, eq s s' -> eq s' s.
  Proof. 
  unfold eq, Equal; intros; destruct (H a); intuition.
  Qed.

  Lemma eq_trans : forall s s' s'' : t, eq s s' -> eq s' s'' -> eq s s''.
  Proof. 
  unfold eq, Equal; intros; destruct (H a); destruct (H0 a); intuition.
  Qed.

  Inductive lt : t -> t -> Prop :=
    | lt_nil : forall (x : elt) (s : t), lt nil (x :: s)
    | lt_cons_lt :
        forall (x y : elt) (s s' : t), ordLt x y -> lt (x :: s) (y :: s')
    | lt_cons_eq :
        forall (x y : elt) (s s' : t),
        ordLt x y -> lt s s' -> lt (x :: s) (y :: s').
  Hint Constructors lt.
   
 Lemma ordlt_trans : forall x y z, x << y -> y << z -> x << z.
 intros. order.
 Qed.

  Lemma lt_trans : forall s s' s'' : t, lt s s' -> lt s' s'' -> lt s s''.
  Proof. 
  intros s s' s'' H; generalize s''; clear s''; elim H.
  intros x l s'' H'; inversion_clear H'; auto.
  intros x x' l l' E s'' H'; inversion_clear H'; auto. 
  constructor. apply ordlt_trans with x'; auto.
  constructor. apply ordlt_trans with x'; auto.
  intros.
  inversion_clear H3.
  constructor; apply ordlt_trans with y; auto.
  constructor 3; auto; apply ordlt_trans with y; auto.  
  Qed. 

  Lemma lt_not_eq :
   forall (s s' : t) (Hs : Sort s) (Hs' : Sort s'), lt s s' -> ~ eq s s'.
  Proof.
    intros. intro.
    assert (eql:eqlistA (@equiv elt (@ordEq elt X)) s s').
    eapply SortA_equivlistA_eqlistA with (ltA := ordLt); intuition; clsubst*; intuition; order.
    induction s; destruct s'; inversion H; inversion eql; subst.
    rewrite H9 in H2. order.
    rewrite H10 in H4. order.
  Qed.

Lemma In_eq : forall l x y, x == y -> In x l -> In y l.
 intros. unfold "==" in *. destruct X. simpl in *.
 destruct setoid_equiv.  destruct ordEq.
  simpl in *.
  apply (@InA_eqA elt equiv Equivalence_Symmetric 
         Equivalence_Transitive l x y H).
  assumption.
Qed.

  End ForNotations. 
  Hint Constructors lt.

End Raw.

Section slist.
Variable (elt:Set).
Context {eltO:OrderedType elt}.

Record slist := MK {this :> list elt; sorted : sort ordLt this}.

Definition slist_Equal (s s' : slist) :=
      forall a : elt,
      (@InA elt (@equiv elt (@ordEq elt eltO)) a (this s)) <->
      (@InA elt (@equiv elt (@ordEq elt eltO)) a (this s')).

Instance slist_Equal_equiv : Equivalence (slist_Equal).
  split; red; unfold Equal; firstorder.
Qed.

Fixpoint ltlistA {A:Type} (eqA ltA : relation A) l1 l2 {struct l1} : Prop := 
  match (l1, l2) with 
    | ([], []) => False
    | ([], _) => True
    | (_, []) => False
    | (x1::l1', x2::l2') => (ltA x1 x2) \/
                            ((eqA x1 x2) /\ ltlistA eqA ltA l1' l2')
  end.

Lemma ltlistA_trans {A:Set} {O:OrderedType A} : Transitive (ltlistA (A:=A) equiv ordLt).
Proof.
  red.
  induction x; destruct y; destruct z; simpl; intuition; try solve[order].
  clsubst*. firstorder.
Qed.

Lemma ltlistA_not_eqlistA {A:Set} {O:OrderedType A} 
  : forall x y : list A, ltlistA equiv ordLt x y -> complement (eqlistA equiv) x y.
Proof. unfold complement.
  induction x; destruct y; simpl; intuition; inversion H0; subst; firstorder.
  rewrite H4 in H1. order.
Qed.

Definition slist_Equal_set : Setoid slist := Build_Setoid slist_Equal_equiv.

Definition slist_lt (a b : slist)
  := match a , b with
       | MK a a' , MK b b' => ltlistA equiv ordLt a b
     end.

Definition list_compare {A} {O:OrderedType A} (x y : list A) : Compare (ltlistA equiv ordLt) (@Equal A O) x y.
Proof.
  refine (fix list_compare {A:Set} O (x y : list A) : Compare (ltlistA equiv ordLt) (@Equal A O) x y 
    := match x, y with
         | [], [] => EQ _ _
         | [], _ => LT _ _
         | _, [] => GT _ _
         | a::xs, b::ys => 
           match ordCompare a b with
             | LT _ => LT _ _
             | EQ _ => match list_compare A O xs ys with
                         | LT _ => LT _ _
                         | EQ _ => EQ _ _
                         | GT _ => GT _ _
                       end
             | GT _ => GT _ _
           end
       end); simpl; unfold Equal in *; intuition.
inversion H.
 subst. left. rewrite H1. auto.
 firstorder.
inversion H.
 subst. left. rewrite e. auto.
 firstorder.
Qed.

Definition slist_compare (x y : slist) : Compare slist_lt slist_Equal x y.
Proof.
intros. unfold slist_Equal, slist_lt. destruct x; destruct y.
destruct (list_compare this0 this1);
  [apply LT|apply EQ|apply GT]; auto.
Qed.

Lemma slist_lt_Transitive : Transitive slist_lt.
Proof.
  red. destruct x; destruct y; destruct z.
  simpl. apply ltlistA_trans.
Qed.

Global Instance slist_order : OrderedType slist :=
{ordEq := slist_Equal_set; 
 ordLt := slist_lt;
 ordCompare := slist_compare;
 ordLt_trans := slist_lt_Transitive}.
unfold complement; destruct x; destruct y. simpl. 
intros.
cut (eqlistA equiv this0 this1). apply (ltlistA_not_eqlistA _ _ H). clear H.

eapply SortA_equivlistA_eqlistA; intuition; try eassumption;
  clsubst*; unfold flip in *; clsubst*; intuition; order. 
Defined.

(** * Encapsulation

   Now, in order to really provide a functor implementing [S], we 
   need to encapsulate everything into a type of strictly ordered lists. *)

 Instance Make : FSetInterfaceNM eltO := 
 {  t := slist;
 
  In := fun x s => (@InA elt 
    (@equiv elt (@ordEq elt eltO)) x s ) ;

  empty := @MK nil (@empty_sort elt eltO) ;

  is_empty := fun s => is_empty elt s ;

  mem  := fun x s => mem elt x s ;

  add  := fun x s => MK (add elt x s) (@add_sort elt eltO s (sorted s) x) ;

  singleton  := fun x => MK (singleton elt x) (singleton_sort x) ;

  remove  := fun x s => MK (remove elt x s) (remove_sort (sorted  s) x) ;

  union  := fun s1 s2 => MK (union elt s1 s2) (union_sort (sorted s1) (sorted s2));

  inter  := fun s s' => MK (inter elt s s') (inter_sort (sorted s) (sorted s')); 

  diff  := fun s s' => MK (diff elt s s') (diff_sort (sorted s) (sorted s'));

  equal  := fun s s' => equal elt s s';

  subset  := fun s s' => subset elt s s' ;

  fold  := fun B f s => fold elt B f s;

  for_all  := fun (f: elt -> bool) s => for_all elt f s;

  exists_   := fun (f: elt -> bool) s => exists_ elt f s ;

  filter  := fun f s => MK (List.filter  f s) 
   (filter_sort  (sorted s) f) ;

  partition  := fun f s => let p := partition elt f s in 
                            (MK (fst p) (partition_sort_1 (sorted s) f),
                             MK (snd p) (partition_sort_2 (sorted s) f)) ;

  cardinal  := fun s => cardinal elt s ;

  elements  := fun s => elements elt s ;

  choose  := fun s => choose elt s ;

  min_elt  := fun s => min_elt elt s;

  max_elt  := fun s => max_elt elt s ;


    In_1  := _ ;

   mem_1  := _;
   mem_2  := _; 
 
   equal_1  := _;
   equal_2  :=  _;

   subset_1  :=  _;
   subset_2  :=  _;

   empty_1  :=  _;

   is_empty_1  :=  _;
   is_empty_2  :=  _;
 
   add_1  :=  _;
   add_2  :=  _;
   add_3  :=  _;

   remove_1  := _;
   remove_2  := _;
   remove_3  := _;

   singleton_1  := _;
   singleton_2  := _; 

   union_1  :=  _;
   union_2  :=  _;
   union_3  :=  _;

   inter_1  := _;
   inter_2  := _;
   inter_3  := _;

   diff_1  := _;
   diff_2  := _;
   diff_3  := _;
 
   fold_1  :=  _;

   cardinal_1  :=  _;

   filter_1  := _;
   filter_2  := _;
   filter_3  := _;

   for_all_1  := _;
   for_all_2  := _;

   exists_1  := _;
   exists_2  := _;

   partition_1  := _;
   partition_2  := _;

   elements_1  := _;
   elements_2  := _;
   elements_3  := _;

   min_elt_1  := _;
   min_elt_2  := _;
   min_elt_3  := _;

   max_elt_1  := _;
   max_elt_2  := _;
   max_elt_3  := _;

   choose_1  := _;
   choose_2  := _ ;

  ordT  := slist_order;

  equivIsEqual := _

}.
 reflexivity.


 (* In_1   *)
 intros.
 apply (@ In_eq elt eltO s x y); assumption. 

 (* mem_1 *)
 intros. apply (@ mem_1 elt eltO). apply (sorted s). assumption.

 (* mem_2 *)
 intros. apply (@ mem_2 elt eltO). assumption.

 (* equal_1 *)
 intros. apply equal_1; try assumption.
 exact (sorted s). exact (sorted s').

 (* equal_2 *)
  intros. apply equal_2; try assumption.

 (* subset_1 *)
   intros. apply subset_1; try assumption.
  exact (sorted s). exact (sorted s').

 (* subset_2 *)
  intros.
  pose subset_2. unfold Subset in s0. 
  apply (@s0 elt eltO s s' H a H0).

 (*  empty_1 *)
  apply empty_1.

 (* is_empty_1 *) 
  pose is_empty_1. intros. eapply e. exact H.
 
 (* is_empty_2 *)
 intros. pose (@is_empty_2 elt eltO s). unfold Empty in *. apply e. assumption.

 (* add_1 *)
 intros. apply add_1. exact (sorted s).
  unfold equiv in *. destruct eltO. destruct ordEq.
 unfold "==" in *. assumption. 
 
 (* add_2 *)
 intros. apply add_2. exact (sorted s). assumption.
 
 (* add_3 *)
 intros. eapply add_3. exact (sorted s).
  unfold equiv in *. destruct ordEq. eauto. eauto.
 
 (* remove_1 *)
 intros. apply remove_1. exact (sorted s).
 unfold equiv in *. destruct eltO. destruct ordEq.
 unfold "==" in *. simpl in H. eauto. eauto. 

 (* remove_2 *)
 intros. apply remove_2. exact (sorted s).
 unfold equiv in *. destruct eltO. destruct ordEq.
 unfold "==" in *. simpl in H. eauto. eauto. 

 (* remove_3 *) 
 intros. eapply remove_3. exact (sorted s).
 unfold equiv in *. destruct ordEq.
 unfold "==" in *. simpl in H. eauto.  

 (* singleton_1 *)
 intros.  pose (@singleton_1 elt eltO x y H).
  unfold "==" in *. simpl in H.
  apply e.

 (* singleton_2 *)
 intros. apply singleton_2. auto.

 (* union_1 *)
 intros. apply union_1. apply (sorted s). apply (sorted s'). assumption. 

 (* union_2 *)
 intros. apply union_2. apply (sorted s). apply (sorted s'). assumption.

 (* union_3 *)
 intros. apply union_3. apply (sorted s). apply (sorted s'). assumption.

 (* inter_1 *)
 intros. eapply inter_1. apply (sorted s). apply (sorted s'). assumption.

 (* inter_2 *)
 intros. eapply inter_2. apply (sorted s). apply (sorted s'). assumption.

 (* inter_3 *)
 intros. eapply inter_3. apply (sorted s). apply (sorted s'). assumption. assumption.

 (* diff_1 *)
 intros. eapply diff_1. apply (sorted s). apply (sorted s'). assumption.

 (* diff_2 *)
 intros. eapply diff_2. apply (sorted s). apply (sorted s'). assumption.

 (* diff_3 *) 
 intros. eapply diff_3. apply (sorted s). apply (sorted s'). assumption. assumption.

 (* fold_1 *)
 intros. eapply fold_1. apply (sorted s). 

 (* cardinal_1 *)
 intros. eapply cardinal_1. apply (sorted s).

 (* filter_1 *)
 intros. eapply filter_1. eauto. simpl in *. assumption.

 (* filter_2 *)
 intros. eapply filter_2.
 unfold compat_bool. intros. apply (H x0 y). 
  unfold "==" in *. 
 unfold equiv in *. destruct ordEq.
 simpl in H. assumption.  eassumption.

 (* filter_3 *)
 intros. eapply filter_3.
 unfold compat_bool. intros. apply (H x0 y). 
  unfold "==" in *. 
 unfold equiv in *. destruct eltO. destruct ordEq.
 simpl in H. assumption.  eassumption. assumption.
 
 (* forall_1 *)
 intros. eapply for_all_1.
 unfold compat_bool. intros. apply (H x y). 
  unfold "==" in *. 
 unfold equiv in *. destruct eltO. destruct ordEq.
 simpl in H. assumption.  eassumption. 

 (* forall_2 *)
 intros. eapply for_all_2.
 unfold compat_bool. intros. apply (H x0 y). 
  unfold "==" in *. 
 unfold equiv in *. destruct eltO. destruct ordEq.
 simpl in H. assumption.  eassumption.  assumption.

 (* exists_1 *)
 intros. eapply exists_1.
 unfold compat_bool. intros. apply (H x y). 
  unfold "==" in *. 
 unfold equiv in *. destruct eltO. destruct ordEq.
 simpl in H. assumption.  eassumption. 

 (* exists_2 *)
 intros. eapply exists_2.
 unfold compat_bool. intros. apply (H x y). 
  unfold "==" in *. 
 unfold equiv in *. destruct eltO. destruct ordEq.
 simpl in H. assumption.  eassumption. 

 (* partition_1 *)
 intros. pose partition_1. unfold Equal in *. intros. 
 simpl in *. apply e.
 unfold compat_bool. intros. apply (H x y). 
  unfold "==" in *. 
 unfold equiv in *. destruct eltO. destruct ordEq.
 simpl in H. assumption.  

 (* partition_2 *)
 intros. pose partition_2. unfold Equal in *. intros. 
 simpl in *. apply e.
 unfold compat_bool. intros. apply (H x y). 
  unfold "==" in *. 
 unfold equiv in *. destruct eltO. destruct ordEq.
 simpl in H. assumption.  

(* elements_1 *)
intros. pose elements_1.
unfold SetoidClass.equiv. 
 pose (i elt eltO s x H). unfold equiv in *. destruct eltO.
 destruct ordEq. simpl. assumption.

(* elements_2 *)
intros. pose elements_2.
unfold SetoidClass.equiv in *. 
unfold equiv in *. apply i. clear i. destruct eltO.
  destruct ordEq. simpl in *. assumption.

(* elements_3 *)
intros. unfold elements. apply (sorted s).

(* min_elt 1 *)
intros. apply min_elt_1. assumption.

(* min_elt 2 *)
intros. eapply min_elt_2 . apply (sorted s). assumption. assumption.

(* min_elt 3 *)
intros. eapply min_elt_3. assumption.

(* max_elt 1 *)
intros. apply max_elt_1. assumption.

(* max_elt 2 *)
intros. eapply max_elt_2 . apply (sorted s). assumption. assumption.

(* max_elt 3 *)
intros. eapply max_elt_3. assumption.

(* choose_1 *)
intros. apply choose_1. assumption.

(* choose_2 *)
intros. apply choose_2. assumption.

Qed.

End slist.
