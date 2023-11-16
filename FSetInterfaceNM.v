(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id: FSetInterface.v 8820 2006-05-15 11:44:05Z letouzey $ *)

(** * Finite set library *)

(** Set interfaces *)

(* begin hide *)
Require Export Bool.
Require Import OrderedType.
Require Import OrderedTypeNM.
Set Implicit Arguments.
Unset Strict Implicit.
(* end hide *)

(** * Non-dependent signature

    Signature [S] presents sets as purely informative programs 
    together with axioms *)

Class FSetInterfaceNM (elt:Set) (E : OrderedType elt) : Type := {
  t : Set; (** the abstract type of sets *)

  (** Logical predicates *)
  In : elt -> t -> Prop;
  Equal := fun s s' => forall a : elt, In a s <-> In a s';
  Subset := fun s s' => forall a : elt, In a s -> In a s';
  Empty := fun s => forall a : elt, ~ In a s;
  For_all := fun (P : elt -> Prop) s => forall x, In x s -> P x;
  Exists := fun (P : elt -> Prop) s => exists x, In x s /\ P x;
  
  empty : t;
  (** The empty set. *)

  is_empty : t -> bool;
  (** Test whether a set is empty or not. *)

  mem : elt -> t -> bool;
  (** [mem x s] tests whether [x] belongs to the set [s]. *)

  add : elt -> t -> t;
  (** [add x s] returns a set containing all elements of [s],
  plus [x]. If [x] was already in [s], [s] is returned unchanged. *)

  singleton : elt -> t;
  (** [singleton x] returns the one-element set containing only [x]. *)

  remove : elt -> t -> t;
  (** [remove x s] returns a set containing all elements of [s],
  except [x]. If [x] was not in [s], [s] is returned unchanged. *)

  union : t -> t -> t;
  (** Set union. *)

  inter : t -> t -> t;
  (** Set intersection. *)

  diff : t -> t -> t;
  (** Set difference. *)

  ordT :> OrderedType t;
  equivIsEqual : equiv = Equal;
(*  eq : t -> t -> Prop := Equal;
  lt : t -> t -> Prop; 
  compare : forall s s' : t, Compare ordLt eq s s'; *)
  (** Total ordering between sets. Can be used as the ordering function
  for doing sets of sets. *)

  equal : t -> t -> bool;
  (** [equal s1 s2] tests whether the sets [s1] and [s2] are
  equal, that is, contain equal elements. *)

  subset : t -> t -> bool;
  (** [subset s1 s2] tests whether the set [s1] is a subset of
  the set [s2]. *)

  (** Coq comment: [iter] is useless in a purely functional world *)
  (**  iter: (elt -> unit) -> set -> unit. i*)
  (** [iter f s] applies [f] in turn to all elements of [s].
  The order in which the elements of [s] are presented to [f]
  is unspecified. *)

  fold : forall A : Set, (elt -> A -> A) -> t -> A -> A;
  (** [fold f s a] computes [(f xN ... (f x2 (f x1 a))...)],
  where [x1 ... xN] are the elements of [s], in increasing order. *)

  for_all : (elt -> bool) -> t -> bool;
  (** [for_all p s] checks if all elements of the set
  satisfy the predicate [p]. *)

  exists_ : (elt -> bool) -> t -> bool;
  (** [exists p s] checks if at least one element of
  the set satisfies the predicate [p]. *)

  filter : (elt -> bool) -> t -> t;
  (** [filter p s] returns the set of all elements in [s]
  that satisfy predicate [p]. *)

  partition : (elt -> bool) -> t -> t * t;
  (** [partition p s] returns a pair of sets [(s1, s2)], where
  [s1] is the set of all the elements of [s] that satisfy the
  predicate [p], and [s2] is the set of all the elements of
  [s] that do not satisfy [p]. *)

  cardinal : t -> nat;
  (** Return the number of elements of a set. *)
  (** Coq comment: nat instead of int ... *)

  elements : t -> list elt;
  (** Return the list of all elements of the given set.
  The returned list is sorted in increasing order with respect
  to the ordering [Ord.compare], where [Ord] is the argument
  given to {!Set.Make}. *)

  min_elt : t -> option elt;
  (** Return the smallest element of the given set
  (with respect to the [Ord.compare] ordering), or raise
  [Not_found] if the set is empty. *)
  (** Coq comment: [Not_found] is represented by the option type *)

  max_elt : t -> option elt;
  (** Same as {!Set.S.min_elt}, but returns the largest element of the
  given set. *)
  (** Coq comment: [Not_found] is represented by the option type *)

  choose : t -> option elt;
  (** Return one element of the given set, or raise [Not_found] if
  the set is empty. Which element is chosen is unspecified,
  but equal elements will be chosen for equal sets. *)
  (** Coq comment: [Not_found] is represented by the option type *)

  (** Specification of [In] *)
   In_1 : forall s x y, x == y -> In x s -> In y s;
 
(*
  (** Specification of [eq] *)
   eq_refl : forall s, eq s s;
   eq_sym : forall s s', eq s s' -> eq s' s;
   eq_trans : forall s s' s'', eq s s' -> eq s' s'' -> eq s s'';
 
  (** Specification of [lt] *)
   lt_trans : forall s s' s'', lt s s' -> lt s' s'' -> lt s s'';
   lt_not_eq : forall s s', lt s s' -> ~ eq s s';
*)
  (** Specification of [mem] *)
   mem_1 : forall s x, In x s -> mem x s = true;
   mem_2 : forall s x, mem x s = true -> In x s; 
 
  (** Specification of [equal] *) 
   equal_1 : forall s s', Equal s s' -> equal s s' = true;
   equal_2 : forall s s', equal s s' = true ->Equal s s';

  (** Specification of [subset] *)
   subset_1 : forall s s', Subset s s' -> subset s s' = true;
   subset_2 : forall s s', subset s s' = true -> Subset s s';

  (** Specification of [empty] *)
   empty_1 : Empty empty;

  (** Specification of [is_empty] *)
   is_empty_1 : forall s, Empty s -> is_empty s = true;
   is_empty_2 : forall s, is_empty s = true -> Empty s;
 
  (** Specification of [add] *)
   add_1 : forall s x y,  x == y -> In y (add x s);
   add_2 : forall s x y, In y s -> In y (add x s);
   add_3 : forall s x y,  x =/= y -> In y (add x s) -> In y s;

  (** Specification of [remove] *)
   remove_1 : forall s x y, x == y -> ~ In y (remove x s);
   remove_2 : forall s x y, x =/= y -> In y s -> In y (remove x s);
   remove_3 : forall s x y, In y (remove x s) -> In y s;

  (** Specification of [singleton] *)
   singleton_1 : forall x y, In y (singleton x) -> x == y;
   singleton_2 : forall x y, x == y -> In y (singleton x); 

  (** Specification of [union] *)
   union_1 : forall s s' x, In x (union s s') -> In x s \/ In x s';
   union_2 : forall s s' x, In x s -> In x (union s s');
   union_3 : forall s s' x, In x s' -> In x (union s s');

  (** Specification of [inter] *)
   inter_1 : forall s s' x, In x (inter s s') -> In x s;
   inter_2 : forall s s' x, In x (inter s s') -> In x s';
   inter_3 : forall s s' x, In x s -> In x s' -> In x (inter s s');

  (** Specification of [diff] *)
   diff_1 : forall s s' x, In x (diff s s') -> In x s;
   diff_2 : forall s s' x, In x (diff s s') -> ~ In x s';
   diff_3 : forall s s' x, In x s -> ~ In x s' -> In x (diff s s');
 
  (** Specification of [fold] *)  
   fold_1 : forall s (A : Set) (i : A) (f : elt -> A -> A),
      fold f s i = fold_left (fun a e => f e a) (elements s) i;

  (** Specification of [cardinal] *)  
   cardinal_1 : forall s, cardinal s = length (elements s);

    (** Specification of [filter] *)
   filter_1 : forall s x (f : elt -> bool), Proper (equiv ==> equiv) f -> In x (filter f s) -> In x s;
   filter_2 : forall s x (f : elt -> bool), Proper (equiv ==> equiv) f -> In x (filter f s) -> f x = true;
   filter_3 : forall s x (f : elt -> bool), 
      Proper (equiv ==> equiv) f -> In x s -> f x = true -> In x (filter f s);

  (** Specification of [for_all] *)
   for_all_1 : forall s (f : elt -> bool), 
      Proper (equiv ==> equiv) f ->
      For_all (fun x => f x = true) s -> for_all f s = true;
   for_all_2 : forall s (f : elt -> bool), 
      Proper (equiv ==> equiv) f ->
      for_all f s = true -> For_all (fun x => f x = true) s;

  (** Specification of [exists] *)
   exists_1 : forall s (f : elt -> bool), 
      Proper (equiv ==> equiv) f ->
      Exists (fun x => f x = true) s -> exists_ f s = true;
   exists_2 : forall s (f : elt -> bool), 
      Proper (equiv ==> equiv) f ->
      exists_ f s = true -> Exists (fun x => f x = true) s;

  (** Specification of [partition] *)
   partition_1 : forall s (f : elt -> bool), Proper (equiv ==> equiv) f -> 
      Equal (fst (partition f s)) (filter f s);
   partition_2 : forall s (f : elt -> bool), Proper (equiv ==> equiv) f -> 
      Equal (snd (partition f s)) (filter (fun x => negb (f x)) s);

  (** Specification of [elements] *)
   elements_1 : forall s x, In x s -> InA equiv x (elements s);
   elements_2 : forall s x, InA equiv x (elements s) -> In x s;
   elements_3 : forall s, sort ordLt (elements s);

  (** Specification of [min_elt] *)
   min_elt_1 : forall s x, min_elt s = Some x -> In x s;
   min_elt_2 : forall s x y, min_elt s = Some x -> In y s -> ~ y << x;
   min_elt_3 : forall s, min_elt s = None -> Empty s;

  (** Specification of [max_elt] *)  
   max_elt_1 : forall s x, max_elt s = Some x -> In x s;
   max_elt_2 : forall s x y, max_elt s = Some x -> In y s -> ~ x << y;
   max_elt_3 : forall s, max_elt s = None -> Empty s;

  (** Specification of [choose] *)
   choose_1 : forall s x, choose s = Some x -> In x s;
   choose_2 : forall s, choose s = None -> Empty s}.

(*   choose_equal: 
      (equal s s')=true -> E.eq (choose s) (choose s'). *)

  (* begin hide *)
  Hint Immediate @In_1.

  Hint Resolve @mem_1 @mem_2 @equal_1 @equal_2 @subset_1 @subset_2 @empty_1
    @is_empty_1 @is_empty_2 @choose_1 @choose_2 @add_1 @add_2 @add_3 @remove_1
    @remove_2 @remove_3 @singleton_1 @singleton_2 @union_1 @union_2 @union_3 @inter_1
    @inter_2 @inter_3 @diff_1 @diff_2 @diff_3 @filter_1 @filter_2 @filter_3 @for_all_1
    @for_all_2 @exists_1 @exists_2 @partition_1 @partition_2 @elements_1 @elements_2
    @elements_3 @min_elt_1 @min_elt_2 @min_elt_3 @max_elt_1 @max_elt_2 @max_elt_3.

  (* end hide *)

(* This should turn over to == *)
Notation "s [=] t" := (Equal s t) (at level 70, no associativity).
Notation "s [<=] t" := (Subset s t) (at level 70, no associativity).

Lemma filter_imp elt (E:OrderedType elt) (F:FSetInterfaceNM E) f1 f2 : 
  Proper (equiv ==> equiv) f1 -> Proper (equiv ==> equiv) f2 -> 
  (forall x, f1 x = true -> f2 x = true) ->
  forall R, (filter f1 R) [<=] (@filter _ _ F f2 R).
Proof.
  unfold Subset. intros.
  apply filter_3; auto.
  eauto.
  apply H1.
  eapply filter_2 with (x:=a); eauto.
Qed.

