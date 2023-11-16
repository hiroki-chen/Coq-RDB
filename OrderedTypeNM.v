(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id: OrderedType.v 10616 2008-03-04 17:33:35Z letouzey $ *)

Require Export SetoidList.
Require Export OrderedType.
Set Implicit Arguments.
Unset Strict Implicit.

(* Require Import Setoid. *)
Require Import Decidable.
Require Export SetoidClass.
Require Export SetoidDec.
Require Export Functions.
Require Export Morphisms.
Require Export Relations.
Require Import Program.

(* This would be nicer if it where broken up some more.
   Particularly, this should be formulated in terms of <=
   Then ordLt is a PartialOrder over ordEq
   also, we should make < notation for type class preorder.
   This is really then a DecidableTotalOrder packaged up into
   a DecidableTotalOrderSet
   *)

Class OrderedType (t:Set) := {
  ordEq :> Setoid t;

  ordLt : t -> t -> Prop;

  ordLt_trans :> Transitive ordLt;
  ordLt_not_eq : forall x y : t, ordLt x y -> x =/= y;

  ordCompare : forall x y : t, Compare ordLt equiv x y
}.

Notation "x << y" := (ordLt x y) (at level 70, no associativity) : type_scope.

(* Hint Resolve eq_refl eq_trans lt_not_eq lt_trans. *)

(** * Ordered types properties *)

(** Additional properties that can be derived from signature
    [OrderedType]. *)

Section OrderedTypeFacts.
  Context {t : Set}.
  Context {O : OrderedType t}.
  Implicit Types x y z : t.

  Global Instance ordLt_irrefl : Irreflexive ordLt.
  Proof. repeat red. intros. apply (ordLt_not_eq H). reflexivity. Qed.

  Global Instance ordLt_eq_morphism : Proper (equiv ==> equiv ==> iff) ordLt.
  Proof.
    cut (Proper ((equiv (Setoid:=ordEq)) ==> equiv ==> impl) ordLt);
      repeat red; intuition.
    repeat red in H; eapply H; eauto.
    repeat red in H; eapply H; eauto; symmetry; auto.
    
    destruct (ordCompare y y0); auto.
    elim (ordLt_not_eq H1). rewrite H, H0; trivial.
    destruct (ordCompare x y0); auto.
    
    elim (ordLt_not_eq (ordLt_trans o0 o)); auto.
    elim (ordLt_not_eq H1). rewrite H0; trivial.
    elim (ordLt_not_eq (ordLt_trans o0 H1)); auto.
    symmetry; trivial.
  Qed.

  Global Instance ordLt_antisym : Asymmetric ordLt.
  Proof. repeat red. intros. 
    rewrite H0 in H. 
    apply (ordLt_irrefl H).
  Qed.

  Global Instance ordEq_dec : EqDec ordEq.
  Proof.
    repeat red. 
    intros; elim (ordCompare x y); intuition; right; intros; intro;
      eapply ordLt_not_eq; eauto; symmetry; auto.
  Qed.

  Global Instance ordEqSet_dec : DecidableSetoid ordEq.
  Proof. generalize ordEq_dec. unfold EqDec, complement.
    repeat red. intros. destruct (H x y); intuition.
  Qed.

  Hint Resolve ordLt_irrefl.

  Lemma ordLt_dec : forall x y , decidable (ordLt x y).
  Proof.
    intros.
   unfold decidable; intros; elim (ordCompare x y); intuition; right.
   rewrite e. apply ordLt_irrefl. rewrite l. apply ordLt_irrefl.
  Qed.

  Notation "x << y" := (ordLt_dec x y) (at level 70, no associativity).

  Definition ordLe x y := x << y \/ x == y.

  Lemma ordLe_dec : forall x y , decidable (ordLe x y).
  Proof.
   unfold decidable, ordLe; intros. 
   destruct (x == y); destruct (x << y); intuition.
  Qed.

  Notation "x <<= y" := (ordLe x y) (at level 70, no associativity) : type_scope.

  Notation "x <<= y" := (ordLe_dec x y) (at level 70, no associativity).

  Lemma le_nlt x y : x <<= y -> ~ y << x.
  Proof.
    unfold ordLe; intros. destruct H; rewrite H; apply ordLt_irrefl.
  Qed.

  Lemma ordLt_nle x y :  x << y -> ~ y <<= x.
  Proof.
    unfold ordLe; intros. intro.
    destruct H0; rewrite H0 in H; eapply ordLt_irrefl; eauto.
  Qed.
  
  Global Instance ordLe_refl : Reflexive ordLe.
  Proof. right. reflexivity. Qed.

  Global Instance ordLe_trans : Transitive ordLe.
  Proof. unfold ordLe; repeat red; intuition;
    try rewrite H in H1; intuition.
    rewrite <- H1 in H. intuition.
  Qed.
  
  Global Instance ordLe_pre : PreOrder ordLe :=
  { PreOrder_Reflexive := ordLe_refl;
    PreOrder_Transitive := ordLe_trans
    }.

  Global Instance ordLe_part : PartialOrder equiv ordLe.
  Proof.
    repeat red.
    unfold relation_conjunction, predicate_intersection, pointwise_extension, flip, ordLe.
    intuition.  rewrite H in H0. elim (ordLt_irrefl H0).
  Qed.

  Global Instance ordLt_le_morphism : Proper (ordLe --> ordLe ++> impl) ordLt.
  Proof.
    repeat red. intros.
    destruct H0; destruct H;
    solve[rewrite H, H1; auto |
    rewrite H, <- H0; auto].
  Qed.

  Global Instance ordLe_lt_morphism : Proper (ordLt --> ordLt ++> impl) ordLe.
  Proof.
    repeat red. unfold flip. intros.
    rewrite H1, H0 in H. intuition. 
  Qed.

  Lemma ordLe_ordLt_trans : forall x y z, ~ y << x -> y << z -> x << z.
  Proof.
   intros; destruct (ordCompare y x); auto.
   elim (H o). rewrite <- e. auto.
   rewrite <- H0. auto.
  Qed.

  Lemma ordLt_le_trans : forall x y z, x << y -> ~ z << y -> x << z.
  Proof.
   intros; destruct (ordCompare z y); auto.
   elim (H0 o).
   rewrite e; auto.
   rewrite H; auto.
  Qed.

  Lemma ordLe_neq : forall x y, ~ x << y -> ~ x == y -> y << x.
  Proof.
    intros; destruct (ordCompare x y); intuition.
  Qed.

  Lemma neq_sym : forall x y, ~x == y -> ~ y == x.
  Proof. intuition. Qed.


  Global Instance ordLe_lt_subr : subrelation ordLt ordLe | 7.
  Proof.
    repeat red. unfold ordLe. intuition.
  Qed.

  Global Instance ordLe_equiv_subr : subrelation equiv ordLe | 7.
  Proof.
    repeat red. unfold ordLe. intuition.
  Qed.

  Global Instance ordLe_eq_morphism : Proper (equiv ==> equiv ==> iff) ordLe.
  Proof. 
    unfold Proper, respectful, ordLe. intros. rewrite H, H0. intuition.
  Qed.

  Lemma ordLt_eq : forall x y z, x << y -> y == z -> x << z.
  Proof. intros. clsubst*. auto. Qed.

  Lemma eq_ordLt : forall x y z, x == y -> y << z -> x << z.    
  Proof. intros. clsubst*. auto. Qed.

  Lemma neq_eq : forall x y z, ~ x == y -> y == z -> ~ x == z.
  Proof. intros. clsubst*. auto. Qed.

  Lemma eq_neq : forall x y z, x == y -> ~ y == z -> ~ x == z.
  Proof. intros. clsubst*. auto. Qed.

  Lemma ordLe_eq : forall x y z, ~ x << y ->  y == z -> ~ x << z.
  Proof. intros. clsubst*. auto. Qed.

  Lemma eq_ordLe : forall x y z, x == y -> ~ y << z -> ~ x << z.
  Proof. intros. clsubst*. auto. Qed.

(* TODO concernant la tactique order: 
   * propagate_lt n'est sans doute pas complet
   * un propagate_le
   * exploiter ordLes hypotheses negatives restant a la fin
   * faire que ca marche meme quand une hypothese depend d'un eq ou ordLt.
*) 
  End OrderedTypeFacts.
Notation "x << y" := (ordLt_dec x y) (at level 70, no associativity).
Notation "x <<= y" := (ordLe x y) (at level 70, no associativity) : type_scope.
Notation "x <<= y" := (ordLe_dec x y) (at level 70, no associativity).

Ltac abstraction := match goal with 
 (* First, some obvious simplifications *)
 | H : False |- _ => elim H
 | H : ?x << ?x |- _ => elim (ordLt_irrefl H)
 | H : ~ (?x == ?x) |- _ => let H := fresh H in elim H; reflexivity
 | H : ~ (?x <<= ?x) |- _ => let H := fresh H in elim H; reflexivity
 | H : ?x =/= ?x |- _ => let H := fresh H in elim H; reflexivity
 | H : ?x == ?x |- _ => clear H; abstraction
 | H : ?x <<= ?x |- _ => clear H; abstraction
 | H : ~ (?x << ?x) |- _ => clear H; abstraction
 | H : ?x <<= ?y |- _ => generalize (le_nlt H); clear H; intro H
 | |- ?x == ?x => reflexivity
 | |- ?x <<= ?x => reflexivity
 | |- ?x << ?x => elimtype False; abstraction
 | |- ~ _ => intro; abstraction
 | H1: ~ (?x << ?y), H2: ~ (?x == ?y) |- _ => 
     generalize (ordLe_neq H1 H2); clear H1 H2; intro; abstraction
 | H1: ~ (?x << ?y), H2: ?y == ?x |- _ => 
     generalize (ordLe_neq H1 (neq_sym H2)); clear H1 H2; intro; abstraction
 (* Then, we generalize all interesting facts *)
 | H : ~ (?x == ?y) |- _ =>  revert H; abstraction
 | H : ~ (?x <<= ?y) |- _ =>  revert H; abstraction
 | H : ~ (?x << ?y) |- _ => revert H; abstraction  
 | H : ?x << ?y |- _ => revert H; abstraction
(* | H : ?x <<= ?y |- _ =>  revert H; abstraction *)
 | H : ?x == ?y |- _ =>  revert H; abstraction
 | _ => idtac
end.

Ltac do_eq a b EQ := match goal with 
 | |- ?x << ?y -> _ => let H := fresh "H" in 
     (intro H; 
      (generalize (eq_ordLt (eq_sym EQ) H); clear H; intro H) ||
      (generalize (ordLt_eq H EQ); clear H; intro H) || 
      idtac); 
      do_eq a b EQ
 | |- ~ ?x << ?y -> _ => let H := fresh "H" in 
     (intro H; 
      (generalize (eq_ordLe (eq_sym EQ) H); clear H; intro H) ||
      (generalize (ordLe_eq H EQ); clear H; intro H) || 
      idtac); 
      do_eq a b EQ 
 | |- ?x == ?y -> _ => let H := fresh "H" in 
     (intro H; 
      (generalize (transitivity (symmetry EQ) H); clear H; intro H) ||
      (generalize (transitivity H EQ); clear H; intro H) || 
      idtac); 
      do_eq a b EQ 
 | |- ~ ?x == ?y -> _ => let H := fresh "H" in 
     (intro H; 
      (generalize (eq_neq (symmetry EQ) H); clear H; intro H) ||
      (generalize (neq_eq H EQ); clear H; intro H) || 
      idtac); 
      do_eq a b EQ 
 | |- a << ?y => apply eq_ordLt with b; [exact EQ|]
 | |- ?y << a => apply ordLt_eq with b; [|exact (symmetry EQ)]
 | |- a == ?y => transitivity b; [exact EQ|]
 | |- ?y == a => transitivity b; [|exact (symmetry EQ)]
 | _ => idtac
 end.

Ltac propagate_eq := abstraction; clear; match goal with 
 (* the abstraction tactic ordLeaves equality facts in head position...*)
 | |- ?a == ?b -> _ => 
     let EQ := fresh "EQ" in (intro EQ; do_eq a b EQ; clear EQ); 
     propagate_eq 
 | _ => idtac
end.

Ltac do_lt x y ORDLT := match goal with 
 (* ORDLT *)
 | |- ordLt x y -> _ => intros _; do_lt x y ORDLT
 | |- ordLt y ?z -> _ => let H := fresh "H" in 
     (intro H; generalize (ordLt_trans ORDLT H); intro); do_lt x y ORDLT
 | |- ordLt ?z x -> _ => let H := fresh "H" in 
     (intro H; generalize (ordLt_trans H ORDLT); intro); do_lt x y ORDLT
 | |- ordLt _ _ -> _ => intro; do_lt x y ORDLT
 (* GE *)
 | |- ~ordLt y x -> _ => intros _; do_lt x y ORDLT
 | |- ~ordLt x ?z -> _ => let H := fresh "H" in 
     (intro H; generalize (ordLe_ordLt_trans H ORDLT); intro); do_lt x y ORDLT
 | |- ~ordLt ?z y -> _ => let H := fresh "H" in 
     (intro H; generalize (ordLt_le_trans ORDLT H); intro); do_lt x y ORDLT
 | |- ~ordLt _ _ -> _ => intro; do_lt x y ORDLT
 | _ => idtac
 end.

Definition hide_lt2 t o := @ordLt t o.

Ltac propagate_lt := abstraction; match goal with 
 (* when no [=] remains, the abstraction tactic lLeaves [<] facts first. *)
 | |- ordLt ?x ?y -> _ => 
     let ORDLT := fresh "ORDLT" in (intro ORDLT; do_lt x y ORDLT; 
     change (hide_lt2 _ x y) in ORDLT); 
     propagate_lt 
 | _ => unfold hide_lt2 in *
end.

Ltac order := 
 intros; clsubst*; 
 propagate_eq; 
 propagate_lt; 
 auto; 
 propagate_lt; 
 eauto.

Ltac false_order := elimtype False; order.

Section MoreFacts.
  Context {t : Set}.
  Context {O : OrderedType t}.
  Implicit Types x y z : t.

  Lemma gt_not_eq : forall x y, y << x -> ~ x == y.
  Proof. order. Qed.
 
  Lemma eq_not_lt : forall x y, equiv x y -> ~ ordLt x y.
  Proof. order. Qed.

  Hint Resolve gt_not_eq eq_not_lt.

  Lemma eq_not_gt : forall x y , equiv x y -> ~ ordLt y x.
  Proof. order. Qed.
    
  Lemma ordLt_not_gt : forall x y , ordLt x y -> ~ ordLt y x.
  Proof. order. Qed. 

  Hint Resolve eq_not_gt ordLt_not_gt.

  Lemma elim_compare_eq :
   forall x y ,
     x == y -> exists H : equiv x y, ordCompare x y = EQ _ H.
  Proof. 
   intros; case (ordCompare x y); intros H'; try solve [false_order].
   exists H'; auto.
  Qed.

  Lemma elim_compare_lt :
   forall x y ,
   ordLt x y -> exists H : ordLt x y, ordCompare x y = LT _ H.
  Proof. 
   intros; case (ordCompare x y); intros H'; try solve [false_order].
   exists H'; auto.
  Qed.

  Lemma elim_compare_gt :
   forall x y ,
   ordLt y x -> exists H : ordLt y x, ordCompare x y = GT _ H.
  Proof. 
   intros; case (ordCompare x y); intros H'; try solve [false_order].
   exists H'; auto.
  Qed.
End MoreFacts.

  Ltac elim_comp := 
    match goal with 
      | |- ?e => match e with 
           | context ctx [ ordCompare ?a ?b ] =>
                let H := fresh in 
                (destruct (ordCompare a b) as [H|H|H]; 
                 try solve [ intros; false_order])
         end
    end.

  Ltac elim_comp_eq x y :=
    elim (elim_compare_eq (x:=x) (y:=y));
     [ intros _1 _2; rewrite _2; clear _1 _2 | auto ]. 

  Ltac elim_comp_lt x y :=
    elim (elim_compare_lt (x:=x) (y:=y));
     [ intros _1 _2; rewrite _2; clear _1 _2 | auto ]. 

  Ltac elim_comp_gt x y :=
    elim (elim_compare_gt (x:=x) (y:=y));
     [ intros _1 _2; rewrite _2; clear _1 _2 | auto ].

Section MoreFacts2.
  Context {t : Set}.
  Context {O : OrderedType t}.
  Implicit Types x y z : t.

  Definition eqb x y : bool := if x == y then true else false.

  Lemma eqb_alt : 
    forall x y, eqb x y = match ordCompare x y with EQ _ => true | _ => false end. 
  Proof.
  unfold eqb; intros; destruct (x == y); elim_comp; auto.
  Qed.

(* Specialization of resuts about lists modulo. *)
  
  Notation In:=(InA equiv).
  Notation Inf:=(lelistA ordLt).
  Notation Sort:=(sort ordLt).
  Notation NoDup:=(NoDupA equiv).

  Lemma In_equiv : forall l x y, x == y -> In x l -> In y l.
  Proof. exact (InA_eqA symmetry transitivity). Qed.

  Lemma ListIn_In : forall l x, List.In x l -> In x l.
  Proof. exact (In_InA reflexivity). Qed.

  Lemma Inf_lt : forall l x y, x << y -> Inf y l -> Inf x l.
  Proof. exact (InfA_ltA transitivity). Qed.

  Lemma Inf_eq : forall l x y, x == y -> Inf y l -> Inf x l.
  Proof. exact (InfA_eqA eq_ordLt). Qed.

  Lemma Sort_Inf_In : forall l x a, Sort l -> Inf a l -> In x l -> a << x.
  Proof. exact (SortA_InfA_InA reflexivity symmetry transitivity ordLt_eq eq_ordLt). Qed.

  Lemma ListIn_Inf : forall l x, (forall y, List.In y l -> x << y) -> Inf x l.
  Proof. exact (@In_InfA t ordLt). Qed.

  Lemma In_Inf : forall l x, (forall y, In y l -> x << y) -> Inf x l.
  Proof. exact (InA_InfA reflexivity (ltA:=ordLt)). Qed.

  Lemma Inf_alt : 
   forall l x, Sort l -> (Inf x l <-> (forall y, In y l -> x << y)).
  Proof. exact (InfA_alt reflexivity symmetry transitivity ordLt_eq eq_ordLt). Qed.

  Lemma Sort_NoDup : forall l, Sort l -> NoDup l.
  Proof. exact (SortA_NoDupA reflexivity symmetry transitivity ordLt_not_eq ordLt_eq eq_ordLt) . Qed.

End MoreFacts2.