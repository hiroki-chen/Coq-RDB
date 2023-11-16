Require Import Assumptions DataModel OrderedTypeNM FSetInterfaceNM List String.
Require Import SetoidClass.
Require Import RelationClasses.

Module FS := FSetInterfaceNM.

Definition eq_str : forall (a b: string), {a = b} + {a <> b}.
intros. repeat decide equality.
Defined.

Set Implicit Arguments. Unset Strict Implicit.

(* this stuff should move *)
Require Import List Sorting SetoidList.

Hint Unfold Proper respectful.
Ltac unp := unfold Proper, respectful.

Instance eqlistA_refl {A} (R:relation A) {r:Reflexive R}: Reflexive (eqlistA R).
Proof. red; induction x; intuition; apply eqlistA_cons. Qed.

Instance eqlistA_sym {A} (R:relation A) {s:Symmetric R} : Symmetric (eqlistA R).
Proof. red.
  induction x; intuition; inversion H; intuition; subst;
  inversion H0; intuition; subst.
Qed.

Instance eqlistA_trans {A} (R:relation A) {t:Transitive R} 
  : Transitive (eqlistA R).
Proof. red.
  induction x; intuition; inversion H; intuition; subst;
  inversion H0; intuition; subst.
  apply eqlistA_cons.
  transitivity x'; eauto.
  eapply IHx; eauto.
Qed.

Instance listEq elt (R:relation elt) 
(eqR:Equivalence R) : Equivalence (eqlistA R).
Proof. split; typeclasses eauto. Qed.

Global Instance listSet elt (s:Setoid elt): Setoid (list elt) :=
{ setoid_equiv := listEq setoid_equiv }.

Lemma PERleft `{p:PER A R} x y : R x y -> R x x.
Proof. intros; transitivity y; [idtac|symmetry]; assumption. Qed.

Lemma PERright `{p:PER A R} x y : R x y -> R y y.
Proof. intros; transitivity x; [symmetry|idtac]; assumption. Qed.

Ltac toEquiv := repeat match goal with
  | [H:?R ?x ?y |- _] => 
    match R with
      | equiv => fail 1
      | _ => change (R x y) with (equiv x y) in H
    end
  | [|- ?R ?x ?y ] =>     match R with
      | equiv => fail 1
      | _ => change (R x y) with (equiv x y)
    end
end.

Lemma fold_right_compat' (A B : Type) (sA:Setoid A) (sB:Setoid B) :
Proper ((equiv ==> equiv ==> equiv) ==> equiv ==> eq ==> equiv) (@fold_right A B).
Proof.  unfold Proper, respectful.
  intros; simpl in *; subst.
  induction y1; simpl; auto. apply H; auto. reflexivity.
Qed.

Require Import SetoidClass.
Require Import RelationClasses.

Instance fold_right_compat (A B : Type) (sA:Setoid A) (sB:Setoid B) : 
Proper ((equiv ==> equiv ==> equiv) ==> equiv ==> equiv ==> equiv) (@fold_right A B).
Proof. 
Proof. intros.
  intros f1 f2 pf.
  generalize (PERright pf).
  unfold Proper, respectful; intros.
simpl in *; subst.
transitivity (
fold_right f2 y x0). eapply fold_right_compat'; eauto.
repeat
  apply fold_right_eqlistA with
    (eqA := equiv)
    (eqB := equiv); auto. 
  apply setoid_equiv.
  unfold compat_op, Proper in *; intros. eauto.
Qed.

Definition mapASet eltA eltB (A : OrderedType eltA) (B:OT.OrderedType eltB) 
  (A':FS.FSetInterfaceNM A) (B':FS.FSetInterfaceNM B) 
  (f:eltA -> eltB) (x: @FS.t _ _ A') : @FS.t _ _ B'
  := FS.fold (fun a y => FS.add (f a) y) x (FS.empty).

Section DBDefs.

Variable A : Typing.

Definition DBSet : Type 
  := FS.FSetInterfaceNM (tupleOrd A).

Definition DBRel (W:DBSet) : Set
  := @FS.t _ _ W.

End DBDefs.

Section X.

Variable F : forall I, DBSet I.

Section DBOps.

Variable I : Typing.

Definition empty0 : DBRel (F I) := @FS.empty _ _ (F I).

Section BinOps.
Variable R S : DBRel  (F I).

Definition union : DBRel (F I)
  := FS.union R S.

Definition inter : DBRel (F I)
  := FS.inter R S.

Definition diff : DBRel (F I)
  := FS.diff R S.

Definition equal : bool
  := FS.equal R S.

Definition Equal : Prop
  := FS.Equal R S.

Definition Subset : Prop
  := FS.Subset R S.

Definition select (P: Tuple I -> bool) (R:DBRel  (F I)) : DBRel  (F I) 
  := FS.filter P R.

End BinOps.

End DBOps.
Definition prod1 (I J: Typing) 
  (x: Tuple I) (b: @t (Tuple J) (tupleOrd J) (F J)) : DBRel  (F (I++J)) 
    := @mapASet (Tuple J) (Tuple (@app typ I J)) (tupleOrd J)
  (tupleOrd (@app typ I J)) (F J) (F (@app typ I J)) 
  (@fuseTuples I J x) b.

Definition prodRel (I J: Typing) 
 (R: DBRel (F I)) (S: DBRel  (F J)) 
 : DBRel  (F (I ++ J))  :=
FS.fold (fun (a: Tuple I) y =>
   union  y (prod1  a S)) R (@empty0 (I++J) ).

Require Import List.

Definition gprojRel l (I: Typing) (pf: bounded I l)
 (R: DBRel  (F I)) : DBRel (F (nthTyps pf))
:= (@mapASet _ _ _ _ (F I) (F (nthTyps pf)) (gprojTuple pf) R).

(********************************************)

Lemma proper_and (A:Set) (s:Setoid A) (f1 f2:A->bool) :
  Proper (equiv ==> equiv) f1 -> 
  Proper (equiv ==> equiv) f2 -> 
  Proper (equiv ==> equiv) (fun x => f1 x && f2 x).
Proof. repeat red. intros.
  rewrite (H _ _ H1).  rewrite (H0 _ _ H1).
  reflexivity.
Qed.

Lemma andTjoin X Y : X && Y = true -> X = true /\ Y = true.
Proof. 
 destruct X; destruct Y; auto. 
Qed.

Lemma andTsplit X Y : X = true /\ Y = true -> X && Y = true.
Proof. 
 destruct X; destruct Y; intuition. 
Qed.

Ltac poses P := let H := fresh "posesH" in pose (H := P); clearbody H.
Ltac unf := unfold Equal, equal, Subset, select, 
  union, inter, diff, compat_bool, empty0.

(* TODO this tactic is duplicated in the equivlances file *)
Ltac fset_simpl_c L :=
    match goal with
      | [H: ?X && ?Y = true |- _] => 
          destruct (andTjoin H); clear H; fset_simpl_c L
      | [|- ?X && ?Y = true] => apply andTsplit; fset_simpl_c L
      | [|- ?X /\ ?Y] => split; intros; fset_simpl_c L
      | [H: FSetInterfaceNM.In _ (FSetInterfaceNM.empty) |- _] => elim (FSetInterfaceNM.empty_1 H)
      | [H1:(@FSetInterfaceNM.In ?E ?T ?W ?a (FSetInterfaceNM.filter ?f ?R)) |- _] => 
        let HH := fresh "HH" in 
          assert (HH: Proper (equiv ==> equiv) f) by L;
            let HH2 := fresh "ffact" in let HH3 := fresh "ffact" in 
              pose (HH2 := FSetInterfaceNM.filter_2 HH H1); clearbody HH2; 
                pose (HH3 := FSetInterfaceNM.filter_1 HH H1); clearbody HH3; clear HH;
                  simpl in HH2; clear H1; rename HH3 into H1; fset_simpl_c L
      | [H:FSetInterfaceNM.In _ (FSetInterfaceNM.union _ _) |- _] => 
  destruct (FSetInterfaceNM.union_1 H); clear H; fset_simpl_c L
      | [H:FSetInterfaceNM.In _ (FSetInterfaceNM.inter _ _) |- _] => 
  poses (FSetInterfaceNM.inter_1 H); poses (FSetInterfaceNM.inter_2 H); clear H
      | [H:FSetInterfaceNM.In _ (FSetInterfaceNM.diff _ _) |- _] => 
  poses (FSetInterfaceNM.diff_1 H); poses (FSetInterfaceNM.diff_2 H); clear H
      | [H:FSetInterfaceNM.In ?a (FSetInterfaceNM.add ?x1 ?x2) |- _] => 
        let e := fresh "e" in  destruct (x1 == a) as [e|e];
          [rewrite e in *|generalize (add_3 e H); intro]; clear H; rename e into H
      | [|- (@FSetInterfaceNM.In ?E ?T ?W ?a (FSetInterfaceNM.filter ?f ?R))] => 
        eapply FSetInterfaceNM.filter_3; fset_simpl_c L
      | [|- (@FSetInterfaceNM.In ?E ?T ?W ?a (FSetInterfaceNM.inter _ _))] => 
        eapply FSetInterfaceNM.inter_3; fset_simpl_c L
      | [|- (@FSetInterfaceNM.In ?E ?T ?W ?a (FSetInterfaceNM.diff _ _))] => 
        eapply FSetInterfaceNM.diff_3; fset_simpl_c L
      | [|- ~ FSetInterfaceNM.In _ _] => intro
(*       | [H:~ FSetInterfaceNM.In _ _ |- ~ FSetInterfaceNM.In _ _] =>  *)
(*         solve[let HH := fresh "HH" in  *)
(*           intro HH; elim H; clear H; fset_simpl_c L] *)
      | _ => progress L
    end.

Ltac unfs :=  unfold FS.Equal, FS.Subset, iff in *; intros.
Ltac fset_simpl := unf; repeat (unfs; fset_simpl_c auto).

Ltac simpPropEq := unfold DBRel; unp; intros; 
  rewrite (@equivIsEqual) in *; unfold FS.Equal in *; intros
    ;  repeat match goal with 
    | [H:?X, H1: (forall (_ : ?X), _) |- _] => generalize (H1 H); clear H1; intro H1
    | [H: _ <-> _ |- _] => destruct H
  end; fset_simpl.

Section Morphs.
Variable A : Typing.
Variable U:FSetInterfaceNM (tupleOrd A).

(* Matthieu: why is this needed? *)
(*Instance UtupleOrd : OrderedType (@DBRel A U). apply (@ordT (Tuple A) (tupleOrd A) U). Defined. *)
(*Instance UtupleOrd : OrderedType (@t _ _ U). apply (@ordT (Tuple A) (tupleOrd A) U). Defined.*)

(* Instance UtupleEq : Equivalence (Tuple A). exact (eqTupleEquiv A). Defined.  *)
(*Instance UtupleSet : Setoid (Tuple A). exact (eqTupleSetoid A). Defined.  *)

(* Instance UtupleOrd : OrderedType (Tuple A). apply (tupleOrd). Defined. *)

Instance IordEq_dec_sp1 : EqDec ordEq := (@ordEq_dec _ (tupleOrd A)).

Instance IordEq_dec_sp2 : EqDec (@ordEq _ (@ordT _ _ U)). apply ordEq_dec. Defined.

Global Instance union_push : Proper (equiv ==> equiv ==> equiv) (@union A).
Proof. simpPropEq. Qed.

Global Instance inter_push : Proper (equiv ==> equiv ==> equiv) (@ inter A).
Proof. simpPropEq. Qed.

Global Instance diff_push : Proper (equiv ==> equiv ==> equiv) (@ diff A).
Proof. simpPropEq. Qed.

Global Instance add_push : Proper (equiv ==> equiv ==> equiv) (FS.add).
Proof. simpPropEq. Qed.

Lemma respect_preserves A B (f1 f2:A->B) (a:A) (x:B) equiv1 equiv2
(eq1:Equivalence equiv1)
  (eq2:Equivalence equiv2) (resp:(equiv1 ==> equiv2)%signature f1 f2) :
  equiv2 (f1 a) x -> equiv2 (f2 a) x.
intros.
rewrite <- H. symmetry. apply resp. reflexivity.
Qed.

Lemma respect_preserves' A B (f1 f2:A->B) (a:A) (x:B) equiv1
(eq1:Equivalence equiv1)
 (resp:(equiv1 ==> eq)%signature f1 f2) :
   f1 a = x -> f2 a = x.
intros.
rewrite <- H. symmetry. apply resp. reflexivity.
Qed.

Hint Resolve respect_preserves'.

Global Instance select_push (I: Typing) :
  Proper ((equiv ==> equiv) ==> equiv ==> equiv) (@select I).
Proof.
Proof.
  intros I f1 f2 pf.
  pose (PERleft pf). pose (PERright pf).
  simpPropEq.

split; intros.
Ltac so := eapply respect_preserves; eauto.

match goal with
  | [H1:(FSetInterfaceNM.In ?a (FSetInterfaceNM.filter ?f ?R)) |- _] =>
    let HH := fresh "HH" in
      assert (HH: Proper (equiv ==> equiv) f) by auto;
        let HH2 := fresh "ffact" in let HH3 := fresh "ffact" in
          pose (HH2 := FSetInterfaceNM.filter_2 HH H1); clearbody HH2;
            pose (HH3 := FSetInterfaceNM.filter_1 HH H1); clearbody
HH3; clear HH;
              simpl in HH2; clear H1; rename HH3 into H1
end.

eapply filter_3; auto.
eapply respect_preserves'; [idtac|idtac|eauto]; eauto. typeclasses eauto.

match goal with
  | [H1:(FSetInterfaceNM.In ?a (FSetInterfaceNM.filter ?f ?R)) |- _] =>
    let HH := fresh "HH" in
      assert (HH: Proper (equiv ==> equiv) f) by auto;
        let HH2 := fresh "ffact" in let HH3 := fresh "ffact" in
          pose (HH2 := FSetInterfaceNM.filter_2 HH H1); clearbody HH2;
            pose (HH3 := FSetInterfaceNM.filter_1 HH H1); clearbody
HH3; clear HH;
              simpl in HH2; clear H1; rename HH3 into H1
end.

eapply filter_3; auto.
eapply respect_preserves'; [idtac|idtac|eauto]; eauto. typeclasses eauto.
red; intros. symmetry. apply pf. symmetry. auto.
Qed.

Global Instance elements_push : Proper (equiv ==> equiv) (@elements _ _ U).
Proof. simpPropEq.
  generalize (elements_3 x). generalize (elements_3 y). intros. simpl.
  eapply SortA_equivlistA_eqlistA; intuition; instantiate; toEquiv;
clsubst*; intuition.
  transitivity y0; auto.

  eapply ordLt_irrefl; eauto.
  intro. pose elements_1 as i.
  split; intros; apply i; [apply -> H | apply <- H]; auto.
Qed.

End Morphs.

Global Instance eqlistA_rev' (A:Type) (s:Setoid A): Proper (equiv ==> equiv) (@rev A).
Proof. repeat red. intros. apply eqlistA_rev. auto. Qed.

Ltac prove_proper :=  unp; intuition clsubst*; reflexivity.
Ltac solvefrp := eapply @fold_right_compat; try (clsubst*; reflexivity); prove_proper.

Hint Extern 1 (equiv (fold_left _ _ _) (fold_left _ _ _)) => (repeat rewrite <- fold_left_rev_right).
Hint Extern 3 (equiv (fold_right _ _ _) (fold_right _ _ _)) => solvefrp.
Hint Extern 1 (equiv (fold _ _ _) (fold _ _ _)) => repeat rewrite fold_1.
Hint Extern 1 (equiv (gprojRel _ _ _) (gprojRel _ _ _)) => unfold gprojRel.
Hint Extern 1 (equiv (mapASet _ _) (mapASet _ _)) => unfold mapASet.

Global Instance gprojRel_push 
 (I : Typing) n (pf: bounded I n)
 : Proper (equiv ==> equiv) (@gprojRel n I pf).
Proof. 
 unfold gprojRel, mapASet. auto. 
Qed.

Global Instance prod1_push (I J:Typing)
  : Proper (equiv ==> equiv ==> equiv) (fun X Y => (@prod1 I J X Y)).
Proof. 
  unfold prod1, mapASet. auto. 
Qed. 

Global Instance prod_push
 ( I : Typing)
 ( J : Typing) :
Proper (equiv ==> equiv ==> equiv) (prodRel (I:=I) (J:=J) ).
Proof. unp; unfold prodRel. intros.
  repeat rewrite fold_1.

 repeat rewrite <- fold_left_rev_right.
 eapply @fold_right_compat; try (clsubst*; reflexivity).
 unp. intros. clsubst*.
 (* Matthieu: doesn't rewrite work here? note that once it does, this whol proof just becomes auto. *)
 eapply @union_push; try reflexivity.
Qed.

  Lemma eq_equiv {A} {s:Setoid A} x y : x = y -> x == y.
  Proof. intros. rewrite H. reflexivity. Qed.

 Lemma elements_cast1 (I J:Typing) (a0:Tuple J) (a: @t (Tuple I) (tupleOrd I) (F I)) (pf1:I=J) :
   InA equiv a0 (elements (cast1 (u:=fun x : Typing => @t (Tuple x) (tupleOrd x) (F x)) a pf1)) ->
   InA equiv a0 (map (fun x => cast1 (u:=Tuple) x pf1) (elements (FSetInterfaceNM:= F I) a)).
 Proof.
   intros. destruct pf1. rewrite cast1_simpl in H.
   induction (elements a); simpl; trivial.
   inversion H; subst.
   left. rewrite cast1_simpl. auto.
   right. auto.
 Qed.

 Lemma in_cast1_switch (I J:Typing) a a0 (pf1:I=J) pf2 :
        FSetInterfaceNM.In (FSetInterfaceNM:=F J) a0 (cast1 (u:=fun x : Typing => @t (Tuple x) (tupleOrd x) (F x)) a pf1)
     -> FSetInterfaceNM.In (cast1 (u:=Tuple) a0 pf2) a.
 Proof.
   intros. destruct pf2. rewrite cast1_simpl in H.
   apply elements_1 in H; apply elements_2.
   induction (elements a); simpl; intuition.
 Qed.

(* External Interface *********************************************** *)

Section Q.

Inductive atomicExp (I : Typing) : typ -> Set :=
| atom : forall t (c: typDenote t), atomicExp I t
| var  : forall n (pf: n < length I), atomicExp I (nthTyp pf).

Inductive compareExp (I : Typing) (t : typ) : Set :=
| compareEq : atomicExp I t -> atomicExp I t -> compareExp I t
| compareLt : atomicExp I t -> atomicExp I t -> compareExp I t
| compareGt : atomicExp I t -> atomicExp I t -> compareExp I t.

Inductive whereExp (I : Typing) :=
| trueExp  : whereExp I
| falseExp : whereExp I
| compExp: forall t, compareExp I t -> whereExp I
| andExp : whereExp I -> whereExp I -> whereExp I
| orExp  : whereExp I -> whereExp I -> whereExp I
| notExp : whereExp I -> whereExp I.

Section Q.

 Hypothesis Var : Typing -> Set.

Inductive raExp : Typing -> Set :=
 | emptyExp  : forall (I: Typing), raExp I
 | varExp    : forall (I: Typing), Var I -> raExp I 
 | unionExp  : forall (I: Typing), 
    raExp I -> raExp I -> raExp I
 | interExp  : forall (I: Typing), 
    raExp I -> raExp I -> raExp I
 | selectExp : forall (I: Typing), 
    raExp I -> whereExp I -> raExp I
 | gprojExp : forall (I : Typing) l (pf: bounded I l),
       raExp I -> raExp (nthTyps (I:=I) pf) 
 | prodExp   : forall (I J: Typing), 
   raExp I -> raExp J -> raExp (I++J).
End Q.

(* Straightforward denotations of RA expressions. *)
Section E.

Definition atomicDenote (I: Typing) (t: typ) (e: atomicExp I t) 
 : Tuple I -> typDenote t.
intros I t e.
refine (
match e in atomicExp _ t' return  Tuple I -> typDenote t' with
  | atom _ c => fun _ => c
  | var n pf  => fun x => _
end ).
  pose (projTupleN pf x).
 simpl in t0. exact (fst t0).
Defined.

(* getting the beta/iota problem *)
Definition compareDenote I t (e: compareExp I t) 
  : Tuple I -> bool.
intros I t e.
destruct e as [a b|a b|a b] ; intros x;
destruct (ordCompare (atomicDenote a x) (atomicDenote b x));
[exact false|exact true|exact false
|exact true|exact false|exact false
|exact false|exact false|exact true].
Defined.

Fixpoint whereDenote I (e: whereExp I) {struct e} : Tuple I -> bool :=
  match e with
    | compExp t e => fun x => compareDenote e x
    | andExp a b => fun x => andb 
      (whereDenote  a x) (whereDenote b x)
    | orExp  a b => fun x => orb  
      (whereDenote a x) (whereDenote b x) 
    | notExp  a  => fun x => negb (whereDenote a x)
    | falseExp => fun x => false
    | trueExp => fun x => true
  end.

Require Import Setoid.

Global Instance atomicDenoteProper I t (e: atomicExp I t) 
: Proper (equiv ==> equiv) (atomicDenote e).
Proof. unfold Proper, respectful.
 induction e; simpl; intros.
   reflexivity.
   apply (projTupleN_push pf H).
Qed.

Lemma atomicDenote_push : forall I t a x y, 
 x == y -> (atomicDenote (I:=I) (t:=t) a x == atomicDenote a y).
Proof. intros. rewrite H. reflexivity. Qed.
 
Lemma lt_ar : forall I t a x,
 @ordLt (typDenote t) (typOrdInst t) (@atomicDenote I t a x) (@atomicDenote I t a x) -> False.
intros.
pose (@ordLt_irrefl (typDenote t) (typOrdInst t) (atomicDenote  a x) ).
apply c. assumption.
Qed.

Lemma a_lt_b_lt_a : forall t I a0 a y,
@ordLt (typDenote t) (typOrdInst t) (@atomicDenote I t a0 y)
         (@atomicDenote I t a y) ->
   @ordLt (typDenote t) (typOrdInst t) (@atomicDenote I t a y)
        (@atomicDenote I t a0 y) -> False.
intros.
pose (@ordLt_trans (typDenote t) (typOrdInst t) _ _ _ H H0).
eapply lt_ar.
eauto.
Qed.

Global Instance compareDenoteProper I t (e: compareExp I t) : 
 Proper (equiv ==> equiv) (compareDenote e).
Proof. intros. unfold Proper, respectful.
 induction e;

 simpl; unfold respectful; unfold Proper; intros;
  remember (atomicDenote  a x); remember (atomicDenote  a0 x);
  remember (atomicDenote  a y); remember (atomicDenote  a0 y);
 remember (ordCompare (atomicDenote a x) (atomicDenote a0 x));
 remember (ordCompare (atomicDenote a y) (atomicDenote a0 y));
 destruct (ordCompare t0 t1);
 destruct (ordCompare t2 t3); try trivial;
 subst;
pose (atomicDenote_push   a H);
pose (atomicDenote_push   a0  H);
 try (rewrite <- e1 in e;
      rewrite <- e in o;
      pose (atomicDenoteProper  a  H); rewrite <- e2 in o;
      elim (lt_ar o));
 try (rewrite e1 in e;
      rewrite <- e in o;
      pose (atomicDenoteProper  a  H); rewrite <- e2 in o;
      elim (lt_ar o));
 try (rewrite e in *; rewrite e0 in *; elim (a_lt_b_lt_a o0 o)).
Qed.

Global Instance whereDenoteProper I (e: whereExp I) 
: Proper (equiv ==> equiv) (whereDenote  e).
Proof.
 intros.
 induction e; 
 try (simpl; auto);
 try (red; unfold respectful;
      unfold whereDenote;
      pose (@compareDenoteProper I t c);
      assert (compareDenote c = fun x => compareDenote  c x);
      try apply ext; trivial; rewrite H in p; assumption);
 try (unfold whereDenote; fold whereDenote; 
 red; unfold Proper in *; unfold respectful in *;
 intros; rewrite (IHe1 x y); 
 try rewrite (IHe2 x y);
 try reflexivity; assumption);
 try (  unfold whereDenote; fold whereDenote; 
        red; unfold Proper in *; unfold respectful in *;
        intros; rewrite (IHe x y); 
        try reflexivity; try assumption). 
Qed.

Section Q.
 
Fixpoint raDenote (I: Typing) (e: raExp (fun I => DBRel (F I)) I) : DBRel (F I) :=
  match e with
    | emptyExp J => empty0 J
    | varExp J v => v 
    | unionExp  J r r0 => union  (raDenote  r) (raDenote r0)
    | interExp  J r r0 => inter  (raDenote r) (raDenote r0)
    | selectExp J r f => select  (whereDenote  f) (raDenote  r) 
    | gprojExp J l pf e => gprojRel  pf (raDenote  e) 
    | prodExp  I0 J0 r0 r1 => 
      prodRel  (raDenote  r0) (raDenote  r1)
  end.

End Q.

Definition Ctx := list (string * Typing).

Fixpoint Env' (T: Typing -> Set) (G: Ctx) : Set :=
 match G with
   | nil => unit
   | (_, J) :: b => T J * (Env' T b)
 end%type.

Definition Env F := Env' (fun I => DBRel (A:=I) (F I)).

Fixpoint lookup' (T: Typing->Set) v I G : Env' T G -> option (T I) :=
 match G as G return Env' T G -> option (T I) with
   | nil => fun _ => None
   | (s,J) :: b => fun E => 
     match eq_str v s, typing_eq_dec J I with
       | left pf1 , left pf2 => Some (@cast1 J I T (fst E) pf2)
       | _ , _ => lookup'  v I (snd E)
     end
 end.

Definition lookup v I G (E: Env F G) : DBRel  (F I) :=
  match @lookup' _ v I G E with 
    | None => empty0 I
    | Some x => x
  end.

Definition inst : forall I G, Env F G -> 
 raExp (fun _ => string) I -> raExp (fun I => DBRel  (F I)) I.
 refine (
fix inst I G (E: Env F G) (e: raExp (fun _ => string) I) {struct e} 
 : raExp (fun I => DBRel (F I)) I :=
   match e in raExp _ I return raExp _ I with
     | emptyExp J => (emptyExp _ J)
     | varExp J s => @varExp _ J (lookup s J E)
     | unionExp  J r r0 => unionExp (inst _ _ _ r) (inst _ _ _ r0)
     | interExp  J r r0 => interExp  (inst _ _ _ r) (inst _ _ _ r0)
     | selectExp J r f => selectExp  (inst _ _ _ r) f
     | gprojExp J l pf e => gprojExp pf (inst _ _ _ e)
     | prodExp  I0 J0 r r0 => prodExp  (inst _ _ _ r) (inst _ _ _ r0)
   end
  ); try eauto.
Defined.

End E.

End Q.

End X.

Fixpoint mkTbl F I (t: list (Tuple I)) : DBRel (F I) := 
  match t with 
    | nil => empty0 F I
    | a :: b => FSetInterfaceNM.add a (mkTbl F b)
  end.


(* These are the facts we want to know about the stored relations.
   For instance, if they are empty. *)
Record Info' := MkInfo' {
  tbl_empty : bool
(* ; prim_key  : list nat *)
 }.

(* The information for an entire database *) 
Definition Info := string -> Typing -> Info'.

(* What it means for information to reflect a database.
   In our case, just that we're correctly tracking empty.
   To put it another way, this is the invariant required for
   the semantic optimizations to be semantics preserving. *)
Definition accurate F (metadata: Info) G (E: Env F G) : Prop :=
 forall s I,
   if tbl_empty (metadata s I) 
     then lookup s I E ==  empty0 F I 
     else lookup s I E =/= empty0 F I.
 
Require Import FSetFacts.

Definition mkInfo (F: forall I, DBSet I) I (d: DBRel (F I)) : Info' 
  := if is_empty d then MkInfo' true else MkInfo' false.

Definition updInfo (m: Info) s i b : Info :=
 fun s' i' => match eq_str s s' , typing_eq_dec i i' with
                | left pf1 , left pf2 => b
                | _ , _ => m s' i'
              end.

Lemma lk2 : forall F I (x: DBRel (A:=I) (F I)) ,
   Empty x -> x [=] empty.
Proof.
 intros. red. intuition. destruct H with (a := a). assumption.
 pose (empty_1 H0 ). elim f.
Qed.

Require Import SetoidClass.

Lemma lk2' : forall F I (x: DBRel (A:=I) (F I)),
 false = is_empty x ->
   x =/= empty0 F I.
Proof.
 unfold DBRel. intros F I x H0.
 red. intros. 
 pose @is_empty_1.
 assert (Empty x). rewrite H. apply empty_1.
 pose (e _ _ _ _ H1). rewrite e0 in H0.
 discriminate.
Qed.

Require Import Eqdep.
Lemma lk3 : forall F
G m I s d x0,
   accurate (F:=F) m (G:=G) x0 ->
   accurate (F:=F) (updInfo m s I (mkInfo (I:=I) (mkTbl F (I:=I) d)))
     (G:=(s, I) :: G) (mkTbl F (I:=I) d, x0).
Proof.
 intros.
  unfold accurate. unfold tbl_empty. 
  intros.
  generalize (mkTbl F (I:=I) d).
  unfold lookup. unfold lookup'. fold lookup'. 
  unfold updInfo. unfold mkInfo.
   destruct (eq_str s s0).
     subst. destruct (eq_str s0 s0).
      destruct (typing_eq_dec I I0).
       (* *) generalize e0. rewrite <- e0.
             intros. unfold cast1. unfold eq_rec_r.
             rewrite <- eq_rec_eq. simpl.
             unfold tbl_empty. 
             remember (is_empty d0). destruct b.
             unfold empty0. unfold DBRel. 
             rewrite @equivIsEqual. 
             symmetry in Heqb.
             pose (is_empty_iff d0). destruct i. 
             pose (H1 Heqb). apply lk2; assumption. apply lk2'; assumption.
      (* *)  simpl. pose (H s0 I0).
             clearbody y. unfold tbl_empty in *. 
             destruct (m s0 I0).
               (* *) destruct tbl_empty0.
                     unfold lookup in y. intros. rewrite <- y. reflexivity.
               (* *) unfold lookup in y. intros. 
                     destruct (lookup' (T:=fun I : Typing => DBRel 
                     (A:=I) (F I)) s0 I0 (G:=G) x0). 
                     assumption. elim y. reflexivity.
             elim n; trivial.
      destruct (eq_str s0 s). subst. elim n; trivial.
      unfold tbl_empty. simpl. intros. apply H.
Qed.

(* todo: this should generalize as well *)
  Lemma gprojTuple_id' I pf 
   (e1: nthTyps (l:=seq 0 (length I)) (I:=I) pf = I)  x  :
    eqTuple (A:=nthTyps (l:=seq 0 (length I)) (I:=I) pf)
     (gprojTuple (l:=seq 0 (length I)) 
        (I:=I) pf (cast1 (u:=Tuple) x e1)) x.
  Proof.
    induction I; simpl; auto.
    intros. destruct pf. simpl.
    split. clear. destruct x; simpl.
    generalize dependent e1. 
    generalize dependent (nthTyps (l:=seq 1 (length I)) (I:=a :: I) b).
    clear. intros. generalize e1. inversion e1. subst I. intros.
    rewrite cast1_simpl. simpl. reflexivity.
    destruct x. simpl. fold Tuple in *.
    inversion e1.
    assert (b0:bounded I (seq 0 (length I))) by apply seq_bounded0. 
    rewrite <- (nthTyps_shift b0) in H0.
    fold Tuple in *.
    assert (teq:(nthTyps (l:=seq 1 (length I)) (I:=a :: I) b) = (nthTyps (l:=seq 0 (length I)) (I:=I) b0))
      by (rewrite <- (nthTyps_shift b0); auto).
    specialize (IHI b0 H0 (cast1 t0 teq)).
    rewrite cast1_nest in IHI.
    symmetry.
    transitivity (
 (@gprojTuple (seq (S O) (@length typ I)) (@cons typ a I) b
        (t, (@cast1
           
          (@nthTyps (seq (S O) (@length typ I)) (@cons typ a I) b)
           I Tuple t0 (eq_trans teq H0))))).
    rewrite (gprojTuple_shift _ _ (eq_sym teq)).
    revert IHI. clear.
    generalize dependent ((gprojTuple (l:=seq 0 (length I)) (I:=I) b0
        (cast1 (u:=Tuple) t0 (eq_trans teq H0)))).
    generalize dependent (nthTyps (l:=seq 1 (length I)) (I:=a :: I) b).
    generalize dependent (nthTyps (l:=seq 0 (length I)) (I:=I) b0).
    intros. destruct H0. destruct teq. rewrite cast1_simpl in *. symmetry. auto.

    clear.
    generalize dependent (nthTyps (l:=seq 0 (length I)) (I:=I) b0).
    intros. destruct H0. 
    cut ((@cast1
           (@cons typ a
              (@nthTyps (seq (S O) (@length typ t1)) (@cons typ a t1) b))
           (@cons typ a t1) Tuple
           (@pair (typDenote a)
              (Tuple
                 (@nthTyps (seq (S O) (@length typ t1)) (@cons typ a t1) b))
              t t0) e1) = 
(@pair (typDenote a) (Tuple t1) t
           (@cast1 (@nthTyps (seq (S O) (@length typ t1)) (@cons typ a t1) b)
              t1 Tuple t0
              (@eq_trans Typing
                 (@nthTyps (seq (S O) (@length typ t1)) (@cons typ a t1) b)
                 t1 t1 teq (@eq_refl (list typ) t1))))).
    intros GG ; rewrite GG; reflexivity.
    clear.
  generalize ((@eq_trans Typing
              (@nthTyps (seq (S O) (@length typ t1)) (@cons typ a t1) b) t1
              t1 teq (@eq_refl (list typ) t1))).
  clear. generalize dependent (nthTyps (l:=seq 1 (length t1)) (I:=a :: t1) b).
  intros. destruct e. repeat rewrite cast1_simpl. auto.
Qed.

Definition SuperKey F I (R: DBRel (A:=I) (F I)) k (pf: bounded I k) : Prop :=
 forall x y, FSetInterfaceNM.In x R -> FSetInterfaceNM.In y R ->
    gprojTuple pf x == gprojTuple pf y -> x == y. 

Inductive cw' I : Set :=
 | existCW' : forall n (pf: n < length  I) , Tuple (nthTyp pf ::nil) -> cw' I. 

Require Import ListSet.
Definition natd : forall x y : nat, {x = y} + {x <> y}. decide equality. Qed.

Fixpoint whereDemands I (e:whereExp I) : list nat
  := match e with
       | trueExp     => nil
       | falseExp    => nil
       | andExp a b  => set_union natd (whereDemands a) (whereDemands b)
       | orExp a b   => set_inter natd (whereDemands a) (whereDemands b)
       | notExp a    => set_diff natd (seq 0 (length I)) (whereDemands a)
       | compExp ty e => 
         match e with
           | compareEq x y => 
             match x, y with
               | atom ty v, var t' v' => t'::nil
               | var t' v', atom ty v => t'::nil
               | _, _ => nil
             end
           | compareLt x y => nil
           | compareGt x y => nil
         end
     end.

Definition whereConv1 I (e: whereExp I) : option (list (cw' I)).
refine (fix whereConv1 I e : option (list (cw' I)) :=
  match e with
    | trueExp  => None
    | falseExp => None
    | compExp t e => 
      match e with
        | compareEq x y => 
          match y as y' in atomicExp _ j return j = t ->  _  with
            | (atom t' v') => fun pfz => 
              match x as x' in atomicExp _ i return i = t -> _  with
                | (var t0 v) => fun  pfx => Some ( _ :: nil)
                | _ => fun _ => None
              end (refl_equal _)
            | _ => fun _ => None
          end (refl_equal _)
        | _ => None
      end
    | andExp a b => 
      match whereConv1 I a , whereConv1 I b with
        | Some l, Some l' => Some (l ++ l')
        | _ , _ => None
      end
    | orExp _ _  => None
    | notExp _ => None
  end).
subst. 
exact (@existCW' I t0 v (v',tt)).
Defined.

Definition nat_eq : forall (a b: nat), {a = b} + {a <> b}.
repeat decide equality.
Qed.

Definition projWhereN' I n (pf: n < length I) (l: list (cw' I)) : option (Tuple ((nthTyp  pf)::nil)).
refine (fix projWhereN' I n (pf: n < length I) (l: list (cw' I)) : option (Tuple ((nthTyp  pf)::nil)) :=
  match l with
    | nil => None
    | (existCW' t0 v a) :: x => 
      match nat_eq n t0 with 
        | left pf =>  _
        | _ =>  projWhereN' I n pf  x
      end
  end).
subst. 
simpl in *.
destruct a.
apply Some. 
erewrite (nthTyp_pf_irrel ).
eexact (t, tt).
Defined.

Definition projWhereN (I: Typing) 
 (n: nat) (pf: n < length I) 
 (e: whereExp I) : option (Tuple ((nthTyp  pf)::nil)).
intros I n pf e.
refine ( match whereConv1 e with
           | None => None
           | Some x => projWhereN' pf x
         end ) .
Defined.

Inductive cw l I : Set :=
 | existCW : forall (pf: bounded I l), Tuple (nthTyps pf) -> cw l I. 

Definition gprojWhere l (I: Typing)  
 (x: whereExp I) : bounded I l -> option (cw l I).
refine (fix gprojWhere l I x : bounded I l -> option (cw l I) :=
  match l as l' return l = l' -> bounded I l' -> option (cw l' I) with
    | nil => fun pfo pf => Some (@existCW nil I pf tt)
    | a :: b => fun pfo pf => 
      match pf with
        | conj H H0 => match gprojWhere b I x H0 as q 
                       return gprojWhere b I x H0 = q 
                       -> option (cw (a::b) I) with
                       | None => fun pfz => None
                       | Some q => fun pfz => _
                     end (refl_equal _) 
      end
  end (refl_equal _)).
Proof.
 refine (
   match q with 
     | existCW lf0 tp0 => match projWhereN H x with
                               | None => None
                               | Some s => Some (@existCW (a::b) I (conj H H0)  _)
                             end 
   end).
 simpl in *. destruct s. constructor. assumption.
 erewrite nthTyps_pf_irrel. 
 eauto.
Defined.

(* todo: any other key should work the same *)
Definition convertWhere 
 : forall I (e: whereExp I) , option (sigT (fun l => cw l I)) .
intros.
 pose (@gprojWhere (seq 0 (length I)) I e (seq_bounded0 _) ).
 destruct o. apply Some. apply (existT _ (seq 0 (length I))). assumption.
 apply None.
Defined.

(**
Definition decideSuperKey : forall F I (R: DBRel (A:=I) (F I)) 
  k (pf: bounded I k), {SuperKey R pf} + {~SuperKey R pf}.
refine (fun F I R k pf =>
  let check := 
    FSetInterfaceNM.for_all (fun x =>
      FSetInterfaceNM.for_all (fun y =>
        match gprojTuple pf x == gprojTuple pf y with
          | left _ => match x == y with
                        | left _ => true
                        | right _ => false
                      end
          | right _ => true
        end) R) R
  in
  match check as check' return check = check' -> _ with
    | true  => fun pf => left _
    | false => fun pf => right _ 
  end (refl_equal _)); unfold SuperKey in *; unfold check in *; intros.
Proof.
  apply for_all_2 in pf0. unfold For_all in *.  apply pf0 in H. apply for_all_2 in H. apply H in H0.
  destruct (equiv_dec (gprojTuple (l:=k) (I:=I) pf x)
             (gprojTuple (l:=k) (I:=I) pf y)).
   destruct (equiv_dec x y). auto. discriminate.
  rewrite H1 in *; order.
  unfold "==>". red. intros.
  repeat match goal with 
           | [ |- context [ if ?X then _ else _ ] ] => destruct X
         end; try reflexivity; elimtype False; try rewrite H2 in *; auto.
  unfold "==>". red. intros.
  case_eq (for_all
     (fun y1 : Tuple I =>
      if equiv_dec (gprojTuple (l:=k) (I:=I) pf x0)
           (gprojTuple (l:=k) (I:=I) pf y1)
      then if equiv_dec x0 y1 then true else false
      else true) R);
  case_eq (for_all
     (fun y1 : Tuple I =>
      if equiv_dec (gprojTuple (l:=k) (I:=I) pf y0)
           (gprojTuple (l:=k) (I:=I) pf y1)
      then if equiv_dec y0 y1 then true else false
      else true) R); intros; try reflexivity; elimtype False.
  rewrite H2 in H4.
  eapply for_all_2 in H4.
(** This is pretty weird to work out **)
**)  
