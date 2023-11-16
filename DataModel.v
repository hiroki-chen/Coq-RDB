(* Copyright (c) 2009, Harvard University
 * All rights reserved.
 *
 * Authors: Ryan Wisnesky, Avraham Shinnar
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

Require Import OrderedTypeNM Omega.
Require Import Ascii String.
(* Require Import Assumptions JMeq Eqdep. *)
Require Import SetoidDec.
Require Import SetoidClass.
Module OT := OrderedTypeNM.

Set Implicit Arguments. Unset Strict Implicit.

Require Export Typ.
Require Import Eqdep.

Definition cast1 : forall (I J: Typing) (u: Typing -> Set), 
 u I -> I = J -> u J.
intros.
subst. assumption.
Defined.

Set Implicit Arguments. Unset Strict Implicit.

Lemma cast1_simpl I (u: Typing -> Set) (x: u I) (pf:I=I) 
 : @cast1 I I u x pf = x.
Proof.
  intros. unfold cast1, eq_rec_r. rewrite <- eq_rec_eq. auto.
Qed.

(* Helpers for cartesian product *************************)

Definition fuseTuples (I J: Typing) 
 (x: Tuple I) (y: Tuple J) : Tuple (I ++ J).
Proof.
 intros.
  induction I. 
   exact y.
   simpl in *. destruct x. constructor. 
    assumption. apply IHI. assumption.
Defined.
(*
Eval compute in (fuseTuples test_tuple test_tuple').
*)

(* Tuple ordering ******************************************)

Fixpoint eqTuple (A: Typing) : forall (x y: Tuple A), Prop :=
   match A as A return (forall (x y: Tuple A), Prop) with
     | nil => fun _ _ => True
     | h :: tl => fun x y => (fst x) == (fst y) /\    
       eqTuple (snd x) (snd y) 
   end.

Fixpoint ltTuple (A: Typing) : forall(x y: Tuple A), Prop :=
 match A return (forall (x y: Tuple A), Prop) with
  | nil => fun _ _ => False
  | h :: t => fun x y =>  (fst x) << (fst y) \/ 
                         ((fst x) == (fst y) /\
                         ltTuple (snd x) (snd y))
 end.

Definition compTuple (A: Typing) : forall (x y: Tuple A), 
  Compare (@ltTuple A) (@eqTuple A) x y.
Proof.
induction A; destruct x; destruct y. 
apply EQ. apply I.
destruct (ordCompare t t1).
apply LT. left. assumption.
destruct (IHA t0 t2);
[apply LT | apply EQ | apply GT]; simpl; intuition.
apply GT. left. assumption.
Defined.

Require Import SetoidClass.
Require Import RelationClasses.

Definition eqTupleEquiv (A:Typing) : Equivalence (@eqTuple A).
Proof. split; unfold Reflexive, Symmetric, Transitive;
  induction A; simpl; intuition.
   simpl in *. rewrite H1. assumption.
   simpl in *. eapply IHA. eauto. eauto.
Qed.

Definition eqTupleSetoid (A:Typing) : Setoid (Tuple A).
Proof. 
  intros. esplit. eexact (eqTupleEquiv A). 
Defined.

Lemma ltTuple_trans (A: Typing) : Transitive (@ltTuple A).
Proof.
  red.
  induction A; simpl; intuition; simpl in *. 
  rewrite H in H1. intuition.
  rewrite H0 in H1. intuition.
  rewrite H. intuition.
  right. split. rewrite H; auto. eapply IHA; eauto.
Qed.

Lemma ltTuple_not_eq (A: Typing) 
 (x y: Tuple A) : ltTuple x y -> ~ eqTuple x y.
Proof.
 induction A. 
   simpl. intuition.
   simpl. intuition; simpl in *.
   rewrite H1 in H0. apply (ordLt_irrefl H0).
   eapply IHA; eauto. 
Qed.

(* tactics are nice.  It looks waaay more painful in agda/alfa *)
Instance tupleOrd (A:Typing): OT.OrderedType (Tuple A).
  intros; refine(@OT.Build_OrderedType
    (@Tuple A)
    (@eqTupleSetoid A)
    (@ltTuple A)
    (@ltTuple_trans A)
    (@ltTuple_not_eq A)
    (@compTuple A)).
Defined.

Canonical Structure tupleOrd.
Canonical Structure eqTupleSetoid.

(* Decidability of typing equality *) 

Lemma typing_eq_dec : forall (a b: Typing), {a = b} + {a <> b}.
Proof.
 intros; repeat decide equality.
Qed.

(* Helpers for iterated projection *********************)

Lemma contra_1 : forall n, n < 0 -> False.
Proof.
 intros; omega.
Qed.

Lemma down_1 : forall a b, S a < S b -> a < b.
Proof.
 intros; omega.
Qed.

Require Import List.
Open Scope list_scope.

Definition nthTyp (I: Typing) (n: nat)  
 (pf: n < length I) : typ.
refine (fix nthTyp' (I: Typing) 
 (n: nat) : n < length I -> typ :=
 match I as I' , n as n' return I = I' -> n = n' -> n' < length I' -> typ with
   | x :: y   , O => fun _ _ _ => x 
   | x :: y   , S n' => fun _ _ _ => nthTyp' y n' _ 
   | _ , _ => fun _ _ _ => False_rec _ _
 end (refl_equal _) (refl_equal _)).
Proof.
  simpl in *. apply contra_1 with (n := n); assumption.
  simpl in *. apply down_1; assumption.
Defined. 

Definition projTupleN (I: Typing) 
 (n: nat) (pf: n < length I) 
 (t: Tuple I) : Tuple ((nthTyp  pf)::nil).
refine (fix projTupleN (I: Typing) 
 (n: nat)    : forall (pf: n  < length I ), Tuple I -> 
                 Tuple ((nthTyp  pf)::nil) :=
 match I as I' , n as n' return  I = I' -> n = n' -> 
               forall (pf: n' < length I'), Tuple I' ->
                 Tuple ((nthTyp  pf)::nil) with
   | x :: y , O => fun _ _ _ t => (fst t, tt) 
   | x :: y , S n' => fun _ _ _ t => projTupleN  y n' _ (snd t) 
   | _ , _ => fun _ _ _ => False_rec _ _
 end (refl_equal _) (refl_equal _)).
Proof.
  simpl in *. apply contra_1 with (n := n); assumption.
Defined.

Fixpoint bounded (I: Typing) (l: list nat) : Prop :=
 match l with
   | nil => True
   | a :: b => a < length I /\ bounded I b
 end.

Definition nthTyps l (I: Typing) (pf: bounded I l) : Typing.
intros l. induction l.
  intros. exact nil.
  simpl. intros. destruct pf.
  apply cons. apply (nthTyp H). apply (IHl I H0).
Defined.

Definition gprojTuple l (I: Typing) (pf: bounded I l) 
 (x: Tuple I)  : Tuple (nthTyps pf).
intros.
 induction l.
  constructor. 
  simpl. case pf. intros. simpl. 
  pose (projTupleN l0 x). simpl in t. exact (fst t, IHl b).
Defined.

(* Projection and Product respect setoid equality *******************)

Instance fuseTuples_push (I J: Typing) : 
  Proper (equiv ==> equiv ==> equiv) (@fuseTuples I J).
Proof. repeat red.
 intros. induction I.
  simpl; trivial.
  simpl in *. destruct x; destruct y; destruct H.
  simpl in *.
   split. 
    assumption.
    apply IHI. trivial.
Qed.

Lemma projTupleN_push0 n I  
 (pf: n < length I) (x y: Tuple I) :
  x == y -> (projTupleN pf x) == (projTupleN pf y).
 double induction n I.
  simpl. intros. assert False. omega. contradiction.
  simpl. intros. destruct H0. split; try constructor; assumption.
  simpl. intros. assert False. omega. contradiction.
  simpl in *. intros. 
  apply H0. destruct H1. assumption.
Qed.


Lemma projTupleN_push' (I: Typing) (n: nat) 
 (pf: n < length I) (x y: Tuple I) :
  eqTuple x y ->  (fst (projTupleN  pf x)) == 
                      (fst (projTupleN  pf y)).
Proof.
 intros. apply (projTupleN_push0 pf H).
Qed.

Instance projTupleN_push n I (pf: n < length I) : 
  Proper (equiv ==> equiv) (@projTupleN I n pf).
Proof.
 intros. constructor; try simpl; trivial.
 apply projTupleN_push'. assumption.
Defined.

Lemma gprojTuple_push0 l (I: Typing) (pf: bounded I l) (x y: Tuple I) :
  eqTuple x y -> eqTuple (gprojTuple pf x) (gprojTuple pf y).
Proof.
 intros. 
  induction l. 
   constructor.
   simpl in *. case pf. intros. pose (IHl b).
   constructor. 
    simpl. apply projTupleN_push'. assumption.
    simpl. assumption.
Qed.

Instance gprojTuple_push l (I: Typing) (pf: bounded I l)  : 
  Proper (equiv ==> equiv) (gprojTuple pf).
Proof.
 unfold Proper. simpl.
 intros. unfold "==>"%signature. 
 apply gprojTuple_push0.
Defined.

  Lemma seq_join n m q : seq n m ++ seq (n+m) q = seq n (m+q).
  Proof. 
    intros n m; revert m n.
    induction m; simpl; intuition.
    f_equal. rewrite <- IHm.
    simpl; rewrite <- plus_n_Sm. auto.
  Qed.

  Lemma bounded_cons I l a: bounded I l -> bounded (a::I) (map S l).
  Proof.
    induction l; simpl; intuition.
  Qed.

  Lemma bounded_len I J l : length I = length J -> bounded I l -> bounded J l.
  Proof. induction l; simpl; intuition. Qed.

  Lemma seq_bounded K I : bounded (K ++ I) (seq (length K) (length I)).
  Proof.
    induction I; simpl; intuition.
    rewrite app_length; simpl; omega.
    rewrite <- seq_shift.
    assert (len:length (a::K++I) = length (K ++ a :: I)) 
      by (repeat (rewrite app_length; simpl); omega).
    apply (bounded_len len).
    apply bounded_cons. auto.
  Qed.

  Lemma seq_bounded0 I : bounded I (seq 0 (length I)).
  Proof. intros. apply (seq_bounded nil). Qed.

  Lemma bounded_app_weaken {I l}: bounded I l -> forall J, bounded (I ++ J) l.
  Proof.
    intros I l b J. revert I l b. 
    induction J; simpl; intuition.
    rewrite app_nil_r. auto.
    replace (I ++ a :: J) with ((I ++ a::nil) ++ J) by (rewrite app_ass; auto).
    apply IHJ.
    induction l; simpl; intuition; simpl; inversion b; auto.
    rewrite app_length. omega.
  Qed.

 Require Import Arith.

  Lemma nth_seq_eq K I J pf : I = nthTyps (l:=seq (length K) (length I)) (I:=K ++ I ++ J) pf.
  Proof.
    intros K I; revert K.
    induction I; intuition.
    simpl. destruct pf.
    f_equal.
    
    induction K; simpl in *; intuition.
      apply IHK. fold bounded seq in *.
      assert (len:length ((a::K++I)++J) = length (K ++ a :: I ++ J)).
      repeat (rewrite app_length; simpl). omega.
      apply (bounded_len len).
      rewrite <- seq_shift. apply bounded_cons.
      apply bounded_app_weaken.
      apply seq_bounded.

    pose (IHI (K++(a::nil)) J) as e.
    rewrite app_length, plus_comm, app_ass in e. simpl in e.
    apply e.
  Qed.

  Lemma nth_seq0_eq {I J} pf : I = nthTyps (l:=seq 0 (length I)) (I:=I ++ J) pf.
  Proof. intros. apply (@nth_seq_eq nil). Qed.

  Lemma bounded_assoc {K I J l} : bounded ((K ++ I) ++ J) l -> bounded (K ++ I ++ J) l.
  Proof.
    intros. rewrite <- app_ass. auto.
  Defined.

  Require Import Eqdep.

  Lemma fuseTuples_assoc I J K (a:Tuple I) (b:Tuple J) (c:Tuple K) 
    : fuseTuples a (fuseTuples b c) = 
      cast1 (fuseTuples (fuseTuples a b) c) ((symmetry (@app_assoc _ I J K))).
  Proof.
    Ltac cast_simpler := match goal with 
      [|- context [@cast1 ?I ?J ?u ?x ?pf]] => 
      (rewrite cast1_simpl) ||
      (cut (I = J)
        ; [let GG:=fresh "GG" in dependent rewrite GG; clear GG|auto])
    end.

    induction I; simpl. intuition.
    cast_simpler. auto.
    intros.
    destruct a0.
    rewrite IHI.
    clear.
    repeat match goal with
      [|- context [cast1 ?x ?y]] => generalize x
    end; intros;
    repeat match goal with
      [|- context [cast1 ?x ?y]] => generalize y
    end; intros. 
    destruct e0.
    repeat rewrite cast1_simpl.
    auto.
  Qed.

  Lemma fcast1_fst I J a (pf:a::I=a::J) x 
    :     fst (A:=typDenote a) (B:=Tuple J) (@cast1 (a::I) (a::J) Tuple x pf) = 
    fst (A:=typDenote a) (B:=Tuple I) x.
  Proof.
    intros I J a pf x.
    inversion pf. destruct H0.
    rewrite cast1_simpl. auto.
  Qed.

  Lemma fcast2_snd I a b (pf:a::I=b::I) x
    : snd  (@cast1 (a::I) (b::I) Tuple x pf) = snd  x.
  Proof.
    intros I a b pf x.
    inversion pf. destruct H0.
    rewrite cast1_simpl. auto.
  Qed.

  Lemma cast1_prop I J (u:Typing->Set) {sI:Setoid (u I)} {sJ:Setoid (u J)}
  (x y : u I) : x == y -> forall (pf : I = J)
    (pfeq:forall x y, (equiv (Setoid:=sI) x y) -> equiv (Setoid:=sJ) (cast1 x pf) (cast1 y pf)),
    cast1  x pf == cast1  y pf.
  Proof.
    intros. destruct pf.
    repeat rewrite cast1_simpl. 
    pose (pfeq _ _ H) as e. repeat rewrite cast1_simpl in e. auto.
  Qed.
  
  Lemma cast1_pf_irrel I J (u:Typing->Set) x (pf1 pf2:I=J) : cast1 x pf1 = cast1 (u:=u) x pf2.
  Proof.
    intros. destruct pf1.
    repeat rewrite cast1_simpl.
    auto.
  Qed.

  Lemma cast1_nest u I J K (pf1:I=J) (pf2:J=K) b : 
    (cast1 (cast1 (u:=u)  b pf1) pf2) = cast1 b (Logic.eq_trans pf1 pf2).
  Proof.
    intros. destruct pf1; destruct pf2. repeat rewrite cast1_simpl. auto.
  Qed.

  Lemma nth_seq1_eq {I J} a pf : I = nthTyps (l:=seq 1 (length I)) (I:=a::I ++ J) pf.
  Proof. intros. pose (@nth_seq_eq (a::nil)). simpl in e. apply e. Qed.

  Lemma nthTyp_pf_irrel I n pf1 pf2 : @nthTyp I n pf1 = @nthTyp I n pf2.
  Proof.
    induction I; simpl.
    inversion pf1.
    destruct n; simpl; auto.
  Qed.

  Lemma nthTyp_shift A I n pf1 pf2 : @nthTyp (A::I) (S n) pf1 = @nthTyp I n pf2.
  Proof.
    intros. simpl. apply nthTyp_pf_irrel.
  Qed.

  Lemma nthTyps_shift M A I n pf1 pf2 : nthTyps (l:=seq n M) (I:=I) pf1 =
   nthTyps (l:=seq (S n) M) (I:=A :: I) pf2.
  Proof. Hint Resolve nthTyp_pf_irrel.
    induction M; simpl; intuition.
    destruct pf1; destruct pf2. f_equal; auto.
  Qed.

  Lemma nthTyps_pf_irrel l I pf1 pf2 : nthTyps (l:=l) (I:=I) pf1 = nthTyps (l:=l) (I:=I) pf2.
  Proof.
    induction l; simpl; intuition.
    destruct pf1; destruct pf2.
    f_equal; auto.
  Qed.

  Lemma projTupleN_pf_irrel I n pf1 pf2 pf3 x : @projTupleN I n pf1 x = cast1 (@projTupleN I n pf2 x) pf3.
  Proof. 
    induction I; simpl. inversion pf1.
    destruct n; simpl; auto. intros.
    repeat rewrite cast1_simpl. auto.
    intros.
    apply IHI.
  Qed.

  Lemma gprojTuple_pf_irrel l I pf1 pf2 ll pf3 : gprojTuple (l:=l) (I:=I) pf1 ll = cast1 (gprojTuple (l:=l) (I:=I) pf2 ll) pf3.
  Proof.
    induction l; simpl; intuition.
    rewrite cast1_simpl; auto.
    destruct pf1; destruct pf2. 
    inversion pf3. 
    rewrite (IHl _ _ _ _ H1).
    assert (pf4:nthTyp (I:=I) (n:=a) l1 :: nil = nthTyp (I:=I) (n:=a) l0 :: nil) by (f_equal; auto).
    rewrite (@projTupleN_pf_irrel _ _ l0 l1 pf4).
    generalize ((projTupleN (I:=I) (n:=a) l1 ll)).
    generalize (gprojTuple (l:=l) (I:=I) b0 ll). intros. clear.
    destruct t0; simpl.
    inversion pf4. destruct H0.
    rewrite cast1_simpl. simpl. 
    inversion pf3. destruct H0.
    repeat rewrite cast1_simpl. auto.
  Qed.

  Lemma fst_cast1s A I J B K K' (t0:typDenote A) (u:Tuple I) (t:Tuple J) pf1 pf2 :
    fst (@cast1 (A::I) (B::K) Tuple (t0, u) pf1) 
    == 
    fst (@cast1 (A::J) (B::K') Tuple (t0, t) pf2).
  Proof.
    intros. inversion pf1. destruct H0. destruct H1.
    rewrite cast1_simpl. simpl. clear.
    inversion pf2. destruct H0. repeat rewrite cast1_simpl. simpl. reflexivity.
  Qed.

  (* (n:nat) *)
  Lemma projTupleN_shift K I k l pf1 pf2 pf3 : 
      projTupleN (I:=K++I) (n:=length K) pf1 (fuseTuples k l) ==
      cast1 (projTupleN (I:=I) (n:=0) pf2 l) pf3.
  Proof.
    induction K; simpl; intros.
      rewrite (projTupleN_pf_irrel pf3 _). intuition.
      
      destruct k. simpl. intuition.
      
      cut ((projTupleN (I:=K ++ I) (n:=length K)
        (down_1 (a:=length K) (b:=length (K ++ I)) pf1)
        (fuseTuples (I:=K) (J:=I) t0 l)) == 
         (cast1 (projTupleN (I:=I) (n:=0) pf2 l) pf3)).
      inversion 1. auto.
      apply IHK.
  Qed.

  Lemma gprojTuple_shift M I n (l:Tuple I) A a pf1 pf2 pf3 : 
      gprojTuple (l:=seq (S n) M) (I:=A::I) pf1 (a,l) ==
      cast1 (gprojTuple (l:=seq n M) (I:=I) pf2 l) pf3.
  Proof.
    induction M; simpl; intuition.
    destruct pf1; destruct pf2. simpl. auto.
    split.
    
    assert (pf3' : nthTyp (I:=I) (n:=n) l1 :: nil =
      nthTyp (I:=I) (n:=n) (down_1 (a:=n) (b:=length I) l0) :: nil)
     by (f_equal; apply nthTyp_pf_irrel).

    rewrite (projTupleN_pf_irrel pf3').
 
    destruct (projTupleN (I:=I) (n:=n) l1 l).  simpl.
    apply (@fst_cast1s (nthTyp (I:=I) (n:=n) l1) nil
      (nthTyps (l:=seq (S n) M) (I:=I) b0)
      (nthTyp (I:=I) (n:=n) (down_1 (a:=n) (b:=length I) l0)) nil
      (nthTyps (l:=seq (S (S n)) M) (I:=A :: I) b) t). 

    assert(pf3' : nthTyps (l:=seq (S n) M) (I:=I) b0 =
      nthTyps (l:=seq (S (S n)) M) (I:=A :: I) b) 
    by eapply nthTyps_shift.
    rewrite (IHM I (S n) l _ a b b0 pf3').
    clear.
    generalize (gprojTuple (l:=seq (S n) M) (I:=I) b0 l).
    generalize (fst (projTupleN (I:=I) (n:=n) l1 l)).
    generalize dependent (nthTyps (l:=seq (S (S n)) M) (I:=A :: I) b). 
    clear. intros.
    destruct pf3'. rewrite cast1_simpl. 
    rewrite fcast2_snd. reflexivity.
  Qed.

  (* let pf := (bounded_assoc (bounded_app_weaken (seq_bounded K I) J)) in *)
  Lemma gprojTuple_fuseTuples_id' I J a b (pf:bounded (I ++ J) (seq 0 (length I))):
    (gprojTuple pf (l:=seq 0 (length I)) (I:=I ++ J)
      (fuseTuples (I:=I) (J:=J) a b)) == cast1 a (nth_seq0_eq pf).
  Proof.
    induction I; simpl; intuition.
    destruct pf. simpl. split.
      rewrite fcast1_fst. reflexivity.

     assert (pf:forall l pf2 pf3, (gprojTuple (l:=seq 1 (length I)) (I:=a :: I ++ J) b1
        (a1, l) ==
     cast1 (gprojTuple (l:=seq 0 (length I)) (I:=I ++ J) pf2 l) pf3)) by (intros; apply gprojTuple_shift).
     assert (pf2 : bounded (I ++ J) (seq 0 (length I))) by apply (bounded_app_weaken (seq_bounded0 I)).
     assert (pf3:nthTyps (l:=seq 0 (length I)) (I:=I ++ J) pf2 =
                nthTyps (l:=seq 1 (length I)) (I:=a :: I ++ J) b1).
       rewrite <- nth_seq0_eq, <- nth_seq1_eq. auto.
     rewrite (pf _ pf2 pf3).
     transitivity (@cast1 _ _ Tuple (@cast1 _ _ Tuple  b (nth_seq0_eq pf2)) pf3).
     eapply cast1_prop.
     apply IHI.
     clear. simpl. intros.
     revert H.
     generalize dependent (nthTyps (l:=seq 0 (length I)) (I:=I ++ J) pf2).
     generalize dependent (nthTyps (l:=seq 1 (length I)) (I:=a :: I ++ J) b1). clear.
     intros. destruct pf3. repeat rewrite cast1_simpl. auto.
     clear.
     rewrite cast1_nest.
     repeat match goal with
              [|- context [cast1 ?x ?y]] => generalize y
            end; intros.
     simpl in e. clear.
     generalize dependent (nthTyps (l:=seq 1 (length I)) (I:=a :: I ++ J) b1).
     intros. destruct e0. repeat rewrite cast1_simpl. simpl. reflexivity.
  Qed.

  Lemma gprojTuple_fuseTuples_id I J a b pf:
    (gprojTuple pf (l:=seq 0 (length I)) (I:=I ++ J)
      (fuseTuples (I:=I) (J:=J) a b)) == cast1 a (nth_seq0_eq pf).
  Proof. intros. apply gprojTuple_fuseTuples_id'. Qed.

(*  Lemma gprojTuple_fuseTuples_id K I J k i j (pf:bounded (K ++ I ++ J) (seq (length K) (length I))): 
    (gprojTuple pf (l:=seq (length K) (length I)) (I:=K ++ I ++ J)
      (fuseTuples k (fuseTuples i j))) == cast1 i (nth_seq_eq pf).
  Proof. *)
