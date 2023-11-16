(* Copyright (c) 2009, Harvard University
 * All rights reserved.
 *
 * Authors: Ryan Wisnesky, Avraham Shinnar, Gregory Malecha
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

Require Import DataModel  Ynot.
Require Import Eqdep String List RAInterface SQL.
Require Import FSetFacts.
Require Import Optimizer.
Require Import FSetInterfaceNM.
Require Import Optimizer.
Require Import RelationalModel.

Set Implicit Arguments. Unset Strict Implicit.

Module Type DBInterface.

 Open Scope hprop_scope.

 Variable F : forall (I: Typing), DBSet I.
 
 (* the database itself *)
 Parameter tx : Set.
 Parameter rep : tx -> forall G, Env F G -> hprop.

 (* individual relations *)
 Parameter u : Typing -> Set.
 Parameter rep' : forall I, u I -> DBRel (F I) -> hprop.

 Parameter init : STsep __ (fun p: tx => @rep p nil tt).

 Parameter execQuery : forall G m (E: [Env F G]) 
    p q, STsep (E ~~ rep p E * [accurate m E] )
   (fun x : option (sigT u) => E ~~ rep p E * [accurate m E] * 
     match x with
       | None => [sql2RA q = None]
       | Some (existT J x) => 
         match sql2RA q with
           | None => [False]
           | Some (existT J' e) => 
             match typing_eq_dec J J' with
               | left pf => rep' (cast1  x pf) (raDenote (inst E e))
               | right _ => [False]
             end
         end
     end).

 Parameter setTable : forall G m (E: [Env F G])
  p I (s: string) (d: list (Tuple I)),
   STsep (E ~~ rep p E * [accurate m E] )
   (fun m' : Info => E ~~ [accurate m E] 
   * [@accurate F m' 
         ((s, I)::G) (mkTbl F d, E) ] *
     (@rep p ((s, I)::G)) (mkTbl F d, E)).

 Parameter printTable : forall I (E: [DBRel (A:=I) (F I)]) x, 
   STsep (E ~~ rep' x E) (fun _ : unit => E ~~ rep' x E).

 Parameter clearTable : forall I (E: [DBRel (A:=I) (F I)]) x,
   STsep (E ~~ rep' x E) (fun _ : unit => __).

 Parameter shutdown : forall G (E: [Env F G]) p, 
   STsep (E ~~ rep p E) (fun _: unit => __).

 Parameter serializeTable : forall G (E: [Env F G]) 
    p (tbl : string),
   STsep (E ~~ rep p E) (fun res : option string => E ~~ rep p E).

End DBInterface.

Module ImperativeDB (e: RAInterface) <: DBInterface.

 Open Scope hprop_scope.
 Open Scope stsepi_scope.

 Definition F := e.F.
 Definition tx := ptr.

 Definition u : Typing -> Set := e.u.
 Definition rep' : forall I, u I -> DBRel (F I) -> hprop := e.rep'.

 Fixpoint repA (G: Ctx) {struct G} : Env F G -> Env' u G -> hprop :=
  match G as G return Env F G -> Env' u G -> hprop with
    | nil => fun E L => [True]
    | (s, J) :: b => fun E L => 
      match E, L with
        | (R, E') , (p, L') => @rep' J p R * repA E' L'
      end
  end.

 Definition rep t (G: Ctx) (E: Env F G) := 
   Exists x :@ Env' u G, t ~~> x * repA E x .

 Ltac printGoal := idtac; 
   match goal with
     [ |- ?x ] => idtac x
   end.

 Fixpoint repA_except v I (G: Ctx) {struct G} 
  : Env F G -> Env' u G -> hprop :=
  match G as G return Env F G -> Env' u G -> hprop with
    | nil => fun E L => [True]
    | (s, J) :: b => fun E L => 
      match E, L with
        | (R, E') , (p, L') => 
          match eq_str v s, typing_eq_dec J I with
            | left pf1 , left pf2 => repA E' L'
            | _, _ => @rep' J p R * repA_except v I E' L'
          end
      end
  end.

 Fixpoint repA_lookup v I (G: Ctx) {struct G} 
  : Env F G -> Env' u G -> hprop :=
  match G as G return Env F G -> Env' u G -> hprop with
    | nil => fun E L => [True]
    | (s, J) :: b => fun E L => 
      match E, L with
        | (R, E') , (p, L') => 
          match eq_str v s, typing_eq_dec J I with
            | left pf1 , left pf2 => @rep' J p R
            | _, _ => repA_lookup v I E' L'
          end
      end
  end.

Lemma repA_join G e e' v I : 
  repA_except v I (G:=G) e e' * repA_lookup v I (G:=G) e e'
  ==> repA (G:=G) e e'.
Proof.
  induction G; simpl.
  sep fail auto.
  intuition.
  destruct e; 
    destruct (eq_str v a0); destruct (typing_eq_dec b I); 
  sep fail auto.
Qed.

Lemma repA_join_ex P Q G e e' v I : 
  P ==> Q ->
  repA_except v I (G:=G) e e' * repA_lookup v I (G:=G) e e' * P
  ==> repA (G:=G) e e' * Q.
Proof.
  intros. apply himp_split; auto.
  apply repA_join.
Qed.

Lemma repA_join_ex' P Q G e e' v I : 
  P ==> Q ->
  repA_lookup v I (G:=G) e e' * repA_except v I (G:=G) e e' * P
  ==> repA (G:=G) e e' * Q.
Proof.
  intros. apply himp_split; auto.
  apply himp_comm_prem.
  apply repA_join.
Qed.

Lemma repA_split G e e' v I : 
  repA (G:=G) e e' ==>
  repA_except v I (G:=G) e e' * repA_lookup v I (G:=G) e e'.
Proof.
  induction G; simpl.
  sep fail auto.
  intuition.
  destruct e; 
    destruct (eq_str v a0); destruct (typing_eq_dec b I); 
  sep fail auto.
Qed.

Definition repA_lookup_rel v I x (G: Ctx)
: forall (e:Env F G) (e':Env' u G) 
   (look:lookup' (T:=u) v I (G:=G) e' = Some x), 
 (DBRel (A:=I) (e.F I)).
Proof.
refine(fix repA_lookup_rel v I x (G: Ctx) {struct G}
: forall (e:Env F G) (e':Env' u G) 
  (look:lookup' (T:=u) v I (G:=G) e' = Some x), 
 (DBRel (A:=I) (e.F I)) :=
match G as G return 
forall (e:Env F G) (e':Env' u G) 
  (look:lookup' (T:=u) v I (G:=G) e' = Some x), 
 (DBRel (A:=I) (e.F I))  with
  | nil => fun E L pf => _
    | (s, J) :: b => fun E L pf => 
      (match E as Ex, L as Lx return E = Ex -> L = Lx -> _ with
        | (R, E') , (p, L') => fun _ _ =>
          match eq_str v s, typing_eq_dec J I with
            | left pf1 , left pf2 => cast1  R pf2
            | _, _ => @repA_lookup_rel v I x b E' L' _
          end
      end) (refl_equal _) (refl_equal _)
  end).
  discriminate.

  simpl in pf.
  destruct (eq_str v s); intuition.
  destruct (typing_eq_dec J I); intuition.
  subst. auto.

  simpl in pf.
  destruct (eq_str v s); intuition.
  subst. auto.
Defined.

Ltac deseqt := repeat  match goal with 
    | [|- context [eq_str ?x ?y]] => destruct (eq_str x y); try solve[intuition]
    | [|- context [typing_eq_dec ?x ?y]] => destruct (typing_eq_dec x y); try solve[intuition]
    | [H:context [eq_str ?x ?y]|- _] => destruct (eq_str x y); try solve[intuition]
    | [H:context [typing_eq_dec ?x ?y]|- _] => destruct (typing_eq_dec x y); try solve[intuition]
  end.

Lemma loopkup_repA_lookup v I G e e' x 
  (pf:lookup' (T:=u) v I (G:=G) e' = Some x) :
    repA_lookup v I (G:=G) e e' = rep' x (lookup v I e).
Proof.
  induction G; simpl; intuition.
  discriminate.
  destruct e. unfold lookup.
  deseqt;
  inversion pf. 
    subst x. 
    generalize e1. rewrite <- e1. intros.
    subst v.
    simpl. deseqt.
    unfold cast1, eq_rec_r.
    repeat rewrite <- eq_rec_eq. reflexivity.

    subst v. 
    simpl. deseqt.
    erewrite IHG; eauto.

    simpl. deseqt. erewrite IHG; eauto.
Qed.

(*
Lemma loopkup_repA_lookup v I G e e' x 
  (pf:lookup' (T:=u) v I (G:=G) e' = Some x) :
    repA_lookup v I (G:=G) e e' = rep' x (repA_lookup_rel e pf).
Proof.
  induction G; simpl; intuition.
  discriminate.
  destruct e.
  destruct (eq_str v a0);
  destruct (typing_eq_dec b I); simpl in *; intuition.
  inversion pf. subst x. 
  generalize e1. rewrite <- e1. intros.
  subst v.
  unfold cast1, eq_rec_r.
  repeat rewrite <- eq_rec_eq. auto.
Qed.
*)
  
(* For: Mathieu
Parameter ff: forall X, X.
Fixpoint repA_lookup_rel' v I x (G: Ctx) {struct G}
: forall (e:Env F G) (e':Env' u G) (look:lookup' (T:=u) v I (G:=G) e' = Some x), 
 (DBRel (A:=I) (e.F I)) :=
match G as G return 
forall (e:Env F G) (e':Env' u G) (look:lookup' (T:=u) v I (G:=G) e' = Some x), 
 (DBRel (A:=I) (e.F I))  with
  | nil => fun E L pf => (ff _)
    | (s, J) :: b => fun E L pf => 
      match E, L with
        | (R, E') , (p, L') => 
          match eq_str v s, typing_eq_dec J I with
            | left pf1 , left pf2 => cast1 (R : (@DBRel _ (F J))) pf2
            | _, _ => @repA_lookup_rel' v I x _ E' L' (ff _)
          end
      end
  end.
Next Obligation.
rewrite pf2 in R. exact R.
Defined.
Next Obligation.
destruct (eq_str v s); destruct (typing_eq_dec J I); simpl in *; intuition.
eelim H. eauto.
Defined.
*)
(*
Program Fixpoint repA_lookup_rel v I (G: Ctx) {struct G} : Env F G -> Env' u G -> 
option (DBRel (A:=I) (e.F I)) :=
match G as G return Env F G -> Env' u G -> option (DBRel (A:=I) (e.F I)) with
    | nil => fun E L => None
    | (s, J) :: b => fun E L => 
      match E, L with
        | (R, E') , (p, L') => 
          match eq_str v s, typing_eq_dec J I with
            | left pf1 , left pf2 => Some _
            | _, _ => repA_lookup_rel v I E' L'
          end
      end
  end.
Next Obligation.
rewrite pf2 in R. exact R.
Defined.
*)

   
Lemma eatany P Q R: P ==> Q * ?? -> P * R ==> Q * ??.
Proof.
  intros. red. intros.
  destruct H0. destruct H0. intuition.
  destruct (H x); auto.
  destruct H2. intuition.
  exists x1. exists (x2 * x0)%heap.
  intuition.
  eapply split_splice'; eauto.
Qed.

Lemma l1 : forall G P Q 
 I v (ee: Env' u G) x 
 (pf : lookup' (T:=u) v I (G:=G) ee = None) , 
(lookup v I x = empty0 F I -> repA (G:=G) x ee * P ==> Q) -> 
 repA (G:=G) x ee * P  ==> Q.
Proof.
  intros. revert H. 
  apply add_fact.
  unfold lookup.
  induction G.
  sep fail auto. firstorder.
  destruct a; destruct x; destruct ee.
  simpl in *. deseqt.
   discriminate.
   pose (IHG e0 e pf).
   apply himp_comm_prem.
   apply eatany.
   auto.

   pose (IHG e0 e pf).
   apply himp_comm_prem.
   apply eatany.
   auto.
Qed.

Definition doRead : forall G (E: [Env F G]) I v p,
 STsep (E ~~ rep p (G:=G) E)
     (fun x : u I => E ~~
         rep p (G:=G) E * rep' x (lookup v (F:=F) I (G:=G) E)).
intros.
refine ( ee <- SepRead p (fun ee => E ~~ repA E ee)  ;
         match @lookup' u v I G ee as pf 
         return  @lookup' u v I G ee = pf -> _ with
           | None => fun pf => {{ e.impNew I (empty0 F I) 
             <@> (E ~~ p ~~> ee * repA E ee) }}
           | Some x => fun pf => {{ e.impDupl 
             (E ~~~ lookup v I E) x
   <@> (E ~~ p ~~> ee * repA_except v I (G:=G) E ee) }} 
         end (refl_equal _)
        ).
unfold rep. sep fail auto.
unfold rep. sep fail auto.
unfold rep. sep fail auto.
erewrite <- loopkup_repA_lookup; eauto.
search_conc ltac:(apply repA_split).
unfold rep, rep'.
sep fail auto.
erewrite <- loopkup_repA_lookup; eauto.
search_conc ltac:(apply repA_join).
sep fail auto.
sep fail auto.
unfold repA.
unfold rep. intros.
 inhabiter. unpack_conc.
search_prem ltac:(eapply l1; auto). eauto.
sep fail auto. rewrite H. sep fail auto.
Qed.

Lemma l19 : forall I f,
 Morphisms.Proper (Morphisms.respectful SetoidClass.equiv SetoidClass.equiv)
    (whereDenote (I:=I) f).
apply whereDenoteProper.
Qed.

Print convertWhere.
Print gprojWhere.

 Definition execQuery' : forall G (E: [Env F G]) I  
  (q: raExp (fun _ => string) I) p, 
  STsep (E ~~ rep p E ) 
  (fun x : u I => E ~~ rep p E * rep' x (@raDenote F I (inst E q))).
 refine (fix execQuery' G (E: [Env F G]) I  
  (q: raExp (fun _ => string) I) p {struct q} : STsep (E ~~ rep p E ) 
  (fun x : u I => E ~~ rep p E * rep' x (@raDenote F I (inst E q))) :=
  match q in raExp _ I return 
  STsep (E ~~ rep p E ) 
  (fun x : u I => E ~~ rep p E * rep' x (@raDenote F I (inst E q)))
 with 
    | emptyExp J => {{ e.impNew J (empty0 F J) <@> _ }}  
    | unionExp  J r r0 => 
      R  <- execQuery' G E J r  p ;

      R0 <- execQuery' G E J r0 p 
  <@> (E ~~  rep' (I:=J) R (raDenote (F:=F) (inst (F:=F) (G:=G) E r))) ;

       e.impUnion 
             (E ~~~ @raDenote F J (inst E r)) 
             (E ~~~ @raDenote F J (inst E r0)) R R0  
      <@> (E ~~ rep p E) ;;

     e.impFree (E ~~~ raDenote (F:=F) (inst (F:=F) (G:=G) E r0)) R0 
     <@> (E ~~  rep p E * 
                rep' R (union  (raDenote (F:=F) (inst (F:=F) (G:=G) E r ))
                               (raDenote (F:=F) (inst (F:=F) (G:=G) E r0))))  ;;

     {{ Return R <@> (E ~~ rep p E *                 
                rep' R (union (raDenote (F:=F) (inst (F:=F) (G:=G) E r ))
                              (raDenote (F:=F) (inst (F:=F) (G:=G) E r0)))) }}

(* *) | interExp  J r r0 => 

      R  <- execQuery' G E J r  p ;

      R0 <- execQuery' G E J r0 p 
  <@> (E ~~  rep' (I:=J) R (raDenote (F:=F) (inst (F:=F) (G:=G) E r))) ;

      x <-  e.impInter 
             (E ~~~ @raDenote F J (inst E r)) 
             (E ~~~ @raDenote F J (inst E r0)) R R0  
      <@> (E ~~ rep p E) ;

     e.impFree (E ~~~ raDenote (F:=F) (inst (F:=F) (G:=G) E r)) R 
     <@> (E ~~ rep' (I:=J) R0  (raDenote (F:=F) (inst (F:=F) (G:=G) E r0)) *
                rep p E * 
                rep' x (inter (raDenote (F:=F) (inst (F:=F) (G:=G) E r ))
                              (raDenote (F:=F) (inst (F:=F) (G:=G) E r0))))  ;;

     e.impFree (E ~~~ raDenote (F:=F) (inst (F:=F) (G:=G) E r0)) R0 
     <@> (E ~~ rep p E * 
                rep' x (inter (raDenote (F:=F) (inst (F:=F) (G:=G) E r ))
                              (raDenote (F:=F) (inst (F:=F) (G:=G) E r0)))) ;;

     {{ Return x <@> (E ~~ rep p E *                 
                rep' x (inter (raDenote (F:=F) (inst (F:=F) (G:=G) E r ))
                              (raDenote (F:=F) (inst (F:=F) (G:=G) E r0)))) }}

(* *)  | prodExp  J0 J1 r0 r1 => 
      R0  <- execQuery' G E J0 r0  p ;

      R1 <- execQuery' G E J1 r1 p 
  <@> (E ~~  rep' (I:=J0) R0 (raDenote (F:=F) (inst (F:=F) (G:=G) E r0))) ;

      x <-  e.impProd 
             (E ~~~ @raDenote F J0 (inst E r0)) 
             (E ~~~ @raDenote F J1 (inst E r1)) R0 R1  
      <@> (E ~~ rep p E) ;

     e.impFree (E ~~~ raDenote (F:=F) (inst (F:=F) (G:=G) E r0)) R0 
     <@> (E ~~ rep' (I:=J1) R1  (raDenote (F:=F) (inst (F:=F) (G:=G) E r1)) *
                rep p E * 
                rep' x (prodRel (raDenote (F:=F) (inst (F:=F) (G:=G) E r0 ))
                                (raDenote (F:=F) (inst (F:=F) (G:=G) E r1)))) ;;

     e.impFree (E ~~~ raDenote (F:=F) (inst (F:=F) (G:=G) E r1)) R1 
     <@> (E ~~ rep p E * 
                rep' x (prodRel (raDenote (F:=F) (inst (F:=F) (G:=G) E r0 ))
                                (raDenote (F:=F) (inst (F:=F) (G:=G) E r1)))) ;;

     {{ Return x <@> (E ~~ rep p E *                 
                rep' x (prodRel (raDenote (F:=F) (inst (F:=F) (G:=G) E r0 ))
                                (raDenote (F:=F) (inst (F:=F) (G:=G) E r1)))) }}

(* *) | selectExp J r f => 

      R  <- execQuery' G E J r p ;
      x <- @e.impSelect _ (whereDenote f) (l19 _ )
                          (E ~~~ @raDenote F J (inst E r)) R <@> (E ~~ rep p E) ;

     e.impFree (E ~~~ raDenote (F:=F) (inst (F:=F) (G:=G) E r)) R 
     <@> (E ~~ rep p E * 
                rep' x (select (whereDenote f)
                   (raDenote (F:=F) (inst (F:=F) (G:=G) E r)))) ;;

     {{ Return x <@> (E ~~ rep p E *                 
                rep' x ((select (whereDenote f)
                   (raDenote (F:=F) (inst (F:=F) (G:=G) E r))))) }}


(* *) | gprojExp J l pf r =>      

      R  <- execQuery' G E J r p ;

      x <-  e.impProj l pf
             (E ~~~ @raDenote F J (inst E r)) R 
      <@> (E ~~ rep p E) ;

     e.impFree (E ~~~ raDenote (F:=F) (inst (F:=F) (G:=G) E r)) R 
     <@> (E ~~ rep p E * 
                rep' x (gprojRel pf 
                   (raDenote (F:=F) (inst (F:=F) (G:=G) E r)))) ;;

     {{ Return x <@> (E ~~ rep p E *                 
               rep' x (gprojRel pf 
                   (raDenote (F:=F) (inst (F:=F) (G:=G) E r)))) }}

     | varExp v pd => {{ doRead E v pd p }}
  end); unfold rep';
  sep fail auto.
Qed.

Lemma rep'_push : forall I x e' e, 
  e [=] e' -> rep' (I:=I) x e' ==> rep' x e.
Proof.
 intros. unfold rep'. apply e.rep'_push.
 unfold "[=]" in *. intros.
 pose (H a). intuition.
Qed.

Definition execQuery : forall G m (E: [Env F G]) 
    p q, STsep (E ~~ rep p E * [accurate m E] )
   (fun x : option (sigT u) => E ~~ rep p E * [accurate m E] * 
     match x with
       | None => [sql2RA q = None]
       | Some (existT J x) => 
         match sql2RA q with
           | None => [False]
           | Some (existT J' e) => 
             match typing_eq_dec J J' with
               | left pf => rep' (cast1  x pf) (raDenote (inst E e))
               | right _ => [False]
             end
         end
     end).
intros. 
refine (
match sql2RA q as pf return sql2RA q = pf -> _ with
  | None => fun pf => {{ Return None <@> (E ~~ rep p E * [accurate m E]) }}
  | Some (existT J' e) => fun pf => 
    e0 <- optimize m E e <@> (E ~~ rep p E) ;
    x <- execQuery' E e0 p   
       <@> (E ~~ [ (raDenote (inst E e)) [=] raDenote (inst E e0)] *
                 [accurate m E] ) ;
    {{ Return (Some (existT u J' x)) 
      <@> (E ~~ rep p E * 
 [ (raDenote (inst E e)) [=] raDenote (inst E e0)] * rep' x (raDenote (inst E e0)) * [accurate m E]) }}
end (refl_equal _) ).
 sep fail auto.
 sep fail auto.
 sep fail auto.
 sep fail auto.
 sep fail auto.
 sep fail auto. rewrite pf. 
  destruct (typing_eq_dec J' J'). unfold cast1. unfold eq_rec_r.
  rewrite <- eq_rec_eq. sep fail auto. 
  apply rep'_push.
  assumption.
  elim n. trivial.
  sep fail auto. 
  sep fail auto.
Qed.

 Definition setTable : forall G m (E: [Env F G])
  p I (s: string) (d: list (Tuple I)),
   STsep (E ~~ rep p E * [accurate m E] )
   (fun m' : Info => E ~~ [accurate m E] 
   * [@accurate F m' 
         ((s, I)::G) (mkTbl F d, E) ] *
     (@rep p ((s, I)::G)) (mkTbl F d, E)).
 intros.
 refine ( l <- SepRead p (fun l => E ~~ repA E l * [accurate m E]) ;
          x <- e.impNew I (mkTbl F d) 
             <@> (E ~~ p ~~> l * repA E l * [accurate m E]) ;
          p ::=  (x,l) <@> (E ~~ repA E l * [accurate m E] ) ;; 
          {{ Return (updInfo m s I (mkInfo (mkTbl F d))) 
          <@> (E ~~ [accurate m E] 
   * [@accurate F (updInfo m s I (mkInfo (mkTbl F d))) 
         ((s, I)::G) (mkTbl F d, E) ] *
            p ~~> (x,l) * repA E l (* 
     (@rep p ((s, I)::G)) (mkTbl F d, E) *) )   }} ).
 unfold rep. sep fail auto.
 sep fail auto.
 sep fail auto.
 sep fail auto.
 sep fail auto.
 sep fail auto.
 unfold rep. simpl. sep fail auto.
 cut (accurate m x0 -> accurate (F:=F) (updInfo m s I (mkInfo (I:=I) (mkTbl F (I:=I) d)))
      (G:=(s, I) :: G) (mkTbl F (I:=I) d, x0)).
 intros. sep fail auto. apply lk3; assumption.
 unfold rep. sep fail auto.
 Qed. 

Definition printTable : forall I (E: [DBRel (A:=I) (F I)]) x, 
   STsep (E ~~ rep' x E) (fun _ : unit => E ~~ rep' x E).
 exact (@e.impPrint).
Qed.

Definition init : STsep __ (fun p: tx => @rep p nil tt).
 refine ( {{ New tt }} );
 unfold rep; sep fail auto.
Qed.

Definition shutdown' G : forall (E: [Env F G])  (p: Env' u G),
  STsep (E ~~ @repA G E p) (fun _:unit => __).
 refine (fix shutdown' G : forall  (E: [Env F G]) (p: Env' u G), 
           STsep (E ~~ @repA G E p) (fun _:unit => __)  :=
   match G with
     | nil => fun _ _ => {{ Return tt }}
     | a :: b => fun E p => _
   end ).
sep fail auto.
sep fail auto. 
 destruct a.
 simpl in *. destruct p.
 refine ( e.impFree (E ~~~ fst E) u0 <@> (E ~~ repA (snd E) e) ;;
         {{ @shutdown' b (E ~~~ snd E) e  }} ).
 unfold rep'.
 sep fail auto.
 destruct x. simpl. sep fail auto.
sep fail auto.
sep fail auto.
sep fail auto.
Qed. 

 Definition shutdown : forall G (E: [Env F G]) p, 
   STsep (E ~~ rep p E) (fun _: unit => __).
 intros. refine ( x <- SepRead p (fun x: Env' u G => E ~~ @repA G E x) ;
                  SepFree p <@> (E ~~ @repA G E x) ;;
                  {{ shutdown'  E _ }} ); 
 unfold rep; sep fail auto.
Qed.

Definition clearTable : forall I (E: [DBRel (A:=I) (F I)]) x,
   STsep (E ~~ rep' x E) (fun _ : unit => __).
 exact (e.impFree).
Qed.

Fixpoint getTyping (tbl : string) (G : Ctx) : [Env F G] -> option (sigT (fun I:Typing => [DBRel (F I)]%type)) :=
  match G as G return [Env' (fun I : Typing => DBRel (A:=I) (F I)) G] -> option (sigT (fun I:Typing => [DBRel (F I)]%type)) with
    | nil => fun _ => None
    | pair tbl' a :: b => fun a' => 
      if string_dec tbl tbl' then Some (existT _ a (a' ~~~ fst a')) else getTyping tbl (a' ~~~ snd a')
  end. 

Definition serializeTable : forall G (E: [Env F G]) p (tbl : string),
  STsep (E ~~ rep p E) (fun res : option string => E ~~ rep p E).
  refine (fun G E p tblName =>
    match getTyping tblName E as q return getTyping tblName E = q -> _ with
      | None   => fun _ => {{ Return None }}
      | Some (existT I' E') => fun pf =>  
        tbl <- doRead E I' tblName p ;
        result <- e.impSerialize (E ~~~ (lookup (F:=F) tblName I' (G:=G) E))
                    tbl <@> (E ~~ rep p E)  ;
        e.impFree (E ~~~ (lookup (F:=F) tblName I' (G:=G) E))
               tbl <@> (E ~~ rep p E) ;;
        {{ Return (Some result) <@> (E ~~ rep p E) }}
    end (refl_equal _));
 sep fail auto.
Qed.

End ImperativeDB.

