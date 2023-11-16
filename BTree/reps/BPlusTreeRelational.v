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
Require Import Minus Div2.
Require Import ProofIrrelevance Eqdep Think.
Require Import List.

Require Import OrderedTypeNM2.

Set Implicit Arguments.

(** sigT in Set **)
Inductive sigTS (A:Set) (P: A -> Set) : Set :=
  existTS : forall x:A, P x -> sigTS (A := A) P.

Section projections_sigTS.
  
  Variable A : Set.
  Variable P : A -> Set.

  Definition projT1S (H:sigTS P) : A := 
    match H with
      | existTS x _ => x
    end.
   
  Definition projT2S : forall x:sigTS P, P (projT1S x) :=
    fun H:sigTS P => match H return P (projT1S H) with
                      | existTS x h => h
                    end.
End projections_sigTS.


(** Axioms **)
Axiom shift : forall (P:Prop), (STsep [P] (fun pf : P => [P]))%hprop.

Section BPlusTreeImpl.

  Variable SIZE : nat.
  Variable pfMin : SIZE > 1.
  Lemma SIZE_S : SIZE = S (SIZE - 1).
    omega.
  Qed.

  Variable key : Set.
  Variable value : key -> Set.

  (** Ordering on Keys **)
  Variable KOT : OrderedType key.
  Definition KLOT := liftOT KOT.

  Parameter value_eq : forall k1 k2 : key, OTeq KOT k1 k2 -> value k1 = value k2.

  Definition key_eq_dec : forall (a b : key), {OTeq KOT a b} + {~OTeq KOT a b}.
    refine (fun a b => 
      match OTcompare KOT a b with
        | EQ pf => left _ _
        | LT pf => right _ _ 
        | GT pf => right _ _ 
      end); order.
  Qed.
  
  Notation "a '#<' b"   := (OTlt KLOT a b) (at level 70, no associativity).
  Notation "a '#?<' b"  := (OTlt KLOT a (Val b)) (at level 70, no associativity).
  Notation "a '#<?' b"  := (OTlt KLOT (Val a) b) (at level 70, no associativity).
  Notation "a '#?<?' b" := (OTlt KLOT a b) (at level 70, no associativity).
  Notation "a '#<=' b" := (~OTlt KLOT b a) (at level 70, no associativity).
  Notation "a '#<=?' b" := (~OTlt KLOT b (Val a)) (at level 70, no associativity).
  Notation "a '#?<=' b" := (~OTlt KLOT (Val b) a) (at level 70, no associativity).

  Definition MinK := @Min key.
  Definition MaxK := @Max key.

  (** Physical Representation **)
  Open Local Scope hprop_scope.

  (** * Node representation **)
  Record nodeType : Set := mkNode {
    height  : nat;
    content : array;
    next    : option ptr
  }.

  Definition repLeaf {T : Set} (ary : array) (s l : nat) (ls : list T) : hprop :=
    {@ (p :~~ array_plus ary i in p ~~> match nth_error ls (i - s) with
                                          | None => @None T
                                          | Some x => Some x
                                        end) | i <- s + l }.

(** With Branching
  Fixpoint repBranch
    (bptree : ptr -> nat ->option ptr -> option ptr -> list (sigTS value) -> hprop) 
    (ary : array) (i l : nat)
    (ls : list (ptr * key * nat * list (sigTS value)))
    (nxt : ptr) {struct l} : hprop :=
    match l with
      | 0   => __
      | S l => 
        match ls with
          | nil =>
            p :~~ array_plus ary i in
            p ~~> @None (key * ptr) * 
            repBranch bptree ary (S i) l nil nxt

          | (((fp, k), n), st) :: nil =>
            p :~~ array_plus ary i in
            Exists p' :@ ptr,
            p ~~> Some (k, p') *
            bptree p' n (Some fp) (Some nxt) st *
            repBranch bptree ary (S i) l nil nxt

          | (((fp, k), n), st) :: ((((lp, _), _), _) :: _) as tl =>
            p :~~ array_plus ary i in
            Exists p' :@ ptr,
            p ~~> Some (k, p') *
            bptree p' n (Some fp) (Some lp) st *
            repBranch bptree ary (S i) l tl nxt
            
        end
    end.

  Fixpoint bptree (h : nat) (p : ptr) (n : nat) (fp lp : option ptr) (ls : list (sigTS value)) {struct h} : hprop :=
    match h with
      | 0 =>
        Exists ary :@ array,
        p ~~> mkNode 0 ary lp * repLeaf ary 0 SIZE ls *
        [Some p = fp] *

        [length ls <= SIZE] * [div2 SIZE <= length ls] * [length ls = n]
      | S h' =>
        Exists children    :@ list (ptr * key * nat * list (sigTS value)),
        Exists nxtChildren :@ list (sigTS value),
        Exists nxtN        :@ nat,
        Exists ary         :@ array,
        Exists nxtP        :@ ptr,
        Exists nxtPBase    :@ ptr,

        p ~~> mkNode h ary (Some nxtP) *

        repBranch (bptree h') ary 0 SIZE children nxtPBase *
        bptree h' nxtP nxtN (Some nxtPBase) lp nxtChildren *


        [flat_map (fun x => snd x) children ++ nxtChildren = ls] * [length ls = n]
    end.
**)

  (** Without Branching **)
  Fixpoint repBranch
    (bptree : ptr -> option ptr -> option ptr -> LiftOrder key -> LiftOrder key -> list (sigTS value) -> hprop) 
    (ary : array) (i l : nat)
    (ls : list (ptr * ptr * key * list (sigTS value)))
    (fp lp : option ptr)
    (min max : LiftOrder key) {struct l} : hprop :=
    match l with
      | 0   => [min #<= max] * [fp = lp]
      | S l => 
        match ls with
          | nil =>
            p :~~ array_plus ary i in
            p ~~> @None (key * ptr) * 
            repBranch bptree ary (S i) l nil fp lp min max

          | (((fp', cp), k), st) :: tl =>
            p :~~ array_plus ary i in
            p ~~> Some (k, cp) *
            bptree cp fp (Some fp') min (Val k) st *
            repBranch bptree ary (S i) l tl (Some fp') lp (Val k) max

        end
    end.

  Fixpoint bptree (h : nat) (p : ptr) (fp lp : option ptr) (min max : LiftOrder key) 
    (ls : list (sigTS value)) {struct h} : hprop :=
    match h with
      | 0 =>
        Exists ary :@ array,
        p ~~> mkNode 0 ary lp * repLeaf ary 0 SIZE ls *
        [Some p = fp] *

        [length ls <= SIZE] * [div2 SIZE <= length ls]
      | S h' =>
        Exists children    :@ list (ptr * ptr * key * list (sigTS value)),
        Exists nxtChildren :@ list (sigTS value),
        Exists ary         :@ array,
        Exists nxtP        :@ ptr,
        let nxtMin   := last (map (fun x => Val (snd (fst x))) children) min in
        let nxtPBase := last (map (fun x => Some (fst (fst (fst x)))) children) fp in

        p ~~> mkNode h ary (Some nxtP) *

        repBranch (bptree h') ary 0 SIZE children fp nxtPBase min nxtMin *
        bptree h' nxtP nxtPBase lp nxtMin max nxtChildren *

        [flat_map (fun x => snd x) children ++ nxtChildren = ls] *
        [div2 SIZE <= length children] * [length children <= SIZE]
    end.

  Open Local Scope stsepi_scope.
  Definition ReadFrame (p : ptr)
    (fr : nat -> option ptr -> option ptr -> LiftOrder key -> LiftOrder key -> list (sigTS value) -> hprop)
    (x : nodeType) : hprop :=
    Exists ls :@ list (sigTS value),
    Exists fp :@ option ptr, Exists lp :@ option ptr, 
    Exists min :@ LiftOrder key, Exists max :@ LiftOrder key,
    fr (height x) fp lp min max ls *
    match height x with
      | 0 => Exists ary :@ array,
        [x = mkNode 0 ary lp] * repLeaf ary 0 SIZE ls *
        [Some p = fp] *
        [length ls <= SIZE] * [div2 SIZE <= length ls]
      | S h' =>
        Exists children    :@ list (ptr * ptr * key * list (sigTS value)),
        Exists nxtChildren :@ list (sigTS value),
        Exists ary         :@ array,
        Exists nxtP        :@ ptr,
        let nxtMin   := last (map (fun x => Val (snd (fst x))) children) min in
        let nxtPBase := last (map (fun x => Some (fst (fst (fst x)))) children) fp in
                               
        [x = mkNode (S h') ary (Some nxtP)] *

        repBranch (bptree h') ary 0 SIZE children fp nxtPBase min nxtMin *
        bptree h' nxtP nxtPBase lp nxtMin max nxtChildren *

        [flat_map (fun x => snd x) children ++ nxtChildren = ls] *
        [div2 SIZE <= length children] * [length children <= SIZE]
    end.

(**
  Definition recur : forall (p : ptr) (ls : [list (sigTS value)])
    (fr : nat -> option ptr -> option ptr -> LiftOrder key -> LiftOrder key -> hprop),
    STsep (ls ~~
           Exists h :@ nat,
           Exists fp :@ option ptr, Exists lp :@ option ptr, 
           Exists min :@ LiftOrder key, Exists max :@ LiftOrder key,
           bptree h p fp lp min max ls * fr h fp lp min max)
          (fun res : bool => ls ~~
            Exists h :@ nat,
            Exists fp :@ option ptr, Exists lp :@ option ptr,
            Exists min :@ LiftOrder key, Exists max :@ LiftOrder key,
            bptree h p fp lp min max ls * fr h fp lp min max *
            [res = match h with
                     | 0 => true
                     | _ => false
                   end]).
    refine (fun p ls fr =>
      nde <- SepRead p (ReadFrame ls p fr) ;
      match height nde as h return height nde = h -> _ with
        | 0 => fun pfH => {{ Return true }}
        | _ => fun pfH => {{ Return false }}
      end (refl_equal _)).
    intros; repeat progress inhabiter; unfold ReadFrame. destruct v; simpl; sep fail auto.
    unfold ReadFrame; sep fail auto.
    simpl; intros; repeat progress inhabiter; rewrite pfH; inhabiter. canceler. sep fail auto.
    sep fail auto.
    simpl; intros; repeat progress inhabiter; rewrite pfH; inhabiter. canceler. sep fail auto.
    sep fail auto.
  Qed.
**)

  (** The technique for addressing this is going to boil down to doing what we do for read.
      Pass these functions around all the time in order to get the correct invariants.
   **)
  Definition minimum : forall (p : ptr)
    (fr : nat -> option ptr -> option ptr -> LiftOrder key -> LiftOrder key -> list (sigTS value) -> hprop),
    STsep (Exists ls :@ list (sigTS value),
           Exists h :@ nat,
           Exists fp :@ option ptr, Exists lp :@ option ptr, 
           Exists min :@ LiftOrder key, Exists max :@ LiftOrder key,
           bptree h p fp lp min max ls * fr h fp lp min max ls)
          (fun res : option (sigTS value) =>
            Exists ls :@ list (sigTS value),
            Exists h :@ nat,
            Exists fp :@ option ptr, Exists lp :@ option ptr,
            Exists min :@ LiftOrder key, Exists max :@ LiftOrder key,
            bptree h p fp lp min max ls * fr h fp lp min max ls *
            [res = head ls]).
    refine (
      Fix2 (fun (p : ptr)
                (fr : nat -> option ptr -> option ptr -> LiftOrder key -> LiftOrder key -> list (sigTS value) -> hprop) =>
             Exists ls :@ list (sigTS value),
             Exists h :@ nat,
             Exists fp :@ option ptr, Exists lp :@ option ptr, 
             Exists min :@ LiftOrder key, Exists max :@ LiftOrder key,
             bptree h p fp lp min max ls * fr h fp lp min max ls)
           (fun p fr (res : option (sigTS value)) =>
            Exists ls :@ list (sigTS value),
            Exists h :@ nat,
            Exists fp :@ option ptr, Exists lp :@ option ptr,
            Exists min :@ LiftOrder key, Exists max :@ LiftOrder key,
            bptree h p fp lp min max ls * fr h fp lp min max ls *
            [res = head ls])
           (fun minimum p fr =>
             nde <- SepRead p (ReadFrame p fr) ;
             match height nde as h return height nde = h -> _ with
               | 0 => fun pfH => 
                 x <- sub_array (content nde) 0 _ ;
                 {{ Return x }}
               | _ => fun pfH => _
             end (refl_equal _))).
    intros; repeat progress inhabiter; unfold ReadFrame. destruct v0; simpl; sep fail auto.
    unfold ReadFrame; sep fail auto.
(**
    simpl; intros; repeat progress inhabiter; rewrite pfH; inhabiter.
      unfold repLeaf. unpack_conc. split_index. instantiate (1 := 0); omega. norm arith.
      intro_pure. rewrite H6 in *. simpl in *. inhabiter. sep fail auto.
**)

    Focus 5.
    refine (
      kp <- sub_array (content nde) 0 _ ;
      let _ : option (key * ptr) := kp in
      match kp as kp' return kp = kp' -> _ with 
        | None => fun pfEq => {{ !!! }}
        | Some (k,p') => fun pfEq =>
          {{ minimum p' (fun h' fp' lp' min' max' ls' => 
            Exists v :@ list (sigTS value),
            Exists fp :@ option ptr, Exists lp :@ option ptr,
            Exists min :@ LiftOrder key, Exists max :@ LiftOrder key,
            Exists children    :@ list (ptr * ptr * key * list (sigTS value)),
            Exists nxtChildren :@ list (sigTS value),
            Exists ary         :@ array,
            Exists nxtP        :@ ptr,
            let nxtMin   := last (map (fun x => Val (snd (fst x))) children) min in
            let nxtPBase := last (map (fun x => Some (fst (fst (fst x)))) children) fp in

            match children with
              | nil => [False]
              | (((fp'', p'''), k), st) :: tl =>
                p :~~ array_plus ary 0 in
                p ~~> Some (k, p') *
                repBranch (bptree n) ary 1 (SIZE - 1) tl (Some fp'') nxtPBase (Val k) nxtMin *
                [fp = fp'] * [Some fp'' = lp'] * [max' = Val k] * [ls' = st] * [p' = p''']
            end *
      
            [nde = mkNode (S n) ary (Some nxtP)] *
            
            bptree n nxtP nxtPBase lp nxtMin max nxtChildren *
            [flat_map (fun x => snd x) children ++ nxtChildren = v] *
            [div2 SIZE <= length children] * [length children <= SIZE] *
            fr (S n) fp lp min max v * p ~~> nde * [h' = n] * [min' = min]) }}
      end (refl_equal _)).
    simpl; intros; repeat progress inhabiter; rewrite pfH; inhabiter. rewrite H.
    Check repBranch.
    instantiate (1 := fun x:option (key * ptr) =>
      Exists v :@ list (sigTS value),
      Exists fp :@ option ptr, Exists lp :@ option ptr,
      Exists min :@ LiftOrder key, Exists max :@ LiftOrder key,
      Exists children    :@ list (ptr * ptr * key * list (sigTS value)),
      Exists nxtChildren :@ list (sigTS value),
      Exists ary         :@ array,
      Exists nxtP        :@ ptr,
      let nxtMin   := last (map (fun x => Val (snd (fst x))) children) min in
      let nxtPBase := last (map (fun x => Some (fst (fst (fst x)))) children) fp in

      match children with
        | nil => [False]
        | (((fp', p'), k), st) :: tl =>
          bptree n p' fp (Some fp') min (Val k) st *
          repBranch (bptree n) ary 1 (SIZE - 1) tl (Some fp') nxtPBase (Val k) nxtMin *
          [x = Some (k,p')]
      end *
      
      [nde = mkNode (S n) ary (Some nxtP)] *

      bptree n nxtP nxtPBase lp nxtMin max nxtChildren *
      [flat_map (fun x => snd x) children ++ nxtChildren = v] *
      [div2 SIZE <= length children] * [length children <= SIZE] *
      fr (S n) fp lp min max v * p ~~> nde).
    intro_pure. rewrite SIZE_S. sep fail auto.
    instantiate (1 := match v4 with 
                        | nil => None
                        | pair (pair (pair _ p') k) _ :: _ => Some (k, p')
                      end).
    destruct v4; sep fail auto.
    simpl in *. elimtype False. generalize pfMin. intros.
    destruct SIZE; simpl in *; try omega. destruct n0; try omega.
    destruct p0. destruct p0. destruct p0. simpl in *. norm arith. solve [ sep fail auto ].
    solve [ sep fail auto ].
    simpl; intros; repeat progress inhabiter. destruct v4; [ intro_pure; think |].
    destruct p1. destruct p1. destruct p1. intro_pure. subst. inversion H9. subst.
    Require Import ThinkList. norm list.
    sep fail auto. 
    try search_prem ltac:(idtac;
      match goal with
        | [ |- fr ?A ?B ?C ?D ?E ?F * _ ==> _ ] => idtac A B C D E F;
          search_conc ltac:(idtac;
            match goal with
              | [ |- _ ==> fr ?A' ?B' ?C' ?D' ?E' ?F' * _ ] => 
                idtac A' B' C' D' E' F';
                try (assert (A = A'); [ reflexivity | ]);
                try (assert (B = B'); [ reflexivity | ]);
                try (assert (C = C'); [ reflexivity | ]);
                try (assert (D = D'); [ reflexivity | ]);
                try (assert (E = E'); [ reflexivity | ]);
                try (assert (F = F'); [ eauto | ])
            end)
      end).
    Show Existentials.
    instantiate (1 := v5).
    instantiate (1 := (p1, p2, k0, l) :: v4). simpl. norm list. auto.
    norm list. sep fail auto.

  Lemma bptree_not_nil : forall v1 p' l v2 p1 v4 k0 P Q,
    (l <> nil -> bptree v1 p' v2 p1 v4 k0 l * P ==> Q)
    -> bptree v1 p' v2 p1 v4 k0 l * P ==> Q.
  Proof.
    induction v1; simpl; intros. destruct l. inhabiter. intro_pure. simpl in *.
    elimtype False.
    destruct SIZE; simpl in *; try omega. destruct n; try omega.
    eapply H; auto. firstorder.
  
  Admitted.

    simpl; intros; repeat progress inhabiter. destruct v11; [intro_pure; think|].
    destruct p1. destruct p1. destruct p1. repeat progress inhabiter. intro_pure.
    Opaque flat_map. 
    eapply himp_empty_conc'. eapply himp_ex_conc. exists v6.
    search_prem ltac:(apply bptree_not_nil).
    sep fail auto. Transparent flat_map. simpl. norm list.
    rewrite SIZE_S at 2. simpl. unpack_conc. search_prem ltac:(apply bptree_not_nil). sep fail auto.
    
    intros. destruct l. firstorder. sep fail auto.
  solve [ sep fail auto ].
  simpl; intros; repeat progress inhabiter. destruct v5; [intro_pure; think|].
Opaque flat_map. destruct p0. destruct p0. destruct p0.  intro_pure. subst. think.

    

  (** TODO : this seems like what it would be like to use this rep.
             Better automation might be possible, but I'm not sure right now
   **)


End BPlusTreeImpl.
  
