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
  
  Notation "a '#<' b"  := (OTlt KLOT a b) (at level 70, no associativity).
  Notation "a '#?<' b"  := (OTlt KLOT a (Val b)) (at level 70, no associativity).
  Notation "a '#<?' b"  := (OTlt KLOT (Val a) b) (at level 70, no associativity).
  Notation "a '#?<?' b" := (OTlt KLOT a b) (at level 70, no associativity).
  Notation "a '#<=?' b" := (~OTlt KLOT b (Val a)) (at level 70, no associativity).
  Notation "a '#?<=' b" := (~OTlt KLOT (Val b) a) (at level 70, no associativity).

  Definition MinK := @Min key.
  Definition MaxK := @Max key.

  (** Model Representation **)
  Fixpoint tree (n : nat) : Set :=
    match n with
      | 0 => list (sigTS value)
      | S n => list (sigTS (fun _:key => tree n)) * tree n
    end%type.

  Fixpoint dlist (T : Set) (f : T -> Set) (ls : list T) : Set :=
    match ls with 
      | nil => unit
      | a :: b => prod (f a) (dlist f b)
    end.

  Fixpoint ptree {n : nat} : tree n -> Set :=
    match n as n return tree n -> Set with
      | 0   => fun _ => ptr
      | S n => fun ls => 
        dlist (fun x => @ptree n (projT2S x)) (fst ls) * @ptree n (snd ls)
    end%type.

  Definition key_between (min : LiftOrder key) (k : key) (max : LiftOrder key) : Prop :=
    min #?< k /\ k #<=? max.

  (** Sorted Properties **)
  (** min < x[0] < x[2] < ... < x[n] <= max **)
  Fixpoint sorted (T : Type) C (ot : OrderedType C) (G : T -> C) (min : C) (ls : list T) (max : C) {struct ls} : Prop :=
    match ls with
      | nil => OTlt ot min max \/ OTeq ot min max
      | f :: r => OTlt ot min (G f) /\ sorted ot G (G f) r max
    end.

  Definition KLsorted (V : key -> Set) min ls max :=
    @sorted (sigTS V) (LiftOrder key) KLOT (fun v => Val (projT1S v)) min ls max.

(*
  Fixpoint contextual (h : nat) (F : LiftOrder key -> sigTS (fun _:key => ptree h) -> Prop) (B : LiftOrder key -> Prop)
    (min : LiftOrder key) (ls : list (sigTS (fun _:key => ptree h))) {struct ls} : Prop :=
    match ls with 
      | nil => B min
      | fs :: rr => F min fs /\ contextual h F B (Val (projT1S fs)) rr
    end.
*)

  Fixpoint contextual (h : nat) (F : LiftOrder key -> sigTS (fun _:key => tree h) -> Prop)
    (min max : LiftOrder key) (ls : list (sigTS (fun _:key => tree h))) {struct ls} : Prop :=
    match ls with 
      | nil => OTeq KLOT min max
      | fs :: rr => F min fs /\ contextual h F (Val (projT1S fs)) max rr
    end.

  Fixpoint lastKey (T : key -> Set) (ls : list (sigTS T)) (d : LiftOrder key) : LiftOrder key :=
    match ls with
      | nil => d
      | a :: b => lastKey b (Val (projT1S a))
    end.

  Fixpoint inv (n : nat) : tree n -> LiftOrder key -> LiftOrder key -> Prop :=
    match n as n return tree n -> LiftOrder key -> LiftOrder key -> Prop with
      | 0 => fun m min max =>
        KLsorted min m max

      | S n => fun m min max =>
        let (ls,nxt) := m in
        let break := lastKey ls min in
(*        KLsorted min ls max /\ (** KLsorted is redundent here and produces problems with identifying the max **)
        contextual n (fun mi c => inv n (projT2S c) mi (Val (projT1S c))) (fun mi => inv n nxt mi max) min ls **)
        contextual n (fun mi c => inv n (projT2S c) mi (Val (projT1S c))) min break ls
        /\ inv n nxt break max
    end.

  (** Logical Representation **)
  (**
  Definition Model := list (sigTS value).

  Fixpoint as_map (n : nat) {struct n} : tree n -> Model :=
    match n as n return tree n -> list (sigTS value) with 
      | 0 => fun ls => ls
      | S n' => fun n =>
        let (ls,nxt) := n in
        List.flat_map (fun x => @as_map n' (projT2S x)) ls ++ as_map n' nxt
    end.
**)

  (** Physical Representation **)
  Open Local Scope hprop_scope.

  (** * Node representation **)
  Record nodeType : Set := mkNode {
    height  : nat;
    parent  : option ptr;
    content : array;
    next    : option ptr
  }.

  Lemma nodeType_eta : forall a b c d n,
    height n = a -> content n = b -> next n = c -> parent n = d -> n = mkNode a d b c.
  Proof.
    destruct n; simpl; think.
  Qed.
  Hint Resolve nodeType_eta.

  Lemma sorted_nil : forall V a, KLsorted a (@nil (sigTS V)) a.
  Proof. Opaque KLOT.
    unfold KLsorted. simpl. right. order.
  Qed.
  Hint Immediate sorted_nil.
  Lemma sorted_nil_lt : forall V a b, 
    OTlt KLOT a b -> KLsorted a (@nil (sigTS V)) b.
  Proof. Opaque KLOT.
    unfold KLsorted. simpl. left. order.
  Qed.
  Hint Resolve sorted_nil_lt.

  (** we iterate from left to right
   **   op is the option pointer to the next child
   **)
  Definition repLeaf (T : Set) (ary : array) (s l : nat) (ls : list T) : hprop :=
    {@ (p :~~ array_plus ary i in p ~~> match nth_error ls (i - s) with
                                          | None => @None T
                                          | Some x => Some x
                                        end) | i <- s + l }.

  Fixpoint lastPtr {h : nat} : forall tr : tree h, ptree tr -> ptr :=
    match h as h return forall tr : tree h, ptree tr -> ptr with
      | 0 => fun _ pm => pm
      | S h => fun m pm => lastPtr (snd m) (snd pm)
    end.

  Fixpoint firstPtr {h : nat} : forall tr : tree h, ptree tr -> ptr :=
    match h as h return forall tr : tree h, ptree tr -> ptr with
      | 0   => fun _ pm => pm
      | S h => fun m => match m as m return @ptree (S h) m -> ptr with
                          | (nil,rm)   => fun pm => firstPtr rm (snd pm)
                          | (a :: _,_) => fun pm => firstPtr (projT2S a) (fst (fst pm))
                        end
    end.

  Fixpoint repBranch (h : nat) (rep' : ptr -> option ptr -> forall tr : tree h, ptree tr -> hprop) 
    (ary : array) (i l : nat)
    (ls : list (sigTS (fun _:key => tree h)))
    (pls : dlist (fun x => @ptree h (projT2S x)) ls)
    (nxt : ptr) {struct l} : hprop :=
    match l with
      | 0 => __
      | S l => 
        match ls as ls return dlist (fun x => @ptree h (projT2S x)) ls -> hprop with
          | nil => fun pls => p :~~ array_plus ary i in p ~~> @None (key * ptr) * 
            repBranch h rep' ary (S i) l nil pls nxt
          | f :: tl => fun pls =>
            match tl as tl return dlist (fun x => @ptree h (projT2S x)) tl -> hprop  with
              | nil => fun _ =>
                p :~~ array_plus ary i in
                Exists p' :@ ptr,
                p ~~> Some (projT1S f, p') *
                rep' p' (Some nxt) (projT2S f) (fst pls) *
                repBranch h rep' ary (S i) l tl (snd pls) nxt
              | r :: rr => fun pls' => 
                p :~~ array_plus ary i in
                Exists p' :@ ptr,
                let next_p := Some (firstPtr (projT2S r) (fst pls')) in
                p ~~> Some (projT1S f, p') *
                rep' p' next_p (projT2S f) (fst pls) *
                repBranch h rep' ary (S i) l tl (snd pls) nxt
            end (snd pls)
        end pls
    end.

  Fixpoint rep' (n : nat) (par : option ptr) (p : ptr) (op_next : option ptr) {struct n} 
    : forall tr : tree n, ptree tr -> hprop :=
    match n as n return forall tr : tree n, ptree tr -> hprop with 
      | 0 => fun m pm =>
        [p = pm] *
        Exists ary :@ array,
        p ~~> mkNode n par ary op_next *
        [array_length ary = SIZE] * [length m <= SIZE] *
        repLeaf ary 0 SIZE m
        
      | S n' => fun m pm =>
        Exists ary :@ array, Exists p' :@ ptr,
        p ~~> mkNode n par ary (Some p') *
        [array_length ary = SIZE] * [length (fst m) <= SIZE] *
        repBranch n' (rep' n' (Some p)) ary 0 SIZE (fst m) (fst pm) (firstPtr (snd m) (snd pm)) *
        rep' n' (Some p) p' op_next (snd m) (snd pm)
    end.

  Definition BptMap := ptr.
  Definition Model := sigTS tree.

  Definition rep (p : BptMap) (m : Model) : hprop :=
    match m with
      | existTS h t => 
        [inv h t MinK MaxK] *
        Exists pt :@ ptree t, rep' h None p None t pt
    end.

(**
  Lemma rep'_ptrFor : forall h p op m,
    rep' h p op m ==> rep' h p op m * [p = ptrFor h m].
  Proof.
    unfold rep'; destruct h; sep fail auto.
  Qed.
  Hint Resolve rep'_ptrFor.
  Lemma rep'_ptrFor_add : forall h p op m Q P,
    (ptrFor h m = p -> rep' h p op m * P ==> Q) ->
    rep' h p op m * P ==> Q.
  Proof. clear.
    intros. destruct h; simpl; destruct m; simpl in *; intro_pure; symmetry in H0; apply H in H0; (eapply himp_trans; [ | eapply H0 ]); sep fail auto.
  Qed.
  Ltac extender :=
    eapply rep'_ptrFor_add.
  Ltac t := sep extender auto.
**)

  (** Specifications **)
  Definition insertType := forall (t : BptMap) (k : key) (v : value k) (m : [Model]),
    STsep (m ~~ rep' t m)
          (fun res:option (value k) => m ~~ __).

(**
  Fixpoint specLookup (m : Model) (k : key) {struct m} : option (value k) :=
    match m with
      | nil => None
      | a :: b =>
        match key_eq_dec (projT1S a) k with
          | left pf => match value_eq (projT1S a) k pf in _ = x return option x with 
                                   | refl_equal => Some (projT2S a)
                                 end
          | _ => specLookup b k
        end
    end.
  Fixpoint specInsert (m : Model) (k : key) (v : value k) {struct m} : Model :=
    match m with
      | nil => existTS _ k v :: nil
      | a :: b => match OTcompare KOT (projT1S a) k with
                    | LT _ => existTS _ k v :: b
                    | EQ _ => a :: specInsert b v
                    | GT _ => existTS _ k v :: a :: b
                  end
    end.
  Fixpoint specDelete (m : Model) (k : key) {struct m} : Model :=
    match m with
      | nil => nil
      | a :: b => 
        match OTcompare KOT (projT1S a) k with
          | EQ _ => b
          | _ => a :: specDelete b k
        end
    end.
**)

  (** Interface Types **)
  Definition newType :=
    STsep (__)
          (fun t : BptMap => rep t nil).

  Definition freeType := forall (t : BptMap) (m : [Model]),
    STsep (m ~~ rep t m)
          (fun _:unit => __).

  Definition lookupType := forall (t : BptMap) (k : key) (m : [Model]), 
    STsep (m ~~ rep t m)
          (fun res:option (value k) => m ~~ rep t m * [res = specLookup m k]).

  Definition insertType := forall (t : BptMap) (k : key) (v : value k) (m : [Model]),
    STsep (m ~~ rep t m)
          (fun res:option (value k) => m ~~ rep t (specInsert m v) * [res = specLookup m k]).

  Definition deleteType := forall (t : BptMap) (k : key) (m : [Model]),
    STsep (m ~~ rep t m)
          (fun res:option (value k) => m ~~ rep t (specDelete m k) * [res = specLookup m k]).

  Definition iterateType := forall (T : Type) (t : BptMap) 
    (I : T -> hprop)
    (fn : forall (k : key) (v:value k) (acc: T), STsep (I acc) (fun a:T => I a)) (acc : T)
    (m : [Model]), 
    STsep (m ~~ rep t m * I acc)
          (fun res:T => m ~~ rep t m * I res).

(** inorder insertion is based on a pointer to the bottom right leaf in the tree,
   and a model that persists between the two **)
(**
  Definition insertIterator : BptMap -> 
  Definition inorderInsert := forall (T : Type) (t : BptMap)
 **)

  (** TODO: There needs to be a fast inorder insert **)
  Record bpt_map : Type := mkBpt {
    bpt_new    : newType;
    bpt_free   : freeType;
    bpt_lookup : lookupType;
    bpt_insert : insertType;
    bpt_delete : deleteType;
    bpt_iterate : iterateType
  }.

  (** Implementation **)
  (********************)

  (** Case Analysis on trees **)
  Open Local Scope stsepi_scope.
  Open Local Scope hprop_scope.

  Definition checkLeaf : forall (h : nat) (m : [sigTS ptree]), [h]%inhabited = (m ~~~ projT1S m) -> h = 0 -> [list (sigTS value)].
  refine (fun h m pf1 pf2 =>
    match m as m' return m = m' -> _ with
      | inhabits x => fun pf => [ _ ]%inhabited
    end (refl_equal _)).
    subst; simpl in *. destruct x. generalize p. simpl in pf1. rewrite <- (pack_injective pf1). simpl. intros. destruct p0. assumption.
  Defined.

  Definition checkBranch (h h' : nat) (m : [sigTS ptree]) :
    [h]%inhabited = (m ~~~ projT1S m) -> h = S h' -> [ptree (S h')].
    refine (fun h h' m pf1 pf2 =>
      match m as m' return m = m' -> _ with
        | inhabits x => fun pf => [ _ ]%inhabited
      end (refl_equal _)).
    case_eq x. intros. rewrite pf in pf1. rewrite H in pf1. simpl in pf1. rewrite pf2 in pf1.
    generalize dependent p. rewrite <- (pack_injective pf1) in *. intros.
    apply p.
  Defined.

  Definition readBranch : forall (p : ptr) (optr: [option ptr]) (h : nat) (m : [ptree (S h)]), 
    STsep (m ~~ optr ~~ rep' (S h) p optr m)
          (fun res : (array * ptr) => m ~~ optr ~~
            let ary := fst res in
            let nxtP := snd res in
            let lsM := fst (snd m) in
            let nxtM := snd (snd m) in
            p ~~> mkNode (S h) ary (Some nxtP) * 
            [array_length ary = SIZE] * [length lsM <= SIZE] *
            repBranch h (rep' h) ary 0 SIZE lsM (firstPtr _ nxtM) *
            rep' h nxtP optr nxtM).
    refine (fun p optr h m => 
      nde <- ! p ;
      pf  <- @shift (next nde <> None) <@> _ ;
      match next nde as nxt return next nde = nxt -> _ with
        | None   => fun pf => False_rect _ _
        | Some p => fun _  => {{ Return (content nde, p) }}
      end (refl_equal _)).
  Proof.
    instantiate (1 := fun v => m ~~ optr ~~ [next v = Some (ptrFor _ (snd (snd m)))] * [height v = S h] *
      [array_length (content v) = SIZE] * [length (fst (snd m)) <= SIZE] *
      repBranch h (rep' h) (content v) 0 SIZE (fst (snd m)) (firstPtr _ (snd (snd m))) *
      rep' h (ptrFor _ (snd (snd m))) optr (snd (snd m))).
    solve [ t ].
    solve [ t ].
    simpl. inhabiter. intro_pure. eapply himp_comm_conc. eapply himp_inj_conc. unfold not; congruence.
      solve [ t ].
    solve [ t ].
    solve [ t ].
    t. inversion H4; eauto. rewrite _H in H0. inversion H0. inversion H4. rewrite H6. simpl; t. 
    solve [ auto ].
  Qed.

  Definition bpt_case : forall (T : Type) (Q : T -> hprop) (P:hprop)
    (p:ptr) (m : [sigTS ptree]) (op : [option ptr]),
    (forall (ary : array) (nxt : option ptr) (ls : [list (sigTS value)]),
     STsep (ls ~~ op ~~ m ~~ 
                  p ~~> mkNode 0 ary nxt * [array_length ary = SIZE] * [length ls <= SIZE] *
                  [p = ptrFor _ (projT2S m)] *
                  repLeaf ary 0 SIZE ls * [nxt = op] * P)
           (fun res:T => Q res)) ->
    (forall (h' : nat) (ary : array) (nxt : ptr) (m : [ptree (S h')]),
     STsep (m ~~ op ~~ 
                 p ~~> mkNode (S h') ary (Some nxt) * [array_length ary = SIZE] * [length (fst (snd m)) <= SIZE] * 
                 [p = ptrFor _ m] * [nxt = ptrFor _ (snd (snd m))] *
                 repBranch h' (rep' h') ary 0 SIZE (fst (snd m)) (firstPtr _ (snd (snd m))) *
                 rep' h' nxt op (snd (snd m)) * P)
           (fun res:T => Q res)) ->
    STsep (m ~~ op ~~ [p = ptrFor _ (projT2S m)] * rep' (projT1S m) p op (projT2S m) * P)
          (fun res:T => Q res).
  refine (fun T Q P p m op CLeaf CBranch => 
    nde <- ! p ;
    pfCorrespond <- shift ([height nde]%inhabited = (m ~~~ projT1S m)) <@> _ ;
    match height nde as h 
      return height nde = h ->
        STsep (m ~~ op ~~ [height nde = projT1S m] * p ~~> nde *
               match m with 
                 | existTS 0 ls => 
                   [height nde = 0] * [array_length (content nde) = SIZE] * [length (snd ls) <= SIZE] *
                   [next nde = op] * [p = ptrFor _ ls] *
                   repLeaf (content nde) 0 SIZE (snd ls)
                   
                 | existTS (S n') m =>
                   let ls  := fst (snd m) in
                   let nxt := snd (snd m) in
                   [height nde = S n'] * [array_length (content nde) = SIZE] * [length ls <= SIZE] *
                   [p = ptrFor _ m] * [next nde = Some (ptrFor _ nxt)] *
                   repBranch n' (rep' n') (content nde) 0 SIZE ls (firstPtr _ nxt) * rep' n' (ptrFor _ nxt) op nxt
               end * P)
        (fun res:T => Q res)
      with
      | 0 => fun pf =>
        {{ CLeaf (content nde) (next nde) _ }}
      | S h' => fun pf =>
        (** Can probably clean this up with readBranch **)
        match next nde as nn return next nde = nn -> _ with
          | None => fun _ => {{ !!! }}
          | Some nn => fun pfNxt => 
            {{ CBranch h' (content nde) nn _ }}
        end (refl_equal _)
    end (refl_equal _)); try clear CLeaf CBranch.
  Proof.
  instantiate (1 := (fun v:nodeType => m ~~ op ~~ [p = ptrFor _ (projT2S m)] *
    match m with 
      | existTS 0 ls =>
        [height v = 0] * [array_length (content v) = SIZE] * [length (snd ls) <= SIZE] *
        [next v = op] * [p = ptrFor _ ls] *
        repLeaf (content v) 0 SIZE (snd ls)

      | existTS (S n') m =>
        let ls  := fst (snd m) in
        let nxt := snd (snd m) in
        [height v = S n'] * [array_length (content v) = SIZE] * [length ls <= SIZE] *
        [next v = Some (ptrFor _ nxt)] *
        repBranch n' (rep' n') (content v) 0 SIZE ls (firstPtr _ nxt) * rep' n' (ptrFor _ nxt) op nxt
    end * P)).
  solve [ unfold rep'; inhabiter; destruct x0; destruct x0; sep fail auto ].
  solve [ sep fail auto ].
  simpl. instantiate (1 := p ~~> nde * P * (m ~~ op ~~
      [height nde = projT1S m] * [p = ptrFor _ (projT2S m)] *
      match m with
      | existTS x m1 =>
          match x as x0 return ptree x0 -> hprop with
          | 0 => fun m2 =>
              let ls := snd m2 in
              [height nde = 0] * [array_length (content nde) = SIZE] *
              [next nde = op] * [length ls <= SIZE] * [next nde = op] * [p = ptrFor _ (projT2S m)] *
              repLeaf (content nde) 0 SIZE ls

          | S n' => fun m2 =>
              let ls := fst (snd m2) in
              let nxt := snd (snd m2) in
              [height nde = S n'] * [array_length (content nde) = SIZE] * [length ls <= SIZE] *
              [next nde = Some (ptrFor _ nxt)] *
              repBranch n' (rep' n') (content nde) 0 SIZE ls (firstPtr _ nxt) * rep' n' (ptrFor _ nxt) op nxt
          end m1
      end)).
  solve [ unfold rep'; inhabiter; destruct x0; destruct x0; sep fail auto ].
  solve [ unfold rep'; inhabiter; destruct x0; destruct x0; sep fail auto ].
  
  (** Leaf Case **)
  instantiate (1 := @checkLeaf (height nde) m pfCorrespond pf).
  sep fail auto.
    destruct x0. destruct x0.
    unfold eq_rec_r. unfold eq_rec. unfold eq_rect.
    generalize (sym_eq (refl_equal [existTS ptree 0 p0]%inhabited)). intro e. rewrite (UIP_refl _ _ e). clear e.
    generalize (sym_eq pf). intro e. generalize e. generalize dependent H. generalize dependent pf. generalize dependent pfCorrespond. rewrite <- e. clear e. intros. rewrite (UIP_refl _ _ e).
    eqdep. sep fail auto.
    sep fail auto. congruence.
  solve [ sep fail auto ].

  (** Branch Case **)
  instantiate (1 := @checkBranch (height nde) h' m pfCorrespond pf).
  simpl. sep fail auto.
    destruct x0. simpl in H. generalize dependent pfCorrespond. generalize dependent p0. rewrite pf in H. rewrite <- H.
      simpl. sep fail auto. unfold eq_rec. unfold eq_rect.
      generalize (pack_injective
             (eq_ind (height nde)
                (fun h : nat => [h]%inhabited = [S h']%inhabited)
                pfCorrespond (S h') pf)). intro. rewrite (UIP_refl _ _ e). simpl. sep fail auto. rewrite H3 in pfNxt. inversion pfNxt. sep fail auto.
  solve [ sep fail auto ].
  sep fail auto. destruct x0.
  destruct x0. simpl in *. congruence.
  simpl in *. sep fail auto. congruence.
  sep fail auto.
  Qed.

  (** Implementation **)
  Definition emptyTree (p:ptr) : ptree 0 := (p, nil).
  Definition emptyTreeInv : forall p:ptr, inv 0 (emptyTree p) MinK MaxK.
    simpl; auto; intros. Transparent KLOT. unfold emptyTree, MinK, MaxK; compute; auto.
  Qed.
  Hint Resolve emptyTreeInv.
  Opaque KLOT.
  
  Hint Extern 1 (?A=?B) => omega.
  Hint Extern 1 (?A<?B) => omega.
  Hint Extern 1 (?A<=?B) => omega.
  Hint Extern 1 (?A>?B) => omega.
  Hint Extern 1 (?A>=?B) => omega.
  Hint Extern 1 (OTlt _ _ _) => order.
  Hint Extern 1 (OTeq _ _ _) => order.

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

  Lemma minus_lt : forall a b, a < b -> b - a = S (pred (b - a)).  
  Proof.
    auto.
  Qed.

  (** TODO: Get rid of this **)
  Lemma array_split_imp : forall (T:Type) ary n s, n < s -> 
    {@hprop_unpack (array_plus ary i) (fun p : ptr => p ~~> (@None T)) | i <- 0 + n} *
    {@hprop_unpack (array_plus ary i) (fun p : ptr => p ~~>?) | i <- n + (s - n)} ==>
    {@hprop_unpack (array_plus ary i) (fun p : ptr => p ~~> (@None T)) | i <- 0 + n} *
    {@hprop_unpack (array_plus ary i) (fun p : ptr => p ~~>?) | i <- (S n) + (s - (S n))} *
    hprop_unpack (array_plus ary n)
      (fun p : ptr => Exists B :@ Set, (Exists w :@ B, p ~~> w)).
  Proof.
    induction n. simpl. destruct s; intros; try solve [ elimtype False; omega ]. simpl. rewrite <- (minus_n_O s). unfold ptsto_any; sep fail auto.
    intros. simpl. destruct n. simpl. remember (s - 1) as ZZZ. destruct ZZZ. elimtype False. omega.
      simpl. assert (ZZZ = s - 2). omega. rewrite <- H0. unfold ptsto_any; sep fail auto.
      simpl. rewrite (minus_lt H). simpl. unfold ptsto_any; sep fail auto. cut (pred (s - S (S n)) = s - S (S (S n))); auto. intros. rewrite H5. sep fail auto.
  Qed.

  Definition new_empty_array : forall (T : Set) s,
    STsep __
          (fun r:array => {@hprop_unpack (array_plus r i) (fun p : ptr => p ~~> @None T) | i <- 0 + s} * 
            [array_length r = s]).
  Proof.
    refine (fun T s => 
      ary <- new_array s ;
      Fix2 (fun (n:nat) (pf:n <= s) => 
                {@ hprop_unpack (array_plus ary i) (fun p : ptr => p ~~> @None T) | i <- 0 + n } *
                {@ hprop_unpack (array_plus ary i) (fun p : ptr => p ~~>?) | i <- n + (s - n) })
           (fun (n:nat) (pf:n <= s) (_:unit) =>
                {@ hprop_unpack (array_plus ary i) (fun p : ptr => p ~~> @None T) | i <- 0 + s })
           (fun self n pf =>
             match le_lt_dec s n with
               | left _ => {{ Return tt }}
               | right pf' =>
                 upd_array ary n (@None T) <@> 
                 ({@ hprop_unpack (array_plus ary i) (fun p : ptr => p ~~> None) | i <- 0 + n} * 
                   {@ hprop_unpack (array_plus ary i) (fun p : ptr => p ~~>?) | i <- (S n) + (s - (S n))}) ;;
                 {{ self (S n) (lt_S_le pf') }}
             end) 0 (O_le s) <@> _ ;;
           {{ Return ary }}).
    sep fail auto.
    sep fail auto.
    sep fail auto.
    unfold iter_sep. rewrite minus_le; try omega. cut (n = s). sep fail auto. omega.
    pose (array_split_imp T ary pf'). simpl in *. apply h.
    sep fail auto.
    canceler. search_conc ltac:(eapply sp_index_conc). instantiate (1 := n); think. norm arith. sep fail auto.
    sep fail auto.
    rewrite <- minus_n_O. simpl. instantiate (1 := [array_length ary = s]). sep fail auto.
    sep fail auto.
    sep fail auto.
    sep fail auto.
  Qed.

  Definition new :
    STsep (__)
          (fun t : BptMap => rep t nil).
  Proof.
    refine (ary <- new_empty_array (sigTS value) SIZE ;
            res <- New (mkNode 0 ary None) <@> [array_length ary = SIZE] * _ ;
            let tr : tH := existTS _ 0 (emptyTree res) in
            let res' : BptMap := (res, inhabits tr) in
            {{ Return res' }}).
    sep fail auto.
    sep fail auto.
    sep fail auto.
    sep fail auto.
    sep fail auto.
    unfold rep, tr, res' in *; sep fail auto.
    rewrite H1 in *. simpl in *. unfold tr in *. rewrite <- (pack_injective H). generalize (emptyTreeInv res). sep fail auto. Opaque inv. 
    unfold rep'. unfold repLeaf. sep fail auto. eapply iter_sep_inj. sep fail auto. destruct x; auto.
  Qed.

  Lemma repLeaf_iter : forall len (T:Set) ary (ls:list T) s,
    length ls <= len ->
    repLeaf ary s len ls ==> {@hprop_unpack (array_plus ary i) (fun p0 : ptr => p0 ~~>?) | i <- s + len}.
  Proof.
    unfold repLeaf. intros. eapply iter_sep_inj. unfold ptsto_any. sep fail auto.
  Qed.
  
  Lemma repLeaf_iter0 : forall (T:Set) ary (ls:list T),
    length ls <= SIZE ->
    repLeaf ary 0 SIZE ls ==> {@hprop_unpack (array_plus ary i) (fun p0 : ptr => p0 ~~>?) | i <- 0 + SIZE}.
  Proof.
    assert (SIZE = SIZE - 0). omega. rewrite H. intros. eapply repLeaf_iter. omega.
  Qed.

  Definition free_leaf : forall (p : ptr) (ary : array)
    (nxt : option ptr) (ls : [list (sigTS value)]),
    STsep (ls ~~ p ~~> mkNode 0 ary nxt * [array_length ary = SIZE] * [length ls <= SIZE] *
             repLeaf ary 0 SIZE ls)
          (fun res:unit => __).
    refine (fun p ary nxt ls =>
      free_array ary <@> (p ~~> mkNode 0 ary nxt) ;;
      Free p <@> _ ;;
      {{ Return tt }});
    sep fail auto; eapply repLeaf_iter; eauto.
  Qed.

  Definition nthDep (T : Type) (ls : list T) (n : nat) : n < length ls -> T.
    intro T. clear.
    refine (fix nthDep (ls:list T) (n:nat) (pf: n < length ls) {struct ls} : T :=
    match ls as ls, n as n return n < length ls -> T with
      | nil, 0      => fun pf => False_rect _ _
      | nil, S n    => fun pf => False_rect _ _
      | f :: _, 0   => fun _  => f
      | _ :: r, S n => fun pf => nthDep r n _
    end pf);
    simpl in *; omega. 
  Defined.
  
  Lemma skip_len : forall n (T : Type) (l : list T),
    length l <= n -> skipn n l = nil.
  Proof.
    induction n; simpl; think. cut (length l = 0); think. destruct l; think. destruct l; think.
  Qed.

  Lemma minus_n_1 : forall a b, a - b - 1 = a - S b.
    intros; omega.
  Qed.
  Lemma skip_len_ne : forall (T : Type) n (ls : list T), 
    n < length ls -> exists f, exists r, skipn n ls = f :: r.
    induction n; induction ls; simpl in *; think; eauto.
  Qed.
  Lemma skipn_shift : forall (T : Type) n (a:T) b c d, skipn n (a :: b) = c :: d -> skipn n b = d.
    clear. induction n; simpl in *; think. destruct b; think. destruct n; simpl in *; think.
  Qed.
  Lemma skipn_nthDep : forall (T : Type) n (a:T) b c d pf, 
    skipn n (a :: b) = c :: d -> @nthDep T (a :: b) n pf = c.
    clear. induction n. simpl. think.
    intros. destruct b. simpl in H. destruct n; think. simpl in H. assert (n < length (t :: b)). simpl in *; think.
    pose (IHn _ _ _ _ H0 H). rewrite <- e. simpl; think. destruct n; think.
    match goal with 
      | [ |- nthDep _ ?X = nthDep _ ?Y ] => generalize X; generalize Y
    end. clear. intros. pose (proof_irrelevance _ l l0). think.
  Qed.

  Lemma nth_error_nthDep : forall (T:Type) (n : nat) (l : list T) pf x,
    @nthDep T l n pf = x -> nth_error l n = Some x.
  Proof.
    clear. induction n; think. destruct l; simpl in *; think. subst. unfold Specif.value. auto.
    destruct l. simpl in pf. think. simpl in pf. generalize pf. think.  
  Qed.
  Opaque nthDep.

  Lemma iter_fb : forall n (x1 x0 : ptr) s ary (T:Set) (v:T),
    array_plus ary s = [x1]%inhabited ->
    array_plus ary (s + n) = [x0]%inhabited ->
    {@hprop_unpack (array_plus ary i) (fun p4 : ptr => p4 ~~>?) | i <- s + n} * x0 ~~> v ==>
    {@hprop_unpack (array_plus ary i) (fun p0 : ptr => p0 ~~>?) | i <- (S s) + n} * x1 ~~>?.
  Proof.
    clear. induction n.
      simpl; intros. norm arith in *. rewrite H in H0. rewrite (pack_injective H0). unfold ptsto_any. sep fail auto.
      simpl; intros. rewrite H. sep fail auto. eapply himp_trans. eapply IHn. eassumption. assert (s + S n = S s + n). omega. rewrite H1 in *. eassumption.
      sep fail auto.
  Qed.

  Definition free_branch : forall (p : ptr) (h : nat) (ary : array) (nxt : ptr) (m : [ptree (S h)]) (op : [option ptr]),
    (forall (p : ptr) (m : [sigTS ptree]) (op: [option ptr]),
       STsep (m ~~ op ~~ rep' (projT1S m) p op (projT2S m))
             (fun _:unit => __)) ->
     STsep (m ~~ op ~~
              p ~~> mkNode (S h) ary (Some nxt) * [array_length ary = SIZE] * [length (fst (snd m)) <= SIZE] *
              [nxt = ptrFor _ (snd (snd m))] *
              repBranch h (rep' h) ary 0 SIZE (fst (snd m)) (firstPtr _ (snd (snd m))) * rep' h nxt op (snd (snd m)))
           (fun _:unit => __).
  Proof.
     clear.
     refine (fun p h ary nxt m op rec =>
       Free p ;;
       rec nxt (m ~~~ existTS ptree h (snd (snd m))) op <@> _ ;;
       {{ Fix2 (fun (n:nat) (pf:n <= SIZE) => m ~~ op ~~
                      let lsM := fst (snd m) in
                      let nxtM := snd (snd m) in 
                      [length lsM <= SIZE] * [array_length ary = SIZE] *
                      {@ p0 :~~ array_plus ary i in p0 ~~>? | i <- 0 + n} *
                      repBranch h (rep' h) ary n (SIZE - n) (skipn n lsM) (firstPtr _ nxtM))
               (fun _ _ (_:unit)    => __)
               (fun self n pf =>
                 match le_lt_dec SIZE n with
                   | left _  => 
                     free_array ary <@> _ ;;
                     {{ Return tt }}
                   | right pfSn =>
                     kv <- sub_array ary n _ ;
                     let _:option (key * ptr) := kv in
                     match kv as kv' return kv = kv' -> _ with
                       | None => fun pf' => {{ self (S n) (lt_S_le pfSn) }}
                       | Some (_,p) => fun pf' =>
                         zz <- rec p (m ~~~ match nth_error (fst (snd m)) n with
                                              | None => existTS ptree (S h) m (** Junk **) 
                                              | Some v => existTS ptree h (projT2S v)
                                            end) _ <@> _ ;
                         {{ self (S n) (lt_S_le pfSn) }}
                     end (refl_equal _)
                 end) 0 (O_le SIZE) }}); clear rec; try clear self.
     solve [ sep fail auto ].
     solve [ sep fail auto ].
     inhabiter. rewrite H0. simpl. unpack_conc. simpl; canceler. sep fail auto.
     solve [ sep fail auto ].
     inhabiter. simpl. assert (n = SIZE); [omega|]. rewrite H1 in *. clear pf. clear l. intro_pure.
       apply skip_len in H2. rewrite H2. simpl. simpl. rewrite H3. canceler. sep fail auto.
     solve [ sep fail auto ].
     solve [ norm arith; sep fail auto ].
     solve [ sep fail auto ].
     instantiate (1 := fun cp:option (key * ptr) => m ~~ op ~~ 
         let lsM := fst (snd m) in
         let nxtM := snd (snd m) in
         {@ p0 :~~ array_plus ary i in p0 ~~>? | i <- 0 + n} * 
         [array_length ary = SIZE] * [length lsM <= SIZE] *
         match le_lt_dec (length lsM) n with
           | right pf' => 
             let k   := projT1S (@nthDep _ lsM n pf') in
             let p'' := ptrFor _ (projT2S (@nthDep _ lsM n pf')) in
             [cp = Some (k, p'')] *
             repBranch h (rep' h) ary (S n) (SIZE - n) (skipn (S n) lsM) (firstPtr _ nxtM)
           | left _ => repBranch h (rep' h) ary (S n) (SIZE - n) (skipn (S n) lsM) (firstPtr _ nxtM) *
             [length lsM <= n] * [cp = None]
           end).
     inhabiter. intro_pure. simpl. destruct x0. simpl in *. pose (l := fst y).
     destruct (le_lt_dec (length l) n).
       (** Before the end **)
       assert (skipn n l = nil). apply skip_len; auto. norm pair. unfold l in H3. rewrite H3 in *. simpl.
       eapply himp_trans.
(** TODO: Finish this
       instantiate (1 := {@hprop_unpack (array_plus ary i) (fun p0 : ptr => p0 ~~>?) | i <- (0) + n} * 
                         (Exists p' :@ ptr, nxt ~~> p' * rep' h p' v cont t) * [array_length ary = SIZE] * [length l <= SIZE] * _). canceler. eapply (@split_array_unroll (SIZE - n) 0 n); omega. norm arith.
       sep fail auto. destruct (le_lt_dec (length l) n); try solve [elimtype False; omega]. 
       match goal with 
         | [ |- context [ repBranch _ _ _ _ ?X _ _ ] ] => assert (X = nil)
       end. destruct l; auto. eapply skip_len. simpl in *. omega. 
       rewrite H7. clear H7. simpl. rewrite H2. sep fail auto.
       (** At the end **)
       generalize (skip_len_ne _ l0). intro. destruct H3. destruct H3. simpl in *. rewrite H3 in *. simpl.
       sep fail auto. destruct (le_lt_dec (length l) n); try solve [elimtype False; omega].
       destruct l; try solve [ simpl in *; elimtype False; omega ].
       assert (nthDep (s :: l) l1 = x); try solve [ eapply skipn_nthDep; eauto ]. rewrite H7.
       assert (skipn n l = x0); try solve [ eapply skipn_shift; eauto ]. rewrite H8. sep fail auto.
     solve [ sep fail auto ].
     instantiate (2 := m ~~ p :~~ array_plus ary n in p ~~> kv * [array_length ary = SIZE] * [length (fst m) <= SIZE] *
       {@hprop_unpack (array_plus ary i) (fun p4 : ptr => p4 ~~>?) | i <- 0 + n}).
     instantiate (1 := (fun op0 : option ptr => m ~~
       repBranch h (rep' h) ary (S n) (skipn (S n) (fst m)) op0
       (fun op1 : option ptr =>
         Exists p' :@ ptr,
         nxt ~~> p' * rep' h p' op1 cont (snd m)))).

     simpl. inhabiter. destruct (le_lt_dec (length (fst x)) n); try solve [ intro_pure; congruence ].
     intro_pure.
     destruct x. simpl in *.
     destruct l0; try solve [simpl in *; elimtype False; omega].
     generalize (skip_len_ne _ l). intro. destruct H5. destruct H5.
     assert (nthDep (s :: l0) l = x); try solve [ eapply skipn_nthDep; eauto ]. rewrite H6.
     assert (skipn n l0 = x2); try solve [ eapply skipn_shift; eauto ]. rewrite H7.
     assert (nth_error (s :: l0) n = Some x). eapply nth_error_nthDep; eauto. rewrite H. simpl. rewrite H8.
     clear H8. clear H6. sep fail auto. instantiate (1 := v). inversion H. eapply rep'_inj.
       intros. sep fail auto. rewrite <- (pack_injective H1). simpl. sep fail auto.

     solve [ sep fail auto ].
     simpl. sep fail auto. eapply iter_fb; eauto.
     solve [ sep fail auto ].
     (** At the end **)
     rewrite pf'. simpl. sep fail auto.
     match goal with 
       | [ |- context [ match ?X with | left _ => _ | right _ => _ end ] ] => destruct X
     end; try solve [ inhabiter; intro_pure; congruence ].
     match goal with 
       | [ |- context [ repBranch _ _ _ _ ?X _ _ ] ] => assert (X = nil)
     end. match goal with 
            | [ |- match ?X with | nil => _ | _ :: _ => _ end = _ ] => destruct X
          end; auto. eapply skip_len. simpl in *. omega.
     rewrite H. sep fail auto. eapply iter_fb; eauto.
     
     solve [ sep fail auto ].
     sep fail auto.
     sep fail auto.
  Qed.
**)
  Admitted.

  Definition free_rec : forall (p : ptr) (m : [sigTS ptree]) (op : [option ptr]),
    STsep (m ~~ op ~~ rep' (projT1S m) p op (projT2S m))
          (fun r:unit => __).
    refine
      (Fix3 (fun p m op => m ~~ op ~~ rep' (projT1S m) p op (projT2S m))
            (fun _ _ _ (r:unit) => __)
            (fun self p m op =>
              {{ @bpt_case (unit) (fun _ => __) (__) p m op
                  (fun a n l => {{ free_leaf p a n l }})
                  (fun h a n m => {{ @free_branch p h a n m op self }}) }})); try clear self;
    t.
  Qed.

  Definition free (t : BptMap) (m : [Model]) :
    STsep (m ~~ rep t m)
          (fun _:unit => __). 
    refine (fun t m =>
      {{ @free_rec (fst t) (snd t) [None] }}).
  Proof.
    solve [ unfold rep; inhabiter; destruct x0; sep fail auto ].
    solve [ sep fail auto ].
  Qed.
    
  Inductive op : Set :=
  | Merge   : ptr -> op
  | Split   : ptr -> key -> ptr -> op
  | Combine : ptr -> op.
(*  | Splice  : ptr -> op. *)

  Definition opModel (h : nat) (m : op) : Set :=
    match m with
      | Merge _ => ptree h
      | Split _ _ _ => ptree h * key * ptree h
      | Combine _ => ptree h
(*
      | Splice _ =>
        match h with 
          | 0 => Empty_set
          | S h' => ptree h'
        end
*)
    end%type.

  Definition as_mapOp (h : nat) (m : op) : opModel h m -> Model :=
    match m with
      | Merge _ => fun opm => as_map h opm
      | Split _ _ _ => fun opm => (as_map h (fst (fst opm))) ++ (as_map h (snd opm))
      | Combine _ => fun opm => as_map h opm
    end.

  Definition firstPtrOp (h : nat) (m : op) : opModel h m -> ptr :=
    match m as m return opModel h m -> ptr with
      | Merge _ => fun m => firstPtr _ m
      | Split _ _ _ => fun m => firstPtr _ (fst (fst m))
      | Combine _ => fun m => firstPtr _ m
    end.

  Definition repOp (h : nat) (o : op) (m : opModel h o) (min max : LiftOrder key) 
    (optr : option ptr) : hprop :=
    match o as o return opModel h o -> hprop with
      | Merge p        => fun m => [inv h m min max] * rep' h p optr m
      | Split lp kp rp => fun lkr => 
        let l := fst (fst lkr) in
        let k := snd (fst lkr) in
        let r := snd lkr in
        [inv h l min (Val k)] * [inv h r (Val k) max] * 
        [lp = ptrFor _ l] * [kp = k] * [rp = ptrFor _ r] *
        rep' h lp (Some (firstPtr _ r)) l * rep' h rp optr r
      | Combine p      => fun m => [inv h m min max] * rep' h p optr m
(*
      | Splice p       => 
        match h as h return opModel h (Splice p) -> hprop with
          | 0   => fun _ => [False]
          | S h => fun m => [inv h m min max] * rep' h p optr m
        end
*)
    end m.

  (** Compute **)
  Section Compute.
    Hypothesis RT : Type.
    Hypothesis P  : hprop.
    Hypothesis Q  : RT -> hprop.
    Hypothesis tK : key.

    Definition RES (n : nat) := (RT * sigT (fun o:op => [opModel n o]%type))%type.

    Hypothesis Spec : key -> list (sigTS value) -> (RT * list (sigTS value)).
    Hypothesis SpecLocal : forall (min' min max max' : LiftOrder key) (k : key) (i ol oh : list (sigTS value)),
      KLsorted min' (ol ++ i ++ oh) max' ->
      KLsorted min i max ->
      key_between min k max ->
      Spec k (ol ++ i ++ oh) = (fst (Spec k i), ol ++ snd (Spec k i) ++ oh).

    Hypothesis Fn : forall (p : ptr) (ary : array) (nxt : option ptr) 
      (ls : [list (sigTS value)]) (min max : [LiftOrder key]),
      STsep (ls ~~ min ~~ max ~~
                p ~~> mkNode 0 ary nxt * repLeaf ary 0 SIZE ls * [KLsorted min ls max] * [key_between min tK max] * P)
            (fun r:RES 0 => min ~~ max ~~ ls ~~ m :~~ projT2 (snd r) in
                repOp 0 (projT1 (snd r)) m min max nxt * Q (fst r) *
                [firstPtrOp _ _ m = p] *
                [Spec tK ls = (fst r, as_mapOp _ _ m)]).

(**
    Definition leafCompute : forall (min max : [LiftOrder key]) 
      (p : ptr) (ary : array) (nxt : option ptr) (ls : [list (sigTS value)]),
      STsep (min ~~ max ~~ ls ~~ p ~~> mkNode 0 ary nxt * [array_length ary = SIZE] *
               [length ls <= SIZE] * repLeaf ary 0 SIZE ls * [KLsorted min ls max] * [key_between min tK max] * P)
            (fun res :RES 0 => min ~~ max ~~ opm :~~ projT2 (snd res) in 
               Exists op' :@ option ptr, repOp 0 (projT1 (snd res)) opm min max op' * Q (fst res))).
      refine (fun min max p ary nxt ls =>
        {{ Fn p ary nxt ls min max }}).
      sep fail auto.
      sep fail auto.
    Qed.
**)
    Lemma div2_mag : forall x,
      1 < x -> x - div2 x >= 1.
    Proof.
      clear. intros.
      assert (0 < x); think. generalize (lt_div2 _ H0). omega.
    Qed.
    Lemma half_list_not_nil : forall T (l:list T),
      1 < length l -> skipn (div2 (length l)) l = nil -> False.
    Proof.
      clear. intros. generalize (firstn_skipn (div2 (length l)) l). intros.
      generalize (div2_mag H). assert (length l = length l); think. rewrite <- H1 in H2 at 2. rewrite H2 in H3.
      assert (length (firstn (div2 (length l)) l) = div2 (length l)).
        generalize (Min.min_dec (div2 (length l)) (length l)). intros. destruct H4. 
        Focus 2. generalize (Min.le_min_l (div2  (length l)) (length l)). rewrite e.
        intros. elimtype False.         
        generalize (lt_div2 (length l)). cut (0 < length l); think.
          
        rewrite <- e. rewrite firstn_length. rewrite <- Min.min_assoc.
        cut (Min.min (length l) (length l) = length l). intros. rewrite H4. auto.
        clear. induction (length l); think.
        rewrite app_length in *. rewrite H4 in *. rewrite H0 in *. simpl in *. norm arith in *. norm list in *.
        generalize H2. generalize H. clear. generalize (length l). clear.
        intros. assert (0 < n); think. generalize (lt_div2 _ H0). think.
    Qed.

    Definition splitContent : forall (h : nat) (lsM : list (sigTS (fun _:key => ptree h)))
      (pf : length lsM = SIZE),
      (list (sigTS (fun _:key => ptree h)) * ptree h * key * list (sigTS (fun _:key => ptree h))).
    refine (fun h lsM pf =>
      match skipn (div2 SIZE) lsM as LL return skipn (div2 SIZE) lsM = LL -> _ with
        | nil => fun _ => False_rec _ _
        | (existTS k v) :: rr => fun _ => 
          (firstn (div2 SIZE) lsM, v, k, rr)
      end (refl_equal _)).
    Proof.
      Hint Resolve half_list_not_nil.
      subst. eauto.
    Defined.

    Definition repBranch_nextPtr {h} (ls : list (sigTS (fun _:key => ptree h))) i (optr : option ptr) : option ptr :=
      match nth_error ls (S i) with
        | None => optr
        | Some (existTS _ v) => Some (firstPtr _ v)
      end.

    Definition repBranchExcept h ary i ls optr : hprop :=
      repBranch h (rep' h) ary 0 i ls (match nth_error ls i with
                                         | None => optr
                                         | Some (existTS _ v) => firstPtr _ v
                                       end) *
      repBranch h (rep' h) ary (S i) (SIZE - S i) (skipn (S i) ls) optr.

    Lemma repBranch_split : forall h ary x0 i s e ls,
      i < e ->
      repBranch h (rep' h) ary s e ls x0 ==>
      repBranch h (rep' h) ary s i ls x0 *
      repBranch h (rep' h) ary (s + i) (e - i) (skipn i ls) x0.
    Proof.
      induction i.
      simpl; intros; norm arith; sep fail auto.
        destruct e; intros. think.
          simpl. destruct ls. t. eapply himp_trans. eapply IHi. think. norm list. norm arith. sep fail auto.
          cut (S (s + i) = s + S i); think.
        destruct ls.
          sep fail auto. eapply himp_trans. eapply IHi. think. sep fail auto. cut (S (s + i) = s + S i); think.
          sep fail auto. eapply himp_trans. eapply IHi. omega. sep fail auto. cut (S (s + i) = s + S i); think.
    Qed.

    Lemma skipn_len : forall (T:Type) i a0,
      length a0 <= i -> skipn i a0 = @nil T.
    Proof.
      induction i; destruct a0; simpl in *; think.
    Qed.

    Lemma nth_error_len : forall i T (x:list T), 
      length x <= i -> nth_error x i = None.
    Proof.
      induction i; destruct x; simpl in *; think.
    Qed.

    Lemma repBranch_splitEnd : forall h ary x0 idx a0,
      idx < SIZE ->
      idx >= length a0 ->
      repBranch h (rep' h) ary 0 SIZE a0 x0 ==>
      repBranchExcept h ary idx a0 x0 *
      (p :~~ array_plus ary idx in p ~~> @None (key * ptr)).
    Proof.
      intros.
      eapply himp_trans. eapply repBranch_split; try eassumption. 
      unfold repBranchExcept. norm arith. cut (SIZE - idx = S (SIZE - S idx)). intros. rewrite H1.
        simpl. cut (skipn idx a0 = nil).  intro. rewrite H2. sep fail auto. destruct a0; sep fail auto. norm list. sep fail auto.        
        cut (skipn idx a0 = nil); intros. rewrite H4. sep fail auto.
        rewrite nth_error_len. sep fail auto. simpl. auto. eapply skipn_len; eauto. eapply skipn_len; eauto. omega.        
    Qed.

    Definition invCF (n0 : nat) (mi : LiftOrder key) (c : sigTS (fun _ : key => ptree n0)) :=
      inv n0 (projT2S c) mi (Val (projT1S c)).
    Definition invCB (n0 : nat) (nxt : ptree n0) (max mi : LiftOrder key) := inv n0 nxt mi max.

(**
    Lemma inv_Merge : forall h p x1 x3 x6 x5 x7,
      contextual h (invCF h) (fun mi : LiftOrder key => mi = x6) x7 x3
      -> inv h x1 x6 x5
      -> inv (S h) (p, (x3, x1)) x7 x5.
    Proof.
      Transparent inv. induction x3. simpl.
        intros. simpl. subst; auto.
        simpl. unfold invCF. think.
    Qed.
    Opaque inv.
**)

    Lemma ltS: forall j b, j < b -> S j <= b.
      intros; omega.
    Qed.

    Ltac combine_le_le := idtac;
      match goal with
        | [ H : ?X <= ?Y, H' : ?Y <= ?X |- _ ] => 
          let H'' := fresh "F" in assert (X = Y); [omega|clear H; clear H']
      end.

    Definition arrayInit : forall (T : Set) (ary : array) (st len : nat) (v : T),
      STsep ({@ p :~~ array_plus ary i in p ~~>? | i <- st + len})
            (fun _:unit => {@ p :~~ array_plus ary i in p ~~> v | i <- st + len}).
      refine (fun T ary st len v =>
         {{ Fix2 (fun j (_ : j <= len) => 
                  {@ p :~~ array_plus ary i in p ~~> v | i <- st + j} * 
                  {@ p :~~ array_plus ary i in p ~~>?  | i <- (st + j) + (len - j)})
               (fun _ _ (r:unit) => 
                  {@ p :~~ array_plus ary i in p ~~> v | i <- st + len})
               (fun self j pf =>
                 match le_lt_dec len j with
                   | left _ => {{ Return tt }}
                   | right pf2 => 
                     upd_array ary (st + j) v <@> _ ;;
                     {{ self (S j) (ltS pf2) }}
                 end)
               0 (O_le len) }} ); try clear self.
      solve [ sep fail auto ].
      combine_le_le. rewrite H. solve [ norm arith; sep fail auto ].
      apply himp_comm_prem.
      split_index'. instantiate (1 := 0); omega. simpl. norm arith. unfold ptsto_any at 1.
      instantiate (1 := 
        {@hprop_unpack (array_plus ary i) (fun p : ptr => p ~~>?) | i <- (S (st + j)) + len - S j} *
        {@hprop_unpack (array_plus ary i) (fun p : ptr => p ~~> v) | i <- (st) + j}).
      solve [ sep fail auto ].
      solve [ sep fail auto ].
      norm arith. canceler. eapply sp_index_conc. instantiate (1 := j); omega. canceler. norm arith. simpl. assert (S (st + j) = st + S j). omega. rewrite H. sep fail auto.
      solve [ sep fail auto ].
      norm arith. solve [ sep fail auto ].
      solve [ sep fail auto ].
    Qed.

    Definition arrayIter2 : forall (src trg : array) (sst tst len : nat) 
      (f f' g g' : nat -> ptr -> hprop)
      (F : forall (i j : nat) ,
        STsep (pi :~~ array_plus src i in pj :~~ array_plus trg j in f i pi * g j pj)
              (fun _:unit => pi :~~ array_plus src i in pj :~~ array_plus trg j in f' i pi * g' j pj)),
      STsep ({@ p :~~ array_plus src i in f i p | i <- sst + len} *
             {@ p :~~ array_plus trg i in g i p | i <- tst + len})
            (fun _:unit =>
               {@ p :~~ array_plus src i in f' i p | i <- sst + len} *
               {@ p :~~ array_plus trg i in g' i p | i <- tst + len}).
      refine (fun src trg sst tst len f f' g g' F =>
        {{ Fix2 (fun j (_ : j <= len) =>
                  ({@ p :~~ array_plus src i in f' i p | i <- sst + j} * 
                   {@ p :~~ array_plus src i in f  i p | i <- (sst + j) + (len - j)}) *
                  ({@ p :~~ array_plus trg i in g' i p | i <- tst + j} * 
                   {@ p :~~ array_plus trg i in g  i p | i <- (tst + j) + (len - j)}))
                (fun _ _ (r:unit) => 
                  {@ p :~~ array_plus src i in f' i p | i <- sst + len} *
                  {@ p :~~ array_plus trg i in g' i p | i <- tst + len})
               (fun self j pf =>
                 match le_lt_dec len j with
                   | left _ => {{ Return tt }}
                   | right pf2 =>
                     F (sst + j) (tst + j) <@> _ ;;
                     {{ self (S j) (ltS pf2) }}
                 end)
               0 (O_le len) }} ); try clear self; try clear F.
    Proof.
      solve [ sep combine_le_le auto ].
      combine_le_le. rewrite H. norm arith. solve [ sep fail auto ].

      simpl. apply himp_assoc_prem2. split_index'. instantiate (1 := 0); omega. norm arith. simpl.
      search_prem ltac:(idtac; match goal with 
                          | [ |- {@hprop_unpack (array_plus trg i) (fun p : ptr => g i p) | i <-
     (tst + j) + len - j} * _ ==> _ ] => split_index'; [ instantiate (1 := 0); omega | ]
                        end).
      norm arith. simpl. inhabiter. rewrite H. rewrite H0. unpack_conc. canceler. solve [ sep fail auto ].
      solve [ sep fail auto ].
      simpl. inhabiter. rewrite H1. rewrite H2.
      assert (sst + S j = S (sst + j)); [omega|].
      assert (tst + S j = S (tst + j)); [omega|].
      rewrite H3. rewrite H4. canceler. sep fail auto.
        generalize dependent x. generalize dependent x0. generalize dependent x3. generalize dependent x4. clear.
        generalize dependent sst. generalize dependent tst.
        induction j.
        simpl. intros; norm arith in *. rewrite H1 in H. rewrite H2 in H0. sep fail auto.
        simpl. intros; norm arith in *. assert (tst + S j = (S tst) + j); [omega|]. assert (sst + S j = (S sst) + j); [omega|]. rewrite H3 in *. rewrite H4 in *.
        inhabiter.
        generalize (IHj _ _ _ H5 _ H6 _ H0 _ H). sep fail auto. eapply himp_trans. Focus 2. eapply himp_trans.
        eapply H7. sep fail auto. sep fail auto.
      solve [ sep fail auto ].
      solve [ norm arith; sep fail auto ].
      solve [ sep fail auto ].
    Qed.

    Definition arrayIter2' : forall (src trg : array) (sst tst len : nat) 
      (f f' g g' : nat -> ptr -> hprop)
      (F : forall (i : nat) (_:i < len),
        STsep (pi :~~ array_plus src (sst + i) in pj :~~ array_plus trg (tst + i) in f i pi * g i pj)
              (fun _:unit => pi :~~ array_plus src (sst + i) in pj :~~ array_plus trg (tst + i) in f' i pi * g' i pj)),
      STsep ({@ p :~~ array_plus src (sst + i) in f i p | i <- 0 + len} *
             {@ p :~~ array_plus trg (tst + i) in g i p | i <- 0 + len})
            (fun _:unit =>
               {@ p :~~ array_plus src (sst + i) in f' i p | i <- 0 + len} *
               {@ p :~~ array_plus trg (tst + i) in g' i p | i <- 0 + len}).
      refine (fun src trg sst tst len f f' g g' F =>
        {{ Fix2 (fun j (_ : j <= len) =>
                  ({@ p :~~ array_plus src (sst + i) in f' i p | i <- 0 + j} * 
                   {@ p :~~ array_plus src (sst + i) in f  i p | i <- j + (len - j)}) *
                  ({@ p :~~ array_plus trg (tst + i) in g' i p | i <- 0 + j} * 
                   {@ p :~~ array_plus trg (tst + i) in g  i p | i <- j + (len - j)}))
                (fun _ _ (r:unit) => 
                  {@ p :~~ array_plus src (sst + i) in f' i p | i <- 0 + len} *
                  {@ p :~~ array_plus trg (tst + i) in g' i p | i <- 0 + len})
               (fun self j pf =>
                 match le_lt_dec len j with
                   | left _ => {{ Return tt }}
                   | right pf2 =>
                     F j pf2 <@> _ ;;
                     {{ self (S j) (ltS pf2) }}
                 end)
               0 (O_le len) }} ); try clear self; try clear F.
    Proof.
(**
      solve [ sep combine_le_le auto ].
      combine_le_le. rewrite H. norm arith. solve [ sep fail auto ].

      simpl. apply himp_assoc_prem2. split_index'. instantiate (1 := 0); omega. norm arith. simpl.
      search_prem ltac:(idtac; match goal with 
                          | [ |- {@hprop_unpack (array_plus trg (tst + i)) (fun p : ptr => g i p) | i <- j + len - j} * _ ==> _ ] => split_index'; [ instantiate (1 := 0); omega | ]
                        end).
      norm arith. simpl. inhabiter. rewrite H. rewrite H0. unpack_conc. canceler. solve [ sep fail auto ].
      solve [ sep fail auto ].
      simpl. inhabiter. rewrite H1. rewrite H2.
      t. 
        generalize dependent x. generalize dependent x0. generalize dependent x3. generalize dependent x4. cut (0 <= j); [|omega]. clear.
        generalize dependent sst. generalize dependent tst. generalize 0.
        induction j.
        simpl. intros; norm arith in *. destruct n; [norm arith in *|think]. sep fail auto.
        simpl. intros; norm arith in *. 
        inhabiter. canceler. destruct n. sep fail auto. split_index'. instantiate (1 := 0). 


assert (tst + S j = (S tst) + j); [omega|]. assert (sst + S j = (S sst) + j); [omega|]. rewrite H3 in *. rewrite H4 in *.
        assert (S sst = S sst + 0); [omega|].
        assert (S tst = S tst + 0); [omega|].
        rewrite H7 in H6. rewrite H8 in H5.
        generalize (IHj _ _ _ H5 _ H6 _ H0 _ H). sep fail auto. eapply himp_trans. Focus 2. eapply himp_trans.
        eapply H9. sep fail auto. sep fail auto.
      solve [ sep fail auto ].
      solve [ norm arith; sep fail auto ].
      solve [ sep fail auto ].
**)
    Admitted.

    Lemma nth_error_len_lt : forall T (ls:list T) i,
      i < length ls -> exists v, nth_error ls i = Some v.
    Proof. clear.
      induction ls. simpl. think.
      simpl. induction i. simpl. intros. eauto. simpl. intros. eapply IHls; think.
    Qed.

(**
    Definition mergeOpNext_copyArray : forall (h : nat) (src trg : array) (lP : ptr) (k : key) (rP : ptr)
      (optr : [option ptr]) (ls : [list (option (key * ptree h))]) (pt1 pt2 : [ptree h]),
      STsep (ls ~~ pt1 ~~ pt1 ~~ optr ~~ 
               repBranch (rep' h) src 0 SIZE ls * rep' h lP (firstPtr _ pt2) pt1 * rep' h rP optr pt2)
            (fun res:([ptree h] * key * [ptree h]) =>
**)              

(** NOTE: We can't write this function because the pointers are in the model and 
          we can't construct a new pointer in a pure term
    Definition specMergeNext (h : nat) (p : ptr) (ls : list (sigTS (fun _:key => ptree h))) op 
      : opModel h op -> sigTS (opModel (S h)).
    refine (fun h p lsM op0  =>
      match op0 as op return opModel h op -> sigTS (opModel (S h)) with
        | Merge m => fun opm => 
          existTS _ (Merge p) (p, (lsM, opm))
        | Split l k r => fun opm =>
          match opm with
            | (lM,kM,rM) =>
              if le_lt_dec SIZE (length lsM) then
                existTS _ (Merge p) (p, (lsM ++ (existTS _ kM lM :: nil), rM))
              else
                let l' := 
                existTS _ (Split 
          end

        | _ => _
      end).
**)

    Definition mergeOpNext : forall (min mid max : [LiftOrder key]) (h : nat)
      (p : ptr) (ary : array) (optr : [option ptr]) (full : nat) (res' : RES h) (m : [ptree (S h)]),
      full <= SIZE ->
      STsep (min ~~ mid ~~ max ~~ m ~~ optr ~~ opm :~~ projT2 (snd res') in
               let o := projT1 (snd res') in
               let lsM  := fst (snd m) in
               let nxtM := snd (snd m) in
               Exists nxt :@ ptr,
               p ~~> mkNode (S h) ary (Some nxt) *
               [length lsM = full] * [array_length ary = SIZE] *
               [mid = lastKey lsM min] *
               [contextual h (fun mi c => inv h (projT2S c) mi (Val (projT1S c))) min mid lsM] *
               repBranch h (rep' h) ary 0 SIZE lsM (firstPtrOp _ _ opm) *
               repOp h o opm mid max optr *
               Q (fst res') *
               (** TODO: Characterize the model of the pieces **) __)
            (fun res : RES (S h) => min ~~ max ~~ optr ~~ m ~~ 
               opm :~~ projT2 (snd res) in opm' :~~ projT2 (snd res') in
               repOp (S h) (projT1 (snd res)) opm min max optr * Q (fst res) *
               [firstPtrOp _ _ opm = match head (fst (snd m)) return ptr with
                                       | None => firstPtrOp _ _ opm'
                                       | Some n => firstPtr _ (projT2S n)
                                     end] *
               [fst res = fst res'] *
               [List.flat_map (fun x => @as_map h (projT2S x)) (fst (snd m)) ++ as_mapOp _ _ opm' = as_mapOp _ _ opm]).
    Admitted.

    Definition mergeOpInternal : forall (min midL midH max : [LiftOrder key]) (h : nat)
      (p : ptr) (ary : array) (nxt : ptr) (optr : [option ptr]) (pos full : nat) (res' : RES h) (m : [ptree (S h)]),
      full <= SIZE ->
      STsep (min ~~ midL ~~ midH ~~ max ~~ m ~~ optr ~~ opm :~~ projT2 (snd res') in
               let o := projT1 (snd res') in
               let lsM  := fst (snd m) in
               let nxtM := snd (snd m) in
               p ~~> mkNode (S h) ary (Some nxt) *
               [length lsM = full] * [array_length ary = SIZE] *
               [midL = lastKey (firstn (pred pos) lsM) min] *
               [midH = lastKey (firstn pos lsM) min] *
               [contextual h (fun mi c => inv h (projT2S c) mi (Val (projT1S c))) min midL (firstn (pred pos) lsM)] *
               [contextual h (fun mi c => inv h (projT2S c) mi (Val (projT1S c))) midH (lastKey lsM midH) (skipn pos lsM)] *
               [inv h nxtM (lastKey lsM midH) max] *
               repBranch h (rep' h) ary 0 pos lsM (firstPtrOp _ _ opm) *
               repBranch h (rep' h) ary (S pos) (SIZE - S pos) (skipn pos lsM) (firstPtr _ nxtM) *
               rep' h nxt optr nxtM *
               repOp h o opm midL midH optr *
               Q (fst res') *
               (** TODO: Characterize the model of the pieces **) __)
            (fun res : RES (S h) => min ~~ max ~~ optr ~~ m ~~ 
               opm :~~ projT2 (snd res) in opm' :~~ projT2 (snd res') in
               repOp (S h) (projT1 (snd res)) opm min max optr * Q (fst res) *
               [firstPtrOp _ _ opm = match head (fst (snd m)) return ptr with
                                       | None => firstPtrOp _ _ opm'
                                       | Some n => firstPtr _ (projT2S n)
                                     end] *
               [fst res = fst res'] *
               [List.flat_map (fun x => @as_map h (projT2S x)) (firstn pos (fst (snd m))) ++ as_mapOp _ _ opm' ++ 
                List.flat_map (fun x => @as_map h (projT2S x)) (skipn (S pos) (fst (snd m))) ++ as_map _ (snd (snd m)) = as_mapOp _ _ opm]).
    Admitted.
(**
      refine (fun min mid max h p ary optr full res m pfFullSize =>
        pflsFull <- shift (exists m', [m']%inhabited = m /\ length (fst (snd m')) = full) <@> _ ;
        let rt := fst res in
        match snd res as OP return snd res = OP -> _ with
          | (existT (Merge p') opm) => fun pf =>
            p ::= mkNode (S h) ary (Some p') ;;
            let rM : [opModel (S h) (Merge p)] := 
                     m ~~~' opm ~~~ (p, (fst (snd m), opm)) in
            {{ Return (rt, existT _ (Merge p) rM) }}
          | (existT (Split l k r) opm) => fun pf => 
            if le_lt_dec SIZE full then
              (** Insufficient space, have to split **)
              aryR <- new_empty_array (key * ptr) SIZE <@> _ ;
              (** copy indicies SIZE / 2 + 1 to SIZE into aryR (write None to the rest) **)
              @arrayIter2' ary aryR (S (div2 SIZE)) 0 (pred (div2 SIZE))
                (fun i p => m ~~ match nth_error (fst (snd m)) i with
                                   | None => [False]
                                   | Some v => p ~~> Some (projT1S v, ptrFor _ (projT2S v))
                                 end)
                (fun i p => p ~~> @None (key * ptr))
                (fun i p => p ~~> @None (key * ptr))
                (fun i p => m ~~ match nth_error (fst (snd m)) i with
                                   | None => [False]
                                   | Some v => p ~~> Some (projT1S v, ptrFor _ (projT2S v))
                                 end) 
                (fun i pfI => 
                  v <- sub_array ary ((S (div2 SIZE)) + i) _ ;
                  upd_array aryR i v <@> 
                      (pi :~~ array_plus ary (S (div2 SIZE) + i) in m ~~ 
                        match nth_error (fst (snd m)) i with
                          | Some v0 => [v = Some (projT1S v0, ptrFor h (projT2S v0))]
                          | None => [False]
                        end * pi ~~> v) ;;
                  upd_array ary ((S (div2 SIZE)) + i) (@None (key * ptr)) <@> 
                      (pj :~~ array_plus aryR i in m ~~ 
                        match nth_error (fst (snd m)) i with
                          | Some v0 => pj ~~> Some (projT1S v0, ptrFor h (projT2S v0))
                          | None => [False]
                        end) ;;
                  {{ Return tt }}) <@> _ ;;
              (** put (k,l) in aryR at SIZE / 2 **)
              upd_array aryR (div2 SIZE) (Some (k,l)) <@> _ ;;
              
              (** **)
              pR <- New (mkNode (S h) aryR (Some r)) ;
              nxtL <- sub_array ary (div2 SIZE) _ ;
              match nxtL as nxtL' return nxtL = nxtL' -> _ with 
                | None           => fun _ => {{ !!! }}
                | Some (kM,nxtL) => fun _ =>
                  (** write None to ary[SIZE/2] **)
                  upd_array ary (div2 SIZE) (@None (key * ptr)) <@> _ ;;
                  p ::= mkNode (S h) ary (Some nxtL) <@> _ ;;
                  {{ Return (rt, existT _ (Split p kM pR) _) }}
              end (refl_equal _)
            else
              (** we can just merge **)
              upd_array ary full (Some (k, l)) <@> _ ;;
              p ::= mkNode (S h) ary (Some r) ;;
              let rM : [opModel (S h) (Merge p)] := 
                opm ~~~' m ~~~
                  let lM := fst (fst opm) in
                  let kM := snd (fst opm) in 
                  let rM := snd opm in
                  (p, (fst (snd m) ++ ((existTS (fun _:key => ptree h) kM lM) :: nil), rM)) in
              {{ Return (rt, existT _ (Merge p) rM) }}
          | (existT (Combine p') opm)  => fun pf => _ (** TODO **)
(*              let rM : [opModel (S h) (Merge p)] := 
                opm ~~~' m ~~~
                  let lM := fst (fst opm) in
                  let kM := snd (fst opm) in 
                  let rM := snd opm in
                  (p, (fst (snd m) ++ ((existTS (fun _:key => ptree h) kM lM) :: nil), rM)) in
              {{ Return (rt, existT _ (Merge p) rM) }}
*)
(**
          | Splice p'   => fun opm => _ (** TODO: a little crazy and not completely necessary **)
**)
        end (refl_equal _)); try clear Fn.
    Proof.
      instantiate (1 := hprop_unpack min
     (fun min0 : LiftOrder key =>
      hprop_unpack mid
        (fun mid0 : LiftOrder key =>
         hprop_unpack max
           (fun max0 : LiftOrder key =>
            hprop_unpack m
              (fun m0 : ptree (S h) =>
               hprop_unpack optr
                 (fun optr0 : option ptr =>
                  let opm := projT2 (snd res) in
                  hprop_unpack opm
                    (fun opm0 : opModel h (projT1 (snd res)) =>
                     let o := projT1 (snd res) in
                     let lsM := fst (snd m0) in
                     let nxtM := snd (snd m0) in
                     Exists nxt :@ ptr,
                     p ~~> mkNode (S h) ary (Some nxt) * [length lsM = full] *
                     [array_length ary = SIZE] * [mid0 = lastKey lsM min0] *
                     [contextual h
                        (fun (mi : LiftOrder key)
                           (c : sigTS (fun _ : key => ptree h)) =>
                         inv h (projT2S c) mi (Val (projT1S c))) min0 mid0
                        lsM] *
                     repBranch h (rep' h) ary 0 SIZE lsM
                       (firstPtrOp h (projT1 (snd res)) opm0) *
                     repOp h o opm0 mid0 max0 optr0 * 
                     Q (fst res) * __))))))).
      inhabiter. simpl. inhabiter. intro_pure. t. cut_pure. exists x. think.
      instantiate (1 := fun _ => hprop_unpack min
     (fun min0 : LiftOrder key =>
      hprop_unpack mid
        (fun mid0 : LiftOrder key =>
         hprop_unpack max
           (fun max0 : LiftOrder key =>
            hprop_unpack m
              (fun m0 : ptree (S h) =>
               hprop_unpack optr
                 (fun optr0 : option ptr =>
                  let opm := projT2 (snd res) in
                  hprop_unpack opm
                    (fun opm0 : opModel h (projT1 (snd res)) =>
                     let o := projT1 (snd res) in
                     let lsM := fst (snd m0) in
                     let nxtM := snd (snd m0) in
                     Exists nxt :@ ptr,
                     p ~~> mkNode (S h) ary (Some nxt) * [length lsM = full] *
                     [array_length ary = SIZE] * [mid0 = lastKey lsM min0] *
                     [contextual h
                        (fun (mi : LiftOrder key)
                           (c : sigTS (fun _ : key => ptree h)) =>
                         inv h (projT2S c) mi (Val (projT1S c))) min0 mid0
                        lsM] *
                     repBranch h (rep' h) ary 0 SIZE lsM
                       (firstPtrOp h (projT1 (snd res)) opm0) *
                     repOp h o opm0 mid0 max0 optr0 * 
                     Q (fst res) * __))))))).
      solve [ t ]. 

      (** Merge **)
      solve [ inhabiter; simpl; inhabiter; sep fail auto ].
      solve [ sep fail auto ].
      solve [ sep fail auto ]. (** TODO: where does this come from? **)
      rewrite pf. simpl. 
      intros. intro_pure. rewrite H. t. simpl. destruct x8. t.
        search_prem ltac:(eapply rep'_ptrFor_add); intros. rewrite <- H15. instantiate (1 := ary). simpl in *.
        unfold rM in *. rewrite H3 in *. rewrite H1 in *. simpl in *. apply pack_injective in H8. inversion H8. simpl.
        inversion H8. t.
      cut_pure. Transparent inv. simpl. Opaque inv. solve [ think ].

      (** Split **)
      solve [ t ].
      solve [ t ].
        (** This is the helper function **)
        simpl. 
        instantiate (1 := fun v' => pj :~~ array_plus aryR i in m ~~ match nth_error (fst (snd m)) i with
                                                                       | Some v => [v' = Some (projT1S v, ptrFor h (projT2S v))]
                                                                       | None => [False]
                                                                     end * pj ~~> @None (key * ptr)).
        destruct pflsFull. destruct H. rewrite <- H. clear min mid max. inhabiter.

        assert (i < length (fst (snd x7))).
          rewrite <- (pack_injective H7). rewrite H0. combine_le_le. rewrite H8 in *. cut (pred (div2 SIZE) < SIZE). omega. 
          generalize (lt_div2 SIZE). omega. generalize (nth_error_len_lt _ H8). intro. destruct H9. rewrite H9. simpl in *.
          destruct x8. fold ptree in *. simpl. t. rewrite H9. cut_pure. think.
        solve [ t ].
        intros. simpl. destruct pflsFull. destruct H. rewrite <- H.
        solve [ t ].
        solve [ t ].
        t. t. match goal with
                | [ |- _ ==> match ?X with | Some _ => _ | None => _ end ] => destruct X
              end; t.
        solve [ t ].
        solve [ t ].
        solve [ t; t ].
     instantiate (1 := hprop_unpack min
      (fun min0 : LiftOrder key =>
       hprop_unpack mid
         (fun mid0 : LiftOrder key =>
          hprop_unpack max
            (fun max0 : LiftOrder key =>
             hprop_unpack m
               (fun m0 : ptree (S h) =>
                hprop_unpack optr
                  (fun optr0 : option ptr =>
                   let opm1 := projT2 (snd res) in
                   hprop_unpack opm1
                     (fun opm2 : opModel h (projT1 (snd res)) =>
                      let o := projT1 (snd res) in
                      let lsM := fst (snd m0) in
                      let nxtM := snd (snd m0) in
                      Exists nxt :@ ptr,
                      p ~~> mkNode (S h) ary (Some nxt) * [length lsM = full] *
                      [array_length ary = SIZE] * [mid0 = lastKey lsM min0] *
                      [contextual h
                         (fun (mi : LiftOrder key)
                            (c : sigTS (fun _ : key => ptree h)) =>
                          inv h (projT2S c) mi (Val (projT1S c))) min0 mid0
                         lsM] *
                      match nth_error lsM (pred (div2 (array_length aryR))) with
                        | Some v => repBranch h (rep' h) ary 0 SIZE lsM (firstPtr _ (projT2S v))
                        | None => [False]
                      end *
                      repOp h o opm2 mid0 max0 optr0 * 
                      Q (fst res))))))) *
    ({@hprop_unpack (array_plus aryR i) (fun p0 : ptr => p0 ~~> None) | i <-
     (pred (div2 (array_length aryR))) + (SIZE - pred (div2 (array_length aryR)))} *
    [array_length aryR = SIZE])).
     destruct pflsFull. destruct H. rewrite <- H.
     t. t.
       apply himp_comm_prem. eapply himp_trans. eapply split_iter. instantiate (1 := pred (div2 (array_length aryR))).
         generalize (lt_div2 (array_length aryR)). omega.
       Focus 2. canceler. fold ptree in *. canceler.
     Check repBranch.


 sep fail auto.
        
          
          
 t.

match goal with 
        | [ |- context [ match ?X with | Some _ => _ | None => _ end ] ] => case_eq X
                  end. t. 
      solve [ t ].
      solve [ t ].

      Focus 4.
      rewrite pf.
      instantiate (1 := min ~~ mid ~~ max ~~
            hprop_unpack m
              (fun m0 : ptree (S h) =>
               hprop_unpack optr
                 (fun optr0 : option ptr =>
                  hprop_unpack opm0
                    (fun opm2 : opModel h (Split l k r) =>
                     let o := Split l k r in
                     let lsM := fst (snd m0) in
                     let nxtM := snd (snd m0) in
                     Exists nxt :@ ptr,
                     p ~~> mkNode (S h) ary (Some nxt) * [length lsM = full] *
                     [full <= SIZE] * [array_length ary = SIZE] *
                     [mid = lastKey lsM min] *
                     [contextual h
                        (fun (mi : LiftOrder key)
                           (c : sigTS (fun _ : key => ptree h)) =>
                         inv h (projT2S c) mi (Val (projT1S c))) min mid
                        lsM] *
                     repBranchExcept h ary full lsM (firstPtrOp h _ opm2) (firstPtrOp h _ opm2) *
                     repOp h o opm2 mid max optr0 * 
                     Q (fst res))))).
      t. rewrite H1.
      pose (@repBranch_splitEnd h ary (firstPtr h (fst (fst x0))) (length a0) a0).
      eapply himp_trans. eapply h0. rewrite H1 in *. think. think. simpl. solve [ t ].
      Focus 4.
      solve [ t ].
      Focus 4.
      instantiate (1 := nodeType).
      instantiate (1 := min ~~ mid ~~ max ~~ m ~~
               hprop_unpack optr
                 (fun optr0 : option ptr =>
                  hprop_unpack opm0
                    (fun opm2 : opModel h (Split l k r) =>
                     let o := Split l k r in
                     let lsM := fst (snd m) in
                     let nxtM := snd (snd m) in
                     Exists nxt :@ ptr, [length lsM = full] *
                     [full <= SIZE] * [array_length ary = SIZE] *
                     [mid = lastKey lsM min] *
                     [contextual h
                        (fun (mi : LiftOrder key)
                           (c : sigTS (fun _ : key => ptree h)) =>
                         inv h (projT2S c) mi (Val (projT1S c))) min mid
                        lsM] *
                     repBranchExcept h ary full lsM (firstPtrOp h _ opm2) (firstPtrOp h _ opm2) *
                     repOp h o opm2 mid max optr0 * 
                     Q (fst res))) *
                 (let p0 := array_plus ary full in
                   hprop_unpack p0 (fun p1 : ptr => p1 ~~> Some (k, l)))).
    t.
    Focus 4.
    solve [ t ].
    Focus 4.
    solve [ t ].
    Focus 4.
    intros. intro_pure.  rewrite H. t. simpl. t. destruct x0. simpl in *. t. instantiate (1 := ary).
    rewrite H20. rewrite H19. rewrite H18. t.
    unfold rM in H0. rewrite H1 in *.  rewrite H3 in *. simpl in *. apply pack_injective in H0. inversion H0.
    simpl in *. t.
    
   Lemma repBranch_NilEnd : forall h ary e e' l s,
      repBranch h (rep' h) ary s l nil e ==> repBranch h (rep' h) ary s l nil e'.
   Proof.
     induction l; sep fail auto; sep fail auto.
   Qed.

    Lemma repBranchExcept_merge : forall h ary x1 x3 p' idx,
      idx = length x3 ->
      (x8 :~~ array_plus ary idx in
        rep' h p' (Some (firstPtr h (snd x1))) (fst (fst x1)) *
        repBranchExcept h ary idx x3 (firstPtr h (fst (fst x1))) (firstPtr h (fst (fst x1))) *
        x8 ~~> Some (snd (fst x1), p')) ==>
        repBranch h (rep' h) ary 0 SIZE
          (x3 ++ existTS (fun _ : key => ptree h) (snd (fst x1)) (fst (fst x1)) :: nil)
          (firstPtr h (snd x1)).
    Proof.
(** TODO
      unfold repBranchExcept. intros. generalize pfMin. generalize SIZE. assert (idx = idx + 0); [omega|]. rewrite H0. generalize 0. generalize H. clear. induction idx.
        intros. destruct x3; [|simpl in *; congruence]. simpl. assert (SIZE0 = S (SIZE0 - 1)); [omega|intros]. rewrite H0. simpl. norm arith. inhabiter.
        search_prem ltac:(apply rep'_ptrFor_add); intros. unpack_conc. canceler. f_equal. f_equal. auto. rewrite H2. canceler. eapply repBranch_NilEnd.

        intros. inhabiter. destruct x3; [simpl in *; congruence|].
        destruct SIZE0; [elimtype False; omega|]. simpl.
        destruct x3. simpl. t.
**)
    Admitted.
    pose (@repBranchExcept_merge h ary x1 (fst (snd x3)) (ptrFor h (fst (fst x1))) (length (fst (snd x3))) (refl_equal _)).
    eapply himp_trans. Focus 2. eapply himp_trans. eapply h0. t. clear h0.
    rewrite app_length. simpl. t. cut_pure.
    Transparent inv. unfold inv. fold inv. Opaque inv. simpl.
    cut (lastKey
        (fst (snd x3) ++
         existTS (fun _ : key => ptree h) (snd (fst x1)) (fst (fst x1))
         :: nil) x7 = Val (snd (fst x1))).
    intros. split.
    Check contextual.
    Lemma contextual_append : forall h (F:forall x, sigTS (fun _ :key=>ptree h) -> Prop)  ls' max ls min mid,
      (forall a b c, OTeq KLOT a b -> F a c -> F b c) ->
      contextual h F min mid ls ->
      contextual h F mid max ls' ->
      contextual h F min max (ls ++ ls').
    Proof.
      clear. induction ls. simpl. intros.
        induction ls'. simpl in *.  order. simpl in *. think.
        simpl. think.
    Qed.
    eapply contextual_append; try eassumption.
    Lemma inv_subst : forall h (a b : LiftOrder key) (c : sigTS (fun _ : key => ptree h)),
      OTeq KLOT a b ->
      inv h (projT2S c) a (Val (projT1S c)) ->
      inv h (projT2S c) b (Val (projT1S c)).
    Proof.
      clear. Transparent inv. induction h.
    Admitted.
    refine (inv_subst h).
    simpl. unfold ptree in *. rewrite H. clear H. fold ptree in *.
    think. 
    unfold ptree in *. rewrite H. fold ptree in *. auto.
    clear. generalize x7. induction (fst (snd x3)). reflexivity. simpl. intros. apply IHl.
    

    (** Combine **)
   

    
      
    
    Admitted.

**)
    (** Final Definition **)
    Lemma eq_le : forall a, a <= a. 
      auto.
    Qed.
    Lemma lt_le : forall a b, a < b -> a <= b.
      auto.
    Qed.

    Lemma firstn_len_le : forall (n : nat) T (ls : list T), 
      length ls <= n -> firstn n ls = ls.
    Proof.
      clear. induction n; simpl; intros; destruct ls; think.
    Qed.

    Lemma inv_Next : forall h t' t ls min min' max,
      inv (S h) t' min' max ->
      ls = fst (snd t') ->
      t  = snd (snd t') ->
      min = lastKey ls min' ->
      inv h t min max. 
    Proof.
      clear. intros. destruct t'. destruct y. subst. Transparent inv. simpl in *. Opaque inv. firstorder.
    Qed.
    Hint Resolve inv_Next.

    Lemma repBranch_read : forall h ary x0 idx a0,
      idx < SIZE ->
      repBranch h (rep' h) ary 0 SIZE a0 x0 ==>
      repBranchExcept h ary idx a0 x0 *
      (p :~~ array_plus ary idx in
        Exists val :@ option (key * ptr),
        p ~~> val *
        [val = match nth_error a0 idx with
                 | None => @None (key * ptr)
                 | Some (existTS k v) => Some (k, ptrFor _ v)
               end] *
        (match nth_error a0 idx with
           | None => [val = @None (key * ptr)] * [idx >= length a0]
           | Some (existTS k v) => [val = Some (k, ptrFor _ v)] * [idx < length a0] *
             rep' h (ptrFor _ v) (repBranch_nextPtr a0 idx (Some x0)) v
         end%hprop)).
    Proof. clear.
      intros.
      eapply himp_trans. eapply repBranch_split; try eassumption.
      unfold repBranchExcept. norm arith. canceler. cut (SIZE - idx = S (SIZE - S idx)); [|omega]. intros. rewrite H0.
        simpl. clear H0.
        destruct (le_lt_dec (length a0) idx).
          rewrite skipn_len; auto. destruct a0. norm list. sep fail auto. simpl in *. rewrite skipn_len; auto. rewrite nth_error_len; eauto. sep fail auto.
        remember (length a0 - idx) as LEN.
          generalize dependent l. clear H. generalize dependent a0.  generalize dependent idx. induction LEN.
          
          Focus 2.
          intros.
    Admitted.
    Lemma repBranch_read' : forall P idx ary h x0 a0 Q,
      idx < SIZE ->
      repBranchExcept h ary idx a0 x0 *
      (p :~~ array_plus ary idx in
        Exists val :@ option (key * ptr),
        p ~~> val * 
        [val = match nth_error a0 idx with
                 | None => @None (key * ptr)
                 | Some (existTS k v) => Some (k, ptrFor _ v)
               end] *
        (match nth_error a0 idx with
           | None => [val = @None (key * ptr)] * [idx >= length a0]
           | Some (existTS k v) => [val = Some (k, ptrFor _ v)] * [idx < length a0] *
             rep' h (ptrFor _ v) (repBranch_nextPtr a0 idx (Some x0)) v
         end)) * P ==> Q ->
      repBranch h (rep' h) ary 0 SIZE a0 x0 * P ==> Q.
    Proof.
      clear. intros. eapply himp_trans. Focus 2. eapply H0. canceler. eapply repBranch_read; eauto.
    Qed.

    Ltac readBranch := idtac;
      match goal with
        | [ |- repBranch _ _ ?A _ _ _ _ * ?P ==> ?Q ] => idtac;
          match Q with 
            | context [ array_plus A ?X ] => eapply (@repBranch_read' P X A); [try omega|]
          end
      end.

    Lemma KLsorted_app : forall (V:key->Set) (l:list (sigTS V)) r max min,
      KLsorted min (l ++ r) max <->
      KLsorted min l (lastKey l min) /\ KLsorted (lastKey l min) r max.
    Proof. clear. split; generalize dependent min; generalize dependent max; generalize dependent r.
      induction l; [auto| unfold KLsorted in *; intros; simpl in *; instantiate; think].
      induction l; unfold KLsorted in *; intros; simpl in *; instantiate; think.        
    Qed.

    Lemma inv_KLsorted : forall h tr min max,
      inv h tr min max -> KLsorted min (as_map h tr) max.
    Proof. clear.
      Transparent inv.
      induction h. simpl. auto.
      simpl. fold ptree in *. destruct tr. destruct p0. induction l. simpl. think.
      simpl in *. think.
      rewrite app_ass.
      rewrite KLsorted_app. split; auto.
    Admitted.
    Hint Resolve inv_KLsorted.

    Lemma contextual_KLsorted : forall h' l x3,
      contextual h'
         (fun (mi : LiftOrder key) (c : sigTS (fun _ : key => ptree h')) =>
          inv h' (projT2S c) mi (Val (projT1S c))) x3 
         (lastKey l x3) l
      -> KLsorted x3
     (flat_map
        (fun x0 : sigTS (fun _ : key => ptree h') => as_map h' (projT2S x0))
        l)
     (lastKey
        (flat_map
           (fun x0 : sigTS (fun _ : key => ptree h') =>
            as_map h' (projT2S x0)) l) x3).
    Proof. clear.
      induction h'. simpl. induction l. intros. simpl. auto. simpl. think. rewrite KLsorted_app. think.
    Admitted.
    Hint Resolve contextual_KLsorted.
    Lemma lastKey_flatten : forall h' l x3, 
      (OTlt KLOT (lastKey
        (flat_map
           (fun x0 : sigTS (fun _ : key => ptree h') =>
            as_map h' (projT2S x0)) l) x3) (lastKey l x3) \/
    OTeq KLOT (lastKey
        (flat_map
           (fun x0 : sigTS (fun _ : key => ptree h') =>
             as_map h' (projT2S x0)) l) x3) (lastKey l x3)).
    Proof.
    Admitted.
    Lemma invWeaken : forall h' p1 min min' x2,
      inv h' p1 min x2
      -> OTlt KLOT min' min
      -> inv h' p1 min' x2.
    Proof. clear.
      induction h'. simpl. think. unfold KLsorted in *. destruct p1. simpl in *.
      induction l. simpl in *. destruct H; [ left; eapply OTlt_trans; eassumption|]. order. simpl in *.  destruct H.  split. eapply OTlt_trans; eassumption. auto.
      destruct p1. fold ptree in *. simpl in *. destruct y. simpl in *. intros.
      destruct H. split. generalize dependent H1. generalize dependent H. induction l. think. simpl in *. order.
      simpl in *. intros. think.
      destruct l. simpl in *. think. think.
    Qed.

    Lemma inv_subst : forall h a b c d,
      inv h d a c ->
      OTeq KLOT a b ->
      inv h d b c.
    Proof.
      clear. induction h.
    Admitted.
    Opaque inv.

    Definition localCompute' : forall (min max : [LiftOrder key]) (optr : [option ptr]) (h : nat) 
      (p : ptr) (m : [ptree h]),
      STsep (min ~~ max ~~ m ~~ optr ~~
                rep' h p optr m * [inv h m min max] * [key_between min tK max] * P)
            (fun res : RES h => m ~~ min ~~ max ~~ optr ~~ opm :~~ projT2 (snd res) in
                repOp h (projT1 (snd res)) opm min max optr * Q (fst res) *
                [firstPtrOp _ _ opm = firstPtr _ m] *
                [Spec tK (as_map _ m) = (fst (Spec tK (as_map _ m)), as_mapOp _ (projT1 (snd res)) opm)]).
      refine (fix localCompute' min max optr h {struct h} : forall (p : ptr) (m : [ptree h]), _ :=
        match h as h return forall (p : ptr) (m : [ptree h]),
          STsep (min ~~ max ~~ m ~~ optr ~~
                   rep' h p optr m * [inv h m min max] * [key_between min tK max] * P)
                (fun res : RES h => m ~~ min ~~ max ~~ optr ~~ opm :~~ projT2 (snd res) in
                   repOp h (projT1 (snd res)) opm min max optr * Q (fst res) *
                   [firstPtrOp _ _ opm = firstPtr _ m] *
                   [Spec tK (as_map _ m) = (fst (Spec tK (as_map _ m)), as_mapOp _ (projT1 (snd res)) opm)])
          with
          | 0    => fun p m =>
            nde <- ! p ;
            {{ Fn p (content nde) (next nde) (m ~~~ snd m) min max <@> _ }}
          | S h' => fun p m => 
            nde' <- readBranch p optr m <@> _ ;
            let ary := fst nde' in
            let nxt := snd nde' in
            pfArySize <- shift (array_length ary = SIZE) <@> _ ;
            {{ Fix3 (fun (i : nat) (min' : [LiftOrder key]) (pfRange : i <= SIZE) =>
                      min ~~ max ~~ min' ~~ optr ~~ m ~~ 
                      let lsM  := fst (snd m) in 
                      let nxtM := snd (snd m) in
                      let nxtP := nxt in
                      p ~~> mkNode (S h') ary (Some nxt) *
                      [length lsM <= SIZE] * [inv (S h') m min max] * [i <= length lsM] *
                      [KLsorted min (firstn i lsM) min'] * [key_between min' tK max] *
                      [min' = lastKey (firstn i lsM) min] * 
                      (** TODO: key requirements **)
                      __ *
                      repBranch h' (rep' h') ary 0 SIZE lsM (firstPtr _ nxtM) *
(*                      repBranch h' (rep' h') ary i (SIZE - i) (skipn i lsM) (firstPtr _ nxtM) * *)
                      rep' h' nxtP optr nxtM * P)
                    (fun _ _ _ (res : RES (S h')) => m ~~ min ~~ max ~~ optr ~~ opm :~~ projT2 (snd res) in
                      repOp (S h') (projT1 (snd res)) opm min max optr * Q (fst res) *
                      [Spec tK (as_map _ m) = (fst (Spec tK (as_map _ m)), as_mapOp _ (projT1 (snd res)) opm)])
                    (fun self i min' pfRange =>
                     match le_lt_dec SIZE i with
                       | left pfLe =>
                         _
(*
                       rr <- localCompute' min' max optr h' nxt (m ~~~ snd (snd m)) <@> _ ;
                       {{ @mergeOpNext min min' max h' p ary optr SIZE rr m (eq_le SIZE) }}
*)
                       | right pfLt =>
                         okv <- sub_array ary i (fun v => m ~~ match nth_error (fst (snd m)) i with
                                                                 | None => [v = @None (key * ptr)] * [i >= length (fst (snd m))]
                                                                 | Some (existTS k' v') => [v = Some (k', ptrFor _ v')] * [i < length (fst (snd m))] * 
                                                                   rep' h' (ptrFor _ v') (repBranch_nextPtr (fst (snd m)) i (Some (firstPtr _ (snd (snd m))))) v'
                                                               end) <@> _ ;
                         let _:option (key * ptr) := okv in
                         match okv as okv' return okv = okv' -> _ with
                           | None => fun _ => _
(**
                             rr <- localCompute' min' max optr h' nxt (m ~~~ snd (snd m)) <@> _ ;
                             {{ @mergeOpNext min min' max h' p ary optr i rr m (lt_le pfLt) <@> _ }}
**)
                           | Some (k', p') => fun _ => _
(**
                             match OTcompare KOT k' tK with
                               | LT _ => _ (** {{ self (S i) [Val k']%inhabited (lt_S_le pfLt) }} **)
                               | (* EQ | GT *) _ => _
(*
                               rr <- localCompute' min' [Val k']%inhabited (m ~~~ match nth_error (fst (snd m)) (S i) with
                                                                                    | Some z => Some (firstPtr _ (projT2S z))
                                                                                    | None => Some (firstPtr _ (snd (snd m)))
                                                                                  end) h' p' (m ~~~ match nth_error (fst (snd m)) i with
                                                                                                      | None => snd (snd m) (** junk **)
                                                                                                      | Some m' => projT2S m'
                                                                                                    end) <@> _ ;
                                                                                                    {{ @mergeOpInternal min max h p cont ary nxt i rr m }}
*)
                             end
**)
                         end (refl_equal _)
                    end) 0 min (O_le SIZE) }}
        end); try clear self; try clear Fn.
    Proof.
      (** Leaf **)
      instantiate (1 := fun v => min ~~ max ~~ m ~~ optr ~~ [key_between min tK max] * [inv 0 m min max] *
        [height v = 0] * [next v = optr] * [p = ptrFor _ m] * [array_length (content v) = SIZE] *
        [length (snd m) <= SIZE] *
        repLeaf (content v) 0 SIZE (snd m) * P).
        solve [ sep fail auto ].
      solve [ sep fail auto ].
      Ltac combine_inh := idtac;
        repeat match goal with
                 | [ H : ?X = [_]%inhabited , H' : inhabit_unpack ?X _ = _ |- _ ] =>
                   rewrite H in H'; simpl in H'; try rewrite <- (pack_injective H') in *
               end.
      inhabiter. intro_pure. unpack_conc. canceler; auto. combine_inh.
      Transparent inv. unfold inv. canceler. Opaque inv. sep fail auto.
      sep fail auto. sep fail auto. rewrite H2. sep fail auto. solve [ cut_pure;  [ simpl; rewrite H6; auto | rewrite H5; auto ] ].
      (** Branch -- Shift Array Size **)
      solve [ sep fail auto; rewrite H2; sep fail auto ].
      solve [ t ].
      solve [ simpl; unfold ary; inhabiter; canceler; fold ary; t ].
      solve [ t ].
      refine (
        rr <- localCompute' min' max optr h' nxt (m ~~~ snd (snd m)) <@> 
            (min ~~ max ~~ min' ~~ optr ~~ m ~~ 
             let lsM := fst (snd m) in
             let nxtM := snd (snd m) in
             p ~~> mkNode (S h') ary (Some nxt) *
             [length lsM <= SIZE] * [inv (S h') m min max] * [i <= length lsM] *
             [key_between min' tK max] * [min' = lastKey (firstn i lsM) min] *
             [KLsorted min (firstn i lsM) min'] *
             repBranch h' (rep' h') ary 0 SIZE lsM
             (firstPtr _ match nth_error lsM i with
                           | Some x => projT2S x
                           | None => nxtM
                         end)) ;
        {{ @mergeOpNext min min' max h' p ary optr SIZE rr m (eq_le SIZE) <@> _ }}); try clear localCompute'.
      t. rewrite (pack_injective H4). rewrite nth_error_len; auto. canceler.

      Hint Resolve pack_injective.
      cut_pure. eapply inv_Next. eassumption. eauto. eauto. rewrite firstn_len_le in H5; eauto.
      solve [ t ].
      instantiate (1 := m ~~ min ~~ min' ~~ max ~~ opm :~~ projT2 (snd rr) in
        [inv (S h') m min max] * 
        [firstPtrOp _ _ opm = firstPtr _ (snd (snd m))] *
        [key_between min' tK max] * [min' = lastKey (firstn i (fst (snd m))) min] *
        [i <= length (fst (snd m))] * [length (fst (snd m)) <= SIZE] *
        [Spec tK (as_map _ (snd (snd m))) = (fst (Spec tK (as_map _ (snd (snd m)))),
          as_mapOp h' (projT1 (snd rr)) opm)]). Opaque as_map.
      t. t. 
      rewrite nth_error_len. destruct x0. destruct p1. simpl. rewrite H7. sep fail auto. fold ptree. Transparent inv. simpl in H0. destruct H0. Opaque inv.
      rewrite firstn_len_le; auto. simpl in *. cut_pure. auto. auto. simpl in *. combine_le_le. rewrite H4. auto. solve [ omega ].
    fold ptree in *.
    t. t. fold ptree in *. Opaque ptree. cut_pure. destruct x0. destruct p1. simpl in *.
    Lemma spec_combine : forall h' p0 l p1 v x4,
      Spec tK (as_map (S h') (p0, (l, p1))) =
      (fst (Spec tK (as_map (S h') (p0, (l, p1)))),
        as_mapOp (S h') v x4).
    Proof.
(**
    pose (@SpecLocal x3 (lastKey l x3) x2 x2 tK (as_map h' p1) 
      (flat_map
        (fun x0 : sigTS (fun _ : key => ptree h') => as_map h' (projT2S x0)) l) nil).
    norm list in e. Transparent as_map. simpl. Transparent ptree. fold ptree. rewrite e; clear e. simpl. f_equal. rewrite <- H6. f_equal. rewrite H3. simpl. auto.
**)
    Admitted.
    solve [ eapply spec_combine ].
(**
    norm list in e. Transparent as_map. simpl. Transparent ptree. fold ptree.
    rewrite e; clear e. 
    Focus 3. eapply inv_KLsorted.
    eauto.
    Focus 2. rewrite KLsorted_app. think.
**)
    (** Branch -- Reading okv **)
    inhabiter. simpl. intro_pure.
    search_prem ltac:(eapply (repBranch_read' pfLt)). simpl. inhabiter. unpack_conc.
    eapply himp_ex_conc. exists v. unpack_conc. canceler. Transparent ptree. fold ptree. canceler. Opaque ptree.
    solve [ sep fail auto ].
    solve [ t ].
    
    
    (** Branch -- Read None **)
    Focus 2.
    refine (
        rr <- localCompute' min' max optr h' nxt (m ~~~ snd (snd m)) <@> 
            (min ~~ max ~~ min' ~~ optr ~~ m ~~ 
             let lsM := fst (snd m) in
             let nxtM := snd (snd m) in
             p ~~> mkNode (S h') ary (Some nxt) *
             [length lsM <= SIZE] * [inv (S h') m min max] * [i <= length lsM] *
             [key_between min' tK max] * [min' = lastKey (firstn i lsM) min] *
             [KLsorted min (firstn i lsM) min'] *
             repBranch h' (rep' h') ary 0 SIZE lsM
             (firstPtr _ match nth_error lsM i with
                           | Some x => projT2S x
                           | None => nxtM
                         end)) ;
        {{ @mergeOpNext min min' max h' p ary optr i rr m pfRange <@> _ }}); try clear localCompute'.
    simpl. inhabiter. intro_pure. combine_inh. unpack_conc. rewrite H0. simpl. unpack_conc. canceler.
    Transparent ptree. fold ptree in *. canceler. fold ptree in *. Opaque ptree.
    

    
    Ltac tester := idtac "here";
      instantiate; simpl;
      match goal with 
        | [|- ?G ] => idtac G
      end;
      search_prem ltac:(readBranch); simpl; inhabiter.
    Check repBranchExcept.
    instantiate (1 := min ~~ max ~~ min' ~~ optr ~~ m ~~
      let lsM := fst (snd m) in
      let nxtM := snd (snd m) in
      let nxtP := nxt in
(*      p ~~> mkNode (S h') ary (Some nxt) * [length lsM <= SIZE] *
      [inv (S h') m min max] * [i <= length lsM] *
      [KLsorted min (firstn i lsM) min'] *
      [key_between min' tK max ] *
      [min' = lastKey (firstn i lsM) min] * *)
      repBranchExcept h' ary i lsM (firstPtr h' nxtM) *
      rep' h' nxtP optr nxtM * P).
      
      
=======
    eauto.
    eapply inv_KLsorted. 
    generalize (lastKey_flatten h' l x3). intros. destruct H12. eapply invWeaken; eauto. 
    eapply inv_subst; eauto.
    simpl. f_equal. rewrite <- H10. f_equal. rewrite H7. simpl. auto.
    rewrite firstn_len_le in H3; auto.
>>>>>>> other

<<<<<<< local
    sep ltac:(tester) auto. Transparent ptree. fold ptree in *. match goal with
    | [|- context [ match ?X with 
                      | Some _ => _ 
                      | None => _
                    end ] ] => destruct X
      end. destruct s. t.
    t.
     
    t.
=======
    (** Reading the array **)
    inhabiter. simpl. intro_pure. (** TODO : HERE **)
    t. t.
    solve [ t ].
    inhabiter. simpl. intro_pure. unfold ary in *. canceler. sep fail auto.
    solve [ t ].
>>>>>>> other

<<<<<<< local
    (** Branch -- Not full-Last **)
    Check mergeOpNext.
=======
    (** End of Array **)
>>>>>>> other
    refine (
<<<<<<< local
      rr <- localCompute' min' max optr h' nxt (m ~~~ snd (snd m)) <@> 
=======
        rr <- localCompute' min' max optr h' nxt (m ~~~ snd (snd m)) <@> 
>>>>>>> other
            (min ~~ max ~~ min' ~~ optr ~~ m ~~ 
             let lsM := fst (snd m) in
             let nxtM := snd (snd m) in
             p ~~> mkNode (S h') ary (Some nxt) *
             [length lsM <= SIZE] * [inv (S h') m min max] * [i <= length lsM] *
<<<<<<< local
             [min' = lastKey (firstn i lsM) min] *
=======
             [key_between min' tK max] * [min' = lastKey (firstn i lsM) min] *
>>>>>>> other
             [KLsorted min (firstn i lsM) min'] *
             repBranch h' (rep' h') ary 0 SIZE lsM
             (firstPtr _ match nth_error lsM i with
                           | Some x => projT2S x
                           | None => nxtM
                         end)) ;
<<<<<<< local
      {{ @mergeOpNext min min' max h' p ary optr i rr m (lt_le pfLt) <@> _ }}); try clear localCompute'.
=======
        {{ @mergeOpNext min min' max h' p ary optr SIZE rr m (eq_le SIZE) <@> _ }}).
     (** TODO : good to find a way to abstract this since it is the same code as before,
         except the inequality is flipped **)
    Opaque inv.
    t. rewrite (pack_injective H4). canceler.
    
>>>>>>> other

<<<<<<< local
    
    (** TODO: A bunch of junk to prove **)
=======

      Lemma KLsorted_app : forall (V:key->Set) b t max a min,
        KLsorted min (a ++ t :: b) max ->
        KLsorted min a (Val (projT1S t)) /\ @KLsorted V (Val (projT1S t)) b max.
      Proof.
        induction a. simpl. think. think.
      Qed.

>>>>>>> other
    


      Lemma inv_Next : forall h' pt a0 b0 x x2 x3 s n,
        inv (S h') pt x3 x2 ->
        KLsorted x3 a0 x ->
        length a0 <= S n ->
        nth_error a0 n = Some s ->
        Val (projT1S s) = x ->
        a0 = fst (snd pt) ->
        b0 = snd (snd pt) ->
        inv h' b0 x x2.
      Proof. clear.
        destruct pt. destruct y. revert p. revert p0. simpl in *. induction l; fold ptree in *.
          intros; subst. norm list in *; think.
          intros; subst. Transparent inv. Opaque ptree. simpl in H. destruct H.
            destruct n. simpl in H2. inversion H2. subst. destruct l; [|simpl in *; elimtype False; omega]. simpl in *. inversion H2. subst; auto.
            eapply IHl. instantiate (3 := p). Focus 3. assert (length l <= S n). simpl in H1; omega. eapply H4. Focus 3. eauto. simpl. split. unfold KLsorted in H. simpl in H. destruct H. eapply H4. destruct H0. instantiate (1 := p0). eapply H3.
            unfold KLsorted in *. simpl in H0. destruct H0. eapply H4. auto. auto. auto.
      Qed.
      

(**

      instantiate (1 := m ~~ optr ~~ min ~~ max ~~ min' ~~
        let lsM := fst (snd m) in
        let nxtM := snd (snd m) in
        let nxtP := ptrFor h' nxtM in
        match nth_error (fst (snd m)) i with
          | None   => repBranch h' (rep' h') ary 0 i lsM nxtM
          | Some v => repBranch h' (rep' h') ary 0 i lsM (projT2S v) * repBranch h' (rep' h') ary (S i) (SIZE - S i) (skipn (S i) lsM) nxtM
        end *
        [array_length ary = SIZE] * [length lsM <= SIZE] * [inv (S h') m min max] * [KLsorted min (firstn i lsM) min'] *
        [key_between min' tK max] * 
        rep' h' nxtP optr nxtM * P).
      Opaque inv. Opaque KLsorted.
      sep fail auto. norm pair. rewrite H in *.
      destruct (le_lt_dec (length a0) i).
        Lemma nth_error_len : forall i T (x:list T), 
          length x <= i -> nth_error x i = None.
        Proof.
          induction i; destruct x; simpl in *; think.
        Qed.
        Hint Resolve nth_error_len.
        rewrite nth_error_len; auto.
        Lemma skipn_len : forall (T:Type) i a0,
          length a0 <= i -> skipn i a0 = @nil T.
        Proof.
          induction i; destruct a0; simpl in *; think.
        Qed.
        Hint Rewrite skipn_len : btree.
        destruct (pack_type_inv (array_plus ary i)); rewrite H4. sep fail auto.
        autorewrite with btree; auto. case_eq (SIZE - i); intros. simpl.


      
      inhabiter. Opaque inv. Opaque KLsorted. simpl. intro_pure.
      case_eq (SIZE - i); intro. simpl repBranch. destruct x0. destruct y. simpl fst in *. simpl snd in *. assert (SIZE = i); try omega. rewrite H10 in *.

        rewrite nth_error_len; auto. rewrite H0.
        autorewrite with btree.


      case_eq (le_lt_dec SIZE i); intros.
      assert (SIZE = i); [think|]. rewrite H0. norm arith. simpl repBranch.

      inhabiter. Opaque inv. Opaque KLsorted. 
      unfold repBranch
      
      t. rewrite H in *.
      
      sep fail ltac:((progress norm arith) || (progress norm pair) || auto).
      sep fail auto.
**)
    Admitted.

(**
   Definition bpt_case_ex : forall (T : Type) (Q : T -> hprop) (P:hprop)
    (p:ptr) (m : [sigTS tree]) (cont : option ptr -> hprop),
    (forall (ary : array) (nxt : option ptr) (ls : [list (sigTS value)]),
     STsep (ls ~~ p ~~> mkNode 0 ary nxt * [array_length ary = SIZE] * [length ls <= SIZE] *
                  repLeaf ary 0 SIZE ls * cont nxt * P)
           (fun res:T => Q res)) ->
    (forall (h' : nat) (ary : array) (nxt : ptr) (m : [tree (S h')]),
     STsep (m ~~ Exists op :@ option ptr, p ~~> mkNode (S h') ary (Some nxt) * 
                 [array_length ary = SIZE] * [length (fst m) <= SIZE] *
                 repBranch h' (rep' h') ary 0 (fst m) op 
                  (fun op => Exists p' :@ ptr, nxt ~~> p' * rep' h' p' op cont (snd m)) * P)
           (fun res:T => Q res)) ->
    STsep (m ~~ Exists op :@ option ptr, rep' (projT1S m) p op cont (projT2S m) * P)
          (fun res:T => Q res).
**)


    (** TODO **)
  End Compute.

  (** TODO: these should go at the top **)
  Fixpoint InKey (k : key) (ls : list (sigTS value)) : Prop :=
    match ls with
      | nil => False
      | f :: r => OTeq KOT k (projT1S f) \/ InKey k r
    end.
  
  Definition KvEq (kv1 kv2 : sigTS value) : Prop.
    refine (fun kv1 kv2 =>
      match OTcompare KOT (projT1S kv1) (projT1S kv2) with
        | EQ pf => _
        | _ => False
      end).
    pose (value_eq _ _ pf).
    pose (projT2S kv2). rewrite <- e in v. refine (projT2S kv1 = v).
  Defined.

  Fixpoint InKeyVal (k : key) (v : value k) (ls : list (sigTS value)) : Prop :=
    match ls with
      | nil => False
      | f :: r => (KvEq (existTS value k v) f) \/ InKeyVal v r
    end.

  Lemma firstn_len_le : forall (n : nat) T (ls : list T), 
    length ls <= n -> firstn n ls = ls.
  Proof.
    clear. induction n; simpl; intros; destruct ls; think.
  Qed.

  Lemma gt_all_not_in : forall (k : key) (x1 : list (sigTS value)),
    (forall k' : key, InKey k' x1 -> OTlt KOT k' k) -> forall v : value k, InKeyVal v x1 -> False.
  Proof.
    clear. induction x1. intros. simpl in *; auto.
    intros. unfold KvEq in H0. simpl in H0. destruct H0; [|think].
    (** SEG FAULT **)
    destruct (OTcompare KOT k (projT1S a)). (* try solve [ simpl in *; eapply IHx1; eauto | simpl in *; think ]. *)
      unfold KvEq in H0. simpl in H0. destruct (OTcompare KOT k (projT1S a)). think. generalize o0. generalize o. clear. order. think.
      generalize (H k). simpl. intro. assert (OTlt KOT k k). auto. order.
      unfold KvEq in H0. simpl in H0. destruct (OTcompare KOT k (projT1S a)). think. generalize o0. generalize o. clear. order. think.
  Qed.

  Lemma KLsorted_gt : forall max ls min,
    KLsorted min ls max ->
    forall k, InKey k ls -> OTlt KLOT min (Val k).
  Proof.
    induction ls. think.
    think. (** order bug **)
    Lemma order_bug : forall x y y',
      x #?<? Val y -> OTeq KOT y' y -> x #?<? Val y'.
    Proof.
      simpl. intros. destruct x; simpl in *; order.
    Qed.
    eapply order_bug; eauto.
    unfold KLsorted in IHls. generalize (IHls _ H1 _ H0). order.
  Qed.
  Lemma nth_sorted : forall T i (ls:list T) t,
    nth_error ls i = Some t -> ls = (firstn i ls) ++ t :: (skipn (S i) ls).
  Proof.
    induction i. simpl. destruct ls; think. inversion H. auto.
    destruct ls. simpl. think.
    simpl. think.
  Qed.
  Lemma KLsorted_app : forall (V:key->Set) b t max a min,
    KLsorted min (a ++ t :: b) max ->
    KLsorted min a (Val (projT1S t)) /\ @KLsorted V (Val (projT1S t)) b max.
  Proof.
    induction a. simpl. think. think.
  Qed.


  Lemma xxxx : forall k kv x1 min max,
    KLsorted min x1 max ->
    forall i, 
      Some kv = nth_error x1 i ->
      OTlt KOT (projT1S kv) k ->
      InKey k (firstn (S i) x1) -> False.
  Proof.
    induction x1. think.
      
      intros. destruct a. 
      destruct H2.  simpl in *. destruct i. simpl in *. inversion H0. subst. simpl in *. order.
      simpl in H1. destruct H. fold sorted in H3. simpl in H3. unfold KLsorted in IHx1.
    Admitted. (** TODO: What is going on here?? **)

    Lemma nth_error_Some_len : forall T (t : T) i (ls : list T), 
      Some t = nth_error ls i -> 
      (Some t = nth_error ls i) /\ i < length ls.
    Proof.
      induction i; destruct ls; simpl; think.
    Qed.
    Hint Resolve nth_error_Some_len.
    Lemma nth_error_None_len : forall T i (ls : list T), 
      None = nth_error ls i -> length ls <= i.
    Proof.
      induction i; try solve [ destruct ls; simpl; think ].
      destruct ls. simpl. intros. omega. simpl. intro XX. generalize (IHi _ XX). think.
    Qed.
    Hint Resolve nth_error_None_len.

  Lemma nth_error_fix : forall a b,
    match nth_error a b with
      | Some x => Some x
      | None => None (A:=sigTS value)
    end = nth_error a b.
  Proof.
    intros; destruct (nth_error a b); think.
  Qed.
  Hint Resolve nth_error_fix.
  Lemma nth_error_skipn : forall T n s (ls : list T), 
    n >= s -> nth_error (skipn s ls) (n - s) = nth_error ls n.
  Proof.
    induction n. destruct s. simpl. intros. destruct ls; auto. intros. think.
    destruct ls. simpl. norm list. auto. intros. simpl. destruct s. simpl. auto. simpl. norm arith in *. eapply IHn. think.
  Qed.
  Lemma nth_error_skipnS : forall T n s (ls : list T), 
    n >= S s -> 
    nth_error
    match ls with
      | nil => nil
      | _ :: ls => skipn s ls
    end (n - S s) = nth_error ls n.
  Proof.
    intros. generalize (@nth_error_skipn _ n (S s) ls). simpl. intros. apply H0; think.
  Qed.

  Hint Rewrite firstn_len_le nth_error_skipnS : btree.
  Lemma InKeyVal_InKey : forall k (v:value k) x1,
    InKeyVal v x1 -> InKey k x1.
  Proof.
    induction x1. think. think. simpl. unfold KvEq in H. simpl in *.
    destruct (OTcompare KOT k (projT1S a)); think.
  Qed.
  Hint Resolve InKeyVal_InKey.


  Theorem himp_inj_conc' : forall h1 (P:Prop), h1 ==> __ -> P -> h1 ==> [P].
    intros. apply himp_empty_conc'. apply himp_inj_conc; auto.
  Qed. 

  Ltac cut_pure tac := 
    let rec handle solver := 
      try search_conc ltac:(idtac; 
        match goal with
          | [ |- _ ==> [?P] ] => eapply himp_inj_conc'
          | [ |- _ ==> [?P] * _ ] => eapply himp_inj_conc; [ | try handle solver ]
        end)
    in handle tac. 

  Lemma iter_sep_unroll_sep : forall P (a l s : nat) (f : nat -> hprop),
    S a <= l -> 0 < l ->
    {@ f i | i <- s + l} * P ==> {@ f i | i <- s + a} * f (s + a) * {@ f i | i <- (s + S a) + (l - S a)} * P.
  Proof.
    intros. canceler. eapply split_array_unroll; auto.
  Qed.
  
  Ltac unroll_at n := idtac;
    search_prem ltac:(idtac; match goal with 
                               | [ |- iter_sep _ _ _ * ?P ==> _ ] => eapply himp_trans; [ eapply (@iter_sep_unroll_sep P n); think | ]
                             end).

  Theorem himp_trans2 : forall Q R,
    Q ==> R -> forall P S, P ==> Q -> R ==> S -> P ==> S.
    intros. repeat (eapply himp_trans; try eauto).
  Qed.
  Lemma addsub_rw : forall a b,
    b < a -> 
    S (a - S b + b) = a.
    intros. omega.
  Qed.
  Hint Rewrite addsub_rw : btree.
  
(**
  match goal with
    | [ |- ?P ==> ?Q ] => idtac;
      match P with 
        | context L [ iter_sep ?F ?St ?E ] => let l' := context L [ __ ] in
          match l' with 
            | context H [ iter_sep ?F' (S E) ?E2 ] => 
              eapply himp_trans2; [ apply (@combine_array F E E2 St) | | ]; sep fail auto; norm arith;
                try solve [ match goal with
                              | [ |- context [ match ?X with | None => _ | Some _ => _ end ] ] => destruct X; think
                            end
                          | autorewrite with btree; ((apply iter_sep_inj; sep fail auto; norm arith; autorewrite with btree; sep fail auto; think) || think) ]
          end
      end
  end.
**)

  Ltac combine := idtac;
    match goal with
      | [ |- ?P ==> _ ] => 
        match P with 
          | context L [ iter_sep ?F ?St ?E ] => let l' := context L [ __ ] in
            match l' with 
              | context H [ iter_sep ?F' (S E) ?E2 ] => 
                eapply himp_trans2; [ apply (@combine_array F E E2 St) | | ]; sep fail auto; norm arith;
                  try solve [ match goal with
                              | [ |- context [ match ?X with | None => _ | Some _ => _ end ] ] => destruct X; think
                              end
                            | autorewrite with btree; ((apply iter_sep_inj; sep fail auto; norm arith; autorewrite with btree; sep fail auto; think) || think) ]
            end
        end
    end.

  Ltac simplr := 
    unfold repLeaf; simpl;
    match goal with 
      | [ |- ?P ==> ?Q ] =>
        match Q with 
          | context [ hprop_unpack (array_plus ?X ?I) _ ] => unroll_at I
        end 
    end.

  Ltac solver :=
    apply iter_sep_inj || auto.
  
  Ltac t :=
    unfold repLeaf; sep simplr solver; autorewrite with btree; cut_pure think; sep fail solver.

    Lemma nth_In : forall k' k v' i x1
      (pf : OTeq KOT k' k),
      Some (existTS value k' v') = nth_error x1 i ->
      InKeyVal
      match value_eq k' k pf in (_ = x3) return x3 with
        | refl_equal => v'
      end x1.
    Proof.
      clear. induction i. think. destruct x1. simpl in *. think. simpl in *. inversion H. left.
      unfold KvEq. simpl. destruct (OTcompare KOT k k'); try solve [ order ]. unfold eq_rec_r. unfold eq_rec. unfold eq_rect.
      clear. generalize dependent (value_eq k' k pf). generalize dependent (value_eq k k' o). clear. intro. generalize v'. generalize e. rewrite e. clear.
      intros. eqdep. auto.
      simpl. destruct x1. think. intros. simpl. right. eapply IHi. eauto.
    Qed.
    Hint Resolve nth_In.

    Lemma xxxxx : forall i x1 k k' v' min max,
      ~InKey k (firstn i x1) ->
      Some (existTS value k' v') = nth_error x1 i ->
      OTlt KOT k k' ->
      KLsorted min x1 max ->
      ~InKey k x1.
    Admitted. (** TODO **)
    Lemma xx : forall k (v : value k) x1,
      InKeyVal v x1 ->
      ~InKey k x1
      -> False.
    Proof.
    Admitted.
    Hint Resolve xx xxxxx.

    Lemma nth_error_None : forall T (ls:list T) i,
      None = nth_error ls i -> i >= length ls.
    Proof.
      induction ls; think. 
    Qed.
    Hint Resolve nth_error_None.
    Lemma firstn_len_ge : forall T (ls : list T) i, 
      i >= length ls -> firstn i ls = ls.
    Proof.
      induction ls. think. norm list. auto. simpl. destruct i. think. think. simpl. think.
    Qed.
    Hint Resolve firstn_len_ge.

    Theorem specLookupOnly : forall ls k (v : value k),
      InKeyVal v ls -> Some v = specLookup ls k.
    Proof.
      induction ls. think.
      simpl. intros. destruct H. unfold KvEq in H. simpl in *. destruct (OTcompare KOT k (projT1S a)); think.
      rewrite H. simpl. unfold eq_rec_r. unfold eq_rec, eq_rect. clear.
      generalize (projT2S a). generalize (sym_eq (value_eq k (projT1S a) o)). generalize (value_eq (projT1S a) k o0). generalize a. clear. intro. intro e.
    Admitted. (** TODO: Second-order unification **)
    Theorem specLookupAll : forall ls k, 
      (forall (v : value k), InKeyVal v ls -> False) -> None = specLookup ls k.
    Proof.
    

    Admitted. (** TODO: Work this out **)
    Hint Resolve specLookupAll specLookupOnly.

  Definition lookupFn : forall (k : key) (h : nat) (p : ptr) (ary : array) (nxt : option ptr) 
    (ls : [list (sigTS value)]) (min max : [LiftOrder key]) 
    (cont : option ptr -> hprop),
    STsep (ls ~~ min ~~ max ~~ 
             p ~~> mkNode 0 ary nxt * repLeaf ary 0 SIZE ls * cont nxt * [array_length ary = SIZE] * [inv 0 ls min max] * [length ls <= SIZE] * [key_between min k max])
          (fun r:(option (value k) * sigT (fun o:op => [opModel 0 o]%type)) =>
             ls ~~ min ~~ max ~~ hprop_unpack (projT2 (snd r)) (fun m => Exists nptr :@ option ptr, 
               repOp 0 (projT1 (snd r)) m min max nptr cont) * [fst r = specLookup (@as_map 0 ls) k]).
    refine (fun k h p ary nxt ls min max cont =>
      x <- Fix (fun (i:nat) => min ~~ max ~~ ls ~~ repLeaf ary 0 SIZE ls * [i <= length ls] * [i <= SIZE] * [length ls <= SIZE] *
                  [~InKey k (firstn i ls)] * [inv 0 ls min max])
               (fun _ (res:option (value k)) => ls ~~ min ~~ max ~~ 
                  repLeaf ary 0 SIZE ls * [inv 0 ls min max] * [length ls <= SIZE] *
                  [match res with
                     | None   => forall (v : value k), ~InKeyVal v ls
                     | Some v => InKeyVal v ls
                   end])
               (fun self i =>
                 if le_lt_dec SIZE i then
                   {{ Return None }}
                 else
                   okv <- sub_array ary i _ ;
                   match okv as okv' return okv = okv' -> _ with 
                     | None => fun _ => {{ Return None }}
                     | Some (existTS k' v') => fun _ => 
                       match OTcompare KOT k' k with
                         | LT _  => {{ self (S i) }}
                         | EQ pf => {{ Return (Some 
                           match value_eq _ _ pf in _ = x return x with
                             | refl_equal => v'
                           end) }}
                         | GT _ => {{ Return None }}
                       end
                   end (refl_equal _)) 0 <@> (cont nxt * [array_length ary = SIZE] * _) ;
      {{ Return (x, existT (fun o:op => [opModel 0 o]%type) (Merge p) ls) }}); try clear self.
    t.
    t. assert (i = SIZE); think. rewrite H5 in *. apply H2. autorewrite with btree; eauto.
    sep simplr auto.
    instantiate (1 := fun v => min ~~ max ~~ ls ~~ [v = nth_error ls i] * [i <= SIZE] * [length ls <= SIZE] *
            [~InKey k (firstn i ls)] * [inv 0 ls min max] *
            repLeaf ary 0 i ls * repLeaf ary (S i) (SIZE - S i) (skipn (S i) ls)).
    sep fail auto. unfold repLeaf. sep fail auto. apply iter_sep_inj.
    t. norm arith.  auto.

    solve [ t].
    (** sep idempotent BUG
        sep fail auto. sep fail auto.
     **)
    t.
    Transparent inv.
    eapply xxxx. unfold inv in *. eassumption. eassumption. eauto. eauto.
    apply nth_error_Some_len in H. think.

    combine.
    t.
    solve [ t ].
    t.
    eauto.
    
    combine.
    solve [ t ].
    t.
    (** TODO : it isn't in the first ones and it is greater than this one, so it can't be in the rest **)
    eauto.
    combine.
    solve [ t ].
    t. apply H3. autorewrite with btree; think. eauto.    
    combine.    
    t.
    t.
    t.
    t.
    destruct x; auto.
  Qed.

  Definition as_mapOp (h : nat) (o : op) (opm : opModel h o) : Model :=
    match o as o return opModel h o -> Model with
      | Merge _ => fun tr => @as_map h tr
      | Split _ _ _ => fun m => @as_map h (fst (fst m)) ++ @as_map h (snd m)
      | Combine _ => fun tr => @as_map h tr
      | _ => fun tr => nil
    end opm.

  Lemma sorted_min_max : forall (V:key->Set) (ls:list (sigTS V)) min max,
    KLsorted min ls max -> OTlt KLOT min max \/ OTeq KLOT min max.
  Proof.
    induction ls. think. intros. unfold KLsorted in *. simpl in *. destruct H. generalize (IHls (Val (projT1S a)) max). simpl. think. destruct max; destruct min; think. simpl in *. order. simpl in *. destruct max; destruct min; think; simpl in *; order.
  Qed.
  Hint Resolve sorted_min_max.

  Lemma delete_notin : forall ls k min max, 
    KLsorted min ls max -> OTlt KLOT max (Val k) -> ls = specDelete ls k.
  Proof.
    induction ls. think. think. simpl. destruct (OTcompare KOT (projT1S a) k); think. simpl in *.
    cut (OTlt KOT (projT1S a) k). order.
    generalize sorted_min_max. unfold KLsorted. intro. generalize (H2 _ _ _ _ H1).
    intro. destruct max; try solve [ think; order ]. simpl in *.
    generalize H0. generalize H. generalize o. generalize H3. clear. intros.
    elimtype False. destruct H3. order. order.
  Qed.
  Hint Resolve delete_notin.
  Lemma OTlt_unfold : forall a b,
    LO_lt KOT a b -> OTlt KLOT a b.
    auto.
  Qed.
  Hint Resolve OTlt_unfold. (** how to get coq to figure this one out? **)
  Ltac lele_eq := idtac;
    match goal with
      | [ H : ?X <= ?Y, H' : ?Y <= ?X |- _ ] => let F := fresh "H" in assert (F : X = Y); [ think | rewrite F in *; clear H; clear H' ]
    end. 

  Lemma specLookup_extend : forall ls i k min max,
    None = specLookup (firstn i ls) k ->
    KLsorted min (firstn i ls) max ->
    OTlt KLOT max (Val k) ->
    None = specLookup ls k.
  Proof.
  Admitted.

  Lemma specDelete_extend : forall ls i k min max,
    None = specLookup (firstn i ls) k ->
    KLsorted min (firstn i ls) max ->
    OTlt KLOT max (Val k) ->
    ls = specDelete ls k.
  Proof.
  Admitted.
  Hint Resolve specDelete_extend specLookup_extend.

  Lemma KLsorted_add : forall (V : key -> Set) (ls:list (sigTS V)) (i:nat) min max k,
    KLsorted min ls max ->
    nth_error ls i = Some k ->
    KLsorted min (firstn (S i) ls) (Val (projT1S k)).
  Proof.
  Admitted. (** TODO **)
  Hint Resolve KLsorted_add.
  Lemma specLookup_add : forall ls k i kv,
    None = specLookup (firstn i ls) k ->
    Some kv = nth_error ls i ->
    ~OTeq KOT (projT1S kv) k ->
    None = specLookup (firstn (S i) ls) k.
  Proof.
  Admitted. Hint Resolve specLookup_add.

  Fixpoint removeNth (T : Set) (n : nat) (ls : list T) {struct ls} : list T :=
    match n,ls with
      | _, nil => nil
      | 0, a :: b => b
      | S n, a :: b => a :: removeNth n b
    end.

  Lemma removeNth_len_decrease : forall (T : Set) (x:list T) rm,
    length (removeNth rm x) <= length x.
  Proof.
    induction x. destruct rm; think. destruct rm; simpl in *; think.
  Qed.
  Hint Resolve removeNth_len_decrease.
      
  Lemma nth_error_len : forall i T (x:list T), 
    length x <= i -> nth_error x i = None.
  Proof.
    induction i; destruct x; simpl in *; think.
  Qed.
  Hint Resolve nth_error_len.
  
  Lemma removeNth_length : forall (T : Set) (x:list T) rm i,
    rm < length x -> length x <= S i -> nth_error (removeNth rm x) i = None.
  Proof.
    intros. cut (length (removeNth rm x) <= i). think.
    generalize dependent rm. generalize dependent x. generalize dependent i. induction i.
    think. destruct x. simpl in *. think. simpl in *. destruct x; simpl in *; think. destruct rm. simpl. think. think.
    destruct x. simpl in *. think.
    simpl. intros. cut (length x <= S i); think. generalize (IHi _ H1). think. destruct rm. think. simpl in *. cut (rm < length x); think.
  Qed.
  Hint Resolve removeNth_length. 
  
  Lemma nth_error_removeNth_shift : forall (T:Set) (x:list T) i t0 rm, 
    rm <= i -> nth_error (removeNth rm (t0 :: x)) i = nth_error x i.
  Proof.
    induction x. simpl. destruct rm; think. destruct i; destruct rm; simpl; norm list; think. 
    simpl. destruct i; destruct rm; simpl; think.    
  Qed.
  Hint Rewrite nth_error_removeNth_shift : btree.

  Lemma iter_sep_after_XX : forall f l s P Q Q',
    P ==> f (s + l) * Q ->
    Q * iter_sep f s (S l) ==> Q' ->
    iter_sep f s l * P ==> Q'. 
  Proof.
    destruct l. simpl. intros. sep fail auto. eapply (@himp_trans _ P Q' H).  norm arith. 
    Check himp_trans. eapply (@himp_trans (Q * (f s * __))). sep fail auto. apply H0.
    sep fail auto. eapply (@himp_trans (Q * (f s * (f (S s) * iter_sep f (S (S s)) l)))); try assumption. sep fail auto.
    eapply (@himp_trans (iter_sep f (S s) l * f (s + S l) * Q)). sep fail auto. sep fail auto.
    clear. generalize s. clear. induction l. simpl. sep fail auto. norm arith. sep fail auto. sep fail auto.
    generalize (IHl (S s)). simpl. norm arith. assert (S (s + S l) = s + S (S l)). omega. rewrite H. auto.
  Qed.

  Ltac Guard t tac :=
    let A := fresh "ASSERT" in
    assert (A : t); [ solve [ tac ] | clear A ].
  
  Ltac split_array :=
    search_prem ltac:(idtac;
      match goal with
        | [ H : array_plus ?A ?I = [?PTR]%inhabited |- iter_sep _ _ _ * ?P ==> ?Q ] =>
          match P with 
            | context [ PTR ] => 
              match Q with
                | context [ PTR ] => fail 2
                | context [ array_plus A I ] => fail 2
                | context [ iter_sep ?F ?S ?L ] => idtac I S L; 
                  Guard (S <= I) omega; idtac "LLL"; Guard (I < S + L) omega; idtac "XXX"; eapply iter_sep_after_XX; [ unpack_conc; canceler | ]
              end
          end
      end).

    Lemma hint_match_none : forall (T:Set) x rm i,
      rm <= i ->
      None =
      match
        match x with
        | nil => error (A:=T)
        | _ :: l => nth_error l i
        end
      with
      | Some x => Some x
      | None => None (A:=T)
      end ->
      None =
      match nth_error (removeNth rm x) i with
        | Some x2 => Some x2
        | None => None (A:=T)
      end.
    Proof.
      destruct x. simpl. destruct rm; intros; norm list; think. intros; autorewrite with btree; think.
    Qed.
    Hint Resolve hint_match_none.
    Lemma hint_match_none_S : forall (T:Set) x rm i,
      rm <= i ->
      None =
      match
        match x with
        | nil => error (A:=T)
        | _ :: l => nth_error l i
        end
      with
      | Some x => Some x
      | None => None (A:=T)
      end ->
      None =
      match match removeNth rm x with
              | nil => error
              | _ :: l => nth_error l i 
            end
        with
        | Some x2 => Some x2
        | None => None (A:=T)
      end.
    Proof.
      induction x. simpl. destruct rm; auto. simpl. destruct rm. destruct x. auto. think. 
        destruct i; simpl in *; think. destruct i; think.
    Qed.
    Hint Resolve hint_match_none_S.

    Lemma sym_match : forall T a b,
      a = b ->
      match a with
        | Some x4 => Some x4
        | None => None (A:=T)
      end =
      match b with
        | Some x4 => Some x4
        | None => None (A:=T)
      end.
    Proof.
      intros; subst; auto.
    Qed.
    Lemma lmXXX : forall (T:Set) t (x:list T) x2 rm i len,
      None = match nth_error x i with
               | Some x => Some x 
               | None => None
             end ->
      x2 >= S (S i) ->
      x2 < S (S (i + (len - S (S i)))) ->
      nth_error (t :: x) x2 = nth_error (removeNth rm (t :: x)) x2.
    Proof.
      clear. intros. cut (nth_error (t :: x) x2 = None). intro. rewrite H2.
      cut (x2 >= length (t :: x)). intros. generalize (removeNth_len_decrease (t :: x) rm). think. cut (x2 >= length (removeNth rm (t :: x))). think.
      symmetry. auto. think. think.
      assert (nth_error x i = None). destruct (nth_error x i). think. think.
      generalize dependent x. generalize dependent t. generalize dependent i. generalize dependent x2. induction x2. think. think. destruct i. destruct x; think. destruct x. simpl; think.
      simpl. eapply IHx2. instantiate (1 := i). think. think. think. think.
    Qed. 
    Hint Resolve sym_match lmXXX.

    Lemma iter_sep_after_conc : forall l s x,
      s <= x -> x < s + l ->
      forall f P Q Q',
      P ==> f x * Q ->
      Q ==> iter_sep f s (x - s) * iter_sep f (S x) (l - S x) * Q' ->
      P ==> iter_sep f s l * Q'.
    Proof.
(*
      intros. eapply (@himp_trans (f' x * Q)); try assumption.
      eapply (@himp_trans (f' x * iter_sep f s (x - s) * iter_sep f (S x) (l - S x) * Q')).
      sep fail auto. eapply (@himp_trans (iter_sep f s (x - s) * iter_sep f (S x) (l - S x) * Q')); try assumption. sep fail auto.
      eapply (@himp_trans (f x * iter_sep f s (x - s) * iter_sep f (S x) (l - S x) * Q')). canceler. assumption.
      canceler. generalize H. generalize H0. clear. generalize s. generalize x. generalize l. clear.
      induction l. simpl. sep fail auto. think.
      intros. norm arith. destruct x. simpl. norm arith. assert (s = 0); think; subst. sep fail auto.
      cut (f (S x) * iter_sep f (S s) ((S x) - (S s)) * iter_sep f (S (S x)) (l - S (S x)) ==> iter_sep f (S s) l).
      simpl. sep fail auto. 
*)
    Admitted. (** TODO: check this **)
        
    Ltac pg := idtac;
      match goal with 
        | [ |- ?G ] => idtac G
      end.
    Lemma AAA : forall (T : Set) rm (x:list T) i len,
      length x <= len ->
      S i < len ->
      nth_error (removeNth rm x) (S i) = None.
    Proof.
  Admitted. 
  Lemma None_match : forall T (a:option T),
    a = None ->
    None = match a with 
             | Some x => Some x
             | None => None 
           end.
  Proof.
    think. subst; think.
  Qed.
  Hint Resolve None_match AAA.

  Lemma hint_1 : forall (T :Set) (x:list T) x2 rm i,
    x2 >= S (S i) ->
    None =
      match
        match x with
        | nil => error (A:=T)
        | _ :: l => nth_error l i
        end
      with
      | Some x => Some x
      | None => None (A:=T)
      end ->

    nth_error x x2 = nth_error (removeNth rm x) x2.
  Proof.
  Admitted.
  Hint Resolve hint_1. 

  Lemma iter_sep_after_conc_app : forall lP lQ s f f' P Q,
    lP > lQ ->
    (forall i, i >= s -> i < s + lQ -> f' i ==> f i) ->
    iter_sep f' (s + lQ) (lP - lQ) * P ==> Q ->
    iter_sep f' s lP * P ==> iter_sep f s lQ * Q.
  Proof.

  Admitted. (** TODO: check this **)
  Lemma removeNth_firstn : forall (T : Set) x i rm,
    i < rm ->    
    match nth_error x i with
      | Some x1 => Some x1
      | None => None (A:=T)
    end =
    match nth_error (removeNth rm x) i with
      | Some x1 => Some x1
      | None => None (A:=T)
    end.
  Proof.
  Admitted.
  Hint Resolve removeNth_firstn. 


  Definition removeNthArray : forall (T : Set) (ary : array) (rm len : nat) (ls : [list T]),
    STsep (ls ~~ {@ p :~~ array_plus ary i in p ~~> match nth_error ls i with 
                                                      | Some x => Some x
                                                      | None => None
                                                    end | i <- 0 + len} * [length ls <= len] * [rm < len])
          (fun _:unit => ls ~~ {@ p :~~ array_plus ary i in p ~~> match nth_error (removeNth rm ls) i with
                                                                    | Some x => Some x
                                                                    | None => None
                                                                  end | i <- 0 + len }).
    refine (fun T ary rm len ls =>
      {{ Fix (fun (i:nat) => ls ~~ [S i <= len] * [length ls <= len] * [rm <= i] * [rm < len] *
                {@ p :~~ array_plus ary i in p ~~> match nth_error (removeNth rm ls) i with 
                                                     | Some x => Some x
                                                     | None => None
                                                   end | i <- 0 + i } *
                {@ p :~~ array_plus ary i in p ~~> match nth_error ls i with 
                                                     | Some x => Some x
                                                     | None => None
                                                   end | i <- i + (len - i) })
             (fun i (_:unit) => ls ~~
               {@ p :~~ array_plus ary i in p ~~> match nth_error (removeNth rm ls) i with
                                                    | Some x => Some x
                                                    | None => None
                                                  end | i <- 0 + len })
             (fun self i => 
               if le_lt_dec len (S i) then
                 upd_array ary i (@None T) <@> _ ;;
                 {{ Return tt }}
               else
                 (** copy next into current **)
                 nxt <- sub_array ary (S i) (fun v => ls ~~ [v = match nth_error ls (S i) with
                                                                   | Some x => Some x
                                                                   | None => None 
                                                                 end] * _) ;
                 upd_array ary i nxt <@> _ ;;
                 match nxt as nxt' return nxt = nxt' -> _ with 
                   | None   => fun _ => {{ Return tt }}
                   | Some _ => fun _ => {{ self (S i) }}
                 end (refl_equal _)) rm }}); try clear self.
    instantiate (1 := ls ~~ 
      {@ p :~~ array_plus ary i0 in p ~~>
        match nth_error (removeNth rm ls) i0 with
          | Some x => Some x
          | None => None (A:=T)
        end | i0 <- (0) + i} * [S i <= len] * [rm <= i] * [rm < len] *
      {@ p :~~ array_plus ary i0 in p ~~> 
        match nth_error ls i0 with
          | Some x => Some x
          | None => None
        end | i0 <- (S i) + (len - S i)} * [length ls <= len]).
    sep fail auto. cut (len - i = S (len - S i)); [intro XXX; rewrite XXX; clear XXX|think]. simpl. solve [ sep fail auto ].
    solve [ t ].
    solve [ t ].
    t. lele_eq. norm arith. simpl.
    generalize (array_split_fb i 0 (fun i => p :~~ array_plus ary i in p ~~> match nth_error (removeNth rm x) i with
                                                                               | Some x => Some x
                                                                               | None => None
                                                                             end)). 
    intro. eapply (himp_trans2 H). clear H. norm arith.  sep fail auto. cut (nth_error (removeNth rm x) i = None). intro. rewrite H; auto.
    destruct (le_lt_dec (length x) rm).
      assert (i >= length x); think.
      generalize (removeNth_len_decrease x rm). think.
      think.
      solve [ sep fail auto ].
    (** Probably want to cut the above **)
    
    assert (len - i = S (S (len - S (S i)))); [ think | ]. rewrite H. Opaque nth_error. simpl.
    instantiate (1 := ls ~~ [S i <= len] * [length ls <= len] * [rm <= i] * [rm < len] *
      {@ p :~~ array_plus ary j in p ~~> match nth_error (removeNth rm ls) j with
                                           | Some x => Some x
                                           | None => None 
                                         end | j <- 0 + i} *
      (p :~~ array_plus ary i in p ~~> match nth_error ls i with
                                         | Some x => Some x
                                         | None => None
                                       end) *
      {@ p :~~ array_plus ary j in p ~~> match nth_error ls j with
                                           | Some x => Some x
                                           | None => None
                                         end | j <- (S (S i)) + (len - S (S i))}).
    sep fail auto. 
    solve [ t ].
    simpl.
    instantiate (1 := ls ~~ [S i <= len] * [length ls <= len] * [rm <= i] * [rm < len] *
      (p :~~ array_plus ary (S i) in p ~~> nxt) * [nxt = match nth_error ls (S i)  with
                                                           | Some x => Some x
                                                           | None => None
                                                         end] *
      {@ p :~~ array_plus ary j in p ~~> match nth_error (removeNth rm ls) j with
                                           | Some x => Some x
                                           | None => None
                                         end | j <- 0 + i} * 
      {@ p :~~ array_plus ary j in p ~~> match nth_error ls j with
                                           | Some x => Some x
                                           | None => None
                                         end | j <- (S (S i)) + (len - S (S i))}).
    solve [ sep fail auto ].
    sep fail auto.
    sep fail auto.
    assert (len - S i = S (len - S (S i))). think. rewrite H4. clear H4. simpl. sep fail auto.
    generalize (array_split_fb i 0 (fun j => p :~~ array_plus ary j in p ~~> match nth_error (removeNth rm x) j with
                                                                               | Some x => Some x
                                                                               | None => None
                                                                             end)).
    intro IM. eapply (himp_trans2 IM); clear IM. sep fail auto.
      rewrite H3. destruct x. simpl. destruct rm; norm list; think. 
    (** CUT THIS ??? **)
    autorewrite with btree; think.
    rewrite H6. sep fail auto.

    sep fail auto.
    solve [ sep fail auto ].
    t. (** holds b/c we're at the end of the list **)
    split_array. eauto. sep fail auto.


    try search_conc ltac:(idtac;
      match goal with
        | [ H : array_plus ?A ?I = [?PTR]%inhabited |- ?P ==> iter_sep ?F ?S ?L * ?Q ] =>
          match P with 
            | context [ PTR ] => 
              match Q with
                | context [ PTR ] => fail 2
                | context [ array_plus A I ] => fail 2
                | _ => idtac I S L; 
                  let F1 := fresh "F" in
                  let F2 := fresh "F" in
                  assert (F1 : S <= I); [ solve [ omega ] |
                  assert (F2 : I < S + L); [ solve [ omega ] | 
                    idtac "HERE"; pg; 
                  eapply (@iter_sep_after_conc L S I F1 F2) ] ] 
              end
          end
      end).
    unpack_conc. canceler; [ | solve [ eapply himp_refl ] ].
  eauto.
  sep fail auto. eapply iter_sep_inj. sep fail auto. eapply sym_match.
  
  eauto.

  (** holds because removeNth doesn't modify the first n elements of the list **)
  sep fail auto.

  try search_prem ltac:(idtac; 
    search_conc ltac:(eapply iter_sep_after_conc_app)).
  think. sep fail auto.

  eauto.
  sep fail auto.
  sep fail auto. 
  Qed.

  Definition coerceKV (k k' : key) (pf : OTeq KOT k k') (v : value k') : value k.
    clear. intros. generalize (value_eq _ _ pf). generalize v. clear. intros. rewrite H in *. apply v.
  Defined.

  Definition deleteFn : forall (k : key) (p : ptr) (ary : array) (nxt : option ptr)
    (ls : [list (sigTS value)]) (min max : [LiftOrder key]) 
    (cont : option ptr -> hprop),
    STsep (ls ~~ min ~~ max ~~ p ~~> mkNode 0 ary nxt * repLeaf ary 0 SIZE ls * cont nxt *
             [array_length ary = SIZE] * [inv 0 ls min max] * [length ls <= SIZE] * [key_between min k max])
          (fun r:(option (value k) * sigT (fun o:op => [opModel 0 o]%type)) =>
             ls ~~ min ~~ max ~~ hprop_unpack (projT2 (snd r)) (fun m => Exists nptr :@ option ptr, 
               repOp 0 (projT1 (snd r)) m min max nptr cont * 
               [fst r = specLookup (@as_map 0 ls) k] * [@as_mapOp 0 _ m = specDelete (@as_map 0 ls) k])).
    refine (fun k p ary nxt ls min max cont =>
      {{ Fix2 (fun (i:nat) (mx:[LiftOrder key]) => ls ~~ mx ~~ min ~~ max ~~
                 p ~~> mkNode 0 ary nxt * cont nxt *
                 [None = specLookup (firstn i ls) k] * [length ls <= SIZE] * [array_length ary = SIZE] *
                 [KLsorted min (firstn i ls) mx] * [KLsorted min ls max] * [i <= SIZE] * [mx #?< k] * repLeaf ary 0 SIZE ls)
              (fun i mx (ret : (option (value k) * sigT (fun o:op => [opModel 0 o]%type))) =>
                 ls ~~ min ~~ max ~~ hprop_unpack (projT2 (snd ret)) (fun m => Exists nptr :@ option ptr,
                   [fst ret = specLookup ls k] * [as_mapOp 0 (projT1 (snd ret)) m = specDelete ls k] * repOp 0 (projT1 (snd ret)) m min max nptr cont))
              (fun self i mx =>
                if le_lt_dec SIZE i then
                  (** didn't occur **)
                  {{ Return (None, existT _ (Merge p) ls) }}
                else
                  okv <- sub_array ary i _ ;
                  match okv as okv' return okv = okv' -> _ with
                    | None => fun pf => (** didn't occur **)
                      {{ Return (None, existT _ (Merge p) ls) }}
                    | Some (existTS k' v') => fun pf => 
                      match OTcompare KOT k k' with
                        | LT _ => (** didn't occur **)
                          {{ Return (None, existT _ (Merge p) ls) }}
                        | EQ pfKv => (** return Some v', 
                                   ** also need to remove this element and copy all
                                   ** of the rest back 1
                                   **)
                          removeNthArray ary i SIZE ls <@> _ ;;
                          {{ Return (Some (coerceKV _ pfKv v'), existT _ (Merge p) (ls ~~~ removeNth i ls)) }} (** maybe not merge **)
                        | GT _ => {{ self (S i) [Val k']%inhabited }}
                      end
                  end (refl_equal _)) 0 min <@> _ }}
      ); try clear self.
    t.
    t; lele_eq. rewrite firstn_len_le in *; think. solve [ rewrite <- H1 in *; rewrite firstn_len_le in *; think; eauto ].     
    simpl. instantiate (1 := fun v => ls ~~ min ~~ max ~~ mx ~~ [v = nth_error ls i] *
    cont nxt * p ~~> mkNode 0 ary nxt * [None = specLookup (firstn i ls) k] * [length ls <= SIZE] * [array_length ary = SIZE] * [KLsorted min (firstn i ls) mx] * [KLsorted min ls max] * [i <= SIZE] * [OTlt _ mx (Val k)] * _ v). sep fail auto. unfold repLeaf. unroll_at i. sep fail auto. norm arith. auto.

    instantiate (1 := fun v => ls ~~ {@hprop_unpack (array_plus ary i0)
       (fun p0 : ptr =>
        p0 ~~>
        match nth_error ls (i0 - 0) with
        | Some x4 => Some x4
        | None => None (A:=sigTS value)
        end) | i0 <- (0) + i} *
   {@hprop_unpack (array_plus ary i0)
       (fun p0 : ptr =>
        p0 ~~>
        match nth_error ls (i0 - 0) with
        | Some x4 => Some x4
        | None => None (A:=sigTS value)
        end) | i0 <- (S i) + array_length ary - S i}). sep fail auto.
    solve [ t ].
    solve [ t ].
    t. eauto. eauto.
    unfold repLeaf. combine.
    (** EQ **)
    simpl. instantiate (1 := ls ~~ min ~~ max ~~ mx ~~ 
      [okv = nth_error ls i] * [None = specLookup (firstn i ls) k] * [length ls <= SIZE] *
      [array_length ary = SIZE] * [KLsorted min (firstn i ls) mx] * [KLsorted min ls max] * [i <= SIZE] * [OTlt KLOT mx (Val k)] *
      cont nxt * p ~~> mkNode 0 ary nxt).
    t. combine.
    t.
    t.
    t.
    Lemma specLookup_found : forall k x3 i k' v' pfKv,
      Some (existTS value k' v') = nth_error x3 i ->
      None = specLookup (firstn i x3) k ->
      Some (coerceKV k pfKv v') = specLookup x3 k.
    Proof.
      induction x3. intros. norm list in *. think.
      induction i. simpl in *. intros. inversion H. simpl. destruct (key_eq_dec k' k); [ | elimtype False; order ].
      unfold coerceKV. unfold eq_rec_r. unfold eq_rec. unfold eq_rect. clear.
(*      generalize (value_eq k' k o). generalize (value_eq k k' pfKv). clear. intro e. generalize dependent (value k). generalize dependent (value k'). clear. intros P P0 e.   *)
      (** TODO : second-order unification **)
    Admitted.
    Hint Resolve specLookup_found. eauto.
    cut (length (removeNth i x2) <= length x2). think. think.

    Lemma KLsorted_remove : forall (V : key -> Set) max (ls:list (sigTS V)) i min,
      KLsorted min ls max -> KLsorted min (removeNth i ls) max.
    Proof.
      induction ls. destruct i; think.
      destruct i. simpl.
       intros. destruct H. fold sorted in H0. unfold KLsorted. think.
       Lemma sortedMin_weaken : forall max (V : key -> Set) (ls:list (sigTS V)) min min',
         OTlt KLOT min' min -> KLsorted min ls max -> KLsorted min' ls max.
       Proof. Opaque KLOT.
         induction ls. simpl. think. eauto. eapply sorted_nil_lt. order.
         simpl. intros. unfold KLsorted in *. simpl in *. think. order. 
       Qed.
       Hint Resolve sortedMin_weaken. generalize sortedMin_weaken. unfold KLsorted. eauto.
       simpl. intros. destruct H. fold sorted in H0. unfold KLsorted in IHls. generalize (IHls i _ H0). think.
     Qed.
     Hint Resolve KLsorted_remove. eauto.
     eauto.
     Lemma removeNth_specDelete : forall i ls k k' v',
       OTeq KOT k k' ->
       Some (existTS value k' v') = nth_error ls i ->
       None = specLookup (firstn i ls) k ->
       removeNth i ls = specDelete ls k.
     Proof.
     Admitted. (** TODO **)
     Hint Resolve removeNth_specDelete. eauto.
     unfold repLeaf. eapply iter_sep_inj. sep fail auto. 
    t.
    symmetry in H. generalize (KLsorted_add _ _ _ _ H4 H). simpl. auto.
    generalize (specLookup_add _ _ H0 H). auto.
    combine.
    solve [ t ].
    solve [ t ].
    t. eauto. eauto. Hint Unfold repLeaf. combine.
    t. Hint Unfold key_between. destruct H1. simpl in H1. auto.
    Hint Resolve sorted_nil.
    auto.
    t.
  Qed.

(**
    Lemma InKey_firstn : forall k ls n,
      InKey k (firstn (S n) ls) -> 
      InKey k (firstn n ls) \/ (exists kv, nth_error ls n = Some kv /\ OTeq KOT k (projT1S kv)).
    Proof.
      induction ls. think. 
      Lemma InKey_firstn_weaken : forall k ls n,
        InKey k (firstn n ls) -> InKey k (firstn (S n) ls).
      Proof.
        induction ls. think. norm list in *. auto. destruct n. simpl. think. think.
      Qed.
      destruct n. intros. destruct H; auto. right. exists a. simpl. unfold Specif.value. think.
      simpl in *. generalize (IHls n). think.
    Qed.
    Lemma nth_error_firstn : forall T i x (ls:list T),
      x < i -> nth_error ls x = nth_error (firstn i ls) x.
    Proof.
      induction i. intros; think. simpl. think. destruct ls. auto. destruct x. auto. simpl. eapply IHi. think.
    Qed.

    Lemma seqeach_lt : forall kv i ls max min,
      Some kv = nth_error ls i ->
      seqeach
         (fun (t : sigTS value) (v : LiftOrder key) =>
          (LO_lt KOT v (Val (projT1S t)), Val (projT1S t)))
         (fun v : LiftOrder key => LO_lt KOT v max) ls min ->
      forall k' : key, InKey k' (firstn i ls) -> OTlt KOT k' (projT1S kv).
    Proof.
      induction i. simpl. destruct ls; think.
      simpl. destruct ls. think. intros. simpl in H0.  destruct H0. eapply (IHi _ _ _ H H2).
      simpl in H1. destruct H1; auto.
    sep fail auto. sep fail auto. assert (forall k'0 : key, InKey k'0 (firstn (S i) x5) -> OTlt KOT k'0 k).
    intros. simpl in H4. destruct x5. simpl in H4. contradiction. simpl in H4. destruct H4. Focus 2.
    


    Lemma iter_sep_combine : forall 

      {@ f i 



    Lemma iter_sep_firstn : forall ary i s x1,
      {@hprop_unpack (array_plus ary i0)
        (fun p0 : ptr =>
          p0 ~~>
          match nth_error x1 i0 with
            | Some x2 => Some x2
            | None => None (A:=sigTS value)
          end) | i0 <- (s) + i} ==>
      {@hprop_unpack (array_plus ary i0)
        (fun p0 : ptr =>
          p0 ~~>
          match nth_error (firstn (i+s) x1) i0 with
            | Some x2 => Some x2
            | None => None (A:=sigTS value)
          end) | i0 <- (s) + i}.
    Proof.
      intros; eapply iter_sep_inj. intros. sep fail auto. rewrite <- nth_error_firstn. auto. omega.
    Qed.
    Lemma iter_sep_XX : forall ary i x1,
      {@hprop_unpack (array_plus ary i0)
        (fun p0 : ptr =>
          p0 ~~>
          match nth_error x1 i0 with
            | Some x2 => Some x2
            | None => None (A:=sigTS value)
          end) | i0 <- (S i) + SIZE - S i} ==>
      {@hprop_unpack (array_plus ary i0)
        (fun p0 : ptr =>
          p0 ~~>
          match nth_error (skipn (S i) x1) i0 with
            | Some x2 => Some x2
            | None => None (A:=sigTS value)
          end) | i0 <- (S i) + SIZE - S i}.
    Proof.
      intros. eapply iter_sep_inj. intros. sep fail auto.
      
      


      induction i. sep fail auto. 
        sep fail auto. destruct x1. norm list. norm list. sep fail auto. generalize (IHi (S s) nil). simpl. norm list. norm list. intro.
        Focus 2.
        sep fail auto. norm arith. simpl. clear. generalize (s0 :: x1). induction s. simpl. destruct l; think. 
          simpl. destruct l; think. eapply iter_sep_inj. sep fail auto. induction s. norm arith. simpl.
          induction s. simpl. auto. simpl.
          simpl. simpl in IHs.

eapply himp_trans. instantiate (1 := [i <= length x1] * 
    [i <= SIZE] * [length x1 <= SIZE] *
    [(forall k' : key, InKey k' (firstn i x1) -> OTlt KOT k' k)] *
    [inv 0 x1 x0 x] * _). canceler. eapply (split_array_unroll). instantiate (1 := i). omega. omega.
    sep fail auto.
**)
        
      
      
    
  

  Definition lookup (t : BptMap) (k : key) (m : [Model]) : 
    STsep (m ~~ rep t m)
          (fun res:option (value k) => m ~~ rep t m * [res = specLookup m k]).
  Proof.
    refine (fun t k m =>
      _
    ).
  Admitted.

  Definition insert (t : BptMap) (k : key) (v : value k) (m : [Model]) :
    STsep (m ~~ rep t m)
          (fun res:option (value k) => m ~~ rep t (specInsert m v) * [res = specLookup m k]).
  Admitted.

  Definition delete (t : BptMap) (k : key) (m : [Model]) :
    STsep (m ~~ rep t m)
          (fun res:option (value k) => m ~~ rep t (specDelete m k) * [res = specLookup m k]).
  Admitted.


  (** Specialized **)
  Definition iterate : forall (T : Type) (t : BptMap) 
    (I : T -> hprop)
    (fn : forall (k : key) (v:value k) (acc: T), STsep (I acc) (fun a:T => I a)) (acc : T)
    (m : [Model]), 
    STsep (m ~~ rep t m * I acc)
          (fun res:T => m ~~ rep t m * I res).
(*forall (T : Type) (t : BptMap) 
    (I : T -> hprop)
    (fn : forall k, value k -> T -> STsep (__) (fun a:T => __)) (acc : T)
    (m : [Model]), 
    STsep (m ~~ rep t m * I acc)
          (fun res:T => m ~~ rep t m * I res).
*)
  Proof.
    refine (fun T t I fn acc m => 
      _).
  Admitted.

  (** THE PRIZE **)
  (*
  Definition BptType : bpt_map := mkBpt new free lookup insert delete iterate.
  *)
End BPlusTreeImpl.
  
