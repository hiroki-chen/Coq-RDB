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

  Definition key_between (min : LiftOrder key) (k : key) (max : LiftOrder key) : Prop :=
    min #?< k /\ k #<? max.

  (** min < x[0] < x[2] < ... < x[n] <= max **)
  Fixpoint sorted (T : Type) C (ot : OrderedType C) (G : T -> C) (min : C) (ls : list T) (max : C) {struct ls} : Prop :=
    match ls with
      | nil => OTlt ot min max \/ OTeq ot min max
      | f :: r => OTlt ot min (G f) /\ sorted ot G (G f) r max
    end.

  Definition KLsorted (V : key -> Set) min ls max :=
    @sorted (sigTS V) (LiftOrder key) KLOT (fun v => Val (projT1S v)) min ls max.
  (** Sorted Properties **)
  (*forall T n ls min max kv
    @KLsorted V min ls max ->
    nth_error ls i = Some kv ->
    (forall kv'
*)

(**
  Fixpoint seqeach (T:Type) (V:Type) (f : T -> V -> (Prop * V)) (b : V -> Prop) (ls : list T) (v:V) : Prop :=
    match ls with
      | nil => b v
      | x :: y =>
        let (p,q) := f x v in
        p /\ seqeach f b y q
    end.
**)
  Inductive contextual (T : Type) C (P : C -> T -> C -> Prop) (G : T -> C) (B : C -> C -> Prop) : C -> list T -> C -> Prop :=
  | ContextualNil    : forall min max, B min max -> contextual P G B min nil max
  | ContextualSingle : forall min max f, P min f max -> contextual P G B min (f :: nil) max
  | ContextualCons   : forall min max a b r, P min a (G b) -> contextual P G B (G a) (b :: r) max.


  Fixpoint inv (n : nat) : tree n -> LiftOrder key -> LiftOrder key -> Prop :=
    match n as n return tree n -> LiftOrder key -> LiftOrder key -> Prop with
      | 0 => fun m min max =>
        KLsorted min m max
(**
        seqeach (fun (t:sigTS value) (v:LiftOrder key) => 
                     (v #?< (projT1S t), Val (projT1S t)))
                (fun v => v #< max) m min
**)
      | S n => fun m min max =>
        KLsorted min (fst m) max /\
        contextual (fun l c r => inv n (projT2S c) l r) (fun v => Val (projT1S v)) (fun min max => inv n (snd m) min max) min (fst m) max
        
(**
        let (ls,nxt) := m in
        seqeach (fun (t:sigTS (fun _:key => tree n)) (v:LiftOrder key) => 
                     (v #?< (projT1S t) /\ inv _ (projT2S t) v (Val (projT1S t)), Val (projT1S t)))
                (fun v => inv _ nxt v max /\ v #< max) ls min
**)
    end.

  (** Logical Representation **)
  Definition Model := list (sigTS value).

  Fixpoint as_map (n : nat) {struct n} : tree n -> Model :=
    match n as n return tree n -> list (sigTS value) with 
      | 0 => fun ls => ls
      | S n' => fun n =>
        let (ls,nxt) := n in
        List.flat_map (fun x => @as_map n' (projT2S x)) ls ++ as_map n' nxt
    end.


  (** Physical Representation **)
  Open Local Scope hprop_scope.

  (** * Node representation **)
  Record nodeType : Set := mkNode {
    height  : nat;
    content : array;
    next    : option ptr
  }.

  (** we iterate from left to right
   **   op is the option pointer to the next child
   **)
  Definition repLeaf (T : Set) (ary : array) (s l : nat) (ls : list T) : hprop :=
    {@ (p :~~ array_plus ary i in p ~~> match nth_error ls (i - s) with
                                          | None => @None T
                                          | Some x => Some x
                                        end) | i <- s + l }.

  Fixpoint repBranch (h : nat) (rep' : ptr -> option ptr -> (option ptr -> hprop) -> tree h -> hprop) 
    (ary : array) (i : nat) (ls : list (sigTS (fun _:key => tree h)))
    (op : option ptr) (c : option ptr-> hprop) {struct ls} : hprop :=
    match ls with
      | nil => {@ (p :~~ array_plus ary i in p ~~> @None (key * ptr)) | i <- i + (SIZE - i)} * c op
      | f :: r => 
        p :~~ array_plus ary i in Exists p' :@ ptr, p ~~> (Some (projT1S f, p')) *
        rep' p' op (fun op => repBranch h rep' ary (S i) r op c) (projT2S f)
    end.

  Fixpoint rep' (n : nat) (p : ptr) (op : option ptr) (c : option ptr -> hprop) {struct n} : tree n -> hprop :=
    fun t =>
      Exists a :@ nodeType, p ~~> a * [height a = n] *
      match n as n return tree n -> hprop with 
        | 0 => fun ls =>
          [array_length (content a) = SIZE] * [op = Some p] * [length ls <= SIZE] *
          repLeaf (content a) 0 SIZE ls * (c (next a))
        
        | S n' => fun m =>
          let ls  := fst m in
          let nxt := snd m in
          [array_length (content a) = SIZE] * [length ls <= SIZE] *
          Exists np :@ ptr, [next a = Some np] *
          repBranch n' (rep' n') (content a) 0 ls op (fun op => Exists p' :@ ptr, np ~~> p' * rep' n' p' op c nxt)
      end t.

  (** (height, tree) pairs **)
  Definition tH := sigTS tree.
  Definition BptMap := (ptr * [tH])%type.

  Definition rep (t : BptMap) (m : Model) : hprop :=
    let p := fst t in
    bpt :~~ snd t in
    match bpt with
      | existTS h t => Exists hdl :@ ptr,
        [m = as_map h t] *
        rep' h p (Some hdl) (fun x:option ptr => [x = None]) t * [inv h t MinK MaxK]
    end.

  (** Specifications **)
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

  Definition checkLeaf : forall (h : nat) (m : [sigTS tree]), [h]%inhabited = (m ~~~ projT1S m) -> h = 0 -> [list (sigTS value)].
  refine (fun h m pf1 pf2 =>
    match m as m' return m = m' -> _ with
      | inhabits x => fun pf => [ _ ]%inhabited
    end (refl_equal _)).
    subst; simpl in *. destruct x. generalize t. simpl in pf1. rewrite <- (pack_injective pf1). auto.
  Defined.

  Definition checkBranch (h h' : nat) (m : [sigTS tree]) :
    [h]%inhabited = (m ~~~ projT1S m) -> h = S h' -> [tree (S h')].
    refine (fun h h' m pf1 pf2 =>
      match m as m' return m = m' -> _ with
        | inhabits x => fun pf => [ _ ]%inhabited
      end (refl_equal _)).
    case_eq x. intros. rewrite pf in pf1. rewrite H in pf1. simpl in pf1. rewrite pf2 in pf1.
    generalize dependent t. rewrite <- (pack_injective pf1) in *. intros.
    apply t.
  Defined.
(*
  Definition bpt_case : forall (T : Type) (Q : T -> hprop) (P:hprop)
    (p:ptr) (m : [sigTS tree]) (cont : option ptr -> hprop) (op : option ptr),
    (forall (ary : array) (nxt : option ptr) (ls : [list (sigTS value)]),
     STsep (ls ~~ p ~~> mkNode 0 ary nxt * [array_length ary = SIZE] * [length ls <= SIZE] *
                  repLeaf ary 0 ls * cont nxt * P)
           (fun res:T => Q res)) ->
    (forall (h' : nat) (ary : array) (nxt : ptr) (m : [tree (S h')]),
     STsep (m ~~ p ~~> mkNode (S h') ary (Some nxt) * [array_length ary = SIZE] * [length (fst m) <= SIZE] * 
                 repBranch h' (rep' h') ary 0 (fst m) op 
                   (fun op => Exists p' :@ ptr, nxt ~~> p' * rep' h' p' op cont (snd m)) * P)
           (fun res:T => Q res)) ->
    STsep (m ~~ rep' (projT1S m) p op cont (projT2S m) * P)
          (fun res:T => Q res).
  refine (fun T Q P p m cont op CLeaf CBranch => 
    nde <- ! p ;
    pfCorrespond <- shift ([height nde]%inhabited = (m ~~~ projT1S m)) <@> _ ;
    match height nde as h 
      return height nde = h ->
        STsep (m ~~ [height nde = projT1S m] * p ~~> nde *
               match m with 
                 | existTS 0 ls => 
                   [height nde = 0] * [array_length (content nde) = SIZE] * [op = Some p] * [length ls <= SIZE] *
                   repLeaf (content nde) 0 ls * (cont (next nde))
                   
                 | existTS (S n') m =>
                   let ls  := fst m in
                   let nxt := snd m in
                   [height nde = S n'] * [array_length (content nde) = SIZE] * [length ls <= SIZE] *
                   Exists np :@ ptr, [next nde = Some np] *
                   repBranch n' (rep' n') (content nde) 0 ls op 
                     (fun op => Exists p' :@ ptr, np ~~> p' * rep' n' p' op cont nxt)
               end * P)
        (fun res:T => Q res)
      with
      | 0 => fun pf =>
        {{ CLeaf (content nde) (next nde) _ }}
      | S h' => fun pf =>
        match next nde as nn return next nde = nn -> _ with
          | None => fun _ => {{ !!! }}
          | Some nn => fun pfNxt => 
            {{ CBranch h' (content nde) nn _ }}
        end (refl_equal _)
    end (refl_equal _)); try clear CLeaf CBranch.
  Proof.
  instantiate (1 := (fun v:nodeType => m ~~
    [height v = projT1S m]*
    match m with 
      | existTS 0 ls => 
        [height v = 0] * [array_length (content v) = SIZE] * [op = Some p] * [length ls <= SIZE] *
        repLeaf (content v) 0 ls * (cont (next v))

      | existTS (S n') m =>
        let ls  := fst m in
        let nxt := snd m in
        [height v = S n'] * [array_length (content v) = SIZE] * [length ls <= SIZE] *
        Exists np :@ ptr, [next v = Some np] *
        repBranch n' (rep' n') (content v) 0 ls op 
        (fun op => Exists p' :@ ptr, np ~~> p' * rep' n' p' op cont nxt)
    end * P)).
  solve [ unfold rep'; inhabiter; destruct x; destruct x; 
            [ simpl; sep fail auto
            | fold rep'; simpl; sep fail auto ] ].
  sep fail auto.
  simpl. instantiate (1 := p ~~> nde *
   hprop_unpack m
     (fun m0 : sigTS tree =>
      [height nde = projT1S m0] *
      match m0 with
      | existTS x m1 =>
          match x as x0 return (tree x0 -> hprop) with
          | 0 => fun m2 =>
              [height nde = 0] * [array_length (content nde) = SIZE] *
              [op = Some p] * [length m2 <= SIZE] *
              repLeaf (content nde) 0 m2 * cont (next nde)
          | S n' => fun m2 =>
              [height nde = S n'] * [array_length (content nde) = SIZE] * [length (fst m2) <= SIZE] *
              (Exists np :@ ptr,
               [next nde = Some np] *
               repBranch n' (rep' n') (content nde) 0 (fst m2) op
               (fun op0 : option ptr =>
                 Exists p' :@ ptr, np ~~> p' * rep' n' p' op0 cont (snd m2)))
          end m1
      end * P)).
  sep fail auto.
  sep fail auto.


  instantiate (1 := @checkLeaf (height nde) m pfCorrespond pf).
  sep fail auto.
    solve [ destruct nde; simpl in *; subst; auto ].
    destruct x. destruct x.
    unfold eq_rec_r. unfold eq_rec. unfold eq_rect.
    generalize (sym_eq (refl_equal [existTS tree 0 t]%inhabited)). intro e. rewrite (UIP_refl _ _ e). clear e.
    generalize (sym_eq pf). intro e. generalize e. generalize dependent H. generalize dependent pf. generalize dependent pfCorrespond. rewrite <- e. clear e. intros. rewrite (UIP_refl _ _ e).
    eqdep. sep fail auto.
    sep fail auto. congruence.
  solve [ sep fail auto ].

  instantiate (1 := @checkBranch (height nde) h' m pfCorrespond pf).
  simpl. sep fail auto.
    solve [ rewrite <- pf; rewrite <- pfNxt; destruct nde; simpl; auto ].
    destruct x. simpl in H. generalize dependent pfCorrespond. generalize dependent t. rewrite pf in H. rewrite <- H.
      simpl. sep fail auto. unfold eq_rec. unfold eq_rect.
      generalize (pack_injective
             (eq_ind (height nde)
                (fun h : nat => [h]%inhabited = [S h']%inhabited)
                pfCorrespond (S h') pf)). intro. rewrite (UIP_refl _ _ e). simpl. sep fail auto.
      rewrite H in pfNxt. inversion pfNxt. sep fail auto.
  solve [ sep fail auto ].
  sep fail auto. destruct x.
  destruct x. simpl in *. congruence.
  simpl in *. sep fail auto. congruence.
  sep fail auto.
  Qed.
**)

  Definition bpt_case_ex_h : forall (h : nat) (T : nat -> Type) (Q : forall h, T h -> hprop) (P:hprop)
    (p:ptr) (m : [tree h]) (cont : option ptr -> hprop),
    (forall (ary : array) (nxt : option ptr) (ls : [list (sigTS value)]),
     STsep (ls ~~ p ~~> mkNode 0 ary nxt * [array_length ary = SIZE] * [length ls <= SIZE] *
                  repLeaf ary 0 SIZE ls * cont nxt * P)
           (fun res:T 0 => Q 0 res)) ->
    (forall (h' : nat) (ary : array) (nxt : ptr) (m : [tree (S h')]),
     STsep (m ~~ Exists op :@ option ptr, p ~~> mkNode (S h') ary (Some nxt) * 
                 [array_length ary = SIZE] * [length (fst m) <= SIZE] *
                 repBranch h' (rep' h') ary 0 (fst m) op 
                  (fun op => Exists p' :@ ptr, nxt ~~> p' * rep' h' p' op cont (snd m)) * P)
           (fun res:T (S h') => Q (S h') res)) ->
    STsep (m ~~ Exists op :@ option ptr, rep' h p op cont m * P)
          (fun res:T h => Q h res).
  refine (fun h T Q P p m cont CLeaf CBranch => 
    match h as h return forall (m : [tree h]),
      STsep (m ~~ Exists op :@ option ptr, rep' h p op cont m * P)
            (fun res:T h => Q h res) 
      with
      | 0    => fun m => 
        nde <- ! p ;
        {{ CLeaf (content nde) (next nde) m }}
      | S h' => fun m =>
        nde <- ! p ;
        match next nde as p return next nde = p -> _ with
          | None => fun _ => {{ !!! }}
          | Some p => fun pf => 
            {{ CBranch h' (content nde) p m }}
        end (refl_equal _)
    end m).
  simpl. sep fail auto. 
  sep fail auto.
  sep fail auto. destruct v0. simpl in *. rewrite H; auto.
  sep fail auto.
  simpl.
  instantiate (1 := fun a => hprop_unpack m0
    (fun m1 : list (sigTS (fun _ : key => tree h')) * tree h' =>
      Exists op :@ option ptr,
       [height a = S h'] *
       ([array_length (content a) = SIZE] * [length (fst m1) <= SIZE] *
        (Exists np :@ ptr,
         [next a = Some np] *
         repBranch h' (rep' h') (content a) 0 (fst m1) op
           (fun op0 : option ptr =>
            Exists p' :@ ptr, np ~~> p' * rep' h' p' op0 cont (snd m1))))) *
      P).
  sep fail auto.
  sep fail auto.
  sep fail auto. destruct nde. simpl in *. think. instantiate (1 := v). cut (p0 = v0). intros. rewrite H5. sep fail auto. think.
  sep fail auto.
  sep fail auto. think.
  sep fail auto.
  Qed.

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
  refine (fun T Q P p m cont CLeaf CBranch => 
    nde <- ! p ;
    pfCorrespond <- shift ([height nde]%inhabited = (m ~~~ projT1S m)) <@> _ ;
    match height nde as h 
      return height nde = h ->
        STsep (m ~~ Exists op :@ option ptr, [height nde = projT1S m] * p ~~> nde *
               match m with 
                 | existTS 0 ls => 
                   [height nde = 0] * [array_length (content nde) = SIZE] * [op = Some p] * [length ls <= SIZE] *
                   repLeaf (content nde) 0 SIZE ls * (cont (next nde))
                   
                 | existTS (S n') m =>
                   let ls  := fst m in
                   let nxt := snd m in
                   [height nde = S n'] * [array_length (content nde) = SIZE] * [length ls <= SIZE] *
                   Exists np :@ ptr, [next nde = Some np] *
                   repBranch n' (rep' n') (content nde) 0 ls op 
                     (fun op => Exists p' :@ ptr, np ~~> p' * rep' n' p' op cont nxt)
               end * P)
        (fun res:T => Q res)
      with
      | 0 => fun pf =>
        {{ CLeaf (content nde) (next nde) _ }}
      | S h' => fun pf =>
        match next nde as nn return next nde = nn -> _ with
          | None => fun _ => {{ !!! }}
          | Some nn => fun pfNxt => 
            {{ CBranch h' (content nde) nn _ }}
        end (refl_equal _)
    end (refl_equal _)); try clear CLeaf CBranch.
  Proof.
  instantiate (1 := (fun v:nodeType => m ~~ Exists op :@ option ptr, 
    [height v = projT1S m]*
    match m with 
      | existTS 0 ls => 
        [height v = 0] * [array_length (content v) = SIZE] * [op = Some p] * [length ls <= SIZE] *
        repLeaf (content v) 0 SIZE ls * (cont (next v))

      | existTS (S n') m =>
        let ls  := fst m in
        let nxt := snd m in
        [height v = S n'] * [array_length (content v) = SIZE] * [length ls <= SIZE] *
        Exists np :@ ptr, [next v = Some np] *
        repBranch n' (rep' n') (content v) 0 ls op 
          (fun op => Exists p' :@ ptr, np ~~> p' * rep' n' p' op cont nxt)
    end * P)).
  solve [ unfold rep'; inhabiter; destruct x; destruct x; 
            [ simpl; sep fail auto
            | fold rep'; simpl; sep fail auto ] ].
  sep fail auto.
  simpl. instantiate (1 := p ~~> nde *
  Exists op :@ option ptr, 
   hprop_unpack m
     (fun m0 : sigTS tree =>
      [height nde = projT1S m0] *
      match m0 with
      | existTS x m1 =>
          match x as x0 return (tree x0 -> hprop) with
          | 0 => fun m2 =>
              [height nde = 0] * [array_length (content nde) = SIZE] * 
              [op = Some p] * [length m2 <= SIZE] *
              repLeaf (content nde) 0 SIZE m2 * cont (next nde)
          | S n' => fun m2 =>
              [height nde = S n'] * [array_length (content nde) = SIZE] * [length (fst m2) <= SIZE] *
              (Exists np :@ ptr,
               [next nde = Some np] *
               repBranch n' (rep' n') (content nde) 0 (fst m2) op
                 (fun op0 : option ptr =>
                  Exists p' :@ ptr, np ~~> p' * rep' n' p' op0 cont (snd m2)))
          end m1
      end * P)).
  sep fail auto.
  sep fail auto.
  instantiate (1 := @checkLeaf (height nde) m pfCorrespond pf).
  sep fail auto.
    solve [ destruct nde; simpl in *; subst; auto ].
    destruct x. destruct x.
    unfold eq_rec_r. unfold eq_rec. unfold eq_rect.
    generalize (sym_eq (refl_equal [existTS tree 0 t]%inhabited)). intro e. rewrite (UIP_refl _ _ e). clear e.
    generalize (sym_eq pf). intro e. generalize e. generalize dependent H. generalize dependent pf. generalize dependent pfCorrespond. rewrite <- e. clear e. intros. rewrite (UIP_refl _ _ e).
    eqdep. sep fail auto.
    sep fail auto. congruence.
  solve [ sep fail auto ].
  instantiate (1 := @checkBranch (height nde) h' m pfCorrespond pf).
  simpl. sep fail auto.
    solve [ rewrite <- pf; rewrite <- pfNxt; destruct nde; simpl; auto ].
    destruct x. simpl in H. generalize dependent pfCorrespond. generalize dependent t. rewrite pf in H. rewrite <- H.
      simpl. sep fail auto. unfold eq_rec. unfold eq_rect.
      generalize (pack_injective
             (eq_ind (height nde)
                (fun h : nat => [h]%inhabited = [S h']%inhabited)
                pfCorrespond (S h') pf)). intro. rewrite (UIP_refl _ _ e). simpl. sep fail auto.
      rewrite H in pfNxt. inversion pfNxt. sep fail auto.
  sep fail auto.
  sep fail auto. destruct x.
  destruct x. simpl in *. congruence.
  simpl in *. sep fail auto. congruence.
  sep fail auto.
  Qed.

  Lemma iter_sep_inj : forall l s (f g : nat -> hprop), 
    (forall x, x >= s -> x < s + l -> f x ==> g x) ->
    {@ f i | i <- s + l} ==> {@ g i | i <- s + l}.
  Proof.
    induction l. sep fail auto.
      sep fail auto. eapply himp_split. sep fail auto. sep fail auto.
  Qed.

  Lemma rep'_inj : forall a c d e b f, 
    (forall x, d x ==> e x) -> rep' a b c d f ==> rep' a b c e f.
  Proof.
    induction a. simpl. sep fail auto.
    intros. unfold rep'. fold rep'. 
    sep fail auto. instantiate (1 := v0). unfold repBranch. sep fail auto.
    generalize 0. generalize c. generalize a0. induction a1; sep fail auto.
  Qed.

  Lemma repBranch_inj : forall a d b c e f g,
    (forall x, f x ==> g x) ->
    repBranch a (rep' a) b c d e f ==> repBranch a (rep' a) b c d e g.
  Proof.
    clear. induction d. sep fail auto.
    sep fail auto. sep fail auto. eapply rep'_inj. unfold repBranch. sep fail auto.
  Qed.

  Hint Resolve iter_sep_inj rep'_inj repBranch_inj.

  Lemma split_array : forall (l a s : nat) (f : nat -> hprop),
    a <= l ->
    {@ f i | i <- s + l} ==> {@ f i | i <- s + a} * {@ f i | i <- (s + a) + (l - a)}.
  Proof.
    induction l. 
      simpl. intros. assert (a = 0); [omega|]. subst. sep fail auto.
      induction a. simpl.
        sep fail auto. assert (s + 0 = s). omega. rewrite H0. sep fail auto.
        simpl. intros. canceler. assert (s + S a = S s + a). omega. rewrite H0. generalize (IHl a (S s) f). sep fail auto.
  Qed.

  Lemma split_array_unroll : forall (l a s : nat) (f : nat -> hprop),
    S a <= l -> 0 < l ->
    {@ f i | i <- s + l} ==> {@ f i | i <- s + a} * f (s + a) * {@ f i | i <- (s + S a) + (l - S a)}.
  Proof.
    intros. eapply himp_trans. eapply (@split_array l a s f). omega. canceler.
    eapply himp_trans. eapply (@split_array (l - a) 1 (s + a)). omega. simpl. sep fail auto.
    norm arith. assert (S (s + a) = s + S a); [omega|]. rewrite H1. sep fail auto. 
  Qed.

  Lemma array_split_fb : forall n a (f : nat -> hprop),
    {@ f i | i <- a + n} * f (a + n) ==>
    f a * {@ f i | i <- (S a) + n}.
  Proof.
    induction n; intros; simpl. cut (a = a + 0); try omega; intros. rewrite <- H. sep fail auto.
    simpl. sep fail auto. pose (IHn (S a) f). sep fail auto. assert (a + S n = S (a + n)); try omega. rewrite H. sep fail auto.
  Qed.

  Lemma iter_sep_after : forall f l s,
    {@ f i | i <- s + l } * f (s + l) ==> {@ f i | i <- s + S l }.
  Proof.
    induction l. simpl. intros. norm arith. sep fail auto.
    sep fail auto. assert (s + S l = S s + l). omega. rewrite H. eapply array_split_fb.
  Qed.
  Lemma iter_sep_append : forall f l s l2,
    {@ f i | i <- s + l } * {@ f i | i <- (s + l) + l2 } ==> {@ f i | i <- s + (l + l2)}.
    induction l. sep fail auto. norm arith. sep fail auto.
    sep fail auto. assert (s + S l = S s + l). omega. rewrite H. sep fail auto.
  Qed.

  Lemma combine_array : forall f i l s,
    {@ f x | x <- s + i} * (f (s + i)) * {@ f x | x <- (S (s + i)) + l } 
    ==>
    {@ f x | x <- s + (l + i + 1)}.
  Proof.
    intros. eapply himp_trans. instantiate (1 := {@f x | x <- (S (s + i)) + l} * _). canceler. eapply iter_sep_after. 
    apply himp_comm_prem. assert (S (s + i) = s + S i). omega. rewrite H. assert (l + i + 1 = S i + l). omega. rewrite H0.
    eapply iter_sep_append.
  Qed.

  Fixpoint repBranch' (h : nat) (rep' : ptr -> option ptr -> (option ptr -> hprop) -> tree h -> hprop) 
    (ary : array) (i : nat) (ls : list (sigTS (fun _:key => tree h)))
    (op : option ptr) (c : option ptr-> hprop) {struct ls} : hprop :=
    match ls with
      | nil => {@ (p :~~ array_plus ary i in p ~~> @None (key * ptr)) | i <- i + (SIZE - i)} * c op
      | f :: r => 
        p :~~ array_plus ary i in Exists p' :@ ptr, p ~~> (Some (projT1S f, p')) *
        rep' p' op (fun op => repBranch h rep' ary (S i) r op c) (projT2S f)
    end.


  Fixpoint repBranchPrefix (h : nat) (rep' : ptr -> option ptr -> (option ptr -> hprop) -> tree h -> hprop) 
    (ary : array) (i l : nat) (ls : list (sigTS (fun _:key => tree h)))
    (op : option ptr) (c : option ptr-> hprop) {struct l} : hprop :=
    match l with
      | 0 => c op
      | S l => 
        match ls with
          | nil => p :~~ array_plus ary i in p ~~> @None (key * ptr) * repBranchPrefix h rep' ary (S i) l nil op c
          | f :: r => 
            p :~~ array_plus ary i in Exists p' :@ ptr, p ~~> (Some (projT1S f, p')) *
            rep' p' op (fun op => repBranchPrefix h rep' ary (S i) l r op c) (projT2S f)
        end
    end.

  Fixpoint repX' (n : nat) (p : ptr) (op : option ptr) (c : option ptr -> hprop) {struct n} : tree n -> hprop :=
    fun t =>
      Exists a :@ nodeType, p ~~> a * [height a = n] *
      match n as n return tree n -> hprop with 
        | 0 => fun ls =>
          [array_length (content a) = SIZE] * [op = Some p] * [length ls <= SIZE] *
          repLeaf (content a) 0 SIZE ls * (c (next a))
        
        | S n' => fun m =>
          let ls  := fst m in
          let nxt := snd m in
          [array_length (content a) = SIZE] * [length ls <= SIZE] *
          Exists np :@ ptr, [next a = Some np] *
          repBranchPrefix n' (repX' n') (content a) 0 SIZE ls op (fun op => Exists p' :@ ptr, np ~~> p' * rep' n' p' op c nxt)
      end t.

  Theorem nat_ind_strong (P : nat -> Prop) : 
    P 0 ->
    (forall n : nat, (forall n' : nat, n' <= n -> P n') -> P (S n)) ->
    forall n : nat, P n.
  Proof.
(**
    intros.
    refine (@nat_ind P H _ n).
    refine (fix rec (n0:nat) (PP: P n0) {struct n0} : P (S n0) :=
      match n0 as n0' return P (S n0') with 
        | 0 => _
        | S n0' => _
      end).
    intros; subst. eapply H0. think. assert (n' = 0); think.
    eapply rec. eapply rec.
**)
  Admitted.

  Lemma repBranchPrefix_inj' : forall l a b d c e f g,
    (forall a' c d e b f, a' <= a -> (forall x, d x ==> e x) -> repX' a' b c d f ==> repX' a' b c e f) ->
    (forall x, f x ==> g x) ->
    repBranchPrefix a (repX' a) b c l d e f ==> repBranchPrefix a (repX' a) b c l d e g.
  Proof.
    clear. induction l. simpl. sep fail auto.
    sep fail auto. destruct d. sep fail auto. sep fail auto. 
  Qed.
  Lemma repInj_single' : forall a c d e b f, 
    (forall a' l b d c e f g, a' < a -> (forall x, f x ==> g x) -> repBranchPrefix a' (repX' a') b c l d e f ==> repBranchPrefix a' (repX' a') b c l d e g) ->
    (forall x, d x ==> e x) -> repX' a b c d f ==> repX' a b c e f.
  Proof.
    clear. induction a.
    simpl. sep fail auto. 
    
    Opaque repBranchPrefix. intros. simpl. sep fail auto. instantiate (1 := v0). sep fail auto. rewrite H4. eapply H. think. sep fail auto.
  Qed.
  
  Theorem repInj_single : forall a c d e b f, 
    (forall x, d x ==> e x) -> repX' a b c d f ==> repX' a b c e f.
  Proof.
    induction a using nat_ind_strong.
    intros. eapply repInj_single'; intros; think.
    intros. eapply repInj_single'; intros; think.
    eapply repBranchPrefix_inj'; think. intros. eapply H; think.
  Qed.
  Theorem repBranchPrefix_inj : forall l a b d c e f g,
    (forall x, f x ==> g x) ->
    repBranchPrefix a (repX' a) b c l d e f ==> repBranchPrefix a (repX' a) b c l d e g.
  Proof.
    intros; eapply repBranchPrefix_inj'; think. intros. eapply repInj_single. auto.
  Qed.
  Theorem repInj_ext : forall a c d e b f P, 
    (forall x, d x ==> e x * P) -> repX' a b c d f ==> repX' a b c e f * P.
  Proof.
(**
    induction a. sep fail auto. apply himp_comm_conc. auto.
      sep fail auto. instantiate (1 := v0). sep fail auto.
      generalize (repBranchPrefix_inj (array_length (content v)) a (content v) a0 0 c
        (fun op : option ptr => Exists p' :@ ptr, v0 ~~> p' * rep' a p' op d b0) 
        (fun op : option ptr => Exists p' :@ ptr, v0 ~~> p' * rep' a p' op e b0 * P)).
      intro. eapply himp_trans. eapply H6. sep fail auto.
**)
  Admitted.
  Theorem repBranchPrefix_ext : forall l a b d c e f g P,
    (forall x, f x ==> g x * P) ->
    repBranchPrefix a (repX' a) b c l d e f ==> repBranchPrefix a (repX' a) b c l d e g * P.
  Proof.
(**
    induction a. sep fail auto. apply himp_comm_conc. auto.
      sep fail auto. instantiate (1 := v0). sep fail auto.
      generalize (repBranchPrefix_inj (array_length (content v)) a (content v) a0 0 c
        (fun op : option ptr => Exists p' :@ ptr, v0 ~~> p' * rep' a p' op d b0) 
        (fun op : option ptr => Exists p' :@ ptr, v0 ~~> p' * rep' a p' op e b0 * P)).
      intro. eapply himp_trans. eapply H6. sep fail auto.
**)
  Admitted.

  Lemma repBranch_unroll_end : forall h ary len st ls op cont,
    repBranchPrefix h (repX' h) ary st (S len) ls op cont
    ==>
    Exists op' :@ option ptr, repBranchPrefix h (repX' h) ary st len ls op (fun opx => [op' = opx]) *
                              match nth_error ls len with
                                | None               => p :~~ array_plus ary (len + st) in p ~~> @None (key * ptr) * cont op'
                                | Some (existTS k t) => p :~~ array_plus ary (len + st) in Exists pc :@ ptr, p ~~> Some (k, pc) * repX' h pc op' cont t
                              end.
  Proof.
    induction len. 
    destruct ls. simpl; sep fail auto.
(*
      simpl. sep fail auto. destruct s. sep fail auto. apply repInj_single. sep fail auto.

    intros. simpl. generalize (IHlen (S st) (skipn 1 ls)). clear. destruct ls. simpl. intros.
    
    eapply (@unpack ptr (array_plus ary st)). intros. rewrite H0. apply himp_empty_prem'. eapply himp_unpack_prem_eq; auto.
    search_prem ltac:(apply himp_empty_prem). apply himp_comm_prem. eapply himp_subst. eapply H.
    sep fail auto. norm list. sep fail auto. assert (len + S st = S (len + st)). think. rewrite H2 in *. sep fail auto.

(** TODO: Need more injectivity lemmas
    intros; inhabiter. sep fail auto. Show Existentials.
    intros. eapply (@unpack ptr (array_plus ary st)). intros. rewrite H0. apply himp_empty_prem'. eapply himp_unpack_prem_eq; auto.
    inhabiter. search_prem ltac:(apply himp_empty_prem). apply himp_comm_prem. eapply himp_subst.
    
    
    
    sep fail auto. sep fail auto. eapply repInj_ext. 
    destruct ls. Focus 2.
      sep fail auto. destruct s0. sep fail auto. 
**)
*)
  Admitted.

  Lemma repBranch_unroll : forall h ary ind idx len st ls op cont,
    ind = idx - st ->
    st <= idx ->
    idx < len + st ->
    repBranchPrefix h (repX' h) ary st len ls op cont 
    ==> 
    Exists op' :@ option ptr, repBranchPrefix h (repX' h) ary st ind ls op (fun opx => [op' = opx]) * 
                              repBranchPrefix h (repX' h) ary idx (len - ind) (skipn ind ls) op' cont.
  Proof.
(*
    clear. intros h ary.
    induction ind. intros. simpl in *. assert (idx = st); think. subst. norm arith. sep fail auto.
    (** **)
    intros. destruct idx. think. destruct len. think. norm arith.
    destruct ls. 
    Focus 2. simpl. inhabiter.
*)    
  Admitted. (** TODO **)


  (** Implementation **)
  Definition emptyTree : tree 0 := nil.
  Definition emptyTreeInv : inv 0 emptyTree MinK MaxK.
    simpl; auto. unfold emptyTree, MinK, MaxK. compute. auto.
  Qed.
  Hint Immediate emptyTreeInv.
  
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
    sep fail auto. pose (array_split_fb n 0 (fun i => hprop_unpack (array_plus ary i) (fun p => p ~~> @None T))).
      simpl in h. apply h.
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
            let tr : tH := existTS _ 0 emptyTree in
            let res' : BptMap := (res, inhabits tr) in
            {{ Return res' }}).
    sep fail auto.
    sep fail auto.
    sep fail auto.
    sep fail auto.
    sep fail auto.
    unfold rep, tr, res' in *; sep fail auto.
    rewrite H1 in *. simpl in *. unfold tr in *. rewrite <- (pack_injective H). generalize emptyTreeInv. sep fail auto. Opaque inv. sep fail auto. destruct (array_length ary); sep fail auto. 
    unfold repLeaf. simpl. canceler. eapply iter_sep_inj. sep fail auto. destruct x; auto.
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

  Definition free_leaf : forall (p : ptr) (cont : option ptr -> hprop) 
    (ary : array) (nxt : option ptr) (ls : [list (sigTS value)]),
    STsep (ls ~~ p ~~> mkNode 0 ary nxt * [array_length ary = SIZE] * [length ls <= SIZE] *
             repLeaf ary 0 SIZE ls * cont nxt)
          (fun res:option ptr => cont res).
    refine (fun p cont ary nxt ls =>
      free_array ary <@> (p ~~> mkNode 0 ary nxt) * _ ;;
      Free p <@> _ ;;
      {{ Return nxt }});
    sep fail auto. eapply repLeaf_iter. eauto.
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
    destruct l. simpl in pf. think. simpl in pf. generalize pf. think.  simpl. assert (n < length l); try omega. eapply IHn. instantiate (1 := H0).  generalize H.
      simpl. 
      match goal with 
        | [ |- context [ @nthDep _ _ _ ?X ] ] => generalize X
      end.
    intros. rewrite (proof_irrelevance _ H0 l0). auto.
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

  Definition free_branch : forall (p : ptr) (cont : option ptr -> hprop) (h : nat) (ary : array) (nxt : ptr) (m : [tree (S h)]),
    (forall (p : ptr) (m : [sigTS tree]) (cont : option ptr -> hprop),
       STsep (m ~~ Exists op :@ option ptr, rep' (projT1S m) p op cont (projT2S m))
             (fun r:option ptr => cont r)) ->
     STsep (m ~~ Exists op :@ option ptr, 
              p ~~> mkNode (S h) ary (Some nxt) * [array_length ary = SIZE] * [length (fst m) <= SIZE] *
              repBranch h (rep' h) ary 0 (fst m) op 
                (fun op => Exists p' :@ ptr, nxt ~~> p' * rep' h p' op cont (snd m)))
           (fun res:option ptr => cont res).
     clear.
     refine (fun p cont h ary nxt m rec =>
       Free p ;;
       {{ Fix2 (fun (n:nat) (pf:n <= SIZE) =>
                  m ~~ Exists op :@ option ptr, [length (fst m) <= SIZE] * [array_length ary = SIZE] *
                      {@hprop_unpack (array_plus ary i) (fun p0 : ptr => p0 ~~>?) | i <- 0 + n} *
                      repBranch h (rep' h) ary n (skipn n (fst m)) op
                      (fun op : option ptr => Exists p' :@ ptr, nxt ~~> p' * rep' h p' op cont (snd m)))
               (fun n pf (r:option ptr)    => cont r)
               (fun self n pf =>
                 match le_lt_dec SIZE n with
                   | left _  => 
                     free_array ary <@> _ ;;
                     cptr <- ! nxt ;
                     Free nxt ;;
                     {{ rec cptr (m ~~~ existTS tree h (snd m)) cont }}
                   | right pfSn =>
                     kv <- sub_array ary n _ ;
                     let _:option (key * ptr) := kv in
                     match kv as kv' return kv = kv' -> _ with
                       | None => fun pf' => {{ self (S n) (lt_S_le pfSn) }}
                       | Some (_,p) => fun pf' =>
                         zz <- rec p (m ~~~ match nth_error (fst m) n with
                                              | None => existTS tree (S h) m (** Junk **) 
                                              | Some v => existTS tree h (projT2S v)
                                            end) _ <@> _ ;
                         {{ self (S n) (lt_S_le pfSn) }}
                     end (refl_equal _)
                 end) 0 (O_le SIZE) }}); try clear self.
     sep fail auto.
     sep fail auto.
     inhabiter. unpack_conc. assert (n = SIZE). omega. rewrite H1 in *. clear pf. clear l. intro_pure.
       apply skip_len in H2. rewrite H2. simpl. simpl. rewrite H3. canceler. sep fail auto.
     solve [ sep fail auto ].
     sep fail auto.
     sep fail auto.
     sep fail auto.
     sep fail auto. norm arith.
     sep fail auto.
     sep fail auto.
     instantiate (1 := fun cp:option (key * ptr) => m ~~
         {@hprop_unpack (array_plus ary i) (fun p0 : ptr => p0 ~~>?) | i <- 0 + n} * [array_length ary = SIZE] * [length (fst m) <= SIZE] *
         Exists op :@ option ptr,
         match le_lt_dec (length (fst m)) n with
           | right pf' => Exists k :@ key, Exists p'' :@ ptr, 
             [cp = Some (k,p'')] * rep' h p'' op 
             (fun op => repBranch h (rep' h) ary (S n) (skipn (S n) (fst m)) op
               (fun op : option ptr => Exists p' :@ ptr, nxt ~~> p' * rep' h p' op cont (snd m))) (projT2S (@nthDep _ (fst m) n pf')) 
           | left _ => repBranch h (rep' h) ary (S n) (skipn (S n) (fst m)) op
             (fun op : option ptr => Exists p' :@ ptr, nxt ~~> p' * rep' h p' op cont (snd m))
             * [length (fst m) <= n] * [cp = None]
           end).
     inhabiter. intro_pure. simpl. destruct x.
     destruct (le_lt_dec (length l) n).
       (** Before the end **)
       assert (skipn n l = nil). apply skip_len; auto. norm pair. rewrite H3 in *. simpl.
       eapply himp_trans.
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

  Definition free_rec : forall (p : ptr) (m : [sigTS tree]) (cont : option ptr -> hprop),
    STsep (m ~~ Exists op :@ option ptr, rep' (projT1S m) p op cont (projT2S m))
          (fun r:option ptr => cont r).
    refine
      (Fix3 (fun p m cont => m ~~ Exists op :@ option ptr, rep' (projT1S m) p op cont (projT2S m))
            (fun _ _ cont (r:option ptr) => cont r)
            (fun self p m cont =>
              {{ @bpt_case_ex (option ptr) (cont) (__) p m cont
                  (fun a n l => {{ free_leaf p cont a n l }})
                  (fun h a n m => {{ @free_branch p cont h a n m self }}) }}));
    sep fail auto. 
  Qed.

  Definition free (t : BptMap) (m : [Model]) :
    STsep (m ~~ rep t m)
          (fun _:unit => __). 
    refine (fun t m =>
      z <- @free_rec (fst t) (snd t) (fun x:option ptr => [x = None]) ;
      {{ Return tt }}).
  Proof.
    unfold rep. inhabiter. destruct x0. sep fail auto.
    sep fail auto.
    sep fail auto.
    sep fail auto.
  Qed.
    
  Inductive op : Set :=
  | Merge   : ptr -> op
  | Split   : ptr -> key -> ptr -> op
  | Combine : ptr -> op
  | Splice  : ptr -> op.

  Definition opModel (h : nat) (m : op) : Set :=
    match m with
      | Merge _ => tree h
      | Split _ _ _ => tree h * key * tree h
      | Combine _ => tree h
      | Splice _ =>
        match h with 
          | 0 => Empty_set
          | S h' => tree h'
        end
    end%type.

  Definition repOp (h : nat) (o : op) (m : opModel h o) (min max : LiftOrder key) 
    (optr : option ptr) (cont : option ptr -> hprop) : hprop :=
    match o as o return opModel h o -> hprop with
      | Merge p        => fun m => [inv h m min max] * rep' h p optr cont m
      | Split lp kp rp => fun lkr => let l := fst (fst lkr) in let k := snd (fst lkr) in let r := snd lkr in
        [inv h l min (Val k)] * [inv h r (Val k) max] * [kp = k] *
        rep' h lp optr (fun op => rep' h rp op cont r) l
      | Combine p      => fun m => [inv h m min max] * rep' h p optr cont m
      | Splice p       => 
        match h as h return opModel h (Splice p) -> hprop with
          | 0   => fun _ => [False]
          | S h => fun m => [inv h m min max] * rep' h p optr cont m
        end
    end m.
(*
  | Merge   : forall n (m:tree n), inv n m min max -> op min max n
  | Split   : forall n (l : tree n) (k: key) (r: tree n), 
    inv n l min (Val k) -> inv n r (Val k) max  -> op min max n
  | Combine : forall n (m:tree n), inv n m min max -> op min max n
  | Splice  : forall n (m:tree n), inv n m min max -> op min max (S n).
*)

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


  (** Compute **)
  Section Compute.
    Hypothesis RT : Type.
    Hypothesis P  : hprop.
    Hypothesis Q  : RT -> hprop.
    Hypothesis tK : key.

    Definition RES (n : nat) := (RT * sigT (fun o:op => [opModel n o]%type))%type.

    Hypothesis Fn : forall (p : ptr) (ary : array) (nxt : option ptr) 
      (ls : [list (sigTS value)]) (min max : [LiftOrder key]) 
      (cont : option ptr -> hprop),
      STsep (ls ~~ min ~~ max ~~
                p ~~> mkNode 0 ary nxt * repLeaf ary 0 SIZE ls * [inv 0 ls min max] * cont nxt * [key_between min tK max] * P)
            (fun r:RES 0 => min ~~ max ~~ hprop_unpack (projT2 (snd r)) (fun m => 
                Exists nptr :@ option ptr, repOp 0 (projT1 (snd r)) m min max nptr cont) * Q (fst r)).
  
    Hypothesis Spec : key -> list (sigTS value) -> (list (sigTS value) * RT).
    Hypothesis SpecLocal : forall (min' min max max' : LiftOrder key) (k : key) (i ol oh : list (sigTS value)),
      KLsorted min' (ol ++ i ++ oh) max' ->
      KLsorted min i max ->
      key_between min k max ->
      Spec k (ol ++ i ++ oh) = (ol ++ fst (Spec k i) ++ oh, snd (Spec k i)).

    Definition leafCompute : forall (min max : [LiftOrder key]) 
      (p : ptr) (cont : option ptr -> hprop)
      (ary : array) (nxt : option ptr) (ls : [list (sigTS value)]),
      STsep (min ~~ max ~~ ls ~~ p ~~> mkNode 0 ary nxt * [array_length ary = SIZE] *
               [length ls <= SIZE] * repLeaf ary 0 SIZE ls * cont nxt * [inv 0 ls min max] * [key_between min tK max] * P)
            (fun res :RES 0 => min ~~ max ~~ hprop_unpack (projT2 (snd res))
               (fun opm => Exists op' :@ option ptr, repOp 0 (projT1 (snd res)) opm min max op' cont * Q (fst res))).
      refine (fun min max p cont ary nxt ls =>
        {{ Fn p ary nxt ls min max cont }}).
      sep fail auto.
      sep fail auto.
    Qed.

    Axiom repBranch_repBranchPrefix : forall a b c e f g h,
      h = SIZE ->
      repBranch a b c 0 e f g ==> repBranchPrefix a b c 0 h e f g.
    Hint Resolve repBranch_repBranchPrefix.

    Axiom localCompute' : forall (min max : [LiftOrder key]) (h : nat)
      (p : ptr) (cont : option ptr -> hprop) (m : [tree h]),
      STsep (min ~~ max ~~ m ~~ Exists op :@ option ptr,
                rep' h p op cont m * [inv h m min max] * [key_between min tK max] * P)
            (fun res : RES h => min ~~ max ~~ opm :~~ projT2 (snd res) in
                Exists op' :@ option ptr, repOp h (projT1 (snd res)) opm min max op' cont * Q (fst res)).

    Definition mergeOpNext : forall (min max : [LiftOrder key]) (h : nat)
      (p : ptr) (cont : option ptr -> hprop)
      (ary : array) (nxt : ptr) (full : nat) (op : RES h) (m : [tree (S h)]),
      STsep (min ~~ max ~~ m ~~
               let lsM  := fst m in
               let nxtM := snd m in
               Exists op :@ option ptr, 
               [inv (S h) m min max] *
               Exists p' :@ ptr, nxt ~~> p' * cont op *
               repBranchPrefix h (rep' h) ary 0 SIZE lsM op 
                 (fun op1 : option ptr => [op1 = op]))
            (fun res : RES (S h) => min ~~ max ~~ opm :~~ projT2 (snd res) in
              Exists op' :@ option ptr, repOp (S h) (projT1 (snd res)) opm min max op' cont * Q (fst res)).
      refine (fun min max h p cont ary nxt full op m =>
        _).
    Admitted.

    Definition mergeOpInternal : forall (min max : [LiftOrder key]) (h : nat)
      (p : ptr) (cont : option ptr -> hprop)
      (ary : array) (nxt : ptr) (idx : nat) (op : RES h) (m : [tree (S h)]),
      STsep (min ~~ max ~~ m ~~
               let lsM  := fst m in
               let nxtM := snd m in
               Exists op :@ option ptr, 
               [inv (S h) m min max] *
               repBranchPrefix h (rep' h) ary 0 idx lsM op 
                 (fun op1 : option ptr => [op1 = op]) * 
               __ *
               repBranchPrefix h (rep' h) ary (S idx) (idx - S idx) lsM op cont)
            (fun res : RES (S h) => min ~~ max ~~ opm :~~ projT2 (snd res) in
              Exists op' :@ option ptr, repOp (S h) (projT1 (snd res)) opm min max op' cont * Q (fst res)).
      refine (fun min max h p cont ary nxt full op m =>
        _).
    Admitted.
    

    Definition branchCompute : forall (min max : [LiftOrder key]) (h : nat)
      (p : ptr) (cont : option ptr -> hprop)
      (ary : array) (nxt : ptr) (m : [tree (S h)]),
      STsep (min ~~ max ~~ m ~~ Exists op0 :@ option ptr, p ~~> mkNode (S h) ary (Some nxt) *
               [array_length ary = SIZE] * [length (fst m) <= SIZE] *
               repBranch h (rep' h) ary 0 (fst m) op0
                 (fun op1 : option ptr => Exists p' :@ ptr, nxt ~~> p' * rep' h p' op1 cont (snd m)) * [inv (S h) m min max])
            (fun res : RES (S h) => min ~~ max ~~ opm :~~ projT2 (snd res) in
              Exists op' :@ option ptr, repOp (S h) (projT1 (snd res)) opm min max op' cont * Q (fst res)).
      refine (fun min max h p cont ary nxt m =>
        {{ Fix2 (fun (i: nat) (min':[LiftOrder key]) => min ~~ max ~~ min' ~~ m ~~ 
                   let lsM  := fst m in
                   let nxtM := snd m in
                   Exists op :@ option ptr, 
                   [KLsorted min (firstn i lsM) min'] * [inv (S h) m min max] * [key_between min' tK max] * [length lsM >= i] *
                   p ~~> mkNode (S h) ary (Some nxt) *
                   repBranchPrefix h (rep' h) ary 0 SIZE lsM op 
                     (fun op1 : option ptr => Exists p' :@ ptr, nxt ~~> p' * rep' h p' op1 cont nxtM))
                (fun i min (res:RES (S h)) => min ~~ max ~~ opm :~~ projT2 (snd res) in
                   Exists op' :@ option ptr, repOp (S h) (projT1 (snd res)) opm min max op' cont * Q (fst res))
                (fun self i min' =>
                  if le_lt_dec SIZE i then
                    rr <- localCompute' min' max h nxt cont (m ~~~ snd m) <@> _ ;
                    {{ @mergeOpNext min max h p cont ary nxt SIZE rr m }}
                  else
                    okv <- sub_array ary i (fun v => m ~~ match nth_error (fst m) i with
                                                            | None => [v = @None (key * ptr)]
                                                            | Some (existTS k' v') => Exists pc :@ ptr, [v = Some (k', pc)]
                                                          end) ;
                    match okv as okv' return okv = okv' -> _ with 
                      | None => fun _ => 
                        rr <- localCompute' min' max h nxt cont (m ~~~ snd m) <@> _ ;
                        {{ @mergeOpNext min max h p cont ary nxt i rr m }}
                      | Some (k', v') => fun _ => 
                        match OTcompare KOT k' tK with
                          | LT _  => {{ self (S i) [Val k']%inhabited }}
                          | EQ pf => _
                          | GT _  =>
                            rr <- localCompute' min' [Val k']%inhabited h v' 
                              (fun op:option ptr => _) (m ~~~ projT2S (@nthDep _ (fst m) i _)) <@> _ ;
                            {{ @mergeOpInternal min max h p cont ary nxt i rr m }}
                        end
                    end (refl_equal _)) 0 min }}).
(*
      Focus 2.
      sep fail auto.
      Focus 2.
      sep fail auto.
*)
    Admitted.
  
    Definition localCompute : forall (min max : [LiftOrder key]) (h : nat)
      (p : ptr) (cont : option ptr -> hprop) (m : [tree h]),
      STsep (min ~~ max ~~ m ~~ Exists op :@ option ptr,
                rep' h p op cont m * [inv h m min max] * [key_between min tK max] * P)
            (fun res : RES h => min ~~ max ~~ opm :~~ projT2 (snd res) in
                Exists op' :@ option ptr, repOp h (projT1 (snd res)) opm min max op' cont * Q (fst res)).
      refine (fun min max h p cont m =>
        {{ @bpt_case_ex_h h (RES) 
              (fun h rt => min ~~ max ~~ opm :~~ projT2 (snd rt) in
                Exists op' :@ option ptr, repOp h (projT1 (snd rt)) opm min max op' cont * Q (fst rt))
              P p m cont
              (fun ary nxt ls => {{ leafCompute min max p cont ary nxt ls }})
              (fun h' ary nxt m => {{ @branchCompute min max h' p cont ary nxt m }})
              }}
        ).
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
  
