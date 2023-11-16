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
Require Import Minus Div2 Even.
Require Import ProofIrrelevance Eqdep.
Require Import Think ThinkList ThinkArith.
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
  Variable SIZE_even : even SIZE. (** Even sizes make life a little bit easier for splits **)

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

  Fixpoint ptree (n : nat) : Set :=
    (ptr * match n return Set with
             | 0 => list (sigTS value)
             | S n => list (sigTS (fun _:key => ptree n)) * ptree n
           end)%type.

  Notation "'BranchCell' h" := (sigTS (fun _:key => ptree h)) (at level 50).

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

  Fixpoint contextual (h : nat) (F : LiftOrder key -> BranchCell h -> Prop)
    (min max : LiftOrder key) (ls : list (BranchCell h)) {struct ls} : Prop :=
    match ls with 
      | nil => OTeq KLOT min max
      | fs :: rr => F min fs /\ contextual h F (Val (projT1S fs)) max rr
    end.

  Fixpoint lastKey (T : key -> Set) (ls : list (sigTS T)) (d : LiftOrder key) : LiftOrder key :=
    match ls with
      | nil => d
      | a :: b => lastKey b (Val (projT1S a))
    end.

  Fixpoint inv (n : nat) : ptree n -> LiftOrder key -> LiftOrder key -> Prop :=
    match n as n return ptree n -> LiftOrder key -> LiftOrder key -> Prop with
      | 0 => fun m min max =>
        KLsorted min (snd m) max

      | S n => fun m min max =>
        let (ls,nxt) := snd m in
        let break := lastKey ls min in
        contextual n (fun mi c => inv n (projT2S c) mi (Val (projT1S c))) min break ls
        /\ inv n nxt break max
    end.

  (** Logical Representation **)
  Definition Model := list (sigTS value).

  Fixpoint as_map (n : nat) {struct n} : ptree n -> Model :=
    match n as n return ptree n -> list (sigTS value) with 
      | 0 => fun ls => snd ls
      | S n' => fun n =>
        let (ls,nxt) := snd n in
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

  Lemma nodeType_eta : forall a b c n,
    height n = a -> content n = b -> next n = c -> n = mkNode a b c.
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
  
  Fixpoint lastPtr (h : nat) : ptree h -> ptr :=
    match h as h return ptree h -> ptr with
      | 0 => fun m => fst m
      | S h => fun m => lastPtr h (snd (snd m))
    end.

  Fixpoint firstPtr (h : nat) : ptree h -> ptr :=
    match h as h return ptree h -> ptr with
      | 0 => fun m => fst m
      | S h => fun m => match fst (snd m) with
                          | nil => firstPtr h (snd (snd m))
                          | a :: _ => firstPtr h (projT2S a)
                        end
    end.
  Definition ptrFor (h : nat) : ptree h -> ptr :=
    match h as h return ptree h -> ptr with
      | 0 => fun x => fst x
      | S n => fun x => fst x
    end.

  Fixpoint repBranch (h : nat) (rep' : ptr -> option ptr -> ptree h -> hprop) 
    (ary : array) (i l : nat) (ls : list (BranchCell h))
    (nxt : ptr) {struct l} : hprop :=
    match l with
      | 0 => __
      | S l => 
        match ls with
          | nil => p :~~ array_plus ary i in p ~~> @None (key * ptr) * 
            repBranch h rep' ary (S i) l nil nxt
          | f :: tl =>
            p :~~ array_plus ary i in
            let p' := ptrFor _ (projT2S f) in
            p ~~> Some (projT1S f, p') *
            repBranch h rep' ary (S i) l tl nxt *
            match tl with
              | nil => rep' p' (Some nxt) (projT2S f)
              | r :: _ => rep' p' (Some (firstPtr _ (projT2S r))) (projT2S f)
            end
        end
    end.

  Fixpoint rep' (n : nat) (p : ptr) (op_next : option ptr) {struct n} : ptree n -> hprop :=
    match n as n return ptree n -> hprop with 
      | 0 => fun m =>
        [p = ptrFor _ m] *
        let (p,ls) := m in
        Exists ary :@ array, p ~~> mkNode n ary op_next *
        [array_length ary = SIZE] * [length ls <= SIZE] *
        repLeaf ary 0 SIZE ls
        
      | S n' => fun m =>
        [p = ptrFor _ m] *
        let (p,m) := m in
        let ls  := fst m in
        let nxt := snd m in
        Exists ary :@ array, p ~~> mkNode n ary (Some (ptrFor _ nxt)) *
        [array_length ary = SIZE] * [length ls <= SIZE] *
        repBranch n' (rep' n') ary 0 SIZE ls (firstPtr _ nxt) *
        rep' n' (ptrFor _ nxt) op_next nxt
    end.

  (** (height, tree) pairs **)
  Definition tH := sigTS ptree.
  Definition BptMap := (ptr * [tH])%type.

  Definition rep (t : BptMap) (m : Model) : hprop :=
    let p := fst t in
    bpt :~~ snd t in
    match bpt with
      | existTS h t => [m = as_map h t] * [inv h t MinK MaxK] *
        rep' h p None t
    end.

(** TODO: This probably isn't actually used **)
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

  Definition repBranch_nextPtr {h} (ls : list (BranchCell h)) i (optr : ptr) : ptr :=
    match nth_error ls (S i) with
      | None => optr
      | Some (existTS _ v) => firstPtr _ v
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

  Lemma repBranch_ignore_end : forall h ARY i s LS a b,
    i < length LS
    -> repBranch h (rep' h) ARY s i LS a ==> repBranch h (rep' h) ARY s i LS b.
  Proof. clear.
    induction i. 
    sep fail auto.
    sep fail auto. destruct LS. simpl in *; elimtype False; omega.
    destruct LS; sep fail auto. elimtype False. omega.
  Qed.

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
           rep' h (ptrFor _ v) (Some (repBranch_nextPtr a0 idx x0)) v
       end%hprop)).
  Proof.
    Hint Extern 1 (?A<=?B) => omega.
    Hint Extern 1 (?A<?B) => omega.
    Hint Resolve nth_error_len_rw skipn_len skipn_shift.
    intros.
    eapply himp_trans. eapply repBranch_split; try eassumption.
    unfold repBranchExcept. norm arith.
    cut (SIZE - idx = S (SIZE - S idx)); [|omega]. intros. rewrite H0.
    simpl. clear H0.
    destruct (le_lt_dec (length a0) idx); norm list.
    destruct a0. sep fail auto. simpl in *. norm list. sep fail auto.

    generalize (skipn_len_ne _ l); intros.
    do 2 destruct H0. rewrite H0.
    generalize (skipn_nth_error _ _ H0); intros. rewrite H1.
    destruct a0. norm list in *; discriminate.
    destruct x. destruct x1. simpl in *. sep fail auto. apply skipn_shift in H0. rewrite H0.
    sep fail auto. unfold repBranch_nextPtr. simpl.
    cut (nth_error a0 idx = None); [intros|eapply nth_error_len_rw;eapply skipn_len;eauto].
    rewrite H3. sep fail auto.
    eapply repBranch_ignore_end; eauto.    
      
    sep fail auto. unfold repBranch_nextPtr. simpl.
      cut (nth_error a0 idx = Some s0); [| apply skipn_shift in H0; eapply skipn_nth_error; eauto ]; intros.
      rewrite H3. destruct s0. simpl. sep fail auto.
      fold ptree in *.
      search_prem ltac:(search_conc ltac:(eapply himp_split; [ solve [ eapply repBranch_ignore_end; eauto ] | ])).
      eapply skipn_shift' in H0. rewrite H0. sep fail auto.
  Qed.

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
           rep' h (ptrFor _ v) (Some (repBranch_nextPtr a0 idx x0)) v
       end)) * P ==> Q ->
    repBranch h (rep' h) ary 0 SIZE a0 x0 * P ==> Q.
  Proof.
    intros. eapply himp_trans. Focus 2. eapply H0. canceler. eapply repBranch_read; eauto.
  Qed.

  Lemma repBranch_splitEnd : forall h ary x0 idx a0,
    idx < SIZE ->
    idx >= length a0 ->
    repBranch h (rep' h) ary 0 SIZE a0 x0 ==>
    repBranchExcept h ary idx a0 x0 *
    (p :~~ array_plus ary idx in p ~~> @None (key * ptr)).
  Proof.
    Hint Resolve repBranch_ignore_end.
    Hint Extern 1 (?A<=?B) => omega.
    intros.
    eapply himp_trans. eapply repBranch_split; try eassumption. 
    unfold repBranchExcept. norm arith. cut (SIZE - idx = S (SIZE - S idx)). intros. rewrite H1.
      simpl. norm list. sep fail auto. destruct a0; sep fail auto. norm list; sep fail auto.
      omega.
  Qed.

  Definition invCF (n0 : nat) (mi : LiftOrder key) (c : sigTS (fun _ : key => ptree n0)) :=
    inv n0 (projT2S c) mi (Val (projT1S c)).
  Definition invCB (n0 : nat) (nxt : ptree n0) (max mi : LiftOrder key) := inv n0 nxt mi max.

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

(**
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
**)

  (** Implementation **)
  Definition emptyTree (p:ptr) : ptree 0 := (p, nil).
  Definition emptyTreeInv : forall p:ptr, inv 0 (emptyTree p) MinK MaxK.
    simpl; auto; intros. Transparent KLOT. unfold emptyTree, MinK, MaxK; compute; auto.
  Qed.
  Hint Resolve emptyTreeInv.
  Opaque KLOT.
  
  Hint Extern 1 (?A=?B)  => omega.
  Hint Extern 1 (?A<?B)  => omega.
  Hint Extern 1 (?A<=?B) => omega.
  Hint Extern 1 (?A>?B)  => omega.
  Hint Extern 1 (?A>=?B) => omega.

  Lemma minus_le : forall m n, n <= m -> n - m = 0.
  Proof. auto.
  Qed.

  Lemma lt_S_le : forall n m, n < m -> S n <= m.
  Proof. auto.
  Qed.
  Lemma O_le : forall n, 0 <= n.
  Proof. auto.
  Qed.

  Lemma minus_lt : forall a b, a < b -> b - a = S (pred (b - a)).  
  Proof. auto.
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

  Lemma minus_n_1 : forall a b, a - b - 1 = a - S b.
    intros; omega.
  Qed.

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

(**
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
       apply skipn_len in H2. rewrite H2. simpl. simpl. rewrite H3. canceler. sep fail auto.
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
**)

    
  Inductive op : Set :=
  | Merge   : ptr -> op
  | Split   : ptr -> key -> ptr -> op.
(*  | Combine : ptr -> op. *)
(*  | Splice  : ptr -> op. *)

  Definition opModel (h : nat) (m : op) : Set :=
    match m with
      | Merge _ => ptree h
      | Split _ _ _ => ptree h * ptree h
(*
      | Combine _ => ptree h
      | Splice _ =>
        match h with 
          | 0 => Empty_set
          | S h' => ptree h'
        end
*)
    end%type.

  Definition as_mapOp (h : nat) (m : op) : opModel h m -> Model :=
    match m as m return opModel h m -> Model with
      | Merge _ => fun opm => as_map h opm
      | Split _ _ _ => fun opm => (as_map h (fst opm)) ++ (as_map h (snd opm))
(*      | Combine _ => fun opm => as_map h opm *)
    end.

  Definition firstPtrOp (h : nat) (m : op) : opModel h m -> ptr :=
    match m as m return opModel h m -> ptr with
      | Merge _ => fun m => firstPtr _ m
      | Split _ _ _ => fun m => firstPtr _ (fst m)
(*      | Combine _ => fun m => firstPtr _ m *)
    end.

  Definition repOp (h : nat) (o : op) (m : opModel h o) (min max : LiftOrder key) 
    (optr : option ptr) : hprop :=
    match o as o return opModel h o -> hprop with
      | Merge p        => fun m => [inv h m min max] * rep' h p optr m
      | Split lp kp rp => fun lkr => 
        let l := fst lkr in
        let r := snd lkr in
        [inv h l min (Val kp)] * [inv h r (Val kp) max] * 
        [lp = ptrFor _ l] * [rp = ptrFor _ r] *
        rep' h lp (Some (firstPtr _ r)) l * rep' h rp optr r
(*
      | Combine p      => fun m => [inv h m min max] * rep' h p optr m
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

    Definition splitContent : forall (h : nat) (lsM : list (BranchCell h))
      (pf : length lsM = SIZE),
      (list (BranchCell h) * ptree h * key * list (BranchCell h)).
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

    Ltac combine_le_le := idtac;
      match goal with
        | [ H : ?X <= ?Y, H' : ?Y <= ?X |- _ ] => 
          let H'' := fresh "F" in assert (X = Y); [omega|clear H; clear H']
      end.
    Ltac compress := idtac;
      let atomic X :=
        match X with 
          | _ _ => fail 1
          | _ _ _ => fail 1
          | _ _ _ _ => fail 1
          | _ _ _ _ _ => fail 1
          | _ _ _ _ _ _ => fail 1
          | _ _ _ _ _ _ _ => fail 1
          | _ _ _ _ _ _ _ _ => fail 1
          | _ => idtac
        end in
      repeat match goal with
               | [ H : ?X <= ?Y, H' : ?Y <= ?X |- _ ] => 
                 let H'' := fresh "F" in assert (X = Y); [omega|clear H; clear H']
               | [ H : ?X, H' : ?X |- _ ] => 
                 match type of X with
                   | Prop => clear H'
                 end
               | [ H : ?X = ?Y |- _ ] =>
                 atomic X;
                 match Y with 
                   | [_]%inhabited => rewrite H in *
                   | _ => match Y with 
                            | [_]%inhabited => fail 2
                            | _ => (try rewrite H in * ); clear H
                          end
                 end
               | [ H : Some _ = Some _ |- _ ] => inversion H; clear H
               | [ H : ?X = ?X |- _ ] => clear H
               | [ H : [_]%inhabited = [_]%inhabited |- _ ] => apply pack_injective in H
               | [ H : ?X = ?Y, H' : ?X = ?Z |- _ ] =>
                 match Y with
                   | Z => clear H'
                   | _ => rewrite H in H'
                 end
               | [ H : ?Y = ?X, H' : ?Z = ?X |- _ ] =>
                 match Y with
                   | Z => clear H'
                   | _ => rewrite <- H in H'
                 end
             end.
    Ltac red_prems :=
      repeat match goal with
               | [ H : ?X = [_]%inhabited, H' : context [ inhabit_unpack ?X _ ] |- _ ] =>
                 rewrite H in H'; simpl inhabit_unpack in H'
               | [ H : ?X = [_]%inhabited, H' : context [ inhabit_unpack' ?X _ ] |- _ ] =>
                 rewrite H in H'; simpl inhabit_unpack' in H'
               | [ H : ?X = [_]%inhabited |- context [ inhabit_unpack ?X _ ] ] =>
                 rewrite H; simpl inhabit_unpack
               | [ H : ?X = [_]%inhabited |- context [ inhabit_unpack' ?X _ ] ] =>
                 rewrite H; simpl inhabit_unpack'
               | [ H : ?X = [_]%inhabited, H' : ?X = [_]%inhabited |- _ ] =>
                 rewrite H in H'; apply pack_injective in H'
               | [ H : exists x, _ |- _ ] => destruct H
               | [ H : ?X = _, H' : context [ match ?X with
                                                | Some _ => _
                                                | None => _
                                              end ] |- _ ] => rewrite H in H'
             end.
      Ltac readBranchArray := idtac;
        match goal with
          | [ |- @repBranch _ _ ?A _ _ _ _ * ?P ==> ?Q ] =>
            match Q with
              | context [ array_plus A ?X ] => eapply (@repBranch_read' P X A); [ solve [ eauto ] |]
            end
          | [ H : array_plus ?A ?I = [?X]%inhabited |- @repBranch _ _ ?A _ _ _ _ * ?P ==> ?Q] =>
            match Q with
              | context [ X ] => eapply (@repBranch_read' P I A); [ solve [ eauto ] | ]
            end
          | [ H : array_plus ?A ?I = [_]%inhabited |- iter_sep ?F 0 ?LEN * ?P ==> ?R ] =>
            match F with
              | context [ array_plus A _ ] => 
                let H' := fresh in
                assert (H' : I < LEN); 
                  [ solve [ eauto ] 
                  | eapply (sp_index_hyp); [ eapply H' | clear H'; norm arith in * ] ]
            end
          | [ H : array_plus ?A ?I = [_]%inhabited |- iter_sep ?F ?ST ?LEN * ?P ==> ?R ] =>
            match F with
              | context [ array_plus A _ ] => 
                let H' := fresh in
                assert (H : I - ST < LEN);
                  [ solve [ eauto ]
                  | eapply (sp_index_hyp); [ eapply H' | clear H'; norm arith in * ] ]
            end
        end.
      Ltac readBranchArray_test := idtac;
        match goal with
          | [ |- @repBranch _ _ ?A _ _ _ _ * ?P ==> ?Q ] =>
            match Q with
              | context [ array_plus A ?X ] => eapply (@repBranch_read' P X A); [ solve [ eauto ] |]
            end
          | [ H : array_plus ?A ?I = [?X]%inhabited |- @repBranch _ _ ?A _ _ _ _ * ?P ==> ?Q] =>
            match Q with
              | context [ X ] => eapply (@repBranch_read' P I A); [ solve [ eauto ] | ]
            end
          | [ H : array_plus ?A ?I = [_]%inhabited |- iter_sep ?F 0 ?LEN * ?P ==> ?R ] =>
            match F with
              | context [ array_plus A _ ] => 
                let H' := fresh in
                assert (H' : I < LEN)
            end
          | [ H : array_plus ?A ?I = [_]%inhabited |- iter_sep ?F ?ST ?LEN * ?P ==> ?R ] =>
            match F with
              | context [ array_plus A _ ] => 
                let H' := fresh in
                assert (H : I - ST < LEN)
            end
        end.

    Lemma himp_elim_trivial : forall T (x : T) P Q,
      P ==> Q -> [x = x] * P ==> Q.
    Proof. clear.
      sep fail auto.
    Qed.
      
    Ltac canceler' tac :=
      let grw l r :=
        let HH := fresh in
        assert (HH : l = r); [ solve [ tac ] | rewrite HH; clear HH ]
      in
      cbv zeta;
      repeat search_conc ltac:(idtac; (** Eliminate the empty heaps on the RHS **)
        match goal with
          | [ |- _ ==> __ * _ ] => apply himp_empty_conc
        end);
      repeat search_prem ltac:(idtac;
        apply himp_empty_prem || (** Eliminate empty heaps on LHS **)
        search_conc ltac:(idtac; 
        (** Eliminate common heaps. The match prevents capturing existentials **)
          match goal with
            | [ |- ?p * _ ==> ?p * _ ] => apply himp_frame
            | [ |- [?X = ?X] * _ ==> _ ] => apply himp_elim_trivial
            | [ |- ?p ~~> _ * _ ==> ?p ~~> _ * _ ] => apply himp_frame_cell; trivial
(** TODO: This is potentially bad... **)
            | [ |- ?F ?X ==> ?F ?Y * _ ] =>
              let HH := fresh in
              assert (HH : X = Y); [ solve [ eauto ] | rewrite HH; clear HH; apply himp_frame ]
            | [ |- ?F ?A ?X ==> ?F ?A ?Y * _ ] =>
              let HH := fresh in
              assert (HH : X = Y); [ solve [ eauto ] | rewrite HH; clear HH; apply himp_frame ]
            | [ |- ?F ?X ?A ==> ?F ?Y ?A * _ ] =>
              let HH := fresh in
              assert (HH : X = Y); [ solve [ eauto ] | rewrite HH; clear HH; apply himp_frame ]
            | [ |- ?F _ _ _ ?D ==> ?F _ _ _ ?Z * _ ] =>
              let HH := fresh in
              assert (HH : D = Z); [ solve [ eauto ] | rewrite HH; clear HH; apply himp_frame ]
            | [ |- ?F ?A ?B ?C ?D ==> ?F ?W ?X ?Y ?Z * _ ] =>
              grw A W; grw B X; grw C Y; grw D Z; apply himp_frame
            | [ |- ?F ?C ?D ?E ?G ?H * _ ==> ?F ?Y ?Z ?P ?Q ?R * _ ] =>
              grw C Y; grw D Z; grw E P; grw G Q; grw H R; apply himp_frame
            | [ |- ?F ?B ?C ?D ?E ?G ?H * _ ==> ?F ?X ?Y ?Z ?P ?Q ?R * _ ] =>
              grw B X; grw C Y; grw D Z; grw E P; grw G Q; grw H R; apply himp_frame
            | [ |- ?F ?A ?B ?C ?D ?E ?G ?H * _ ==> ?F ?W ?X ?Y ?Z ?P ?Q ?R * _ ] =>
              grw A W; grw B X; grw C Y; grw D Z; grw E P; grw G Q; grw H R; apply himp_frame
          end));
      repeat search_conc ltac:(idtac;
        match goal with
          | [ |- _ ==> [?P] * _ ] => apply himp_inj_conc; [ solve [ tac ] | ]
        end).

    Ltac pick_existentials :=
      search_conc ltac:(idtac;
        match goal with
          | [ |- ?P ==> (Exists B :@ _, Exists w :@ B, ?PTR ~~> w) * _ ] =>
            match P with
              | context [ PTR ~~> ?V ] => 
                let T := type of V in
                eapply himp_ex_conc; exists T; eapply himp_ex_conc; exists V
            end
          | [ |- ?P ==> (Exists v :@ _, ?PTR ~~> v) * _ ] =>
            match P with
              | context [ PTR ~~> ?V ] => eapply himp_ex_conc; exists V
            end
          | [ |- ?P ==> (Exists v :@ _, ?PTR ~~> v * _) * _ ] =>
            match P with
              | context [ PTR ~~> ?V ] => eapply himp_ex_conc; exists V
            end
        end).

    Ltac combine_inh := idtac;
      match goal with
        | [ H : ?X = [_]%inhabited, H' : ?X = [_]%inhabited |- _ ] => rewrite H in H'; apply pack_injective in H'; rewrite H' in *
        | [ H : ?X = [_]%inhabited, H' : [_]%inhabited = ?X |- _ ] => rewrite H in H'; apply pack_injective in H'; rewrite H' in *
        | [ H : [_]%inhabited = ?X, H' : [_]%inhabited = ?X |- _ ] => rewrite <- H in H'; apply pack_injective in H'; rewrite H' in *
      end.

    Ltac tac :=
      intros; simpl;
      (repeat match goal with
                | [ H : exists x, _ |- _ ] => destruct H
                | [ H : _ /\ _ |- _ ] => destruct H
                | [ H : [_]%inhabited = ?X |- _ ] =>
                  match X with 
                    | [_]%inhabited => apply pack_injective in H
                    | [_]%inhabited => fail 1
                    | _ => symmetry in H
                  end
              end);
      repeat progress inhabiter; intro_pure;
      repeat (unpack_conc || pick_existentials);
      (repeat match goal with
                | [ H : ?X = [_]%inhabited, H' : ?X = [_]%inhabited |- _ ] => rewrite H in H'; apply pack_injective in H'; rewrite H' in *
                | [ H : ?X = [_]%inhabited, H' : [_]%inhabited = ?X |- _ ] => rewrite H in H'; apply pack_injective in H'; rewrite H' in *
                | [ H : [_]%inhabited = ?X, H' : [_]%inhabited = ?X |- _ ] => rewrite <- H in H'; apply pack_injective in H'; rewrite H' in *
                | [ H : ?X = [_]%inhabited, H' : context [ inhabit_unpack ?X _ ] |- _ ] => 
                  rewrite H in H'; simpl inhabit_unpack in H'
                | [ H : [_]%inhabited = ?X, H' : context [ inhabit_unpack ?X _ ] |- _ ] => 
                  rewrite <- H in H'; simpl inhabit_unpack in H'
              end);
      norm list in *; canceler' ltac:(eauto).

    Lemma div2_SIZE_lt_SIZE : div2 SIZE < SIZE.
    Proof.
      destruct SIZE. think. destruct n; think.
    Qed.

    Lemma div2_gt_0 : div2 SIZE > 0.
      destruct SIZE using ind_0_1_SS; simpl; think.
    Qed.
    Hint Immediate div2_gt_0.

    Lemma pred_div2_SIZE_lt_div2_SIZE : pred (div2 SIZE) < div2 SIZE.
    Proof.
      destruct SIZE; think. destruct n; think.
    Qed.

    Lemma repBranch_nil' : forall P Q h p ary LEN ST,
      P ==> Q ->
      {@ p :~~ array_plus ary i in p ~~> @None (key * ptr) | i <- ST + LEN } * P
      ==>
      repBranch h (rep' h) ary ST LEN nil p * Q.
    Proof. clear. 
      induction LEN; do 2 sep fail auto.
    Qed.

    Lemma repBranch_single_merge : forall P Q ary h (X:sigTS (fun _:key=>ptree h)) ST LEN OPTR,
      LEN > 0 ->
      P ==> (p :~~ array_plus ary ST in 
        p ~~> Some (projT1S X, ptrFor _ (projT2S X)) *
        rep' h (ptrFor _ (projT2S X)) (Some OPTR) (projT2S X) *
        {@ p :~~ array_plus ary i in p ~~> @None (key * ptr) | i <- (S ST) + (LEN - 1)}) * Q
      -> 
      P ==> repBranch h (rep' h) ary ST LEN (X :: nil) OPTR * Q.
    Proof. clear.
      intros. eapply himp_trans; [ eassumption | ]. canceler; clear H0 P Q.
      generalize dependent H. generalize dependent ST.
      destruct LEN. intros; think. intros.
        destruct LEN. norm arith. simpl. sep fail auto.
        sep fail auto.
        sep fail auto. eapply himp_trans. search_prem ltac:(eapply repBranch_nil'). sep fail auto. sep fail auto.
    Qed.

    Lemma repBranch_app_merge : forall P Q ary h (LS LS' : list (sigTS (fun _:key=>ptree h))) ST LEN OPTR,
      LEN >= length LS ->
      P ==> repBranch h (rep' h) ary ST (length LS) LS (match LS' with
                                                        | nil => OPTR
                                                        | a :: _ => firstPtr _ (projT2S a)
                                                      end) *
      repBranch h (rep' h) ary (ST + length LS) (LEN - length LS) LS' OPTR * Q
      -> 
      P ==> repBranch h (rep' h) ary ST LEN (LS ++ LS') OPTR * Q.
    Proof. clear.
      intros. eapply himp_trans; [ eassumption | ]. canceler.  clear H0 P Q.
      generalize dependent LEN. generalize dependent ST. induction LS.
        simpl; intros. norm arith. sep fail auto.
        simpl; intros. destruct LEN. elimtype False; omega.
            
        simpl. destruct LS. simpl; norm arith. destruct LS'; sep fail auto.
        simpl. sep fail auto. generalize (IHLS (S ST) LEN); intros.
        eapply himp_trans; [ | eapply H2; try omega ].
        repeat rewrite bubble_S. sep fail auto.
    Qed.

    Lemma repBranch_combine : forall h ary s i ls x0 e P Q,
      i < e
      -> P ==> repBranch h (rep' h) ary s i ls x0 *
               repBranch h (rep' h) ary (s + i) (e - i) (skipn i ls) x0 * Q
      -> P ==> repBranch h (rep' h) ary s e ls x0 * Q.
    Proof. clear.
      intros. eapply himp_trans; [ eapply H0 | ]. canceler. clear H0 P Q.
      generalize dependent i. generalize dependent ls. generalize dependent s. clear. induction e.
        intros. elimtype False. omega.
        destruct i. simpl. norm arith. sep fail auto.
        norm arith. simpl. destruct ls; sep fail auto. generalize (IHe (S s) nil i). norm list. intros. 
          cut (s + S i = S s + i); intros. rewrite H2. auto. omega.
        destruct ls. sep fail auto. generalize (IHe (S s) nil i). norm list. intros. 
          cut (s + S i = S s + i); intros. rewrite H2. search_prem ltac:(apply H1); omega. omega.
        sep fail auto. cut (s + S i = S s + i); intros. rewrite H1.
        search_prem ltac:(solve [ auto ]). omega.
    Qed.

    Lemma nth_error_skipn_cons : forall T i LS (x : T),
      nth_error LS i = Some x -> skipn i LS = x :: skipn (S i) LS.
    Proof. clear.
      induction i; destruct LS; simpl in *; firstorder; inversion H; auto.
    Qed.

    Lemma repBranchExcept_combine : forall h i LS OPTR ARY P Q,
      length LS <= SIZE
      -> i < SIZE
      -> P ==> repBranchExcept h ARY i LS OPTR * 
               (p :~~ array_plus ARY i in
                 match nth_error LS i with
                   | Some (existTS k' TR) => 
                     p ~~> Some (k', ptrFor _ TR) * rep' h (ptrFor _ TR) (Some (repBranch_nextPtr LS i OPTR)) TR
                   | None => p ~~> @None (key * ptr)
                 end) * Q
      -> P ==> repBranch h (rep' h) ARY 0 SIZE LS OPTR * Q.
    Proof. clear.
      Hint Resolve nth_error_None_length.
      intros. eapply himp_trans. eassumption. canceler; clear H1 P Q.
      unfold repBranchExcept. eapply himp_empty_conc'. eapply repBranch_combine; try eassumption.
      norm arith. sep fail auto. 
      case_eq (nth_error LS i); intros. destruct s.
      search_prem ltac:(idtac;
        search_conc ltac:(idtac;
          eapply himp_split; [ eapply repBranch_ignore_end | ])).
      eauto.
      cut (SIZE - i = S (SIZE - S i)); try omega; intros. rewrite H3. simpl.

      erewrite nth_error_skipn_cons; eauto. sep fail auto.
      unfold repBranch_nextPtr.
      destruct LS. norm list in *; discriminate. simpl.
      case_eq (nth_error LS i); intros. erewrite nth_error_skipn_cons; eauto. destruct s0; sep fail auto.
      rewrite skipn_len_rw. sep fail auto.
      eauto.
      sep fail auto.
      cut (SIZE - i = S (SIZE - S i)); try omega. intros. rewrite H3. simpl.
      norm list. sep fail auto. destruct LS; sep fail auto.
      rewrite skipn_len_rw. sep fail auto.
      cut (i >= length (s :: LS)); eauto.
    Qed.

    Lemma div2_pred : forall i, i < div2 SIZE -> div2 SIZE + i < SIZE.
    Proof.
      intros. rewrite <- (twice_half SIZE) at 2; eauto.
    Qed.      
    Hint Resolve div2_pred.
    Lemma pred_div2_SIZE_lt_SIZE : pred (div2 SIZE) < SIZE.
    Proof.
      generalize div2_SIZE_lt_SIZE; think.
    Qed.
    Hint Immediate pred_div2_SIZE_lt_SIZE.

    Lemma repBranch_nil_ignore : forall a c e d f g,
      repBranch a (rep' a) c d e nil f ==> repBranch a (rep' a) c d e nil g.
    Proof. clear.
      induction e. sep fail auto. intros. simpl. sep fail auto.
    Qed.

    Lemma repBranch_prefix_shift' : forall OPTR OPTR' h ary X LS ST,
      X < length LS ->
      repBranch h (rep' h) ary ST X (firstn (X + 1) LS) OPTR
      ==>
      repBranch h (rep' h) ary ST X (firstn X LS) 
        match nth_error LS X with
          | None => OPTR'
          | Some (existTS _ v) => firstPtr _ v
        end.
    Proof. clear. Opaque skipn. Opaque nth_error. Opaque firstn.
      induction X; [ sep fail auto | ]. intros; simpl repBranch.
        destruct LS. norm list. Focus 2. Transparent firstn. simpl firstn. Opaque firstn.
         simpl. sep fail auto. Transparent nth_error. simpl nth_error. Opaque nth_error.
         
         Transparent skipn. Transparent nth_error. Transparent firstn.
         destruct LS. simpl in *. elimtype False. omega.
         search_prem ltac:(search_conc ltac:(eapply himp_split; [ apply IHX; omega | ])).
         
         destruct X. simpl. destruct s0. sep fail auto.
         simpl. sep fail auto.

         sep fail auto.
    Qed.

    Lemma repBranch_prefix_shift : forall P Q OPTR OPTR' OPTR'' h ary X LS,
      X < length LS ->
      OPTR' = match nth_error LS X with
                | None => OPTR''
                | Some (existTS _ v) => firstPtr _ v
              end ->
      P ==> Q ->
      repBranch h (rep' h) ary 0 X (firstn (X + 1) LS) OPTR * P
      ==>
      repBranch h (rep' h) ary 0 X (firstn X LS) OPTR' * Q.
    Proof. clear. 
      intros. apply himp_split; try auto. rewrite H0. apply repBranch_prefix_shift'; auto.
    Qed.

    Definition moveBranch_nextOp : forall {h} {l} {k} {r} ary aryR (m : [ptree (S h)]) (opm : [opModel h (Split l k r)]),
      STsep (opm ~~ m ~~
               [length (fst (snd m)) = SIZE] *
               repBranch h (rep' h) ary 0 SIZE (fst (snd m)) (firstPtrOp h _ opm) *
               {@ p :~~ array_plus aryR j in p ~~> @None (key * ptr) | j <- 0 + (div2 SIZE - 1)} *
               repBranch h (rep' h) aryR (div2 SIZE - 1) (div2 SIZE + 1) 
                 (existTS (fun _:key => ptree h) k (fst opm) :: nil) (firstPtr _ (snd opm)))
            (fun _:unit => opm ~~ m ~~
               repBranch h (rep' h) ary 0 SIZE (firstn (div2 SIZE + 1) (fst (snd m)))
                 (repBranch_nextPtr (fst (snd m)) (div2 SIZE)
                   (firstPtrOp h _ opm)) *
               repBranch h (rep' h) aryR 0 SIZE 
                 (skipn (div2 SIZE + 1) (fst (snd m)) ++ (existTS (fun _:key => ptree h)) k (fst opm) :: nil)
                 (firstPtr _ (snd opm))).
      refine (fun h l k r ary aryR m opm =>
        {{ Fix2 (fun (i : nat) (_ : i < div2 SIZE) => opm ~~ m ~~
                  [length (fst (snd m)) = SIZE] *
                  repBranch h (rep' h) ary 0 SIZE (firstn (i + 1 + div2 SIZE) (fst (snd m)))
                  (repBranch_nextPtr (fst (snd m)) (i + div2 SIZE)
                    (firstPtrOp h _ opm)) *
                  {@ p :~~ array_plus aryR j in p ~~> @None (key * ptr) | j <- 0 + i} *
                  repBranch h (rep' h) aryR i (SIZE - i)
                    (skipn (i + 1 + div2 SIZE) (fst (snd m)) ++ (existTS (fun _:key => ptree h)) k (fst opm) :: nil)
                    (firstPtr _ (snd opm)))
                (fun _ _ (_:unit) => opm ~~ m ~~
                  repBranch h (rep' h) ary 0 SIZE (firstn (div2 SIZE + 1) (fst (snd m)))
                    (repBranch_nextPtr (fst (snd m)) (div2 SIZE)
                      (firstPtrOp h _ opm)) *
                  repBranch h (rep' h) aryR 0 SIZE 
                    (skipn (div2 SIZE + 1) (fst (snd m)) ++ (existTS (fun _:key => ptree h)) k (fst opm) :: nil)
                    (firstPtr _ (snd opm)))
                (fun self i pfI =>
                  match eq_nat_dec i 0 with
                    | left pfEq => {{ Return tt }}
                    | right pfNeq => 
                      v <- sub_array ary (div2 SIZE + i) (fun v' : option (key * ptr) => _) ;
                      upd_array aryR (pred i) v <@> _ ;;
                      upd_array ary (div2 SIZE + i) (@None (key * ptr)) <@> _ ;;
                      {{ self (pred i) (pred_le _ _ pfI) }}
                  end)
                (pred (div2 SIZE)) pred_div2_SIZE_lt_div2_SIZE }}); 
        try clear self; clear Spec SpecLocal Fn tK.
      Proof.
(** Proof works, but takes a while.
        solve [ tac; sep fail auto ].
        solve [ rewrite pfEq; tac; norm arith; tac; sep fail auto ].

        solve [ tac; search_prem ltac:(readBranchArray); tac; clear H3; sep fail idtac ].
        solve [ sep fail idtac ].

        tac; split_index. instantiate (1 := pred i); omega. tac. sep fail idtac.
        solve [ sep fail idtac ].

        solve [ tac; sep fail idtac ].
        solve [ sep fail idtac ].

        (** TODO : This case should be automated, but I don't really know where to start **)
        tac.
        Opaque skipn. Opaque firstn.
        rewrite nth_error_firstn in *; eauto.
        assert (div2 SIZE + i < length (fst (snd x0))); [ rewrite H3; eauto |].
        generalize (nth_error_len_lt _ H5); intros; fold ptree in *.
        destruct H6. rewrite H6. destruct x3.
        intro_pure. repeat search_prem ltac:(eapply himp_inj_prem; intro XX; clear XX).
        norm arith.

        rewrite S_pred in *; eauto. norm arith. simpl iter_sep.
        norm list.
        search_conc ltac:(eapply repBranchExcept_combine).
        rewrite <- H3 at 2; eauto.
        instantiate (1 := div2 SIZE + i); eauto.

        tac. unfold repBranchExcept. norm list. canceler.

        search_prem ltac:(search_conc ltac:(apply himp_split; [ apply repBranch_nil_ignore | ])).

        unfold repBranch_nextPtr. norm list.
        cut (S (pred i + div2 SIZE) = div2 SIZE + i); eauto; intros XX; rewrite XX; clear XX.
        rewrite H6.

        cut (S (i + div2 SIZE) = (i + div2 SIZE) + 1); eauto; intros XX; rewrite XX at 1; clear XX.
        rewrite (comm_plus (div2 SIZE) i).
        eapply himp_trans; [ eapply himp_trans; [ | eapply repBranch_prefix_shift ] | ].
        eapply himp_split. eapply himp_refl. eapply himp_refl. eauto. eauto. eapply himp_refl.
        eapply himp_split. instantiate (1 := firstPtr h p). fold ptree in *. rewrite (comm_plus i (div2 SIZE)). rewrite H6. apply himp_refl.

        cut (SIZE - pred i = S (SIZE - i)); try omega; intros XX; fold ptree in *; rewrite XX; clear XX.
        simpl repBranch. rewrite (comm_plus i (div2 SIZE)) in *.
        generalize (nth_error_skipn_ex _ _ H6); intros XX; destruct XX. fold ptree in *. rewrite H9.
        simpl. tac. rewrite S_pred; eauto.
        generalize (skipn_S_cons _ _ H9); intros XX; rewrite XX; clear XX.
        Transparent skipn.
        destruct x4. norm list. simpl.
        cut (nth_error (fst (snd x0)) (S (div2 SIZE + i)) = None). intros XX; simpl in XX. fold ptree in *. rewrite XX. sep fail auto.
        Hint Resolve nth_error_len_rw len_skipn_nil.
        eapply nth_error_len_rw; eapply len_skipn_nil. eapply skipn_S_cons. eassumption.
        cut (nth_error (fst (snd x0)) (S (div2 SIZE + i)) = Some s). intros XX; simpl in XX; fold ptree in *; rewrite XX. simpl. destruct s. sep fail auto.
        eapply skipn_nth_error. eapply skipn_S_cons. eassumption.

        solve [ sep fail auto ].
        tac.
        cut (pred (div2 SIZE) + 1 + div2 SIZE = SIZE). intros. rewrite H2. norm list.
        rewrite pred_minus.
        cut (SIZE - pred (div2 SIZE) = div2 SIZE + 1). intros XX; rewrite XX; clear XX.
        canceler.
        unfold repBranch_nextPtr.
        cut (S (pred (div2 SIZE) + div2 SIZE) = SIZE). intros XX; rewrite XX; clear XX.
        fold ptree in *. norm list. sep fail auto.
        rewrite <- (twice_half SIZE) at 3; eauto. 
        rewrite <- (twice_half SIZE) at 1; eauto.
        rewrite <- (twice_half SIZE) at 3; eauto.
        generalize pred_div2_SIZE_lt_div2_SIZE. omega.

        solve [ sep fail auto ].
**)
    Admitted.

    Lemma lastKey_nth_error : forall h i v' k' LS x6 x3,
      Val k' = x6
      -> nth_error LS i = Some (existTS (fun _:key => ptree h) k' v')
      -> lastKey LS x6 = lastKey LS x3.
    Proof. clear.
      destruct LS; intros; norm list in *; think.
    Qed.
    Lemma lastKey_firstn_nth_error : forall h i LS k' x9 x3,
      nth_error LS i = Some (existTS (fun _ : key => ptree h) k' x9)
      -> Val k' = lastKey (firstn (S i) LS) x3.
    Proof. clear.
      induction i; simpl.
      destruct LS; intros; try discriminate.  inversion H. simpl. auto.
      intros. destruct LS; try discriminate. erewrite IHi. Focus 2. eauto. simpl. eauto.
    Qed.
    Lemma inv_contextual_firstn : forall h' i x0 x3 x2 x,
      inv (S h') x0 x3 x2
      -> x = lastKey (firstn i (fst (snd x0))) x3
      -> contextual h'
      (fun (mi : LiftOrder key) (c : sigTS (fun _ : key => ptree h')) =>
        inv h' (projT2S c) mi (Val (projT1S c)))
      x3 x (firstn i (fst (snd x0))).
    Proof. clear.
      destruct x0. destruct y. simpl. generalize dependent l. generalize dependent p0. 
      induction i; simpl.
        intros; subst; order.
        fold ptree in *.
        intros; subst. destruct l. simpl in *. order.
          Transparent inv. simpl inv in *. Opaque inv. destruct H. destruct H.
          split; try tauto. eapply IHi. split. auto. eauto. eauto.
    Qed.
    Lemma inv_contextual_skipn : forall h' i x0 x3 x2 k' x6 x9,
      inv (S h') x0 x3 x2
      -> Val k' = x6
      -> nth_error (fst (snd x0)) i = Some (existTS (fun _ : key => ptree h') k' x9)
      -> contextual h'
      (fun (mi : LiftOrder key) (c : sigTS (fun _ : key => ptree h')) =>
        inv h' (projT2S c) mi (Val (projT1S c))) x6
      (lastKey (fst (snd x0)) x3) (skipn (S i) (fst (snd x0))).
    Proof. clear.
      destruct x0. destruct y. simpl. generalize dependent l. generalize dependent p0.
      fold ptree in *.
      induction i; simpl.
        destruct l; simpl; intros; try discriminate. inversion H0.
        destruct H. Transparent inv. fold inv in *. Opaque inv. simpl in *.
        inversion H1. subst. simpl in *. tauto.

        destruct l. simpl. intros; discriminate.
        intros. simpl. eapply IHi. Focus 2. eauto. Focus 2. eauto. 
        Transparent inv. simpl in *. think. Opaque inv. eapply H2.
    Qed.

    Lemma destruct_head : forall h (LS : list (sigTS (fun _:key => ptree h ))) Z X Y,
      length LS >= 1->
      Z >= 1 ->
      match firstn Z LS with
        | nil => X
        | a :: _ => firstPtr h (projT2S a)
      end =
      match head LS with
        | Some n => firstPtr h (projT2S n)
        | None => Y
      end.
    Proof.
      destruct LS; intros; simpl in *; firstorder. elimtype False; omega.
      destruct Z. elimtype False; omega. simpl. auto.
    Qed.
    Hint Resolve destruct_head.

    Lemma x_minus_div2_x : forall x, even x -> x - div2 x = div2 x.
      intros. rewrite <- (twice_half x) at 1; auto.
    Qed.
    Lemma repBranch_nil : forall P Q h p ary LEN ST,
      P ==> Q ->
      repBranch h (rep' h) ary ST LEN nil p * P
      ==> 
      {@ p :~~ array_plus ary i in p ~~> @None (key * ptr) | i <- ST + LEN } * Q.
    Proof. clear. Transparent iter_sep.
      induction LEN; do 2 sep fail auto.
    Opaque iter_sep.
    Qed.
    Lemma rep'_frame : forall P Q a b b' c c' d d',
      b = b' -> c = c' -> d = d' ->
      P ==> Q ->
      rep' a b c d * P ==> rep' a b' c' d' * Q.
    Proof. clear; sep fail auto.
    Qed.
  
    Definition splitContent' {h} {l} {k} {r} (lptr rptr: ptr)
      (lsM : list (BranchCell h)) (opm : opModel h (Split l k r)) :
      (ptree (S h) * ptree (S h)) :=
      match skipn (div2 SIZE) lsM with
        | nil => ((lptr, (nil, fst opm)), (rptr, (nil, snd opm)))
        | (existTS _ v) :: rr => 
          ((lptr, (firstn (div2 SIZE) lsM, v)),
           (rptr, (rr ++ existTS (fun _:key => ptree h) k (fst opm) :: nil, snd opm)))
      end.

    Lemma inv_contextual_firstn' : forall h' i ls x3 x,
      contextual h'
        (fun (mi : LiftOrder key) (c : BranchCell h') =>
          inv h' (projT2S c) mi (Val (projT1S c))) x3 
        (lastKey ls x3) ls
      -> x = lastKey (firstn i ls) x3
      -> contextual h'
      (fun (mi : LiftOrder key) (c : sigTS (fun _ : key => ptree h')) =>
        inv h' (projT2S c) mi (Val (projT1S c)))
      x3 x (firstn i ls).
    Proof. clear.
      induction i; simpl.
        intros; subst; order.
        intros; subst. destruct ls. simpl in *. order.
          simpl contextual in H.
          split; try tauto. eapply IHi. auto. tauto. simpl. auto.
    Qed.
    Lemma inv_contextual_skipn' : forall h' i ls x3 k' x6 x9,
      contextual h'
      (fun (mi : LiftOrder key) (c : BranchCell h') =>
          inv h' (projT2S c) mi (Val (projT1S c))) x3 
        (lastKey ls x3) ls
      -> Val k' = x6
      -> nth_error ls i = Some (existTS (fun _ : key => ptree h') k' x9)
      -> contextual h'
      (fun (mi : LiftOrder key) (c : sigTS (fun _ : key => ptree h')) =>
        inv h' (projT2S c) mi (Val (projT1S c))) x6
      (lastKey ls x3) (skipn (S i) ls).
    Proof. clear.
      fold ptree in *.
      induction i; simpl.
        destruct ls; simpl; intros; try discriminate. inversion H0.
        destruct H. Transparent skipn. Transparent nth_error. simpl in *.
        inversion H1. subst. simpl in *. tauto.

        destruct ls. simpl. intros; discriminate.
        intros. simpl. eapply IHi. Focus 2. eauto. Focus 2. eauto. 
        Transparent inv. simpl in *. think. Opaque inv.
    Qed.

    Lemma contextual_nth_inv : forall h x2 x0 N x5 p4 x6,
      contextual h
        (fun (mi : LiftOrder key) (c : BranchCell h) =>
         inv h (projT2S c) mi (Val (projT1S c))) x6 
        (lastKey x0 x6) x0
      -> nth_error x0 N = Some (existTS (fun _ : key => ptree h) x5 p4)
      -> x2 = lastKey (firstn N x0) x6
      -> inv h p4 x2 (Val x5).
    Proof. clear.
      intros. subst. generalize dependent x6. generalize dependent N. generalize dependent x0. 
      induction x0; simpl; intros.
        norm list in *. discriminate.
        destruct N. simpl in *. inversion H0. subst. simpl in *. tauto.
        simpl. apply IHx0. tauto. simpl in H0. tauto.
    Qed.

    Lemma split_inv_firstn : forall h x0 x5 p4 p2 x6,
      contextual h
        (fun (mi : LiftOrder key) (c : BranchCell h) =>
          inv h (projT2S c) mi (Val (projT1S c))) x6
        (lastKey x0 x6) x0
      -> nth_error x0 (div2 SIZE) =
         Some (existTS (fun _ : key => ptree h) x5 p4)
      -> inv (S h) (p2, (firstn (div2 SIZE) x0, p4)) x6 (Val x5).
    Proof. clear.
      Hint Resolve inv_contextual_firstn.
      Transparent inv. simpl inv. firstorder.
      generalize inv_contextual_firstn'. firstorder.
      Hint Resolve contextual_nth_inv.
      eauto.
    Qed.

    Lemma nth_error_lastKey : forall h N LS p4 x5 x6,
      nth_error LS N = Some (existTS (fun _ : key => ptree h) x5 p4)
      -> Val x5 = lastKey (firstn (S N) LS) x6.
    Proof. clear.
      induction N.
        destruct LS; simpl; intros. discriminate.
        inversion H. auto.
        destruct LS; simpl; intros; try discriminate.
        simpl in IHN. eapply IHN. eauto.
    Qed.
    Hint Resolve nth_error_lastKey.

    Lemma lastKey_last : forall h XS Y (X : sigTS (fun _:key => ptree h)),
      lastKey (XS ++ X :: nil) Y = Val (projT1S X).
    Proof. clear.
      induction XS; simpl; auto.
    Qed.

    Lemma contextual_append : forall h (F:forall x, sigTS (fun _ :key=>ptree h) -> Prop)  ls' max ls min mid,
      (forall a b c, OTeq KLOT a b -> F a c -> F b c) ->
      contextual h F min mid ls ->
      contextual h F mid max ls' ->
      contextual h F min max (ls ++ ls').
    Proof. clear.
      induction ls. simpl. intros.
        induction ls'. simpl in *.  order. simpl in *. think.
        simpl. think.
    Qed.

    Lemma KLsorted_subst : forall (X:list (sigTS value)) C (a b : LiftOrder key),
      OTeq KLOT a b -> KLsorted a X C -> KLsorted b X C.
    Proof. clear.
      induction X; simpl; firstorder.
      unfold KLsorted. simpl. left; order. unfold KLsorted. simpl. right; order.
      order.
    Qed.
    
    Lemma inv_subst : forall h X (a b c d: LiftOrder key),
      OTeq KLOT a b -> OTeq KLOT c d -> inv h X a c -> inv h X b d.
    Proof. clear.
      Hint Resolve KLsorted_subst.
      induction h; simpl; firstorder.
    Admitted.
    Hint Immediate inv_subst.


    Lemma split_inv_skipn : forall h (x0:ptree (S h)) x5 p4 x4 p3 p x1 x9 k x6,
      contextual h
        (fun (mi : LiftOrder key) (c : BranchCell h) =>
          inv h (projT2S c) mi (Val (projT1S c))) x6
        (lastKey (fst (snd x0)) x6) (fst (snd x0))
      -> inv h (fst x9) (lastKey (fst (snd x0)) x6) (Val k)
      -> inv h (snd x9) (Val k) x4
      -> nth_error (fst (snd x0)) (div2 SIZE) =
         Some (existTS (fun _ : key => ptree h) x5 p4)
      -> nth_error (fst (snd x0)) (S (div2 SIZE)) =
         Some (existTS (fun _ : key => ptree h) x1 p)
      -> inv (S h)
         (p3,
           (existTS (fun _ : key => ptree h) x1 p
             :: skipn (S (S (div2 SIZE))) (fst (snd x0)) ++
             existTS (fun _ : key => ptree h) k (fst x9) :: nil, 
             snd x9)) (Val x5) x4.
    Proof. clear. Opaque skipn.
      intros. simpl inv; firstorder. eapply contextual_nth_inv. eauto. eauto.
      eauto.
      rewrite lastKey_last. simpl. eapply contextual_append; eauto.      
      eapply inv_contextual_skipn'; eauto. 
      simpl. eauto.
      rewrite lastKey_last. simpl. eauto.
      Transparent skipn.
    Qed.

    Lemma SIZE_is_two : {SIZE = 2} + {S (div2 SIZE) < SIZE}.
    Proof. clear Spec SpecLocal Fn tK.
      destruct (lt_eq_lt_dec SIZE 2). destruct s.
      elimtype False. omega. firstorder.
      right. rewrite <- (twice_half SIZE) at 2; eauto.  cut (1 < div2 SIZE). omega.
      induction SIZE using ind_0_1_SS; try solve [ elimtype False; omega ].
      induction n using ind_0_1_SS; try solve [ elimtype False; omega ]. inversion SIZE_even. inversion H0. inversion H2. inversion H4.
      simpl. omega.
    Qed.

    Lemma split_merge_single : forall h p0 x7 k x5 p2 p3,
      inv h p0 x7 (Val k)
      -> inv h p3 (Val k) x5
      -> inv (S h) (p2, (existTS (fun _ : key => ptree h) k p0 :: nil, p3)) x7 x5.
    Proof. clear.
      Transparent inv. simpl; firstorder. Opaque inv.
    Qed.
    Hint Resolve split_merge_single.
    
    Lemma skipn_nil_next_nil : forall T n n' (ls : list T),
      skipn n ls = nil
      -> n' >= n
      -> skipn n' ls = nil.
    Proof. clear.
    Admitted.

    Lemma repBranch_combineRead : forall (h : nat) (ary : array) (s i : nat) (ls : list (BranchCell h))
      (x0 : ptr) (e : nat) (P Q : hprop),
      i < e ->
      P ==>
      repBranch h (rep' h) ary s i ls x0 * 
      match skipn i ls with
        | nil =>
          p :~~ array_plus ary (s + i) in
          p ~~> @None (key * ptr)
        | f :: tl =>
          p :~~ array_plus ary (s + i) in
          let p' := ptrFor h (projT2S f) in
          p ~~> Some (projT1S f, ptrFor h (projT2S f)) *
          match tl with
            | nil => rep' h p' (Some x0) (projT2S f)
            | r :: _ => rep' h p' (Some (firstPtr h (projT2S r))) (projT2S f)
          end
      end *
      repBranch h (rep' h) ary (s + S i) (e - S i) (skipn (S i) ls) x0 * Q ->
      P ==> repBranch h (rep' h) ary s e ls x0 * Q.
    Proof. clear. Opaque skipn.
      intros. eapply repBranch_combine; try eassumption. eapply himp_trans; [ eassumption | ].
      canceler. cut (e - i = S (e - S i)); try omega; intros XX; rewrite XX; clear XX.
      simpl. case_eq (skipn i ls); intros.
      sep fail auto. cut (s + S i = S (s + i)); try omega; intros XX; rewrite XX; clear XX.

      erewrite skipn_nil_next_nil; eauto. sep fail auto.
      sep fail auto. cut (s + S i = S (s + i)); try omega; intros XX; rewrite XX; clear XX.
      erewrite skipn_S_cons; eauto. sep fail auto.
      Transparent skipn.
    Qed.

    Lemma odd_merge : forall h ary ll n  k p0 l OPTR',
      ll = length l ->
      repBranch h (rep' h) ary n ll l (firstPtr h p0) ==>
      repBranch h (rep' h) ary n ll
      (l ++ existTS (fun _ : key => ptree h) k p0 :: nil) 
      OPTR'.
    Proof. clear.
      induction ll. sep fail auto.
      destruct l. sep fail auto. discriminate.
      sep fail auto. sep fail auto. apply himp_comm_conc. apply himp_split. apply IHll. auto.
      destruct l; sep fail auto.
    Qed.
    Lemma skipn_app : forall T (ls ls' : list T) N,
      N = length ls -> skipn N (ls ++ ls') = ls'.
    Proof.
      induction ls; simpl in *; intros; subst; firstorder.
    Qed.

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
               Q (fst res'))
            (fun res : RES (S h) => min ~~ max ~~ optr ~~ m ~~ 
               opm :~~ projT2 (snd res) in opm' :~~ projT2 (snd res') in
               repOp (S h) (projT1 (snd res)) opm min max optr * Q (fst res) *
               [firstPtrOp _ _ opm = match head (fst (snd m)) return ptr with
                                       | None => firstPtrOp _ _ opm'
                                       | Some n => firstPtr _ (projT2S n)
                                     end] *
               [fst res = fst res'] *
               [List.flat_map (fun x => @as_map h (projT2S x)) (fst (snd m)) ++ as_mapOp _ _ opm' = as_mapOp _ _ opm]).
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

              (** put (k,l) in aryR at SIZE / 2 **)
              upd_array aryR (pred (div2 SIZE)) (Some (k,l)) <@> _ ;;

              (** copy indicies [SIZE / 2, SIZE) into aryR (write None to the rest) **)
              moveBranch_nextOp ary aryR m opm <@> _ ;;

              (** **)
              pR <- New (mkNode (S h) aryR (Some r)) ;
              nxtL <- sub_array ary (div2 SIZE) (fun v : option (key * ptr) => _ ) ;
              match nxtL as nxtL' return nxtL = nxtL' -> _ with 
                | None           => fun _ => {{ !!! }}
                | Some (kM,nxtL) => fun _ =>
                  (** write None to ary[SIZE/2] **)
                  upd_array ary (div2 SIZE) (@None (key * ptr)) <@> _ ;;
                  p ::= mkNode (S h) ary (Some nxtL) ;;
                  {{ Return (rt, existT _ (Split p kM pR)
                        (opm ~~~' inhabit_unpack m (fun pM =>
                           splitContent' p pR (fst (snd pM)) opm))) }}
              end (refl_equal _)
            else
              (** we can just merge **)
              upd_array ary full (Some (k, l)) <@> _ ;;
              p ::= mkNode (S h) ary (Some r) ;;
              let rM : [opModel (S h) (Merge p)] := 
                opm ~~~' m ~~~
                  let (lM,rM) := opm in
                  (p, (fst (snd m) ++ ((existTS (fun _ => ptree h) k lM) :: nil), rM)) in
              {{ Return (rt, existT _ (Merge p) rM) }}
(** Don't actually need these yet
          | (existT (Combine p') opm)  => fun pf => _ (** TODO **)
(*              let rM : [opModel (S h) (Merge p)] := 
                opm ~~~' m ~~~
                  let lM := fst (fst opm) in
                  let kM := snd (fst opm) in 
                  let rM := snd opm in
                  (p, (fst (snd m) ++ ((existTS (BranchCell h) kM lM) :: nil), rM)) in
              {{ Return (rt, existT _ (Merge p) rM) }}
*)
(**
          | Splice p'   => fun opm => _ (** TODO: a little crazy and not completely necessary **)
**)
**)
        end (refl_equal _)); try clear Fn.
    Proof.
(**
      solve [ tac; sep fail auto ].
      solve [ sep fail auto ].
      solve [ tac; sep fail auto ].
      solve [ sep fail auto ].
      solve [ sep fail auto ].
      rewrite pf. unfold rt in *. unfold rM in *. subst. simpl. tac. fold ptree in *.
      destruct v. inversion H14. unfold rM in *. clear rM. subst. simpl. destruct x8. 
      simpl in *. apply pack_injective in H8. inversion H8. simpl.
      canceler' ltac:(eauto).
      search_prem ltac:(eapply rep'_ptrFor_add); intros. t.
      cut_pure. destruct x0. destruct p1. simpl in *. destruct l; auto. solve [ think ]. (** TODO: probably want a lemma for this **)

      (** Split **)
      solve [ sep fail auto ].
      solve [ sep fail auto ].
      tac. search_prem ltac:(readBranchArray). tac. sep fail idtac.
      solve [ sep fail idtac ].
     
      tac. rewrite S_pred. rewrite x_minus_div2_x. norm arith. rewrite pred_minus.
      canceler' ltac:(eauto).
      generalize dependent res. intros res rt pf. rewrite pf. intros. simpl projT1.
      simpl in H7. combine_inh. simpl firstPtrOp. canceler. simpl repBranch. tac.

      eauto.

      rewrite S_pred.
      try search_prem ltac:(idtac;
        match goal with 
          | [ |- iter_sep _ _ _ * _ ==> _ ] => idtac "searching";
            search_conc ltac:(idtac;
              match goal with
                | [ |- _ ==> repBranch _ _ _ _ _ _ _  * _ ] => idtac "found";
                  apply repBranch_nil'
              end)
        end).
      search_prem ltac:(search_conc ltac:(idtac;
        match goal with
          | [ |- rep' _ _ _ _ * _ ==> rep' _ _ _ _ * _ ] => eapply rep'_frame; [ solve [ eauto ] | solve [ eauto ] | solve [ eauto ] | ]
        end)).
      sep fail idtac. eauto. eauto. eauto. simpl.

      solve [ sep fail idtac ].
      solve [ sep fail idtac ].
      solve [ sep fail idtac ].


      tac. search_prem ltac:(readBranchArray). tac. clear H19. sep fail idtac.

      solve [ sep fail idtac ].
      solve [ tac; sep fail idtac ].
      solve [ sep fail idtac ].

      solve [ tac; sep fail idtac ].
      solve [ sep fail idtac ].
      solve [ sep fail idtac ].

      Opaque nth_error. Opaque skipn. Opaque firstn.
      tac.
      generalize dependent x8. rewrite H20 in *.
      generalize dependent x9. rewrite pf in *.
      fold ptree in *. intros. simpl in *. intro_pure.
      repeat search_prem ltac:(apply himp_inj_prem; intros XX; clear XX).
      clear H20. subst. clear H19. unfold rt in *. simpl in *. clear H21.
      fold ptree in *. rewrite H10 in *.
      cut (nth_error (firstn (div2 SIZE + 1) (fst (snd x0))) (div2 SIZE) = nth_error (fst (snd x0)) (div2 SIZE)); [ intros | norm list; eauto ].
      fold ptree in *. rewrite H in *. norm arith in *.
      case_eq (nth_error (fst (snd x0)) (div2 SIZE)); [ | intros XX; rewrite XX in *; simpl in *; discriminate ].
      destruct s. intros XX. rewrite XX in *.

      fold ptree in *. unfold rt in *; clear rt. canceler' ltac:(eauto).
      destruct x8. simpl in *. destruct p2; simpl in *. destruct p4; simpl in *.
      destruct p3; simpl in *. destruct p5; simpl in *. simpl.
      subst; simpl in *.
      try search_conc ltac:(idtac;
        match goal with
          | [ |- _ ==> (Exists v :@ array, _) * _ ] => eapply himp_ex_conc
        end).
      exists ary.
      try search_conc ltac:(idtac;
        match goal with
          | [ |- _ ==> (Exists v :@ array, _) * _ ] => eapply himp_ex_conc
        end).
      exists aryR. 
      repeat match goal with
               | [ H : [_]%inhabited = [_]%inhabited |- _ ] => apply pack_injective in H
             end.
      unfold splitContent' in *.
      cut (skipn (div2 SIZE) (fst (snd x0)) = existTS (fun _ : key => ptree h) x5 p1 :: skipn (S (div2 SIZE)) (fst (snd x0))); intros (*** TODO ***).
      rewrite H0 in *. inversion H8. fold ptree in *. norm list.
      fold ptree in *. canceler' ltac:(eauto). inversion H13. subst. auto. subst.
      
      unfold repBranchExcept. rewrite H10 in *. clear H10. norm arith. norm list. rewrite XX.
      inversion H13. subst. rewrite H18 in *; clear H18.
      canceler' ltac:(eauto). unfold repBranch_nextPtr. norm list.
      tac.
      case_eq (nth_error (fst (snd x0)) (S (div2 SIZE))); intros.

      erewrite skipn_nth_error_skipn; [ | eassumption ].
      simpl. destruct s. simpl. norm list.
      search_conc ltac:(eapply repBranch_combine). instantiate (1 := div2 SIZE). eauto.
      norm arith.
      cut (SIZE - div2 SIZE = S (pred (div2 SIZE))); intros. rewrite H3. simpl.
      norm list. tac.
      cut (SIZE - S (div2 SIZE) = pred (div2 SIZE)); eauto; intros XX'; rewrite XX'; clear XX'.
      canceler.
      search_prem ltac:(search_conc ltac:(apply himp_split; [ apply repBranch_nil_ignore | ])).
      cut (S (div2 SIZE) = div2 SIZE + 1); eauto; intros. rewrite H4 at 1.
      search_prem ltac:(search_conc ltac:(eapply repBranch_prefix_shift)); eauto.
      instantiate (1 := p3). fold ptree in *. rewrite XX. auto.


      assert (S
       (length
          (skipn (S (S (div2 SIZE))) (fst (snd x0)) ++
           existTS (fun _ : key => ptree h) k (fst x9) :: nil)) <= SIZE).
      rewrite app_length. simpl. norm arith.
      rewrite length_skipn. omega.
      canceler' ltac:(eauto).
      
      
      assert (flat_map (fun x8 : BranchCell h => as_map h (projT2S x8)) (fst (snd x0)) ++
           as_map h (fst x9) ++ as_map h (snd x9) =
           flat_map (fun x8 : BranchCell h => as_map h (projT2S x8))
           (firstn (div2 SIZE) (fst (snd x0))) ++
           as_map h p4 ++
           as_map h p ++
           flat_map (fun x8 : BranchCell h => as_map h (projT2S x8))
           (skipn (S (S (div2 SIZE))) (fst (snd x0)) ++
             existTS (fun _ : key => ptree h) k (fst x9) :: nil) ++
           as_map h (snd x9)).
      rewrite (ls_expand _ (fst (snd x0))) at 1; [ | eapply XX ]. norm list.
      repeat rewrite flat_map_app. simpl. norm list. f_equal. f_equal. repeat rewrite <- app_ass. f_equal.
      f_equal. fold ptree in *. rewrite (skipn_nth_error_skipn _ _ H2). simpl. auto.

      Hint Resolve split_inv_firstn split_inv_skipn.      
      canceler' ltac:(eauto).
      sep fail idtac.
      
      rewrite <- (twice_half SIZE) at 1. rewrite S_pred. eauto. eauto. eauto.

      (** This is the other size of the case_eq **)
      Opaque inv.
      norm list; simpl. canceler' ltac:(eauto).
      cut (SIZE = 2); intros. rewrite H3 in *; clear H3. 
      assert (flat_map (fun x1 : BranchCell h => as_map h (projT2S x1)) (fst (snd x0)) ++
              as_map h (fst x9) ++ as_map h (snd x9) =
              flat_map (fun x1 : BranchCell h => as_map h (projT2S x1))
              (firstn (div2 2) (fst (snd x0))) ++
              as_map h p4 ++ as_map h (fst x9) ++ as_map h (snd x9)).
      repeat rewrite <- app_ass. f_equal. f_equal.
      simpl in *.
      destruct (fst (snd x0)). simpl in *. elimtype False; omega.
      destruct l. simpl in *; elimtype False; omega. simpl. norm list. simpl in *.
      cut (l = nil); intros; subst. simpl.  norm list. destruct s0. simpl. f_equal. f_equal. inversion H. auto.
      Lemma firstn_S_cons : forall T n (x:T) xs,
        firstn (S n) (x :: xs) = x :: firstn n xs.
      Proof. Transparent firstn. intros; reflexivity. Opaque firstn.
      Qed. Transparent firstn. simpl firstn. Opaque firstn. simpl flat_map. norm list. auto.
      simpl in *. Transparent nth_error. simpl nth_error in XX. inversion XX. auto. simpl in H2. destruct l; auto; discriminate. Opaque nth_error.
      canceler' ltac:(auto). simpl in *. destruct (fst (snd x0)); try discriminate.
      destruct l; try discriminate.  sep fail auto. inversion H. simpl.
      assert (inv (S h)
        (p3, (existTS (fun _ : key => ptree h) k (fst x9) :: nil, snd x9))
        (Val x5) x4).
      Transparent inv. simpl. Opaque inv. intuition eauto. Transparent nth_error. Transparent firstn. simpl in H12.  
      rewrite H12 in *. simpl in *. 
      destruct l; simpl in *; eauto. discriminate. sep fail auto.
      
      cut (length (fst (snd x0)) = SIZE); try omega; intros. 
      destruct SIZE_is_two; auto. cut (S (div2 SIZE) >= length (fst (snd x0))); eauto.
      
      erewrite skipn_nth_error_skipn; eauto.
      rewrite H10 in *. auto.


      tac. elimtype False.
      cut (length (fst (snd x0)) = SIZE); eauto; intros.
      destruct SIZE_is_two; try rewrite e in *; simpl in *.
      fold ptree in *.
      destruct (fst (snd x0)); simpl in *; try discriminate.
      destruct l0; simpl in *; try discriminate.
      destruct l0; simpl in *; try omega. destruct s0. rewrite _H0 in *. discriminate.
      norm arith in *. rewrite nth_error_firstn in H9; eauto.
      cut (length (fst (snd x0)) <= div2 SIZE); intros.
      fold ptree in *. rewrite H19 in *. omega. eapply nth_error_len. rewrite _H0 in *.
      fold ptree in *.
      case_eq (nth_error (fst (snd x0)) (div2 SIZE)); eauto; intros. rewrite H20 in *. destruct s. discriminate.
      solve [ sep fail idtac ].

      (** Don't need to split **)
      tac. search_prem ltac:(readBranchArray). tac. sep fail idtac.
      Ltac sep_unify :=
        intros; canceler; eapply himp_refl.
      solve [ sep_unify ].

      solve [ tac; sep fail idtac ].
      solve [ sep_unify ].
      solve [ sep_unify ].

      tac. unfold rt in *; clear rt. unfold rM in *; clear rM.  
      generalize dependent x10. rewrite H17 in *; clear H17.
      generalize dependent x8. rewrite pf in *; clear pf.
      subst. simpl in *. fold ptree in *. intros.
      repeat search_prem ltac:(apply himp_inj_prem; intros).
      repeat match goal with 
               | [ H : [_]%inhabited = [_]%inhabited |- _ ] => apply pack_injective in H
             end.
      norm arith in *; norm list in *.
      destruct x2. destruct x10. destruct p3. simpl in *.
      search_conc ltac:(idtac;
        match goal with
          | [ |- _ ==> (Exists v :@ array, _) * _ ] => eapply himp_ex_conc
        end).
      exists ary. inversion H10.
      rewrite <- H8 in *; clear H8. simpl.
      rewrite H13 in *; clear H13. rewrite H15 in *; clear H15.
      rewrite H21 in *; clear H21. rewrite H19 in *; clear H19.
      rewrite <- H20 in *; clear H20. 
      repeat match goal with
               | [ H : ?X = ?X |- _ ] => clear H
               | [ H : ?X, H' : ?X |- _ ] => clear H'
             end.
      clear H16. simpl in *.
      canceler' ltac:(eauto).
      (** nil **)
      case_eq (fst (snd x0)); intros.
      rewrite H in *. simpl in *. unfold repBranchExcept. simpl. tac.
      cut (SIZE = S (SIZE - 1)); eauto; intros. rewrite H2 at 2. simpl.
      tac. fold ptree in *.
      apply himp_comm_prem.
      search_prem ltac:(idtac;
        search_conc ltac:(idtac;
          eapply himp_split; [ eapply repBranch_nil_ignore | ] )).
      cut_pure. sep fail idtac.
      eauto.
      
      (** Not nil **)
      match goal with
        | [ H : array_plus ?ARY ?I = [?PTR]%inhabited |- ?P ==> ?Q ] => idtac;
          match P with 
            | context [ PTR ~~> _ ] => idtac;
              match Q with 
                | context [ repBranch _ _ ARY 0 ?LEN _ _ ] => idtac ST I LEN;
                  let H' := fresh in
                  assert (I < LEN); 
                    [ solve [ eauto ]
                    | search_conc ltac:(idtac;
                      match goal with
                        | [ |- _ ==> repBranch _ _ _ _ _ _ _ * _ ] =>
                          apply (repBranch_combineRead _ _ _ _ _ H2)
                      end); clear H' ]
                | context [ repBranch _ _ ARY ?ST ?LEN _ _ ] => idtac ST I LEN;
                  let H'' := fresh in
                  assert (H'' : I >= ST); 
                    [ solve [ eauto ]
                    | let H' := fresh "H" in
                      assert (I - ST < LEN); 
                        [ solve [ eauto ]
                        | search_conc ltac:(idtac;
                          match goal with
                            | [ |- _ ==> repBranch _ _ _ _ _ _ _ * _ ] =>
                              apply (repBranch_combineRead _ _ _ _ _ H2)
                          end); clear H'' H' ]]
              end
          end
      end; norm arith in *. norm list.
      unfold repBranchExcept.
      rewrite H. norm list.
      assert (skipn (S (length (s :: l)))
        (s :: l ++ existTS (fun _ : key => ptree h) k p0 :: nil) = nil).
      simpl length. apply skipn_len_rw. repeat progress (rewrite app_length || simpl length). omega.
      rewrite H0.
      search_prem ltac:(search_conc ltac:(apply himp_split; [ apply repBranch_nil_ignore | ])).
      cut (skipn (length (s :: l))
       (s :: l ++ existTS (fun _ : key => ptree h) k p0 :: nil) = existTS (fun _ : key => ptree h) k p0 :: nil); intros.
      rewrite H2. tac.
      assert (as_map h (projT2S s) ++
        flat_map (fun x10 : BranchCell h => as_map h (projT2S x10)) l ++
        as_map h p0 ++ as_map h p3 =
        as_map h (projT2S s) ++
        flat_map (fun x10 : BranchCell h => as_map h (projT2S x10))
        (l ++ existTS (fun _ : key => ptree h) k p0 :: nil) ++ 
        as_map h p3).
      f_equal. repeat rewrite flat_map_app. simpl. norm list. auto.

      Lemma split_merge : forall h p0 x7 k x5 p2 p3 l,
        contextual h
          (fun (mi : LiftOrder key) (c : BranchCell h) =>
           inv h (projT2S c) mi (Val (projT1S c))) x7
          (lastKey l x7) l
        -> inv h p0 (lastKey l x7) (Val k)
        -> inv h p3 (Val k) x5
        -> inv (S h) (p2, (l ++ existTS (fun _ : key => ptree h) k p0 :: nil, p3)) x7 x5.
      Proof. clear.
        Transparent inv. simpl; firstorder.
        Hint Resolve inv_subst.
        eapply contextual_append; eauto.
        rewrite lastKey_last. simpl. firstorder.
        rewrite lastKey_last. simpl. eauto.
      Qed.
      Hint Resolve split_merge.
      
      rewrite H in *.
      assert (inv (S h) (p2, ((s :: l) ++ existTS (fun _ : key => ptree h) k p0 :: nil, p3)) x7 x5).
      eapply split_merge; auto.
      assert (S (length (l ++ existTS (fun _ : key => ptree h) k p0 :: nil)) <= SIZE).
      repeat (rewrite app_length || simpl). rewrite H12 in *. simpl in *. omega.

      canceler' ltac:(assumption).
      assert (x6 = x9). simpl in *. rewrite H4 in H9. apply pack_injective; auto. rewrite H15 in *.
      cut (repBranch h (rep' h) ary 1 (length l) l (firstPtr h p0) ==> 
           repBranch h (rep' h) ary 1 (length l)
           (l ++ existTS (fun _ : key => ptree h) k p0 :: nil) 
           (firstPtr h p3)); intros.
      search_prem ltac:(search_conc ltac:(apply himp_split; [ apply H16 | ])).
      canceler.
      destruct l; sep fail auto.

      apply odd_merge; auto.
      simpl. Transparent skipn. simpl.
      rewrite skipn_app; auto.
**)
    Admitted.

    Definition mergeOpInternal : forall (min midL max : [LiftOrder key]) (midH : [key]) (h : nat)
      (p : ptr) (ary : array) (nxt : ptr) (optr : [option ptr]) (pos : nat) (res' : RES h) (m : [ptree (S h)]),
      STsep (min ~~ midL ~~ midH ~~ max ~~ m ~~ optr ~~ opm :~~ projT2 (snd res') in
               let o := projT1 (snd res') in
               let lsM  := fst (snd m) in
               let nxtM := snd (snd m) in
               p' :~~ array_plus ary pos in
               p ~~> mkNode (S h) ary (Some nxt) *
               Exists p'' :@ ptr,
               p' ~~> Some (midH, p'') * 
               [array_length ary = SIZE] *
               [midL = lastKey (firstn pos lsM) min] *
               [Val midH = lastKey (firstn (S pos) lsM) min] *
               [contextual h (fun mi c => inv h (projT2S c) mi (Val (projT1S c))) min midL (firstn pos lsM)] *
               [contextual h (fun mi c => inv h (projT2S c) mi (Val (projT1S c))) (Val midH) (lastKey lsM (Val midH)) (skipn (S pos) lsM)] *
               [inv h nxtM (lastKey lsM (Val midH)) max] *
               repBranch h (rep' h) ary 0 pos lsM (firstPtrOp _ _ opm) *
               repBranch h (rep' h) ary (S pos) (SIZE - S pos) (skipn (S pos) lsM) (firstPtr _ nxtM) *
               rep' h nxt optr nxtM *
               repOp h o opm midL (Val midH) (repBranch_nextPtr lsM pos (Some (firstPtr h nxtM))) *
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


    (** Final Definition **)
    Lemma KLsorted_app : forall (V:key->Set) (l:list (sigTS V)) r max min,
      KLsorted min (l ++ r) max <->
      KLsorted min l (lastKey l min) /\ KLsorted (lastKey l min) r max.
    Proof. clear. split; generalize dependent min; generalize dependent max; generalize dependent r.
      induction l; [auto| unfold KLsorted in *; intros; simpl in *; instantiate; think].
      induction l; unfold KLsorted in *; intros; simpl in *; instantiate; think.        
    Qed.

    Lemma inv_KLsorted_map : forall h ls tr min max,
      inv h tr min max 
      -> ls = as_map h tr
      -> KLsorted min ls max.
    Proof. clear.
      Transparent inv.
(**
      induction h. simpl. auto.
      simpl. fold ptree in *. destruct tr. destruct p. induction l. simpl. think.
      simpl in *. think.
      rewrite app_ass.
      rewrite KLsorted_app. split; auto.
**)
    Admitted.
    Hint Resolve inv_KLsorted_map.

    Lemma inv_Next : forall h' tr p1 x2 x3 l lk,
      inv (S h') tr x3 x2
      -> p1 = snd (snd tr)
      -> l = fst (snd tr)
      -> lk = lastKey l x3
      -> inv h' p1 lk x2.
    Proof. clear. fold ptree.
      intros; simpl in *. destruct tr as [ ? [ ? ? ] ]. simpl in *. subst. tauto.
    Qed.
    Hint Resolve inv_Next.

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

    Opaque inv.

    Lemma inv_contextual : forall h' x0 x3 x2 x,
      inv (S h') x0 x3 x2
      -> x = lastKey (fst (snd x0)) x3
      -> contextual h'
           (fun (mi : LiftOrder key) (c : sigTS (fun _ : key => ptree h')) =>
             inv h' (projT2S c) mi (Val (projT1S c))) x3 x 
           (fst (snd x0)).
    Proof. clear.
      Transparent inv. unfold inv. destruct x0. destruct y. simpl. firstorder. subst; auto. Opaque inv.
    Qed.

    Hint Resolve pack_injective.

        Lemma nth_error_len_Some : forall i T (x:list T) t,
          nth_error x i = Some t -> length x > i.
        Proof. clear.            
          induction i; destruct x; simpl in *; firstorder; try discriminate.
          apply IHi in H. omega.
        Qed.
        Hint Resolve nth_error_len_Some.

        Lemma nth_error_skipn_ex : forall T i (LS : list T) t,
          nth_error LS i = Some t
          -> exists LS', skipn i LS = t :: LS'.
        Proof. clear.
          induction i. simpl. destruct LS; intros. discriminate. exists LS. inversion H; auto.
          intros. destruct LS. norm list in *. discriminate. simpl in *. firstorder.
        Qed.

        Lemma skipn_nth_error : forall T i LS (a:T) b,
          skipn i LS = a :: b -> nth_error LS (S i) = match b with 
                                                        | nil => error
                                                        | a :: _ => Some a
                                                      end.
        Proof. clear.
          induction i; simpl; intros; subst. auto. destruct LS; try discriminate. 
          eapply IHi in H. rewrite <- H. simpl. auto.
        Qed.


        Lemma skipn_cons_len : forall T i ls (a:T) b,
          skipn i ls = a :: b -> length ls >= S i.
        Proof. clear.
          induction i. simpl; intros; subst; simpl; omega. simpl. destruct ls. simpl; intros. discriminate. simpl. intros.
          apply IHi in H. omega.
        Qed.

        Lemma skipn_nth_error_S : forall (T : Type) LS i (x s : T) x0,
          skipn i LS = x :: s :: x0 ->
          nth_error LS (S i) = Some s.
        Proof. clear.
          induction LS. intros; norm list in *. discriminate.
          simpl. intros. destruct i. simpl in *. inversion H. auto.
          eapply IHLS. simpl in *. eauto.
        Qed.
      


      Lemma nth_error_lastKey : forall h' LS i x6 p1 x3 x5,
        nth_error LS i = Some (existTS (fun _ : key => ptree h') x6 p1)
        -> x5 = Val x6
        -> x5 = lastKey match LS with
                          | nil => nil
                          | a :: l => a :: firstn i l
                        end x3.
      Proof. clear.
        induction LS.
          intros; norm list in *. discriminate.
          simpl. intros. destruct i. simpl in *.  inversion H. auto.
          simpl in *. eapply IHLS. eauto. eauto.
      Qed.

      Lemma key_between_low_inc : forall x tK x2 k',
        key_between x tK x2
        -> OTlt KOT k' tK
        -> key_between (Val k') tK x2.
      Proof. clear.
        unfold key_between. firstorder.
      Qed.

      Lemma inv_child : forall h' x0 i x2 x3 p1 x x5 x8,
        inv (S h') x0 x3 x2
        -> nth_error (fst (snd x0)) i = Some (existTS (fun _ : key => ptree h') x8 p1)
        -> x = lastKey (firstn i (fst (snd x0))) x3
        -> Val x8 = x5
        -> inv h' p1 x x5.
      Proof. clear.
        Transparent inv. simpl. Opaque inv. destruct x0. simpl. destruct p0. simpl in *.
        Transparent ptree. fold ptree in *. Opaque ptree. 
        intro i. generalize dependent l. induction i.
        intros. simpl in *. destruct l; try discriminate. subst. inversion H0. rewrite H2 in *. simpl in *. tauto.
        intros. destruct l. simpl in *. discriminate.
        simpl in *. eapply IHi. destruct H. destruct H. split. eassumption. eassumption. eauto. eauto. eauto.
      Qed.
      Lemma key_between_child : forall x tK x2 x5 k',
        key_between x tK x2
        -> OTeq KOT k' tK \/ OTlt KOT tK k'
        -> Val k' = x5
        -> key_between x tK x5.
      Proof. clear.
        unfold key_between. intros. destruct H.
        split. trivial. subst. unfold not. intros. destruct H0. order.
        Transparent KLOT. unfold KLOT in H1. simpl in H1. Opaque KLOT.
        eapply OTlt_antirefl. eapply OTlt_trans. eassumption. eassumption.
      Qed.

(**
    Definition CaseLtEqGt T (P:hprop) (Q:T -> hprop) (x y : key)
      (clt : OTlt KOT x y -> STsep P Q) (ceq : OTeq KOT x y -> STsep P Q) (cgt : OTlt KOT y x -> STsep P Q) : STsep P Q :=
      match OTcompare KOT x y with
        | LT pfLt => clt pfLt
        | EQ pfEq => ceq pfEq
        | GT pfGt => cgt pfGt
      end.
**)

      Lemma lastKey_nth_error : forall h i v' k' LS x6 x3,
        Val k' = x6
        -> nth_error LS i = Some (existTS (BranchCell h) k' v')
        -> lastKey LS x6 = lastKey LS x3.
      Proof. clear.
        destruct LS; intros; norm list in *; think.
      Qed.
      Lemma lastKey_firstn_nth_error : forall h i LS k' x9 x3,
        nth_error LS i = Some (existTS (fun _ : key => ptree h) k' x9)
        -> Val k' = lastKey (firstn (S i) LS) x3.
      Proof. clear.
        induction i; simpl.
          destruct LS; intros; try discriminate.  inversion H. simpl. auto.
          intros. destruct LS; try discriminate. erewrite IHi. Focus 2. eauto. simpl. eauto.
      Qed.
      Lemma inv_contextual_firstn : forall h' i x0 x3 x2 x,
        inv (S h') x0 x3 x2
        -> x = lastKey (firstn i (fst (snd x0))) x3
        -> contextual h'
        (fun (mi : LiftOrder key) (c : sigTS (fun _ : key => ptree h')) =>
          inv h' (projT2S c) mi (Val (projT1S c)))
        x3 x (firstn i (fst (snd x0))).
      Proof. clear.
        destruct x0. destruct y. simpl. generalize dependent l. generalize dependent p0. 
        induction i; simpl.
          intros; subst; order.
          Transparent ptree. fold ptree in *. Opaque ptree.
          intros; subst. destruct l. simpl in *. order.
            Transparent inv. simpl inv in *. Opaque inv. destruct H. destruct H.
            split; try tauto. eapply IHi. split. auto. eauto. eauto.
      Qed.
      Lemma inv_contextual_skipn : forall h' i x0 x3 x2 k' x6 x9,
        inv (S h') x0 x3 x2
        -> Val k' = x6
        -> nth_error (fst (snd x0)) i = Some (existTS (fun _ : key => ptree h') k' x9)
        -> contextual h'
        (fun (mi : LiftOrder key) (c : sigTS (fun _ : key => ptree h')) =>
          inv h' (projT2S c) mi (Val (projT1S c))) x6
        (lastKey (fst (snd x0)) x3) (skipn (S i) (fst (snd x0))).
      Proof. clear.
        destruct x0. destruct y. simpl. generalize dependent l. generalize dependent p0.
        Transparent ptree. fold ptree in *. Opaque ptree.
        induction i; simpl.
          destruct l; simpl; intros; try discriminate. inversion H0.
          destruct H. Transparent inv. fold inv in *. Opaque inv. simpl in *.
          inversion H1. subst. simpl in *. tauto.

          destruct l. simpl. intros; discriminate.
          intros. simpl. eapply IHi. Focus 2. eauto. Focus 2. eauto. 
          Transparent inv. simpl in *. think. Opaque inv. eapply H2.
      Qed.

      Lemma repOp_full : forall h A B C D E F G H I, 
        B = F -> C = G -> D = H -> E = I ->
        repOp h A B C D E ==> repOp h A F G H I.
      Proof. clear.
        intros; subst; apply himp_refl.
      Qed.
      Definition repOp_facts (h : nat) (o : op) (m : opModel h o) (min max : LiftOrder key) : Prop :=
        match o as o return opModel h o -> Prop with
          | Merge p        => fun m => inv h m min max
          | Split lp kp rp => fun lkr => 
            let l := fst (fst lkr) in
            let k := snd (fst lkr) in
            let r := snd lkr in
            inv h l min (Val k) /\ inv h r (Val k) max /\
            lp = ptrFor _ l /\ kp = k /\ rp = ptrFor _ r
          | Combine p      => fun m => inv h m min max
        end m.

      Lemma repOp_pure : forall h A B C D E P Q,
        (repOp_facts h A B C D -> repOp h A B C D E * P ==> Q) 
        -> repOp h A B C D E * P ==> Q.
      Proof. clear.
        destruct A; simpl in *; intros; intro_pure; (eapply himp_trans; [ | eapply H ]); sep fail auto.
      Qed.

      Lemma xxx : forall h' i x0 (v : RES (S h')) (rr : RES h') x4 x6 x2 x3,
        inv (S h') x0 x3 x2
        -> i < length (fst (snd x0))
        -> repOp_facts (S h') (projT1 (snd v)) x6 x3 x2
        -> flat_map (fun x : sigTS (fun _ : key => ptree h') => as_map h' (projT2S x))
        (firstn i (fst (snd x0))) ++ as_mapOp h' (projT1 (snd rr)) x4 ++
        flat_map (fun x : sigTS (fun _ : key => ptree h') => as_map h' (projT2S x))
        match fst (snd x0) with
          | nil => nil
          | _ :: l => skipn i l
        end ++ as_map h' (snd (snd x0)) =
        as_mapOp (S h') (projT1 (snd v)) x6
        -> Spec tK
          (as_map h'
             match nth_error (fst (snd x0)) i with
             | Some m' => projT2S m'
             | None => snd (snd x0)
             end) =
        (fst
           (Spec tK
              (as_map h'
                 match nth_error (fst (snd x0)) i with
                 | Some m' => projT2S m'
                 | None => snd (snd x0)
                 end)), as_mapOp h' (projT1 (snd rr)) x4)
        -> Spec tK
        (let (ls, nxt0) := snd x0 in
          flat_map
          (fun x7 : sigTS (fun _ : key => ptree h') => as_map h' (projT2S x7))
          ls ++ as_map h' nxt0) =
        (fst
          (Spec tK
            (let (ls, nxt0) := snd x0 in
              flat_map
              (fun x7 : sigTS (fun _ : key => ptree h') =>
                as_map h' (projT2S x7)) ls ++ as_map h' nxt0)),
          as_mapOp (S h') (projT1 (snd v)) x6).
      Proof. clear Fn.
        intros.
        remember (firstn i (fst (snd x0))) as BEFORE.
        remember (skipn (S i) (fst (snd x0))) as AFTER.
        Lemma list_destruct_length : forall T i (LS:list T),
          i < length LS
          -> exists x, LS = (firstn i LS) ++ x :: (skipn (S i) LS).
        Proof. clear.
          induction i; simpl; intros.
            destruct LS; simpl in *; try (elimtype False; omega); eauto.
            destruct LS; simpl in *; try (elimtype False; omega). 
              assert (i < length LS). omega. apply IHi in H0. destruct H0. exists x.
              f_equal. auto.
        Qed.
        generalize (list_destruct_length _ H0); intros. rewrite <- HeqAFTER in H4. rewrite <- HeqBEFORE in H4.
        destruct H4.
        cut (nth_error (fst (snd x0)) i = Some x); intros.
        Focus 2. rewrite H4. rewrite HeqBEFORE.
        Lemma nth_error_firstn_exact : forall T LS i (LS' : list T) x,
          length LS = i -> nth_error (LS ++ x :: LS') i = Some x.
        Proof. clear.
          induction LS; norm list in *; simpl; intros.
            subst. simpl. auto.
            subst. simpl. auto. 
        Qed. apply nth_error_firstn_exact.
        rewrite firstn_length. eapply Min.min_l. omega.
        rewrite H5 in *.
        Transparent ptree. fold ptree in *. 
        generalize (@inv_contextual_firstn _ i _ _ _ _ H (refl_equal _)).
        generalize (@inv_contextual_skipn _ i _ _ _ (projT1S x) (Val (projT1S x)) (projT2S x) H (refl_equal _)).
        cut (inv _ (projT2S x) (lastKey (firstn i (fst (snd x0))) x3) (Val (projT1S x))); [ | destruct x; eapply inv_child; eauto ].
        intros.

        case_eq (nth_error (fst (snd x0)) i); intros;
          [ | elimtype False; apply nth_error_len in H9; fold ptree in *; omega ].
        destruct s.
        rewrite H4 in *. rewrite <- H2. destruct rr. simpl. destruct s. simpl in *.
        cut (match BEFORE ++ x :: AFTER with
               | nil => nil
               | _ :: l => skipn i l
             end = AFTER); intros; [ | destruct BEFORE; norm list; auto ].
        rewrite H10 in *. clear H10.
        generalize (@SpecLocal x3 (lastKey (firstn i (fst (snd x0))) x3) (Val (projT1S x)) x2 tK
         (@as_map _ (projT2S x)) (flat_map (fun x7 => as_map h' (projT2S x7)) BEFORE) (flat_map (fun x7 => as_map h' (projT2S x7)) AFTER ++ as_map _ (snd (snd x0)))).
        intros.
        destruct x0. destruct p1. simpl in *. rewrite H4 in *. simpl in *. 
        rewrite flat_map_app in *. simpl in *. norm list in *.
        rewrite H10. simpl. f_equal. f_equal. f_equal. rewrite H3. simpl. auto.

        (** MY ASSUMPTIONS **)

      Admitted.


      Definition recur : forall h' min max optr k' p p' m ary nxt i min'
        (pfEq : OTeq KOT k' tK \/ OTlt KOT tK k')
        (localCompute' : forall (min max : [LiftOrder key]) 
                    (optr : [option ptr])
                    (p : ptr) (m : [ptree h']),
                  STsep
                    (hprop_unpack min
                       (fun min0 : LiftOrder key =>
                        hprop_unpack max
                          (fun max0 : LiftOrder key =>
                           hprop_unpack m
                             (fun m0 : ptree h' =>
                              hprop_unpack optr
                                (fun optr0 : option ptr =>
                                 rep' h' p optr0 m0 * [inv h' m0 min0 max0] *
                                 [key_between min0 tK max0] * P)))))
                    (fun res : RES h' =>
                     hprop_unpack m
                       (fun m0 : ptree h' =>
                        hprop_unpack min
                          (fun min0 : LiftOrder key =>
                           hprop_unpack max
                             (fun max0 : LiftOrder key =>
                              hprop_unpack optr
                                (fun optr0 : option ptr =>
                                 let opm := projT2 (snd res) in
                                 hprop_unpack opm
                                   (fun opm0 : opModel h' (projT1 (snd res)) =>
                                    repOp h' (projT1 (snd res)) opm0 min0 max0
                                      optr0 * Q (fst res) *
                                    [firstPtrOp h' (projT1 (snd res)) opm0 =
                                     firstPtr h' m0] *
                                    [Spec tK (as_map h' m0) =
                                     (fst (Spec tK (as_map h' m0)),
                                     as_mapOp h' (projT1 (snd res)) opm0)]))))))),
        STsep (
          Exists o0 :@ option (key * ptr),
          hprop_unpack min'
          (fun l : LiftOrder key =>
           hprop_unpack m
             (fun p1 : ptree (S h') =>
              hprop_unpack optr
                (fun o1 : option ptr =>
                 hprop_unpack max
                   (fun l0 : LiftOrder key =>
                    hprop_unpack min
                      (fun l1 : LiftOrder key =>
                       p ~~> mkNode (S h') ary (Some nxt) *
                       [length (fst (snd p1)) <= SIZE] *
                       [inv (S h') p1 l1 l0] * [i <= length (fst (snd p1))] *
                       [key_between l tK l0] * [array_length ary = SIZE] *
                       [l = lastKey (firstn i (fst (snd p1))) l1] *
                       (repBranchExcept h' ary i (fst (snd p1))
                          (firstPtr h' (snd (snd p1))) *
                        [o0 =
                         match nth_error (fst (snd p1)) i with
                         | Some (existTS k v) => Some (k, ptrFor h' v)
                         | None => None
                         end] * (rep' h' nxt o1 (snd (snd p1)) * P))))))) *
        hprop_unpack (array_plus ary i)        
          (fun p2 : ptr =>
           p2 ~~> Some (k', p') *
           hprop_unpack m
             (fun m0 : ptree (S h') =>
              match nth_error (fst (snd m0)) i with
              | Some (existTS k'0 v') =>
                  [Some (k', p') = Some (k'0, ptrFor h' v')] *
                  [i < length (fst (snd m0))] *
                  rep' h' (ptrFor h' v')
                    (repBranch_nextPtr (fst (snd m0)) i
                       (Some (firstPtr h' (snd (snd m0))))) v'
              | None => [Some (k', p') = None] * [i >= length (fst (snd m0))]
              end)))
     (fun res : RES (S h') =>
      hprop_unpack m
        (fun m0 : ptree (S h') =>
         hprop_unpack min
           (fun min0 : LiftOrder key =>
            hprop_unpack max
              (fun max0 : LiftOrder key =>
               hprop_unpack optr
                 (fun optr0 : option ptr =>
                  hprop_unpack (projT2 (snd res))
                    (fun opm0 : opModel (S h') (projT1 (snd res)) =>
                     repOp (S h') (projT1 (snd res)) opm0 min0 max0 optr0 *
                     Q (fst res) *
                     [firstPtrOp _ _ opm0 = firstPtr _ m0] *
                     [Spec tK (as_map (S h') m0) =
                      (fst (Spec tK (as_map (S h') m0)),
                      as_mapOp (S h') (projT1 (snd res)) opm0)])))))).
      intros.
      refine (
        rr <- localCompute' min' [Val k']%inhabited (m ~~~ repBranch_nextPtr (fst (snd m)) i (Some (firstPtr _ (snd (snd m)))))
                            p' (m ~~~ match nth_error (fst (snd m)) i with
                                        | None => snd (snd m) (** junk **)
                                        | Some m' => projT2S m'
                                      end) <@> _ ;
        {{ @mergeOpInternal min min' max [k']%inhabited h' p ary nxt optr i rr m <@> _ }});
      clear localCompute'; clear Fn.
      instantiate (1 := m ~~ min ~~ min' ~~ max ~~ optr ~~ 
        (p'' :~~ array_plus ary i in
          p'' ~~> Some (k', p') * p ~~> mkNode (S h') ary (Some nxt) *
          [length (fst (snd m)) <= SIZE] * [inv (S h') m min max] *
          [i <= length (fst (snd m))] * [key_between min' tK max] *
          [min' = lastKey (firstn i (fst (snd m))) min] * [array_length ary = SIZE] *
          [exists v' : ptree h', p' = ptrFor h' v' /\ nth_error (fst (snd m)) i = Some (existTS (fun _:key => ptree h') k' v')] *
          repBranchExcept h' ary i (fst (snd m)) (firstPtr h' (snd (snd m))) *
          rep' h' nxt optr (snd (snd m)) *
          [i < length (fst (snd m))])).
      simpl. repeat progress inhabiter. intro_pure.

      Transparent ptree. fold ptree in *. Opaque ptree. red_prems. 
      match goal with 
        | [ |- context [ match ?Y with
                           | Some _ => _
                           | None => _ 
                         end] ] => case_eq Y; intros; [ | subst; intro_pure; discriminate ]
      end. red_prems. destruct s. unpack_conc. rewrite <- (pack_injective H7).
      simpl in *. rewrite <- (pack_injective H6). intro_pure. inversion H16.
      inversion H17. 
      Hint Resolve key_between_child inv_child.
      canceler' ltac:(eauto). 
      cut_pure. sep fail auto. eapply inv_child. eauto. eauto. eauto. subst. eauto.

      solve [ sep fail auto ].

      instantiate (1 := m ~~ min ~~ min' ~~ max ~~
        (opm :~~ projT2 (snd rr) in
          (p'' :~~ array_plus ary i in
          let m'' := match nth_error (fst (snd m)) i with
                       | Some m' => projT2S m' 
                       | None => snd (snd m)
                     end in
          [(exists v' : ptree h', 
            p' = ptrFor h' v' /\ nth_error (fst (snd m)) i = Some (existTS (fun _ : key => ptree h') k' v'))] *
          [i < length (fst (snd m))] *
          [Spec tK (as_map h' m'') =
            (fst (Spec tK (as_map h' m'')), as_mapOp h' (projT1 (snd rr)) opm)] *
          [firstPtrOp h' (projT1 (snd rr)) opm = firstPtr h' m''] *
          [key_between min' tK max] *
          [i <= length (fst (snd m))] * [inv (S h') m min max] *
          [length (fst (snd m)) <= array_length ary]))).
      simpl; repeat progress inhabiter. intro_pure; unpack_conc.
      search_conc ltac:(idtac;
        match goal with
          | [ |- _ ==> (Exists p :@ ptr, _) * _ ] => eapply himp_ex_conc
        end). exists p'.
      Transparent ptree. fold ptree in *. Opaque ptree. red_prems.
      unfold repBranchExcept. apply pack_injective in H5.
      Transparent ptree. fold ptree in *.
      case_eq (nth_error (fst (snd x0)) i); intros; [ | fold ptree in *; rewrite H20 in *; destruct H18; discriminate ].
      fold ptree in *. red_prems. Opaque ptree.
      destruct s. simpl in H5. rewrite H5 in *. rewrite H10. rewrite H20.
      simpl skipn at 1. rewrite (pack_injective H7). 
      Hint Resolve inv_contextual_firstn inv_contextual_skipn.
      Transparent ptree. fold ptree in *. Opaque ptree.
      destruct H18. canceler' ltac:(eauto). 
      repeat f_equal; eauto.





      pose (lastKey_firstn_nth_error _ _ _ x3 H21). simpl in e.      

      Hint Resolve repOp_full.
      Hint Resolve lastKey_nth_error.
      rewrite H6.
      canceler' ltac:(auto). rewrite <- H6. canceler' ltac:(eauto).
      cut_pure. sep fail auto. clear e.
      erewrite lastKey_nth_error.
      eapply inv_contextual_skipn. eauto. eauto. eauto. eauto. eauto.


      intros; simpl; repeat progress inhabiter. intro_pure. unpack_conc.
      search_prem ltac:(apply repOp_pure; intros).
      canceler' ltac:(eauto).

      Transparent ptree. fold ptree in *. Opaque ptree.
      Hint Resolve xxx.
      canceler' ltac:(eauto).
      cut_pure. sep fail auto.
      rewrite H7. rewrite H13. destruct x0. destruct y. simpl in *. destruct l. simpl. norm list. auto.
      simpl. auto.
    Defined. (** Odd **)

    Definition localCompute' : forall (h : nat) (min max : [LiftOrder key]) (optr : [option ptr])
      (p : ptr) (m : [ptree h]),
      STsep (min ~~ max ~~ m ~~ optr ~~
                rep' h p optr m * [inv h m min max] * [key_between min tK max] * P)
            (fun res : RES h => m ~~ min ~~ max ~~ optr ~~ opm :~~ projT2 (snd res) in
                repOp h (projT1 (snd res)) opm min max optr * Q (fst res) *
                [firstPtrOp _ _ opm = firstPtr _ m] *
                [Spec tK (as_map _ m) = (fst (Spec tK (as_map _ m)), as_mapOp _ (projT1 (snd res)) opm)]).
      refine (fix localCompute' h min max optr {struct h} : forall (p : ptr) (m : [ptree h]), _ :=
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
                      (*[KLsorted min (firstn i lsM) min'] *) [key_between min' tK max] *
                      [min' = lastKey (firstn i lsM) min] * 
                      (** TODO: key requirements **)
                      __ *
                      repBranch h' (rep' h') ary 0 SIZE lsM (firstPtr _ nxtM) *
(*                      repBranch h' (rep' h') ary i (SIZE - i) (skipn i lsM) (firstPtr _ nxtM) * *)
                      rep' h' nxtP optr nxtM * P)
                    (fun _ _ _ (res : RES (S h')) => m ~~ min ~~ max ~~ optr ~~ opm :~~ projT2 (snd res) in
                      repOp (S h') (projT1 (snd res)) opm min max optr * Q (fst res) *
                      [firstPtrOp _ _ opm = firstPtr _ m] *
                      [Spec tK (as_map _ m) = (fst (Spec tK (as_map _ m)), as_mapOp _ (projT1 (snd res)) opm)])
                    (fun self i min' pfRange =>
                     match le_lt_dec SIZE i with
                       | left pfLe =>
                         _
                       | right pfLt =>
                         okv <- sub_array ary i (fun v => m ~~ match nth_error (fst (snd m)) i with
                                                                 | None => [v = @None (key * ptr)] * [i >= length (fst (snd m))]
                                                                 | Some (existTS k' v') => [v = Some (k', ptrFor _ v')] * [i < length (fst (snd m))] * 
                                                                   rep' h' (ptrFor _ v') (repBranch_nextPtr (fst (snd m)) i (Some (firstPtr _ (snd (snd m))))) v'
                                                               end) <@> _ ;
                         let _:option (key * ptr) := okv in
                         match okv as okv' return okv = okv' -> _ with
                           | None => fun _ => _
                           | Some (k', p') => fun _ =>
                             match OTcompare KOT k' tK with
                               | LT _ => {{ self (S i) [Val k']%inhabited (lt_S_le pfLt) }}
                               | EQ pfEq => _
                               | GT pfGT => _
                             end
                         end (refl_equal _)
                     end) 0 min (O_le SIZE) }}
        end); try clear self; try clear Fn.
    Proof.
      (** Leaf **)
      instantiate (1 := fun v => min ~~ max ~~ m ~~ optr ~~ [key_between min tK max] * [inv 0 m min max] *
        [height v = 0] * [next v = optr] * [p = ptrFor _ m] * [array_length (content v) = SIZE] *
        [length (snd m) <= SIZE] *
        repLeaf (content v) 0 SIZE (snd m) * P).
        solve [ inhabiter; destruct x; sep fail auto ].
      solve [ sep fail auto ].
      simpl; inhabiter; intro_pure. unpack_conc. canceler' ltac:(eauto); eauto. rewrite H in H3. simpl in H3. rewrite (pack_injective H3).
      canceler' ltac:(eauto). solve [ sep fail auto ].
      sep fail auto. rewrite H2. sep fail auto. simpl; cut_pure. rewrite <- H1; auto. rewrite H7; auto.

      (** Branch -- Full-Last **)
      simpl; inhabiter; intro_pure. unpack_conc. canceler' ltac:(eauto). solve [ sep fail auto ].
      solve [ t ].
      simpl; inhabiter; intro_pure. canceler' ltac:(eauto). solve [ sep fail auto ].
      solve [ t ].
      refine (
        rr <- localCompute' h' min' max optr nxt (m ~~~ snd (snd m)) <@> 
            (min ~~ max ~~ min' ~~ optr ~~ m ~~ 
             let lsM := fst (snd m) in
             let nxtM := snd (snd m) in
             p ~~> mkNode (S h') ary (Some nxt) *
             [length lsM <= SIZE] * [inv (S h') m min max] * [i <= length lsM] *
             [key_between min' tK max] * [min' = lastKey (firstn i lsM) min] *
             repBranch h' (rep' h') ary 0 SIZE lsM
             (firstPtr _ match nth_error lsM i with
                           | Some x => projT2S x
                           | None => nxtM
                         end)) ;
        {{ @mergeOpNext min min' max h' p ary optr SIZE rr m (eq_le SIZE) <@> _ }}); try clear localCompute'.
      Opaque inv.
      tac. solve [ sep fail auto ].
      solve [ sep fail auto ].
      intros; simpl; inhabiter; intro_pure. unpack_conc.
      (repeat match goal with
                | [ H : ?X = [_]%inhabited, H' : context [ inhabit_unpack ?X _ ] |- _ ] => 
                  rewrite H in H'; simpl inhabit_unpack in H'
              end).
      list_grw_goal ltac:(eauto). eapply himp_ex_conc. exists nxt.
      canceler' ltac:(eauto). rewrite <- (pack_injective H4) in H6. rewrite <- H6.
      Hint Resolve inv_contextual. norm list in H12. canceler' ltac:(eauto). specFinder ltac:(idtac).
      solve [ sep fail auto ].

      intros; simpl; repeat progress inhabiter. intro_pure. unpack_conc. 
      Transparent ptree. fold ptree in *. Opaque ptree.

      Lemma ptr_equalities : forall h' (v:RES (S h')) x5 (x0:ptree (S h')) (rr:RES h') x6 x4,
        firstPtrOp (S h') (projT1 (snd v)) x5 =
        match head (fst (snd x0)) with
          | Some n => firstPtr h' (projT2S n)
          | None => firstPtrOp h' (projT1 (snd rr)) x4
        end
        -> snd (snd x0) = x6
        -> firstPtrOp h' (projT1 (snd rr)) x4 = firstPtr h' x6
        -> projT2 (snd rr) = [x4]%inhabited
        -> firstPtrOp (S h') (projT1 (snd v)) x5 =
        match fst (snd x0) with
          | nil => firstPtr h' (snd (snd x0))
          | a :: _ => firstPtr h' (projT2S a)
        end.
      Proof. clear.
        intros. rewrite H. rewrite H1. subst.
        destruct x0. destruct y. simpl in *. case_eq l; intros; simpl in *; auto.
      Qed.
      Hint Resolve ptr_equalities.
        
      canceler' ltac:(eauto). 
      cut_pure; [ sep fail auto | ].
      destruct x0. destruct y. simpl in *.
      Lemma sub : forall h' l p1 v x5 ,
        Spec tK
     (flat_map
        (fun x0 : sigTS (fun _ : key => ptree h') => as_map h' (projT2S x0))
        l ++ as_map h' p1) =
   (fst
      (Spec tK
         (flat_map
            (fun x0 : sigTS (fun _ : key => ptree h') =>
             as_map h' (projT2S x0)) l ++ as_map h' p1)),
   as_mapOp (S h') v x5).
(**
      generalize (@SpecLocal x3 x x2 x2 tK (as_map h' p1) (flat_map
        (fun x0 : sigTS (fun _ : key => ptree h') => as_map h' (projT2S x0))
        l) nil). norm list. intros. rewrite H17. simpl. f_equal. rewrite <- H16. f_equal. rewrite (pack_injective H6). rewrite H7. auto.
      eapply KLsorted_app; split; think. Transparent inv. fold inv in *. Opaque inv.
      Lemma KLsorted_weaken_min : forall (ls : list (sigTS value)) min min' max,
        KLsorted min ls max
        -> ~min #< min'
        -> KLsorted min' ls max.
      Proof. clear.
        induction ls.
      Admitted.
      eapply KLsorted_weaken_min. eauto. (** TODO **)
      (** eapply inv_KLsorted_map. **)
**)
    Admitted. (** TODO **)
    solve [ apply sub; eauto ].
      
      (** Reading the array **)
    Transparent ptree.
      inhabiter. simpl. intro_pure. 
      search_prem ltac:(eapply repBranch_read'). eassumption. simpl. inhabiter. unpack_conc.
      eapply himp_ex_conc; exists v. unpack_conc. fold ptree in *. canceler' ltac:(eauto). solve [ sep fail auto ].
      solve [ sep fail auto ].

      (** Branch -- Read Some (not there yet) **)
      simpl; inhabiter. intro_pure. unfold ary in *. unpack_conc. canceler' ltac:(eauto). norm list in *.
      search_conc ltac:(idtac;
        match goal with
          | [ |- _ ==> repBranch _ _ _ _ _ _ _ * _ ] => eapply repBranchExcept_combine
        end); eauto. simpl. unpack_conc.
      unfold ptree in *. rewrite _H0. case_eq (nth_error (fst (snd x0)) i); [ | intros; intro_pure; discriminate ]. fold ptree in *. 
      Opaque ptree. destruct s. intros. intro_pure. canceler' ltac:(eauto). cut_pure; eauto. sep fail auto.
      eapply nth_error_lastKey; eauto. inversion H14. rewrite H19 in *. eauto.
      rewrite <- (pack_injective H5).
      eapply key_between_low_inc; eauto. 

      solve [ sep fail auto ].
      (** Branch -- Equal **)
      refine {{ @recur h' min max optr k' p p' m ary nxt i min' (or_introl _ pfEq) (localCompute' h') }};
        auto; solve [ sep fail auto; simpl; sep fail auto ].
      (** Branch -- Greater Than **)
      refine {{ @recur h' min max optr k' p p' m ary nxt i min' (or_intror _ pfGT) (localCompute' h') }};
        auto; solve [ sep fail auto; simpl; sep fail auto ].
      (** Branch -- Read None (TODO: REPEATED CODE) **)
      Focus.
      refine (
        rr <- localCompute' h' min' max optr nxt (m ~~~ snd (snd m)) <@> 
            (min ~~ max ~~ min' ~~ optr ~~ m ~~ 
             let lsM := fst (snd m) in
             let nxtM := snd (snd m) in
             p ~~> mkNode (S h') ary (Some nxt) *
             [length lsM <= SIZE] * [inv (S h') m min max] * [i = length lsM] *
             [key_between min' tK max] * [min' = lastKey (firstn i lsM) min] *
             repBranch h' (rep' h') ary 0 SIZE lsM (firstPtr _ nxtM)) ;
        {{ @mergeOpNext min min' max h' p ary optr i rr m _ <@> _ }}); try clear localCompute'.
      
      tac. case_eq (nth_error (fst (snd x0)) i); intros. destruct s. intro_pure. subst. discriminate.
      Transparent ptree. fold ptree in *. rewrite H13 in *. Opaque ptree.
      search_conc ltac:(idtac;
        match goal with
          | [ |- _ ==> repBranch _ _ _ _ _ _ _ * _ ] => eapply repBranchExcept_combine
        end); eauto. simpl. unpack_conc. rewrite H13. subst. rewrite <- (pack_injective H5) in *.
      canceler' ltac:(eauto). 
      Lemma firstn_length : forall T (LS: list T) i,
        i >= length LS -> firstn i LS = LS.
      Proof. clear.
        induction LS; simpl in *; intros; auto.
          destruct i. elimtype False; omega. simpl. f_equal. auto.
      Qed.
      Lemma nth_error_None_length : forall T (LS:list T) i,
        nth_error LS i = None -> length LS <= i.
      Proof. clear.
        induction LS; simpl in *; intros; norm list in *. auto.
          destruct i. simpl in *; discriminate. simpl in *. apply IHLS in H. omega.
      Qed.
      Hint Resolve nth_error_None_length.
      cut_pure. sep fail auto.
      cut (length (fst (snd x0)) <= i); eauto. intros. 
      Transparent ptree. fold ptree in *. Opaque ptree. omega.      
      eapply inv_Next. eauto. eauto. eauto. f_equal.
      apply firstn_length;  eauto.

      solve [ sep fail auto ].
      
      auto.
      intros; simpl; repeat progress inhabiter; intro_pure. unpack_conc.
      (repeat match goal with
                | [ H : ?X = [_]%inhabited, H' : context [ inhabit_unpack ?X _ ] |- _ ] => 
                  rewrite H in H'; simpl inhabit_unpack in H'
              end).
      list_grw_goal ltac:(eauto). eapply himp_ex_conc. exists nxt.
      Transparent ptree. fold ptree in *. Opaque ptree.
      rewrite <- (pack_injective H4) in H6. rewrite <- H6. canceler' ltac:(eauto).
      cut (length (fst (snd x0)) = i); eauto; intros.
      rewrite firstn_len_le_rw in H12; eauto.
      norm list in H12.
      canceler' ltac:(eauto). solve [ sep fail auto ].

      Opaque as_map.
      intros; simpl; repeat progress inhabiter. intro_pure. unpack_conc.
      canceler' ltac:(eauto).
      Transparent ptree. fold ptree in *. Opaque ptree. 
      Lemma xxx_spec : forall h' (v:RES (S h')) x5 x0 (rr:RES h') x6 x2 x3 x4,
        inv (S h') x0 x3 x2
        -> Spec tK (as_map h' x6) =
           (fst (Spec tK (as_map h' x6)), as_mapOp h' (projT1 (snd rr)) x4)
        -> flat_map
        (fun x : sigTS (fun _ : key => ptree h') => as_map h' (projT2S x))
        (fst (snd x0)) ++ as_mapOp h' (projT1 (snd rr)) x4 =
        as_mapOp (S h') (projT1 (snd v)) x5
        -> Spec tK (as_map (S h') x0) =
        (fst (Spec tK (as_map (S h') x0)), as_mapOp (S h') (projT1 (snd v)) x5).
(**
      generalize (@SpecLocal x3 x x2 x2 tK (as_map h' p1) (flat_map
        (fun x0 : sigTS (fun _ : key => ptree h') => as_map h' (projT2S x0))
        l) nil). norm list. intros. rewrite H17. simpl. f_equal. rewrite <- H16. f_equal. rewrite (pack_injective H6). rewrite H7. auto.
      eapply KLsorted_app; split; think. Transparent inv. fold inv in *. Opaque inv.
      Lemma KLsorted_weaken_min : forall (ls : list (sigTS value)) min min' max,
        KLsorted min ls max
        -> ~min #< min'
        -> KLsorted min' ls max.
      Proof. clear.
        induction ls.
      Admitted.
      eapply KLsorted_weaken_min. eauto. (** TODO **)
      (** eapply inv_KLsorted_map. **)
**)
    Admitted. (** TODO **)
    Hint Resolve xxx_spec.
    Transparent ptree. fold ptree in *. Opaque ptree. canceler' ltac:(eauto).
    solve [ sep fail auto ].
    
    (** Begin Iteration **)
    tac. unfold ary. unfold nxt. solve [ sep fail auto ].
    solve [ tac; sep fail auto ].
  Qed.


(**
      Lemma repBranchExcept_combine : forall h i LS OPTR ARY k' p' TR P Q,
        length LS < SIZE
        -> p' = ptrFor _ TR
        -> nth_error LS i = Some (existTS (BranchCell h) k' TR)
        -> P ==> repBranchExcept h ARY i LS OPTR * 
                 (p :~~ array_plus ARY i in
                   p ~~> Some (k', p') * rep' h p' (repBranch_nextPtr LS i (Some OPTR)) TR) * Q
        -> P ==> repBranch h (rep' h) ARY 0 SIZE LS OPTR * Q.
      Proof. clear.
        simpl. intros. eapply himp_trans. eassumption. canceler.
        cut (SIZE - i = S (SIZE - S i)); try omega. intros. rewrite H5.
        instantiate (1 := S i). apply nth_error_len_Some in H1. omega.
        norm arith. inhabiter. unfold repBranchExcept. rewrite H1. canceler.
        eapply repBranch_combine. instantiate (1 := i). omega. norm arith. cut (S i - i = 1); try omega. intro. rewrite H4.
        simpl. 
        generalize (nth_error_skipn_ex _ _ H1). intros. destruct H5. rewrite H5. simpl.
        destruct x0. unfold repBranch_nextPtr.

                erewrite skipn_nth_error; eauto. simpl. sep fail auto. clear H2. 
        eapply repBranch_ignore_end; eauto.
        eapply skipn_cons_len in H5. omega.
        sep fail auto. unfold repBranch_nextPtr.
        cut (nth_error LS (S i) = Some s).
        intros. rewrite H0. destruct s. simpl. sep fail auto. eapply repBranch_ignore_end; eauto.
        eapply skipn_cons_len in H5; omega.
        generalize dependent H5. clear.
        apply skipn_nth_error_S.
      Qed.
**)
        
        
          
            
          

        
        
        

 sep fail auto.

        simpl. assert (i < length LS). eapply nth_error_len_Some. eauto.
        
        destruct LS. simpl in *; elimtype False; omega.
        destruct i. simpl.

clear H1. generalize dependent H0. generalize dependent H.
        unfold repBranchExcept. unfold repBranch_nextPtr. sep fail auto. assert (i < length LS).
        eapply nth_error_len_Some in H0. omega. cut (SIZE - i = S (SIZE - S i)); try omega. intros. 
        rewrite H0. sep fail auto. destruct LS. simpl in *; elimtype False; omega.
        destruct i. simpl. destruct LS. simpl. sep fail auto. inversion H0. simpl.
        destruct LS. norm list. sep fail auto.
        
        induction i. simpl. intros.
        
        


        generalize (@repBranch_combine h ARY 0 i LS OPTR SIZE); intros. Set Printing All.
       


      solve [ t ].

      


      Focus 3. eauto.
      
      intro. rewrite H17.


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
      

    Qed.

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
  
