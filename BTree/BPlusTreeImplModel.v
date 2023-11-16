Require Import Ynot Array.
Require Import Peano_dec Compare_dec.
Require Import Minus Div2 Even.
Require Import Think ThinkList ThinkArith.
Require Import List.
Require Import Setoid.

Require Import OrderedTypeNM LiftOrder.

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
   
  Definition projT2S (x:sigTS P) : P (projT1S x) :=
    match x return P (projT1S x) with
      | existTS x h => h
    end.
End projections_sigTS.


(** Axioms **)
Axiom shift : forall (P:Prop), (STsep [P] (fun pf:P => [P]))%hprop.
Definition shift' : forall (P:Prop), (STsep [P] (fun pf : P => __))%hprop.
  refine (fun P => {{ shift P }}); sep fail auto.
Qed.

Section BPlusTreeImplModel.
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
  (* Definition KLOT := liftOT KOT. todo *)

  (* this is a type level equality *)
  Variable value_eq : forall k1 k2 : key, k1 == k2 -> value k1 = value k2.

  Definition key_eq_dec : forall (a b : key), {a == b} + {a =/= b}.
  apply equiv_dec.
  Qed.

  Notation "a '#<' b"  := (ordLt a b) (at level 70, no associativity).
  Notation "a '#?<' b"  := (ordLt a (Val b)) (at level 70, no associativity).
  Notation "a '#<?' b"  := (ordLt (Val a) b) (at level 70, no associativity).
  Notation "a '#?<?' b" := (ordLt a b) (at level 70, no associativity).
  Notation "a '#<=?' b" := (ordLt (Val a) b \/ (Val a) == b) (at level 70, no associativity).
  Notation "a '#?<=' b" := (ordLt a (Val b) \/ a == Val b) (at level 70, no associativity).

  Definition MinK := @Min key.
  Definition MaxK := @Max key.

  (** Model Representation **)

  Fixpoint ptree (n : nat) : Set :=
    (ptr * match n return Set with
             | 0 => list (sigTS value)
             | S n => list (sigTS (fun _:key => ptree n)) * ptree n
           end)%type.

  Definition _cont {h} (x : ptree (S h)) := fst (snd x).
  Definition _next {h} (x : ptree (S h)) := snd (snd x).
  Definition ptrFor {h : nat} : ptree h -> ptr :=
    match h as h return ptree h -> ptr with
      | 0 => fun x => fst x
      | S n => fun x => fst x
    end.

  Notation "'BranchCell' h" := (sigTS (fun _:key => ptree h)) (at level 50).

  Definition key_between (min : LiftOrder key) (k : key) (max : LiftOrder key) : Prop :=
    min << (Val k) /\ (Val k) <<= max.

  (** Sorted Properties **)
  (** min < x[0] < x[2] < ... < x[n] <= max **)
  Fixpoint sorted (T : Type) C (ot : OrderedType C) 
   (G : T -> C) (min : C) (ls : list T) (max : C) {struct ls} : Prop :=
    match ls with
      | nil => ordLt min max \/ min == max 
      | f :: r => ordLt min (G f) /\ sorted ot G (G f) r max
    end%type.

  Definition KLsorted (V : key -> Set) min ls max :=
    @sorted (sigTS V) (LiftOrder key) _ (fun v => Val (projT1S v)) min ls max.

  Fixpoint contextual (h : nat) (F : LiftOrder key -> BranchCell h -> Prop)
    (min max : LiftOrder key) (ls : list (BranchCell h)) {struct ls} : Prop :=
    match ls with 
      | nil => min <<= max
      | fs :: rr => F min fs /\ contextual h F (Val (projT1S fs)) max rr
    end%type.

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

  Fixpoint as_map {n : nat} {struct n} : ptree n -> Model :=
    match n as n return ptree n -> list (sigTS value) with 
      | 0 => fun ls => snd ls
      | S n' => fun n =>
        let ls := _cont n in
        let nxt := _next n in
        List.flat_map (fun x => @as_map n' (projT2S x)) ls ++ as_map nxt
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

  Lemma sorted_nil : forall a, KLsorted a (@nil (sigTS value)) a.
  Proof. 
    unfold KLsorted. simpl. intros. right. apply LO_eq_refl. (** Why not reflexivity? **)
  Qed.
  Hint Immediate sorted_nil.
  Lemma sorted_nil_lt : forall a b, 
    (a << b \/ a == b) -> KLsorted a (@nil (sigTS value)) b.
  Proof. 
    unfold KLsorted. simpl. auto.
  Qed.
  Hint Resolve sorted_nil_lt.

  Global Instance sorted_prop (T:Type) (C:Set) {ot:OrderedType C} (G:T->C) :
  Proper (ordLe --> eq ==> ordLe ==> Basics.impl) (@sorted T C ot G).
  Proof. clear.
    unfold Proper, respectful, Basics.impl. 
    intros T C ot G x y lee ls ls' eqq2 x1 y1 lee2 S1.
    subst ls'. revert x y lee x1 y1 lee2 S1.
    induction ls; simpl in *; intros.
    destruct S1 as [S1|S1]. 
      rewrite lee, lee2 in S1; intuition.
      symmetry in S1. rewrite S1, lee in lee2. intuition.
      
    destruct S1. rewrite <- lee. 
    intuition. eapply IHls; eauto. reflexivity.
  Qed.

  (** we iterate from left to right
   **   op is the option pointer to the next child
   **)
  Definition exc2opt (T : Type) (a : Exc T) : option T :=
    match a with
      | None => None
      | Some x => Some x
    end.
    
  Definition repLeaf (T : Set) (ary : array) (s l : nat) (ls : list T) : hprop :=
    {@ p :~~ array_plus ary i in
      p ~~> exc2opt (nth_error ls (i - s)) | i <- s + l }.
  
  Fixpoint lastPtr {h : nat} : ptree h -> ptr :=
    match h as h return ptree h -> ptr with
      | 0 => fun m => fst m
      | S h => fun m => lastPtr (_next m)
    end.

  Fixpoint firstPtr {h : nat} : ptree h -> ptr :=
    match h as h return ptree h -> ptr with
      | 0 => fun m => fst m
      | S h => fun m => match _cont m with
                          | nil => firstPtr (_next m)
                          | a :: _ => firstPtr (projT2S a)
                        end
    end.

  Definition repBranch_nextPtr {h} (ls : list (BranchCell h)) i (optr : ptr) : ptr :=
    match nth_error ls (S i) with
      | None => optr
      | Some v => firstPtr (projT2S v)
    end.

  Definition repBranch (h : nat) (rep' : ptr -> option ptr -> ptree h -> hprop) 
    (ary : array) (i l : nat) (ls : list (BranchCell h))
    (nxt : ptr) : hprop :=
    {@ p :~~ array_plus ary (i + j) in
       match nth_error ls j with
         | None => p ~~> @None (key * ptr)
         | Some v => 
           p ~~> Some (projT1S v, ptrFor (projT2S v)) *
           rep' (ptrFor (projT2S v)) (Some (repBranch_nextPtr ls j nxt)) (projT2S v)
       end | j <- 0 + l }.

  Fixpoint rep' {n : nat} (p : ptr) (op_next : option ptr) {struct n} : ptree n -> hprop :=
    match n as n return ptree n -> hprop with 
      | 0 => fun m =>
        [p = ptrFor m] *
        let p := fst m in
        let ls := snd m in
        Exists ary :@ array, p ~~> mkNode n ary op_next *
        [array_length ary = SIZE] * [length ls <= SIZE] *
        repLeaf ary 0 SIZE ls
        
      | S n' => fun m =>
        [p = ptrFor m] *
        Exists ary :@ array, p ~~> mkNode n ary (Some (ptrFor (_next m))) *
        [array_length ary = SIZE] * [length (_cont m) <= SIZE] *
        repBranch n' rep' ary 0 SIZE (_cont m) (firstPtr (_next m)) *
        rep' (ptrFor (_next m)) op_next (_next m)
    end.

  (** (height, tree) pairs **)
  Definition tH := sigTS ptree.
  Definition BptMap := ptr.

  Require Import SetoidList.
  Require Import SetoidClass.

  Definition entry_eq (a b: sigTS value) : Prop.
    intros. refine ( 
    match key_eq_dec (projT1S a) (projT1S b) with
      | left pf => _
      | right pf => False
    end
    ).
    pose (value_eq _ _ pf).
    pose (projT2S a).
    pose (projT2S b).
    rewrite <- e in v0.
    exact (v = v0).
  Defined.


  Definition rep (p : BptMap) (m : Model) : hprop :=
    Exists pRoot :@ ptr, Exists h :@ nat, Exists tr :@ ptree h,
    p ~~> (pRoot, existTS (fun h:nat => [ptree h]%type) h [tr]%inhabited) *
    [eqlistA entry_eq m (as_map tr)] * [inv _ tr MinK MaxK] *
    rep' pRoot None tr.

  Definition rep_frame (p:ptr) (m : [Model]) (v : ptr * sigTS (fun h:nat => [ptree h]%type)) : hprop :=
    m ~~ Exists pRoot :@ ptr, Exists h :@ nat, Exists tr :@ ptree h,
    [v = (pRoot, existTS (fun h:nat => [ptree h]%type) h [tr]%inhabited)] *
    [eqlistA entry_eq m (as_map tr)] * [inv _ tr MinK MaxK] *
    rep' pRoot None tr.

  Lemma rep'_ptrFor : forall h p op (m : ptree h),
    rep' p op m ==> rep' p op m * [p = ptrFor m].
  Proof.
    unfold rep'; destruct h; sep fail auto.
  Qed.
  Hint Resolve rep'_ptrFor.
  Lemma rep'_ptrFor_add : forall h p op (m : ptree h) Q P,
    (ptrFor m = p -> rep' p op m * P ==> Q) ->
    rep' p op m * P ==> Q.
  Proof. clear.
    intros. destruct h; simpl; destruct m; simpl in *; intro_pure; symmetry in H0; apply H in H0; (eapply himp_trans; [ | eapply H0 ]); sep fail auto.
  Qed.

  (** Specifications **)
  Fixpoint specLookup (k : key) (m : Model) {struct m} : option (value k) :=
    match m with
      | nil => None
      | a :: b =>
        match (projT1S a) == k with
          | left pf => match value_eq (projT1S a) k pf in _ = x return option x with 
                         | refl_equal => Some (projT2S a)
                       end
          | _ => specLookup k b
        end
    end.

  Fixpoint specInsert (k : key) (v : value k) (m : Model) {struct m} : Model :=
    match m with
      | nil => existTS _ k v :: nil
      | a :: b => match ordCompare (projT1S a) k with
                    | LT _ => a :: specInsert v b
                    | EQ _ => existTS _ k v :: b
                    | GT _ => existTS _ k v :: a :: b
                  end
    end.

(**
  Fixpoint specDelete (m : Model) (k : key) {struct m} : Model :=
    match m with
      | nil => nil
      | a :: b => 
        match ordCompare (projT1S a) k with
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
          (fun res:option (value k) => m ~~ rep t m * [res = specLookup k m]).

  Definition insertType := forall (t : BptMap) (k : key) (v : value k) (m : [Model]),
    STsep (m ~~ rep t m)
          (fun res:option (value k) => m ~~ rep t (specInsert v m) * [res = specLookup k m]).

(**
  Definition deleteType := forall (t : BptMap) (k : key) (m : [Model]),
    STsep (m ~~ rep t m)
          (fun res:option (value k) => m ~~ rep t (specDelete m k) * [res = specLookup m k]).
**)

  Require Import Eqdep.
  Inductive Permutation_eq : Model -> Model -> Prop :=
  | perm_nil: Permutation_eq (@nil (sigTS value)) nil
  | perm_skip: forall (x x':sigTS value) (l l': Model),
    entry_eq x x' -> Permutation_eq l l' -> Permutation_eq (x :: l) (x' :: l')
  | perm_swap: forall (x y x' y':sigTS value) (l l':Model),
    entry_eq x x' -> entry_eq y y' -> eqlistA (entry_eq) l l' -> Permutation_eq (y :: x :: l) (x' :: y' :: l')
  | perm_trans: forall (l l' l'':Model), Permutation_eq l l' -> Permutation_eq l' l'' -> Permutation_eq l l''.

  Global Instance entry_eq_refl : Reflexive (entry_eq).
  Proof.
    unfold Reflexive; intros; unfold entry_eq.
    destruct (key_eq_dec (projT1S x) (projT1S x)). unfold eq_rec_r. unfold eq_rec. unfold eq_rect.
      generalize (value_eq (projT1S x) (projT1S x) e). intros. rewrite (UIP_refl _ _ e0). simpl. auto.
      apply c; reflexivity.
  Qed.

  Definition iterateType := forall (T : Type) (t : BptMap)
    (I : T -> Model -> hprop)
    (tm : [Model])
    (fn : forall (k : key) (v:value k) (acc: T) lm,
         STsep (lm ~~ I acc lm)
               (fun a:T => lm ~~ I a (lm ++ existTS _ _ v :: nil)))
    (acc : T),
    STsep (tm ~~ rep t tm * I acc nil)
          (fun res:T => tm ~~ Exists tm' :@ Model, 
            [Permutation_eq tm tm'] * rep t tm * I res tm').

  Definition orderedIterateType := forall (T : Type) (t : BptMap)
    (I : T -> Model -> hprop)
    (tm : [Model])
    (fn : forall (k : key) (v:value k) (acc: T) lm,
         STsep (lm ~~ I acc lm)
               (fun a:T => lm ~~ I a (lm ++ existTS _ _ v :: nil)))
    (acc : T),
    STsep (tm ~~ rep t tm * I acc nil)
          (fun res:T => tm ~~ Exists tm' :@ Model, 
            [eqlistA (entry_eq) tm tm'] *
            rep t tm * I res tm').

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
(**    bpt_delete : deleteType; **)
    bpt_iterate : iterateType;
    bpt_orderedIterate : orderedIterateType
  }.

  (** Invariant Facts **)
  Lemma KLsorted_subst : forall (X:list (sigTS value))  (a b d c: LiftOrder key),
    b <<= a -> c <<= d -> KLsorted a X c -> KLsorted b X d.
  Proof. clear.
    induction X. intros. unfold KLsorted in *. unfold sorted in *.
      destruct H1. rewrite <- H in H1. rewrite H0 in H1. tauto.
      destruct H; destruct H0; rewrite H1 in *; try (rewrite H0 in *); auto. rewrite H in *. auto.
    intros. unfold KLsorted in *. destruct H1. rewrite H in *. simpl.  split; auto.
    eapply IHX; [ | | eassumption ]; eauto. reflexivity.
  Qed.

  Global Instance KLsorted_prop : Proper (equiv ==> eq ==> equiv ==> iff) (@KLsorted value).
  Proof.
    unfold Proper, respectful. intros. subst.
    split; eapply KLsorted_subst; intuition; try rewrite H; try rewrite H1; try reflexivity.
  Qed.

  Global Instance KLsorted_prop_le : Proper (Basics.flip ordLe ==> eq ==> ordLe ==> Basics.impl) (@KLsorted value).
  Proof.
    unfold Proper, respectful. intros. subst.
    unfold Basics.impl. eapply KLsorted_subst; intuition.
  Qed.

  Lemma contextual_subst' : forall h l a b c d (F : LiftOrder key -> BranchCell h -> Prop),
    contextual h F a b l ->
    a == c -> b == d ->
    (forall a b c, a == b -> F a c -> F b c) ->
    contextual h F c d l.
  Proof. clear.
    induction l. simpl. intros. rewrite <- H0. rewrite H. auto.
    simpl. intros. rewrite H1. reflexivity.
    intros. simpl. simpl in H. intuition eauto. eapply IHl; eauto. reflexivity.
  Qed.

  Lemma contextual_subst_le : forall h l a b c d (F : LiftOrder key -> BranchCell h -> Prop),
    contextual h F a b l ->
    c <<= a -> b <<= d ->
    (forall a b c, b <<= a -> F a c -> F b c) ->
    contextual h F c d l.
  Proof. clear.
    induction l. simpl. intros. rewrite <- H1. rewrite H0. auto.
    simpl. intros. intuition. eapply H2; eauto.
    eapply IHl; eauto. reflexivity.
  Qed.   
    
  Global Instance contextual_prop' h (F : LiftOrder key -> BranchCell h -> Prop) :
  Proper (equiv ==> eq ==> Basics.impl) F ->
  Proper (equiv ==> equiv ==> eq ==> Basics.impl) (contextual h F).
  Proof. clear. unfold Proper, respectful, Basics.impl. intros.
    subst. eapply contextual_subst'; eauto. 
  Qed.

  Lemma lastKey_cons : forall h b (a : BranchCell h) c d,
    lastKey (a :: b) c == lastKey (a :: b) d.
  Proof.
    induction b. simpl. reflexivity.
    intros. unfold lastKey. simpl length. norm arith. norm list.
    unfold lastKey in IHb. simpl length in IHb. norm arith in IHb. auto.
  Qed.

  Lemma inv_subst : forall h X (a b c d: LiftOrder key),
    b <<= a -> c <<= d -> inv h X a c -> inv h X b d.
  Proof. clear.
    Hint Resolve KLsorted_subst.
    induction h; simpl. intros. eapply KLsorted_subst; eauto.
    intros. destruct X. simpl. destruct p0. simpl in *. destruct H1. fold ptree in *. split.
      destruct l. simpl. reflexivity. simpl in *. intuition. eapply IHh. eauto. reflexivity. auto.
    destruct l. simpl in *. eapply IHh; eauto. simpl in *. eapply IHh; eauto. reflexivity.
  Qed.

  Global Instance inv_prop_le h X : Proper (Basics.flip ordLe ==> ordLe ==> Basics.impl) (inv h X).
  Proof. clear. unfold Proper, respectful. intros.
    unfold Basics.impl; intros; eapply inv_subst; eauto.
  Qed.

  Global Instance inv_prop h X : Proper (equiv ==> equiv ==> iff) (inv h X).
  Proof. clear. unfold Proper, respectful. intros.
    split; eapply inv_subst; try rewrite H; try rewrite H0; try reflexivity.
  Qed.

  Lemma contextual_append : forall h (F: LiftOrder key -> sigTS (fun _:key => ptree h) -> Prop)  ls' max ls min mid,
    (forall (a b : LiftOrder key) c, b <<= a -> F a c -> F b c) ->
    contextual h F min mid ls ->
    contextual h F mid max ls' ->
    contextual h F min max (ls ++ ls').
  Proof. clear.
    induction ls. simpl. intros.
    induction ls'. simpl in *. rewrite H0. auto. simpl in *. intuition eauto.
    simpl. think.
  Qed.

  Lemma contextual_split : forall h (F: LiftOrder key -> sigTS (fun _:key => ptree h) -> Prop)  ls' max ls min,
    (forall (a b : LiftOrder key) c, b <<= a -> F a c -> F b c) ->
    contextual h F min max (ls ++ ls') ->
    contextual h F min (lastKey ls min) ls /\ contextual h F (lastKey ls min) max ls'.
  Proof. clear.
    induction ls. simpl. intros. split; auto. reflexivity.
    intros. simpl in H0. destruct H0. simpl. destruct (IHls _ H H1).  intuition.
  Qed.

  Lemma KLsorted_app : forall (l r : list (sigTS value)) max min,
    KLsorted min (l ++ r) max <->
    KLsorted min l (lastKey l min) /\ KLsorted (lastKey l min) r max.
  Proof. clear. split; generalize dependent min; generalize dependent max; generalize dependent r.
    induction l; [auto| unfold KLsorted in *; intros; simpl in *; instantiate; think].
    induction l; unfold KLsorted in *; intros; simpl in *; instantiate; think.
  Qed.

  Lemma KLsorted_app_ex : forall (l r : list (sigTS value)) max mid min,
    KLsorted min l mid -> KLsorted mid r max ->
    KLsorted min (l ++ r) max.
  Proof. 
    induction l; simpl; intros; unfold KLsorted in *.
      simpl in H. assert (min <<= mid); auto. change (KLsorted min r max).  rewrite H1. auto.
      simpl in *. intuition eauto.
  Qed.

  Lemma inv_KLsorted_0 : forall a b c (d : ptree 0),
    inv 0 d a b ->
    c = snd d ->
    KLsorted a c b.
  Proof. clear. intros; subst; auto. Qed.

  Lemma lastKey_app T a b d : lastKey (T:=T) (a ++ b) d = lastKey b (lastKey a d).
  Proof. induction a; simpl; auto. Qed.

  Global Instance lastKey_default_le T l : Proper (ordLe ==> ordLe) (lastKey (T:=T) l).
  Proof. unfold Proper, respectful.  induction l; simpl; intuition. Qed.

  Global Instance lastKey_prop_def T l : Proper (equiv ==> equiv) (lastKey (T:=T) l).
  Proof. unfold Proper, respectful. induction l; simpl; intuition. Qed.

  Lemma KLsorted_lastkey_lt_max V l min max : KLsorted (V:=V) min l max -> lastKey l min <<= max.
  Proof. induction l; simpl; inversion 1; auto. Qed.

  Lemma inv_lastkey_max h p min max : inv h p min max -> lastKey (as_map p) min <<= max.
  Proof.
    induction h; simpl; destruct p; simpl. apply KLsorted_lastkey_lt_max.
    destruct p0. intuition.
    unfold _next, _cont. simpl.
    fold ptree. 
    rewrite lastKey_app.

    pose (IHh _ _ _ H1) as o.
    eapply transitivity; [|eauto].
    apply lastKey_default_le. 
    revert H0. clear o. revert IHh. clear.
    revert min.
    induction l. 
      simpl; intuition.
      simpl. intros.
    destruct H0.
    rewrite lastKey_app.
    rewrite <- IHl; auto. apply lastKey_default_le.
    auto.
  Qed.

  Lemma lastKey_last : forall (T' : key -> Set) XS Y (X : sigTS T'),
    lastKey (XS ++ X :: nil) Y = Val (projT1S X).
  Proof. clear.
    induction XS. auto.
      intros. norm list. simpl. eauto.
  Qed.

  Lemma lastKey_flat_map h l min max :
    contextual h (fun (mi : LiftOrder key) (c : sigTS (fun _ : key => ptree h)) =>
      inv h (projT2S c) mi (Val (projT1S c))) min max l ->
    (lastKey (flat_map (fun x : BranchCell h => as_map (projT2S x)) l) min) <<= lastKey l min.
  Proof.
    induction l; simpl; intuition.
    rewrite lastKey_app.
    rewrite <- (IHl _ _ H1).
    apply lastKey_default_le.
    apply inv_lastkey_max; auto.
  Qed.

  Global Instance sorted_prop_lelift T f
    : Proper (Basics.flip ordLe ==> eq ==> ordLe ==> Basics.impl) (sorted (T:=T) (LiftOrderIsOrder KOT) f).
  Proof. unfold Proper, respectful, Basics.impl, Basics.flip.
    intros T f x y yxle x0 y0 x0eq. subst y0.
    revert x y yxle.
    induction x0; simpl; intuition.
      left. change (y << y0). rewrite yxle, <- H. auto.
      rewrite <- H1, <- yxle in H. auto.
      change (y << f a). rewrite yxle. auto.
      eapply IHx0; eauto. reflexivity.
  Qed.

  Global Instance sorted_prop_le T f:  Proper (Basics.flip ordLe ==> eq ==> ordLe ==> Basics.impl) (sorted (T:=T) KOT f).
  Proof. unfold Proper, respectful, Basics.impl, Basics.flip.
    intros T f x y yxle x0 y0 x0eq. subst y0.
    revert x y yxle.
    induction x0; simpl; intuition.
      left. rewrite yxle, <- H. auto.
      rewrite <- H1, <- yxle in H. auto.
      rewrite yxle. auto.
      eapply IHx0; eauto. reflexivity.
  Qed.

  Global Instance inv_le h p0 : Proper (Basics.flip ordLe ==> ordLe ==> Basics.impl) (inv h p0).
  Proof. unfold Proper, respectful, Basics.flip, Basics.impl.
    induction h; simpl; unfold KLsorted; simpl; intuition; simpl in *; intuition; auto.
    rewrite H, <- H0; auto.
    revert H2 H IHh. clear.
    induction a0; simpl; intuition.
    eapply IHh; eauto. intuition.

    eapply IHh; eauto; apply lastKey_default_le; auto.
  Qed.

  Lemma KLsorted_narrow_max V ls min k : KLsorted (V:=V) min ls k -> KLsorted min ls (lastKey ls min).
  Proof. unfold KLsorted; induction ls; simpl; intuition; eauto. Qed.

  Lemma inv_weaken_ub : forall h tr min max max',
    inv h tr min max -> max <<= max' -> inv h tr min max'.
  Proof.
    induction h; simpl; intros.
      unfold KLsorted in *. rewrite H0 in H. auto.
      destruct tr as [ ? [ ? ? ] ]. simpl in *. intuition. eauto.
  Qed.

  Lemma contextual_KLsorted' : forall h l x3 x2,
       contextual h
         (fun (mi : LiftOrder key) (c : sigTS (fun _ : key => ptree h)) =>
           inv h (projT2S c) mi (Val (projT1S c))) x3 
         x2 l
    -> (forall ls tr min max, inv h tr min max -> ls = (as_map tr) -> KLsorted min ls max) 
    -> KLsorted x3 (flat_map (fun x0 : sigTS (fun _ : key => ptree h) => as_map (projT2S x0)) l) x2.
  Proof. clear.
    induction l. simpl; intuition.
    intuition.
    eapply KLsorted_app. split.
      destruct H. eapply H0 in H; [ | reflexivity ]. generalize H; generalize (Val (projT1S a)). generalize x3. generalize (as_map (projT2S a)); clear.
      induction m. auto. intros. unfold KLsorted in *. simpl in *. intuition eauto.
    eapply IHl; eauto.
      destruct H. eapply inv_lastkey_max in H.
      eapply contextual_subst_le. eassumption. auto. reflexivity. intros.
      rewrite H2. auto.
  Qed.

  Lemma inv_KLsorted_map : forall h ls tr min max,
       inv h tr min max 
    -> ls = (as_map tr)
    -> KLsorted min ls max.
  Proof. clear.
    induction h; simpl. congruence.
    intros.
    destruct tr. destruct p0. simpl in *. destruct H.
    unfold _cont, _next. simpl. fold ptree in *. 
    subst.
    eapply KLsorted_app.
    split.
    eapply KLsorted_narrow_max.
    eapply contextual_KLsorted'; eauto.

    eapply IHh; eauto.
    eapply inv_le; eauto.
    eapply lastKey_flat_map; eauto. intuition.
  Qed.

  Lemma contextual_KLsorted : forall h' l x3 x2, 
       contextual h'
         (fun (mi : LiftOrder key) (c : sigTS (fun _ : key => ptree h')) =>
           inv h' (projT2S c) mi (Val (projT1S c))) x3 
         x2 l
    -> x2 = lastKey l x3
    -> KLsorted x3 (flat_map (fun x0 : sigTS (fun _ : key => ptree h') => as_map (projT2S x0)) l) x2.
  Proof. clear.
    intros. eapply contextual_KLsorted'. auto. eapply inv_KLsorted_map.
  Qed.


  Lemma contextual_denote_mid : forall h i min max ls x x',
       contextual h
         (fun (mi : LiftOrder key) (c : BranchCell h) =>
           inv h (projT2S c) mi (Val (projT1S c))) 
         min max ls
    -> nth_error ls i = Some x
    -> nth_error ls (S i) = Some x'
    -> inv h (projT2S x') (Val (projT1S x)) (Val (projT1S x')).
  Proof. clear.
    induction i.
    intros; destruct ls. norm list in *. discriminate. destruct ls. norm list in *. discriminate.
    norm list in *. simpl in *. inversion H0. inversion H1. subst. tauto.
    destruct ls. intros; norm list in *. discriminate.
    intros; norm list in *. simpl in H. destruct H. eauto.
  Qed.


End BPlusTreeImplModel.

Hint Transparent _cont _next.

(**
Notation repBranchExcept h ary st i len ls optr := 
  (@repBranch _ _ _ (@rep' _ _ _ h) ary st i ls (@repBranch_nextPtr _ _ _ ls i optr) *
   @repBranch _ _ _ (@rep' _ _ _ h) ary (S i) (len - S i) (skipn (S i) ls) optr)%hprop.
**)
