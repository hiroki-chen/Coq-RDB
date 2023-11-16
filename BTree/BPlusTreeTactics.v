Require Import BPlusTreeImplModel.
Require Import BPlusTreeModelFacts.

Hint Resolve SIZE_S.
Hint Resolve nodeType_eta.
Hint Resolve sorted_nil.
Hint Resolve sorted_nil_lt.

Require Import Ynot.
Require Import Think ThinkList ThinkArith.
Require Import Array.
Require Import OrderedTypeNM.

Open Local Scope hprop_scope.
Open Local Scope stsepi_scope.

Theorem himp_iter_sep_0_prem : forall F a b P Q,
  b = 0 ->
  P ==> Q ->
  {@ F i | i <- a + b } * P ==> Q.
Proof.
  intros; subst; sep fail auto.
Qed.

Theorem himp_iter_sep_0_conc : forall F a b P Q,
  b = 0 ->
  P ==> Q ->
  P ==> {@ F i | i <- a + b } * Q.
Proof.
  intros; subst; sep fail auto.
Qed.

Lemma readArray : forall F len st idx P Q,
  st <= idx -> idx < st + len ->
  F idx * ({@ F i | i <- st + (idx - st) } * {@ F i | i <- (S idx) + (len - (S idx - st)) } * P) ==> Q ->
  {@ F i | i <- st + len} * P ==> Q.
Proof.
  intros; split_index. instantiate (1 := idx - st); omega.
  eapply himp_trans; [ | eapply H1 ].
  Change (st + (idx - st)) into idx using omega. norm arith.
  Change (S st + (idx - st)) into (S idx) using omega.
  Change (pred (len - (idx - st))) into (len - (S idx - st)) using omega.
  sep fail auto.
Qed.

Lemma combineArray : forall F len st idx P Q,
  st <= idx -> idx < st + len ->
  P ==> F idx * ({@ F i | i <- st + (idx - st) } * {@ F i | i <- (S idx) + (len - (S idx - st)) } * Q) ->
  P ==> {@ F i | i <- st + len} * Q.
Proof.
  intros; split_index. instantiate (1 := idx - st); omega.
  eapply himp_trans; [ eapply H1 | ].
  Change (st + (idx - st)) into idx using omega. norm arith.
  Change (S st + (idx - st)) into (S idx) using omega.
  Change (pred (len - (idx - st))) into (len - (S idx - st)) using omega.
  sep fail auto.
Qed.


Create HintDb bpt_rw discriminated.
Create HintDb bpt_sep discriminated.
Hint Opaque BPlusTreeImplModel.repBranch BPlusTreeImplModel.rep' hprop_sep hprop_ex : bpt_sep bpt_rw.
Hint Opaque BPlusTreeImplModel.repLeaf : bpt_sep bpt_rw.
Hint Opaque firstn skipn nth_error : bpt_rw bpt_sep.

Hint Resolve repBranch_nextPtr_ignore_default.
Hint Resolve repBranch_nextPtr_eq2.
Hint Resolve repBranch_nextPtr_eq3_l.
Hint Resolve repBranch_nextPtr_eq3_r.
Hint Resolve repBranch_nextPtr_choose_default.
Hint Resolve repBranch_nextPtr_eq4.
Hint Resolve repBranch_nextPtr_eq5.
Hint Resolve himp_iter_sep_eq.
Hint Resolve himp_rep'_eq                 : bpt_sep.
Hint Resolve himp_repBranch_eq            : bpt_sep.
Hint Resolve repBranch_ignore_end         : bpt_sep.
Hint Resolve repBranch_prefix             : bpt_sep.
Hint Immediate repBranch_nil_ignore       : bpt_sep.
Hint Resolve repBranch_ending             : bpt_sep.
Hint Resolve repBranch_nextPtr_firstn_rw  : bpt_sep.
Hint Resolve repBranch_firstn_prefix      : bpt_sep.

Hint Resolve repBranch_nil repBranch_nil'.

Ltac eauto_with_norm_list_length := solve [ eauto with norm_list_length ].
Ltac eapply_refl_equal_omega := solve [ eapply refl_equal | omega ].

Hint Rewrite repBranch_nextPtr_choose_default using eauto_with_norm_list_length : bpt_rw.
Hint Rewrite <- repBranch_nextPtr_eq2 using eauto_with_norm_list_length : bpt_rw.
Hint Rewrite <- repBranch_nextPtr_eq5 using eauto_with_norm_list_length : bpt_rw.
Hint Rewrite repBranch_nextPtr_eq3_l using eapply_refl_equal_omega : bpt_rw.
Hint Rewrite _next_red _cont_red ptrFor_red0 ptrFor_redS : bpt_rw.

Lemma let_destruct_pair : forall (A B : Type) (x : A * B),
  x = (fst x, snd x).
Proof.
  destruct x; auto.
Qed.
Lemma let_destruct_sigT : forall A (B : A -> Type) x,
  x = existT B (projT1 x) (projT2 x).
Proof.
  destruct x; auto.
Qed.
Lemma let_destruct_sigTS : forall (A : Set) (B : A -> Set) x,
  x = existTS B (projT1S x) (projT2S x).
Proof.
  destruct x; auto.
Qed.

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

Ltac guard X Y tac :=
  let H := fresh in
  assert (H : X = Y); [ solve [ tac ] | ]; clear H.

Ltac passIdent id :=
  match goal with 
    | [ H : _ |- _ ] =>
      match H with
        | id => idtac
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
           | [ H  : array_plus ?A ?I1 = [_]%inhabited, 
               H' : array_plus ?A ?I2 = [_]%inhabited |- _ ] =>
             let H'' := fresh in
             assert (H'' : I1 = I2);
               [ solve [ omega | eauto ]
               | rewrite <- H'' in H'; rewrite H in H'; clear H'';
                 rewrite <- (pack_injective H'); clear H' ]
           | [ H : ?X = [_]%inhabited, H' : ?X = [_]%inhabited |- _ ] => rewrite H in H'; apply pack_injective in H'; rewrite H' in *
           | [ H : ?X = [_]%inhabited, H' : [_]%inhabited = ?X |- _ ] => rewrite H in H'; apply pack_injective in H'; rewrite H' in *
           | [ H : [_]%inhabited = ?X, H' : [_]%inhabited = ?X |- _ ] => rewrite <- H in H'; apply pack_injective in H'; rewrite H' in *
           | [ H : [_]%inhabited = [_]%inhabited |- _ ] => apply pack_injective in H
             (** ident = ident **)
           | [ H : ?X = ?Y |- _ ] =>
             passIdent X; passIdent Y; rewrite H in *; clear H
         end.

Lemma himp_elim_trivial : forall T (x : T) P Q,
  P ==> Q -> [x = x] * P ==> Q.
Proof. 
  sep fail auto.
Qed.

Lemma himp_frame_cell_var : forall T p q (r s : T) P Q,
  p = q -> r = s ->
  P ==> Q ->
  p ~~> r * P ==> q ~~> s * Q.
Proof.
  sep fail auto.
Qed.
Lemma himp_ptsto_any : forall (T:Set) p q (r : T) P Q,
  p = q ->
  P ==> Q ->
  p ~~> r * P ==> q ~~>? * Q.
Proof.
  unfold ptsto_any. sep fail auto.
Qed.
Lemma himp_split' : forall P Q R S,
  P ==> Q -> R ==> S -> R * P ==> S * Q.
Proof.
  intros; apply himp_split; auto.
Qed.

Ltac unpack_prem :=
  repeat search_prem ltac:(idtac;
    match goal with
      | [ |- hprop_unpack _ _ * _ ==> _ ] => 
        eapply himp_unpack_prem_eq ; [eassumption |]
      | [ |- hprop_ex _ * _ ==> _ ] =>
        apply himp_ex_prem; do 2 intro
    end).

Ltac canceler' ext solver :=
  let TestHprop P :=
    match P with
      | P => 0
      | ?P' * _ =>
        match P' with
          | P' => 0
          | _ => 1
        end
      | Exists v :@ _, _ => 0
      | _ => 1
    end
  in
  cbv zeta;
  match goal with
    | [ |- _ ==> [False] ] =>
      solve [ elimtype False; solver ] || fail 1
    | _ =>
      repeat search_conc ltac:(idtac; (** Eliminate the empty heaps on the RHS **)
        match goal with
          | [ |- _ ==> __ * _ ] => apply himp_empty_conc
          | [ |- _ ==> [?P] * _ ] => apply himp_inj_conc; [ solve [ trivial | solver ] | ]
        end);
      repeat search_prem ltac:(idtac;
        match goal with
          | [ |- __ * _ ==> _ ] => apply himp_empty_prem
          | [ |- [?X = ?X] * _ ==> _ ] => apply himp_elim_trivial
        end);  (** Eliminate empty heaps on LHS **)
      repeat search_prem ltac:(idtac;
        match goal with 
          | [ |- [_] * _ ==> _ ] => fail 1
          | [ |- (_ * _) * _ ==> _ ] => fail 1
          | [ |- ?P ==> _ ] => let x := TestHprop P in fail x
          | [ |- _ ] =>
            search_conc ltac:(idtac; 
              (** Eliminate common heaps. The match prevents capturing existentials **)
              match goal with
                | [ |- _ ==> [_] * _ ] => fail 1 (** ignore pure information so that we aren't doing extra work **)
                | [ |- _ ==> (_ * _) * _ ] => fail 1 (** tactics don't rely on having pairs **)
                | [ |- _ ==> ?P ] => let x := TestHprop P in fail x
                | [ |- _ ] => 
                     (apply himp_frame)
                  || (apply himp_frame_cell; [ solver | ])
                  || (apply himp_frame_cell_var; [ solve [ solver ] | solver | ])
                  || (apply himp_ptsto_any; [ solve [ solver ] | ])
                | _ => progress (ext solver)
              end)
        end)
  end.

Ltac instantiate_conc v :=
  search_conc ltac:(idtac; match goal with
                             | [ |- _ ==> hprop_ex _ * _ ] =>
                               simple apply himp_ex_conc; exists v
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
      | [ |- ?P ==> (Exists v :@ _, ?PTR ~~> v * _) * _ ] =>
        match P with
          | context [ PTR ~~> ?V ] => eapply himp_ex_conc; exists V
          | context [ ?PTR' ~~> ?V ] =>
            let H := fresh in
            assert (H : PTR' = PTR); [ solve [ eauto ] | rewrite H; clear H; eapply himp_ex_conc; exists V ]
        end
      | [ |- ?P ==> (Exists v :@ _, ?PTR ~~> v) * _ ] =>
        match P with
          | context [ PTR ~~> ?V ] => eapply himp_ex_conc; exists V
          | context [ ?PTR' ~~> ?V ] =>
            let H := fresh in
            assert (H : PTR' = PTR); [ solve [ eauto ] | rewrite H; clear H; eapply himp_ex_conc; exists V ]
        end
      | [ |- ?P ==> (Exists v :@ _, ?PTR ~~> v * _ * _ * _ ) * _ ] =>
        match P with
          | context [ PTR ~~> ?V ] => eapply himp_ex_conc; exists V
        end
      | [ |- ?P ==> (Exists v :@ _, ?PTR ~~> v * _ * _) * _ ] =>
        match P with
          | context [ PTR ~~> ?V ] => eapply himp_ex_conc; exists V
        end
      | [ |- ?P ==> (Exists v :@ _, ?PTR ~~> v * _) * _ ] =>
        match P with
          | context [ PTR ~~> ?V ] => eapply himp_ex_conc; exists V
        end
      | [ |- ?P ==> (@hprop_ex ?T ?Q) * _ ] =>
        let e := fresh in
        evar (e : T);
        let v := eval compute in e in
        clear e;
        let bod := eval simpl in (Q v) in
        match bod with 
          | context [ ?PTR ~~> mkNode ?X _ _ ] =>
            match P with
              | context [ PTR ~~> mkNode X ?Z _ ] =>
                eapply himp_ex_conc; exists Z; assert (v = Z); [ reflexivity | ]
            end
          | context [ ?PTR ~~> Some (_, _) ] =>
            match P with
              | context [ PTR ~~> Some (_,?V) ] =>
                eapply himp_ex_conc; exists V; assert (v = V); [ reflexivity | ]
            end
        end
    end).

Ltac combine_inh := idtac;
  match goal with
    | [ H : ?X = [_]%inhabited, H' : ?X = [_]%inhabited |- _ ] => rewrite H in H'; apply pack_injective in H'; rewrite H' in *
    | [ H : ?X = [_]%inhabited, H' : [_]%inhabited = ?X |- _ ] => rewrite H in H'; apply pack_injective in H'; rewrite H' in *
    | [ H : [_]%inhabited = ?X, H' : [_]%inhabited = ?X |- _ ] => rewrite <- H in H'; apply pack_injective in H'; rewrite H' in *
  end.

Lemma himp_refl_emp : forall P, P ==> P * __.
Proof. sep fail auto. Qed.

(** This is part of specFinder **)
Ltac sep_unify := intros;
  match goal with
    | [ |- ?P ==> emp ] =>
      let H := fresh in
      repeat (search_prem ltac:(apply himp_inj_prem; intros H; clear H));
      apply himp_refl
    | [ |- ?P ==> ?Q ] =>
      try match Q with 
            | _ ?v => idtac;
              match goal with 
                | [ M : isExistential v |- _ ] => clear M
              end
          end;
      let F := fresh "F" with F2 := fresh "F2" in
      pose (F := P);
      repeat match goal with
               | [ H : ?x = [?v]%inhabited |- _ ] =>
                 let y := eval cbv delta [F] in F in
                 match y with
                   | context[v] =>
                     pattern v in F;
                     let y := eval cbv delta [F] in F in
                     match y with
                       | ?F' _ =>
                         pose (F2 := hprop_unpack x F');
                         clear F; rename F2 into F
                     end
                 end
             end;
      repeat match goal with
               | [ _ : isExistential ?X |- _ ] =>
                 let y := eval cbv delta [F] in F in
                 match y with
                   | context[X] =>
                     pattern X in F;
                     let y := eval cbv delta [F] in F in
                     match y with
                       | ?F' _ => pose (F2 := hprop_ex F'); clear F; rename F2 into F
                     end
                 end
             end;
      match Q with
        | ?F' ?v =>
          match F' with
            | F' => fail 2
            | _ =>
              pattern v in F;
              let y := eval cbv delta [F] in F in
              match y with
                | ?F'' _ => equate F' F''
              end
          end
        | _ => 
          let y := eval cbv delta [F] in F in
          (   equate Q y
           || instantiate (1 := y) || instantiate (2 := y)
           || instantiate (3 := y) || instantiate (4 := y))
      end
  end; 
  simpl; (** the RHS is an application, we need to simplify it **)
  (** attempts to re-create the existentials **)
  repeat match goal with
           | [ H : ?T |- _ ==> @hprop_ex ?T _ ] => idtac;
             match goal with 
               | [ H' : isExistential H |- _ ] => 
                 apply himp_empty_conc'; apply himp_ex_conc; exists H; clear H'
             end
           | [ H : ?T |- _ ==> @hprop_ex ?T _ * _ ] => idtac;
             match goal with 
               | [ H' : isExistential H |- _ ] => 
                 apply himp_ex_conc; exists H; clear H'
             end
         end;
  unpack_conc; (** we packed up the function, so we need to unpack it **)
  (   apply himp_refl     (** handle cases where unpack_conc did nothing **)
   || apply himp_refl_emp (** unpack_conc leaves an extra emp **)
      (** last-ditch effort, shoudn't ever get here **)
   || solve [ idtac "oops"; match goal with 
                              | [ |- ?G ] => idtac G
                            end; sep fail idtac ]).

Ltac sep2 elab tac :=
  intros; lazy zeta;
  (repeat match goal with
            | [ H : exists x, _ |- _ ] => destruct H
            | [ H : _ /\ _ |- _ ] => destruct H
            | [ H : [_]%inhabited = ?X |- _ ] =>
              match X with 
                | [_]%inhabited => apply pack_injective in H
                | [_]%inhabited => fail 1
                | _ => symmetry in H
              end
            | [ |- context [ match ?X with 
                               | (_,_) => _
                             end ] ] => 
              rewrite (let_destruct_pair _ _ X); simpl fst; simpl snd
            | [ |- context [ match ?X with 
                               | existT _ _ => _
                             end ] ] => 
              rewrite (let_destruct_sigT _ _ X); simpl projT1; simpl projT2
            | [ |- context [ match ?X with 
                               | existTS _ _ => _
                             end ] ] => 
              rewrite (let_destruct_sigTS _ _ X); simpl projT1S; simpl projT2S
          end);
  (repeat progress inhabiter); intro_pure;
  (repeat match goal with
            | [ H : exists x, _ |- _ ] => destruct H
            | [ H : _ /\ _ |- _ ] => destruct H
            | [ H : [_]%inhabited = ?X |- _ ] =>
              match X with 
                | [_]%inhabited => apply pack_injective in H
                | [_]%inhabited => fail 1
                | _ => symmetry in H
              end
            | _ => lazy zeta; (progress unpack_prem); intro_pure
            | _ => (progress elab); intros
          end);
  (repeat (unpack_conc || pick_existentials));
  red_prems;
  repeat ((pick_existentials; unpack_conc) || canceler' tac ltac:(eauto)).

Ltac reinhabit := repeat (progress inhabiter); intro_pure; red_prems.

(** B+Tree Plugin **)
Ltac bpt_reader_combiner solver := idtac;
     (simple eapply rep'_combine; [ assumption | ])
  || (simple eapply rep'_expand; [ assumption | ])
  || match goal with
       (** Splitting repLeaf **)
       | [ H : array_plus ?A ?I = [?PTR]%inhabited
         |- @BPlusTreeImplModel.repLeaf _ ?A _ _ _ * _ ==> _ ] =>
         simple apply (@repLeaf_read _ _ _ I A _ _ _ _ PTR H);
           [ solve [ solver ] | solve [ solver ] | reinhabit ]

       | [ H : array_plus ?A _ = [?PTR]%inhabited
         |- ?P ==> @BPlusTreeImplModel.repLeaf _ ?A _ _ _ * _ ] =>
         match P with 
           | context [ PTR ~~> _ ] =>
             simple apply (@repLeaf_combine _ _ _ _ A _ _ _ _ PTR H);
               [ solve [ solver ] | solve [ solver ] | reinhabit ]
         end

       (** Splitting repBranch **)
       | [ H : array_plus ?A ?I = [?PTR]%inhabited
         |- @BPlusTreeImplModel.repBranch _ _ _ _ ?A _ _ _ _ * _ ==> _ ] =>
         simple apply (@repBranch_read _ _ _ _ I A _ _ _ _ _ _ PTR H);
           [ solve [ solver ] | solve [ solver ] | reinhabit ]

       | [ H : array_plus ?A _ = [?PTR]%inhabited
         |- ?P ==> @BPlusTreeImplModel.repBranch _ _ _ _ ?A _ _ _ _ * _ ] =>
         match P with 
           | context [ PTR ~~> _ ] =>
             simple apply (@repBranch_combineRead _ _ _ _ A _ _ _ _ _ PTR _ _ H);
               [ solve [ solver ] | solve [ solver ] | reinhabit ]
         end

       (** Can't go under repBranch **)
       | [ H : array_plus ?A ?I = [_]%inhabited
         |- ?P ==> iter_sep ?F ?ST ?LEN * ?Q ] =>
         match F with
           | context [ array_plus A _ ] => 
             simple apply (@combineArray F LEN ST I P Q);
               [ solve [ solver ] | solve [ solver ] | reinhabit ]
         end
       | [ H : array_plus ?A ?I = [_]%inhabited
         |- iter_sep ?F ?ST ?LEN * ?P ==> ?Q ] =>
         match F with
           | context [ array_plus A _ ] => simple apply (@readArray F LEN ST I P Q);
             [ solve [ eauto ] | solve [ eauto ] | inhabiter; red_prems ]
         end
     end.

Lemma hide : forall (a : Prop), (True -> a) -> a.
Proof. auto. Qed.

Ltac bpt_elab := 
  repeat search_prem ltac:(idtac;
    match goal with
      | [ |- @BPlusTreeImplModel.rep' _ _ _ _ ?P _ ?M * _ ==> _ ] =>
        match goal with
          | [ H : @BPlusTreeImplModel.ptrFor _ _ _ M = P |- _ ] => fail 1
          | [ H : P = @BPlusTreeImplModel.ptrFor _ _ _ M |- _ ] => fail 1
          | _ => apply rep'_ptrFor_add; intros
        end
    end).

Ltac hideHimp := idtac "hiding..."; apply hide.

Ltac bpt_elim' reducer solver := 
     (simple apply himp_repBranch_0_prem; [ solve [ solver ] | ])
  || (simple apply himp_repBranch_0_conc; [ solve [ solver ] | ])
  || (simple apply himp_iter_sep_0_prem;  [ solve [ solver ] | ])
  || (simple apply himp_iter_sep_0_conc;  [ solve [ solver ] | ])
  || (simple apply himp_repLeaf_frame; 
       [ solve [ solver ] | solve [ solver ] | solve [ solver ]
       | reducer; eauto | ])
  || (simple apply himp_rep'_frame; 
       [ solve [ solver ] | solver | reducer; eauto | ])
  || (simple apply himp_rep'_frame; 
       [        | solve [ solver ] | reducer; eauto | ])
  || (simple apply himp_repBranch_frame;
       [ solve [ solver ] | solve [ solver ] | solve [ solver ] | reducer; eauto with bpt_sep; hideHimp | ])
  || (bpt_reader_combiner solver; unpack_conc)
  || (simple apply himp_split; [ solve [ solver ] | ]).
     (** I'd like a tactic to auto apply everything in a hint database **)

Ltac bpt_elim solver :=
  bpt_elim' ltac:(norm arith; norm list; norm arith; autorewrite with bpt_rw) solver.

Hint Extern 0 (mkNode _ _ _ = mkNode _ _ _) => f_equal.
Hint Extern 0 (firstPtr ?X = firstPtr ?Y) => f_equal.
Hint Extern 0 (ptrFor ?X = ptrFor ?Y) => f_equal.

Hint Resolve himp_refl.
