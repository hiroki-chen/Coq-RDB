Require Import Eqdep.
Require Import Omega.
Require Import Div2.
Require Import Even.
Require Import Plus Minus.

(** Arithmetic normalization **)
Lemma n_plus_1 : forall n, n + 1 = S n.
  intros; omega.
Qed.
Lemma I_plus_n : forall n, 1 + n = S n.
  reflexivity.
Qed.
Lemma O_minus : forall n, 0 - n = 0.
  reflexivity.
Qed.
Lemma S_minus_S : forall a b, S a - S b = a - b.
  intros; omega.
Qed.
Lemma n_minus_n : forall n, n - n = 0.
  intros; omega.
Qed.
Lemma n_minus_a_b : forall n a b, n - a - b = n - (a + b).
  intros; omega.
Qed.
Lemma mult_0 : forall a, a * 0 = 0.
  intros; omega.
Qed.
Lemma O_mult : forall a, 0 * a = 0.
  reflexivity.
Qed.
Lemma pred_minus : forall x, x - 1 = pred x.
  intros; omega.
Qed.
Lemma bubble_S : forall a b, a + S b = S (a + b).
  intros; omega.
Qed.
Lemma plus_minus : forall a b, a + b - b = a.
  intros; omega.
Qed.
Lemma plus_minus2 : forall a b, b + a - b = a.
  intros; omega.
Qed.

Lemma pred_S : forall i, pred (S i) = i.
  reflexivity.
Qed.
Lemma Sn_minus_n : forall i, S i - i = 1.
  intros; omega.
Qed.

(** Guarded **)
Lemma twice_half : forall x, even x -> div2 x + div2 x = x.
  intros. induction x using ind_0_1_SS; simpl; auto.
  inversion H. inversion H1.
  cut (S (div2 x + S (div2 x)) = S (S (div2 x + div2 x))); try omega. intros.
  rewrite H0. rewrite IHx; auto. inversion H. inversion H2. auto.
Qed.

Lemma minus_half : forall x, even x -> x - div2 x = div2 x.
  intros. rewrite <- (twice_half x) at 1. omega. auto.
Qed.

Lemma S_pred : forall x, x > 0 -> S (pred x) = x.
  intros; omega.
Qed.

Lemma plus_minus_cancel : forall a b c,
  a >= b -> a - b + b - c = a - c.
  intros; omega.
Qed.

Lemma comm_plus : forall a b, a + b = b + a.
  intros; omega.
Qed.

Ltac normalize_order := idtac;
  repeat match goal with
           | [ H : context [ ?X + ?Y ], H' : context [ ?Y + ?X ] |- _ ] =>
             rewrite (comm_plus X Y) in *
           | [ H : context [ ?X + ?Y ] |- context [ ?Y + ?X ] ] =>
             rewrite (comm_plus X Y) in *
           | [ |- context H [ ?Y + ?X ] ] =>
             let H' := context H [ 0 ] in
             match H' with
               | context [ X + Y ] => 
                 rewrite (comm_plus X Y) in *
             end
           | [ H' : context H [ ?Y + ?X ] |- _ ] =>
             let H' := context H [ 0 ] in
             match H' with
               | context [ X + Y ] => 
                 rewrite (comm_plus X Y) in *
             end
         end.

Tactic Notation "norm" "arith" :=
  autorewrite with norm_arith_rw; normalize_order.
Tactic Notation "norm" "arith" "in" constr(H) :=
  autorewrite with norm_arith_rw in H; normalize_order.
Tactic Notation "norm" "arith" "in" "*" :=
  autorewrite with norm_arith_rw in *; normalize_order.

Ltac omega2 := idtac;
  let rec omegable G :=
    match G with 
      | @eq nat _ _  => idtac
      | lt _ _  => idtac
      | le _ _  => idtac
      | gt _ _  => idtac
      | ge _ _  => idtac
      | not ?G' => omegable G'
      | ?G' -> False => omegable G'
      | _ => fail 2 "not omegable"
    end
  in
  intros;
  match goal with 
    | [ |- ?G ] => omegable G; abstract solve [ norm arith; omega ]
    | _ => fail 1 "omega failed to solve equation"
  end.

Hint Rewrite plus_0_l plus_0_r : norm_arith_rw.
Hint Rewrite <- minus_n_O : norm_arith_rw.

Hint Rewrite n_plus_1 I_plus_n O_minus S_minus_S n_minus_n n_minus_a_b : norm_arith_rw.
Hint Rewrite mult_0 O_mult plus_minus plus_minus2 pred_S : norm_arith_rw.
Hint Rewrite pred_minus twice_half minus_half S_pred Sn_minus_n using solve [ eauto ] : norm_arith_rw.
Hint Rewrite plus_minus_cancel using solve [ omega ] : norm_arith_rw.


(** Other **)
Lemma neq_0_gt : forall a, a <> 0 -> a > 0.
  intros; omega.
Qed.

Lemma ltS: forall j b, j < b -> S j <= b.
  intros; omega.
Qed.

Lemma lt_le : forall a b, a < b -> a <= b.
  intros; omega.
Qed.

Lemma div2_lt : forall x, x > 0 -> div2 x < x.
  induction x using ind_0_1_SS; firstorder.
Qed.
Hint Resolve neq_0_gt ltS lt_le div2_lt.


(** Loop Proof Initialization **)
Lemma pred_lt : forall a b, a < b -> pred a < b.
  intros; omega.
Qed.

Lemma pred_le : forall a b, a < b -> pred a < b.
  intros; omega.
Qed.

Lemma eq_le : forall a, a <= a.
  intros; omega.
Qed.

Lemma div2_le : forall x, div2 x <= x.
Proof.
  induction x using ind_0_1_SS; simpl in *; firstorder.
Qed.

Lemma div2_plus_lt_div2_base : forall a i, 
  i < div2 a -> i + div2 a < a.
Proof.
  induction a using ind_0_1_SS; simpl; firstorder.
  simpl in *. destruct i. norm arith. apply Lt.lt_n_S. 
  destruct a using ind_0_1_SS; firstorder. apply Lt.lt_S_n in H.  apply IHa in H. omega.
Qed.

Lemma div2_plus_lt_div2 : forall a x i, 
  x = a -> i < div2 a -> div2 x + i < a.
Proof.
  intros; subst; rewrite comm_plus; apply div2_plus_lt_div2_base; auto.
Qed.

Lemma div2_plus_lt_div2' : forall a x i, 
  x = a -> i < div2 a -> i + div2 x < a.
Proof.
  intros; subst; apply div2_plus_lt_div2_base; auto.
Qed.

Lemma simpl_minus1 : forall a b c, 
  a >= b + c -> a - b - (a - (b + c)) = c.
  intros; omega.
Qed.

Lemma minus_lt : forall a b, a < b -> b - a = S (pred (b - a)).  
  intros; omega.
Qed.

Hint Resolve div2_le div2_plus_lt_div2 div2_plus_lt_div2'.


Hint Extern 1 (@eq nat ?A ?B) => omega2.
Hint Extern 1 (?A <  ?B) => omega2.
Hint Extern 1 (?A <= ?B) => omega2.
Hint Extern 1 (?A >  ?B) => omega2.
Hint Extern 1 (?A >= ?B) => omega2.