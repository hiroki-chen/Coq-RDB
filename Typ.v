(* Copyright (c) 2009, Harvard University
 * All rights reserved.
 *
 * Authors: Avraham Shinnar, Ryan Wisnesky
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
Require Import Basis.
Require Import SetoidDec.
Require Import SetoidClass.

Module OT := OrderedTypeNM.

Set Implicit Arguments. Unset Strict Implicit.

Definition nat_dec : forall (a b: nat), {a = b} + {a < b} + {a > b}.
 intros. pose (lt_eq_lt_dec a b).
 destruct s. destruct s. auto. auto. auto.
Qed.

(* natural numbers, and unit, as the column types for now *)
Inductive typ0 : Set :=
| nt  : typ0
| unt : typ0
| boo : typ0
| chr : typ0
| str : typ0
| lst : typ0 -> typ0
| opt : typ0 -> typ0.

(* nat is an ordered type *)
Definition natEq (a b: nat) : Prop := a = b.
Definition natLt (a b: nat) : Prop := a < b.

Definition nat_trans : Transitive natLt.
unfold Transitive. unfold natLt. intros. omega.
Defined.

Definition natOrd : OT.OrderedType nat.
refine (@ OT.Build_OrderedType nat (eq_setoid nat) natLt nat_trans _ _);
 unfold natLt, Transitive, complement; intros; simpl in *; try omega.
 destruct (nat_dec x y). destruct s.
  apply EQ. assumption.
  apply LT. assumption.
  apply GT. omega.
Defined.

(* unit is an ordered type *)
Definition unitEq (a b: unit) : Prop := True.
Definition unitLt (a b: unit) : Prop := False.

Definition unit_trans : Transitive unitLt.
unfold Transitive. unfold unitLt. intros. contradiction.
Defined.

Definition unitOrd : OT.OrderedType unit. 
refine (@ OT.Build_OrderedType unit (eq_setoid unit) unitLt unit_trans _ _);
 unfold unitEq; unfold unitLt; intuition.
 apply EQ. destruct x; destruct y. reflexivity.
Defined.

(* bool is an ordered type *)
Definition boolEq (a b : bool) : Prop := a = b.
Definition boolLt (a b : bool) : Prop := a = false /\ b = true.

Definition bool_trans : Transitive boolLt.
unfold Transitive. unfold boolLt. destruct x; destruct y; destruct z; tauto.
Defined.

Definition boolOrd : OT.OrderedType bool.
refine (@ OT.Build_OrderedType bool (eq_setoid bool) boolLt bool_trans _ _);
 unfold boolEq; unfold boolLt; intuition; subst; try congruence.
 destruct x; destruct y.
   refine (EQ _ _); simpl; auto.
   refine (GT _ _); simpl; auto.
   refine (LT _ _); simpl; auto.
   refine (EQ _ _); simpl; auto.
Defined.

(* ascii is an ordered type *)
Definition to_lower (a' : ascii) : ascii :=
  let a := nat_of_ascii a' in
  if le_lt_dec a (nat_of_ascii "z"%char) then
    if le_lt_dec (nat_of_ascii "a"%char) a then
      ascii_of_nat (a - nat_of_ascii "a"%char + nat_of_ascii "A")
    else a'
  else a'.

Definition charEq (a b : ascii) : Prop := 
  let a := nat_of_ascii (to_lower a) in
  let b := nat_of_ascii (to_lower b) in
  a = b.
Definition charLt (a b : ascii) : Prop := 
  let a := nat_of_ascii (to_lower a) in
  let b := nat_of_ascii (to_lower b) in
  a < b.

Definition char_trans : Transitive charLt.
unfold Transitive. unfold charLt. intros. eapply lt_trans; eassumption.
Qed.

Instance charEq_Setoid : Setoid ascii.
refine (@Build_Setoid _ charEq _).
  unfold charEq. intuition.
Defined.

Definition asciiOrd : OT.OrderedType ascii.
refine (@ OT.Build_OrderedType ascii charEq_Setoid charLt char_trans _ _);
 unfold charEq; unfold charLt; intuition. 
 unfold complement. intros. simpl in H0. unfold charEq in H0. rewrite H0 in *. omega.
 destruct (nat_dec (nat_of_ascii (to_lower x)) (nat_of_ascii (to_lower y))). destruct s.
   refine (EQ _ _). unfold equiv. simpl. unfold charEq. auto. 
   refine (LT _ _); auto.
   refine (GT _ _); auto.
Defined.

(* string is an ordered type *)

Fixpoint strEq (a b : string) : Prop :=
  match a,b with
    | EmptyString, EmptyString => True
    | String x a', String y b' => charEq x y /\ strEq a' b'
    | _, _ => False
  end.
Fixpoint strLt (a b : string) : Prop :=
  match a,b with
    | EmptyString, String _ _ => True
    | String x a', String y b' => charLt x y \/ (charEq x y /\ strLt a' b')
    | _, _ => False
  end.

Lemma strEq_trans : Transitive strEq.
unfold Transitive. induction x; destruct y; destruct z; intuition eauto.
 inversion H. inversion H. simpl in *.  intuition. unfold charEq in *. rewrite H1; auto.
 specialize (IHx _ _ H2 H3). auto.
Qed.

Definition strEq_Setoid : Setoid string.
refine (@Build_Setoid _ strEq _); unfold strEq; intuition.
unfold Reflexive. induction x; intuition.
unfold Symmetric; induction x; destruct y; intuition eauto. symmetry. auto.
 specialize (IHx _ H1); auto.
exact strEq_trans.
Defined.

Definition strOrd : OT.OrderedType string.
refine (@ OT.Build_OrderedType string (strEq_Setoid) strLt _ _ _);
 unfold strEq; unfold strLt; intuition.
  unfold Transitive.
   induction x; destruct y; destruct z; unfold charLt in *; intuition eauto. left; omega.
     unfold charEq in *. rewrite H0 in *. tauto.
     unfold charEq in *. rewrite H in *; tauto.
     unfold charEq in *. rewrite H in *; rewrite H0 in *. right. intuition.
     eapply IHx; eauto.
  generalize dependent y; induction x; destruct y; unfold charLt in *; simpl in *; intuition eauto.
    unfold complement. simpl. auto.
    unfold complement; simpl. intuition. unfold charEq in *.  omega.
    unfold complement; simpl; intuition. eapply IHx; eauto.
  generalize dependent y; induction x; destruct y; intros.
    refine (EQ _ _); simpl; auto.
    refine (LT _ _); simpl; auto.
    refine (GT _ _); simpl; auto.
    pose asciiOrd.
    destruct (ordCompare a a0).
      refine (LT _ _); auto.
      destruct (IHx y). refine (LT _ _); auto. refine (EQ _ _); simpl; auto. refine (GT _ _); intuition.
      refine (GT _ _). intuition.
Defined.

(* option A is an ordered type if A is *)
Section OptOrd.
Variable (A:Set).
Variable (O:OT.OrderedType A).
Definition optEq (a b : option A) : Prop := 
  match a, b with
    | None, None => True
    | Some x, Some y => (x == y)%type
    | _, _ => False
  end.

Definition optLt (a b : option A) : Prop := 
  match a, b with
    | None, None => False
    | None, Some _ => True
    | Some _, None => False
    | Some x, Some y => (x << y)%type
  end.

Definition opt_equiv : Equivalence optEq.
Proof. split; red; destruct x; try destruct y; try destruct z; simpl; intuition; clsubst*; intuition. Qed.

Definition optCompare (a b : option A) : Compare optLt optEq a b.
destruct a; destruct b; unfold optLt, optEq; simpl.
destruct (ordCompare a a0).
  apply LT; auto.
  apply EQ; auto.
  apply GT; auto.
apply GT; auto.
apply LT; auto.
apply EQ; auto.
Qed.

Definition optOrd : OT.OrderedType (option A).
refine (@ OT.Build_OrderedType (option A) (Build_Setoid opt_equiv) optLt _ _ optCompare);
 unfold optEq; unfold optLt; intuition; subst; try congruence.
red; destruct x; destruct y; intuition; destruct z; intuition; rewrite H; intuition.
red; destruct x; destruct y; simpl; intuition; order.
Qed.

End OptOrd.


(* option A is an ordered type if A is *)
Section ListOrd.
Variable (A:Set).
Variable (O:OT.OrderedType A).

Fixpoint listEq (a b : list A) :=
  match a,b with
    | nil,nil => True
    | l :: ls, r :: rs => l == r /\ listEq ls rs
    | _, _ => False
  end.

Fixpoint listLt (a b : list A) :=
  match a,b with
    | nil,nil => False
    | l :: ls, r :: rs => l << r \/ (l == r /\ listLt ls rs)
    | nil,_ => True
    | _,nil => False
  end.

Definition list_equiv : Equivalence listEq.
Proof. split; red; induction x; try destruct y; try destruct z; simpl; intuition; clsubst*; intuition. eauto. Qed.

Definition listCompare (a b : list A) : Compare listLt listEq a b.
induction a; destruct b; unfold listLt, listEq; simpl.
apply EQ; auto.
apply LT; auto.
apply GT; auto.
destruct (ordCompare a a1).
  apply LT; auto.
  destruct (IHa b).
    apply LT; auto.
    apply EQ; auto.
    apply GT; intuition.
  apply GT; intuition.
Defined.

Lemma listLt_trans : Transitive listLt.
Proof. red.
  induction x; destruct y; destruct z; simpl; intuition; try solve[order].
  right. clsubst*. intuition. eauto.
Qed.

Lemma listLt_not_eq x y : listLt x y -> complement listEq x y.
Proof. red.
  induction x; destruct y; simpl; intuition. order. eauto.
Qed.

Definition listOrd : OT.OrderedType (list A).
refine (@ OT.Build_OrderedType (list A) (Build_Setoid list_equiv) listLt listLt_trans listLt_not_eq listCompare).
Qed.

End ListOrd.

Fixpoint typDenote0 (t:typ0) : Set :=
  match t with
    | nt => nat
    | unt => unit
    | boo => bool
    | chr => ascii
    | str => string
    | opt t' => option (typDenote0 t')
    | lst t' => list (typDenote0 t')
  end.

Fixpoint typOrd0 (t: typ0) : OT.OrderedType (typDenote0 t) :=
 match t with
   | nt => natOrd
   | unt => unitOrd
   | boo => boolOrd
   | chr => asciiOrd
   | str => strOrd
   | opt t' => optOrd (typOrd0 t')
   | lst t' => listOrd (typOrd0 t')
 end.

Module Type TNAMES.

Parameter typ: Set.
Parameter typDenote: typ -> Set.
Parameter tname_dec_eq :
 forall (n1 n2: typ), {n1=n2} + {n1<>n2}.

Parameter typOrd : forall (t: typ), OT.OrderedType (typDenote t).

End TNAMES.

Module OURTNAMES <: TNAMES.
 Definition typ := typ0.
 Definition typDenote := typDenote0.
 Definition tname_dec_eq : 
   forall (n1 n2: typ), {n1=n2} + {n1<>n2}.
 intros; decide equality.
 Defined.
 Definition typOrd := typOrd0.
 (* the other requirements are from the typeclass mechanism *)  
End OURTNAMES.

Export OURTNAMES.
Definition Typing : Set := list typ.

Fixpoint Tuple (A: Typing) : Set :=
 match A with
   | nil => unit
   | h :: t => typDenote h * Tuple t
 end%type.

Instance typOrdInst (t:typ) : OrderedType (typDenote t). 
intros. exact (typOrd t). Defined.

Definition test_typing : Typing :=
 nt :: unt :: nt :: opt nt :: nil.
 
Definition test_tuple : Tuple test_typing :=
 (0, (tt, (1, (Some 3, tt)))).

Definition test_typing' :=
 unt :: nt :: nil.

Definition test_tuple' : Tuple test_typing' :=
 (tt, (2, tt)).

Definition test_tuple'' : Tuple (test_typing ++ test_typing') 
 := (0, (tt, (1, (None, (tt, (2, tt)))))).

Fixpoint str_to_list (s:string) : list ascii :=
  match s with
    | EmptyString => nil
    | String a b => a :: (str_to_list b)
  end.

Definition showTyp A : typDenote A -> list ascii -> list ascii.
refine (fix showTyp A :=
  match A as A' return A = A' -> _ with
        | nt => fun pf1 t => _
        | unt => fun pf2 t => _
        | boo => fun pf2 t => _
        | chr => fun pf2 t => _
        | str => fun pf2 t => _
        | opt T => fun pf2 t => _
        | lst T => fun pf2 t => _
      end (refl_equal _)); subst; intros r.
 exact (dd t :: "," :: " "::r)%char.
 exact ( "t" ::"," :: " " :: r)%char.
 exact ((if t then "T" else "F")::","::" "::r)%char.
 exact (t::","::" "::r)%char.
 exact (str_to_list t ++ (","::" "::r))%char.
 simpl in t.
 induction t.
   exact ("}"::r)%char.
   exact (showTyp T a (","::" "::IHt)%char).
 exact (match t with
          | None => "?"::r
          | Some x => "!"::showTyp T x r
        end)%char.
Defined.

Definition showTuple I : Tuple I -> list ascii.
refine (fix showTuple I : Tuple I -> list ascii :=
  match I with
    | nil => fun _ => nil
    | a :: b => fun t => showTyp (fst t) (showTuple b (snd t))
  end).
Defined.

Fixpoint printTypName A (r:list ascii): list ascii:=
  match A with
        | nt =>  "N"%char::r
        | unt => "U"%char::r
        | boo => "B"%char::r
        | chr => "C"%char::r
        | str => "S"%char::r
        | opt T => "O"%char::printTypName T r
        | lst T => "L"%char::printTypName T r
  end.

Fixpoint readTypName (inp:list ascii): option (typ*list ascii):=
  match inp with
    | "N"%char::r => Some (nt, r)
    | "U"%char::r => Some (unt, r)
    | "B"%char::r => Some(boo, r)
    | "C"%char::r => Some (chr, r)
    | "S"%char::r => Some (str, r)
    | "O"%char::r => match readTypName r with 
                       | None => None
                       | Some (T, r') => Some (opt T, r')
                     end
    | "L"%char::r => match readTypName r with
                       | None => None
                       | Some (T, r') => Some (lst T, r')
                     end
    | _ => None
  end.

Lemma typNameRT A r : readTypName (printTypName A r) = Some (A, r).
Proof. induction A; simpl; auto; intros; rewrite IHA; auto. Qed.

Definition digitToascii (d:nat) (pf:d < 16) : ascii.
intros d. 
refine (match d as d' return d' < 16 -> ascii with
       | 0 => fun pf => "0"
       | 1 => fun pf => "1"
       | 2 => fun pf => "2"
       | 3 => fun pf => "3"
       | 4 => fun pf => "4"
       | 5 => fun pf => "5"
       | 6 => fun pf => "6"
       | 7 => fun pf => "7"
       | 8 => fun pf => "8"
       | 9 => fun pf => "9"
       | 10 => fun pf => "A"
       | 11 => fun pf => "B"
       | 12 => fun pf => "C"
       | 13 => fun pf => "D"
       | 14 => fun pf => "E"
       | 15 => fun pf => "F"
       | x => fun pf => False_rec ascii _
     end)%char.
omega.
Defined.

Definition asciiToDigit (a:ascii) : option nat
:= match a with
     | "0" => Some 0
     | "1" => Some 1
     | "2" => Some 2
     | "3" => Some 3
     | "4" => Some 4
     | "5" => Some 5
     | "6" => Some 6
     | "7" => Some 7
     | "8" => Some 8
     | "9" => Some 9
     | "A"|"a" => Some 10
     | "B"|"b" => Some 11
     | "C"|"c" => Some 12
     | "D"|"d" => Some 13
     | "E"|"e" => Some 14
     | "F"|"f" => Some 15
     | _ => None
   end%char.

Lemma digitRT d (pf:d<16) : asciiToDigit (digitToascii pf) = Some d.
Proof. do 16 (destruct d; auto). intros. elimtype False. omega. Qed.

Fixpoint ascii16_revToNum (l:list ascii) (pos:nat): option nat
  := match l with
       | nil => Some 0
       | x::y => match (asciiToDigit x), ascii16_revToNum y (pos * 16) with
                   | None, _ => None
                   | _, None => None
                   | Some d, Some r => Some (d*pos + r)
                 end
     end.

Definition ascii16toNum l := ascii16_revToNum (rev l) 1.

Lemma ascii16_revToNum_None_shift x s s' :
  ascii16_revToNum x s = None ->
  ascii16_revToNum x s' = None.
Proof.
  induction x; simpl; auto.
  intros. destruct (asciiToDigit a); auto.
  specialize (IHx (s*16) (s'*16)).
  destruct (ascii16_revToNum x (s*16)); try discriminate.
  rewrite IHx; auto.
Qed.

Lemma ascii16_revToNum_shift x q s m: 
  ascii16_revToNum x s = Some q ->
  ascii16_revToNum x (m*s) = Some (m*q).
Proof.
  induction x; simpl; intros.
    inversion H. f_equal. omega. 
    destruct (asciiToDigit a); try discriminate.
    generalize (@ascii16_revToNum_None_shift x (s*16) (m*s*16)).
    generalize (fun q => IHx q (s*16) m). intros.
    destruct (ascii16_revToNum x (s*16)); try discriminate.
    inversion H.
    rewrite <- mult_assoc.
    rewrite (H0 n0); auto.
      f_equal. rewrite mult_plus_distr_l. f_equal.  
      rewrite mult_assoc, mult_comm, mult_assoc, mult_comm. f_equal.
      rewrite mult_comm. auto.
Qed.

Lemma digitToAscii_dotless d pf : @digitToascii d pf <> "."%char.
Proof.
  intros. do 16 (destruct d; [simpl; discriminate|]). elimtype False. omega.
Qed.

Require Import Euclid.
(* returns a number as a backward base 16 ascii string *)
Program Fixpoint numTo16ascii_rev (n:nat) {measure n}: {l:list ascii|ascii16_revToNum l 1 = Some n /\ ~ In "."%char l}
  := let '(divex q r pf1 pf2) := eucl_dev 16 _ n
    in  @digitToascii r _ ::
    match q with
         | 0 => nil
         | S _ => numTo16ascii_rev q
    end.
Next Obligation.
omega.
Qed.
Next Obligation.
omega.
Qed.
Next Obligation.
rewrite digitRT.
destruct q.
simpl. split. f_equal. omega. intuition. elim (digitToAscii_dotless H0).
remember ((numTo16ascii_rev (S q)
             (numTo16ascii_rev_obligation_3 Heq_anonymous (eq_refl (S q))))).
destruct s. destruct a. simpl.
pose (ascii16_revToNum_shift 16 e). 
rewrite mult_1_r in e0. rewrite e0. split. 
  rewrite pf2. f_equal. omega.
  intuition. elim (digitToAscii_dotless H0).
Qed.
Next Obligation.
Require Import Program.Wf.
apply measure_wf.
apply lt_wf.
Defined.

Program Definition numTo16ascii n := rev (numTo16ascii_rev n).

Program Lemma num_revRT n : ascii16_revToNum (numTo16ascii_rev n) 1 = Some n.
Proof. intros n. destruct (numTo16ascii_rev n); simpl;  intuition. Qed.

Lemma numRT n : ascii16toNum (numTo16ascii n) = Some n.
Proof. unfold ascii16toNum, numTo16ascii; intros.
  rewrite rev_involutive. apply num_revRT.
Qed.

Program Definition tnumTo16ascii n r := rev_append (numTo16ascii_rev n) ("."%char::r).

Fixpoint splitAtDot (l:list ascii) : option (list ascii*list ascii)
  := match l with
       | nil => None
       | x::y => if (ascii_dec x "."%char)
         then Some (nil, y)
         else match splitAtDot y with
                | None => None
                | Some (l, y) => Some (x::l, y)
              end
     end.

Lemma splitAtDot_app l r : ~ In "."%char l -> splitAtDot (l ++ ("."%char :: r)) = Some (l, r).
Proof.
  induction l; auto. 
  simpl. intros.
  destruct (ascii_dec a "."%char).
    subst; intuition.
    rewrite IHl; auto.
Qed.

Lemma splitAtDot_revapp l r : ~ In "."%char l -> splitAtDot (rev_append l ("."%char :: r)) = Some (rev l, r).
Proof.
  intros. rewrite rev_append_rev, splitAtDot_app; auto.
  intro. elim H. apply <- In_rev; auto.
Qed.

Definition tascii16toNum (l:list ascii) : option (nat*list ascii)
  := match splitAtDot l with
       | None => None
       | Some (nl, rl) => 
         match ascii16toNum nl with
           | None => None
           | Some n => Some (n, rl)
         end
     end.

Lemma numTo16ascii_rev_dotless n  : ~ In "."%char (proj1_sig (numTo16ascii_rev n)).
Proof.
Proof. intros n. destruct (numTo16ascii_rev n); simpl;  intuition. Qed.

Lemma tnumRT n r : tascii16toNum (tnumTo16ascii n r) = Some (n, r).
Proof. 
  unfold tascii16toNum, tnumTo16ascii; intros.
  rewrite splitAtDot_revapp.
  pose (numRT n)as e. unfold numTo16ascii in e.
  rewrite e. auto.
  apply numTo16ascii_rev_dotless.
Qed.

Definition printNat n r := tnumTo16ascii n r.
Definition readNat l := tascii16toNum l.
Lemma natRT n r : readNat (printNat n r) = Some (n, r).
Proof. apply tnumRT. Qed.

Definition printTypDenote A : typDenote A -> list ascii -> list ascii.
refine (fix printTypDenote A :=
  match A as A' return A = A' -> _ with
        | nt => fun pf1 t  => _
        | unt => fun pf2 t => _
        | boo => fun pf2 t => _
        | chr => fun pf2 t => _
        | str => fun pf2 t => _
        | opt T => fun pf2 t => _
        | lst T => fun pf2 t => _
      end (refl_equal _)); subst; intros r.
 exact (printNat t r).
 exact (r).
 exact ((if t then "T" else "F")::r)%char.
 exact (t::r)%char.
 pose (str_to_list t).
 refine (printNat (List.length l) _).
 induction l.
   exact r.
   exact (a::IHl).
 simpl in t.
 refine (printNat (List.length t) _).
 induction t.
 exact r.
 exact (printTypDenote T a IHt).
 simpl in t.
 exact (match t with
          | None => "?"::r
          | Some x => "!"::printTypDenote T x r
        end)%char.
Defined.

Require Import Sumbool.
Definition readTypDenote A : list ascii -> option (typDenote A * list ascii).
refine (fix readTypDenote A :=
  match A as A' return A = A' -> _ with
        | nt => fun pf1  => _
        | unt => fun pf2 => _
        | boo => fun pf2 => _
        | chr => fun pf2 => _
        | str => fun pf2 => _
        | opt T => fun pf2 => _
        | lst T => fun pf2 => _
      end (refl_equal _)); subst; simpl; intros r.
 exact (readNat r).
 exact (Some (tt, r)).
 exact (match r with
          | nil => None
          | x::y => 
            if (sumbool_or _ _ _ _ (ascii_dec x "T") (ascii_dec x "t"))
              then Some (true, y)
              else if sumbool_or _ _ _ _ (ascii_dec x "F") (ascii_dec x "f")
                then Some (false, y)
                  else None
        end)%char.
 exact (match r with
          | nil => None
          | x::y => Some (x, y)
        end).
(* string *)
refine (match (readNat r) with
          | None => None
          | Some (len, r') => _
        end).
revert r'. induction len; intros r'.
 exact (Some (EmptyString, r')).
 refine (match r' with
           | nil => None
           | x::y => match (IHlen y) with
                            | None => None
                            | Some (s,r'') => Some (String x s, r'')
                          end
         end).
(* list *)
refine (match (readNat r) with
          | None => None
          | Some (len, r') => _
        end).
revert r'. induction len; intros r'.
 exact (Some (nil, r')).
 refine (match readTypDenote T r' with
           | None => None
           | Some (td, r'') => match (IHlen r'') with
                            | None => None
                            | Some (s,r''') => Some (td::s, r''')
                          end
         end).
   exact (match r with
          | nil => None
          | x::y => 
            if (ascii_dec x "?")
              then Some (None, y)
              else if (ascii_dec x "!")
                then match readTypDenote T y with
                       | None => None
                       | Some (td, r'') => Some (Some td, r'')
                     end
                else None
        end)%char.
Defined.

Lemma typDenoteRT A d r : readTypDenote A (printTypDenote d r) = Some (d, r).
Proof. induction A; simpl; intros.
  apply natRT.
  destruct d; auto.
  destruct d; simpl; auto.
  auto.
  rewrite natRT.
  remember (List.length (str_to_list d)) as n.
  revert d Heqn.
  induction n; intros; simpl;
  destruct d; simpl in *; try discriminate. 
    auto.
    inversion Heqn. subst n. clear Heqn.
    rewrite IHn; auto.
    
  rewrite natRT.
  remember (List.length d) as n.
  revert d Heqn.
  induction n; intros; simpl;
  destruct d; simpl in *; try discriminate. 
    auto.
    inversion Heqn. subst n. clear Heqn.
    rewrite IHA, IHn; auto.
  
  destruct d; simpl in *; auto.
  rewrite IHA; auto.
Qed.

Definition printTypNameDenote A (d:typDenote A) (r:list ascii) : list ascii
  := printTypName A (printTypDenote d r).

Definition readTypNameDenote (r:list ascii) : option (sigS typDenote *list ascii)
  := match readTypName r with
       | None => None
       | Some (T,r') =>
         match readTypDenote T r' with
           | None => None
           | Some (t, r'') => Some (existS _ _ t, r'')
         end
     end.

Lemma typNameDenoteRT A d r : readTypNameDenote (@printTypNameDenote A d r) = Some (existS _ _ d, r).
Proof. unfold readTypNameDenote, printTypNameDenote. intros.
  rewrite typNameRT, typDenoteRT. auto.
Qed.

Definition printTuple' I : Tuple I -> list ascii -> list ascii.
refine (fix printTuple' I : Tuple I -> list ascii -> list ascii :=
  match I with
    | nil => fun _ r => r
    | a :: b => fun t r => printTypNameDenote (fst t) (printTuple' b (snd t) r)
  end).
Defined.

Definition printTuple I (t:Tuple I) (r:list ascii) : list ascii
  := printNat (List.length I) (printTuple' t r).

Fixpoint readTuple' (r:list ascii) n : option (sigS Tuple * list ascii) :=
  match n with
    | 0 => Some (existS Tuple nil tt, r)
    | S n' => 
      match readTypNameDenote r with
        | None => None
        | Some (existS T td, r') => 
          match readTuple' r' n' with
            | None => None
            | Some (existS rI rd, r'') => Some (existS Tuple (T::rI) (td,rd), r'')
          end
      end
  end.

Definition readTuple (r:list ascii) : option (sigS Tuple * list ascii) :=
  match readNat r with
    | None => None
    | Some (n, r'') => readTuple' r'' n
  end.

Lemma tuple'RT I T r : readTuple' (@printTuple' I T r) (List.length I) = Some (existS _ I T, r).
Proof.
  induction I; simpl; intros.
    destruct T; auto.
    rewrite typNameDenoteRT, IHI, <- surjective_pairing; auto.
Qed.

Lemma tupleRT I T r : readTuple (@printTuple I T r) = Some (existS _ I T, r).
Proof. unfold printTuple, readTuple; intros.
  rewrite natRT, tuple'RT. auto.
Qed.
