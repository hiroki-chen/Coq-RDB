(* Copyright (c) 2009, Harvard University
 * All rights reserved.
 *
 * Authors: Ryan Wisnesky
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

(* SQL style queries ****************************************)

Require Import Omega DataModel RelationalModel String List.

Definition ndec : forall (a b: nat), {a < b} + {a >= b}.
  refine (fun a b => 
    match le_gt_dec b a with
      | left _ => right _ 
      | right _ => left _
    end); omega.
Qed.

Definition checkBound n (I:Typing) : {n < length I} + {n >= length I}.
  exact (fun n I => ndec n (length I)).
Qed.

Definition checkBounds : forall (l: list nat) (I: Typing),
 {bounded I l} + {~bounded I l}.
 intros l I; revert l.
  refine (fix checkBounds (l : list nat) : {bounded I l} + {~bounded I l} :=
    match l as l' return {bounded I l'} + {~bounded I l'} with
      | nil => left _
      | a :: b => 
        if checkBound a I then
          if checkBounds b then left _ else right _
        else right _
    end); clear checkBounds; simpl; try tauto; intuition omega.
Qed.
Definition typ_eq_dec : forall (t u: typ), {t = u} + {t <> u}.
  decide equality.
Qed.

(* The main difference between SQL and RA is that SQL queries
   aren't explicitly typed. *)
Inductive atomicExp' : Set :=
| atom' : forall t (c: typDenote t), atomicExp'
| var'  : forall (n: nat), atomicExp'.

Inductive compareExp' : Set :=
| compareEq' : atomicExp' -> atomicExp' -> compareExp'
| compareLt' : atomicExp' -> atomicExp' -> compareExp'
| compareGt' : atomicExp' -> atomicExp' -> compareExp'.

Inductive whereExp' : Set :=
| trueExp'  : whereExp' 
| falseExp' : whereExp' 
| compExp': compareExp' -> whereExp'
| andExp' : whereExp' -> whereExp' -> whereExp'
| orExp'  : whereExp' -> whereExp' -> whereExp'
| notExp' : whereExp' -> whereExp'.

Inductive raExp' : Set :=
 | varExp'    : string -> Typing -> raExp'  
 | unionExp'  : raExp' -> raExp' -> raExp'
 | interExp'  : raExp' -> raExp' -> raExp'
 | selectExp' : raExp' -> whereExp'  -> raExp'
 | gprojExp'  : list nat -> raExp' -> raExp' 
 | prodExp'   : raExp' -> raExp' -> raExp'.
 

(* Translation into relational algebra ********************** *) 
(* To translate, we have to type-check as we go. *)

Section Z.

Variable F : forall I, DBSet I.

(*
Fixpoint checkBounds (l: list nat) (I: Typing) :
  option (list { x | x < length I }) :=
 match l with
   | nil => Some nil
   | a :: b => match ndec a (length I) with
                 | left pf => 
                   match checkBounds b I with
                     | None => None
                     | Some l' => Some (cons (exist _ a pf) l')
                   end
                 | right _ => None
               end
 end.
*)

Fixpoint atomicConv I e {struct e} : option (sigT (atomicExp I)) := 
 match e with
   | atom' t c => Some (existT _ t (atom I c))
   | var' n => match checkBound n I with
                 | left pf => Some (existT _ (nthTyp pf) (var pf))
                 | right pf => None
               end
end.

Definition compareConv I (e: compareExp') : option (sigT (compareExp I)).
intros I. refine (fix compareConv e {struct e} : option (sigT (compareExp I)) :=
 match e with
   | compareEq' a b => match atomicConv I a , atomicConv I b with
                         | Some (existT ta a') , Some (existT tb b') => 
                           match typ_eq_dec ta tb with
                             | left pf => _
                             | right pf => None
                           end
                         | _ , _ => None
                       end
   | compareLt' a b => match atomicConv I a , atomicConv I b with
                         | Some (existT ta a') , Some (existT tb b') => 
                           match typ_eq_dec ta tb with
                             | left pf => _
                             | right pf => None
                           end
                         | _ , _ => None
                       end
   | compareGt' a b => match atomicConv I a , atomicConv I b with
                         | Some (existT ta a') , Some (existT tb b') => 
                           match typ_eq_dec ta tb with
                             | left pf => _
                             | right pf => None
                           end
                         | _ , _ => None
                       end
 end ).
subst; exact (Some (existT _ _ (compareEq a' b' ))).
subst; exact (Some (existT _ _ (compareLt a' b' ))).
subst; exact (Some (existT _ _ (compareGt a' b' ))).
Defined.

Fixpoint sql2RA' I (e: whereExp') {struct e} : option (whereExp I) :=
 match e with
   | trueExp'  => Some (trueExp I)
   | falseExp' => Some (falseExp I)
   | compExp' c => match compareConv I c with
                       | Some (existT ta a')  => Some (compExp a')
                       | None => None
                     end
   | andExp' a b  => match sql2RA' I a , sql2RA' I b with
                       | Some a' , Some b' => Some (andExp a' b')
                       | _ , _ => None
                     end
   | orExp' a b => match sql2RA' I a , sql2RA' I b with
                       | Some a' , Some b' => Some (orExp a' b')
                       | _ , _ => None
                     end
   | notExp' a => match sql2RA' I a with
                    | Some a' => Some (notExp a')
                    | None => None
                  end
 end.

Definition sigBin T (x y: sigT (raExp T)) (op: forall (I : Typing), 
  raExp T I -> raExp T I -> raExp T I)
  : option (sigT (raExp T)).
intros; refine (
  match x , y with
    | existT J R , existT J' R' => 
      match typing_eq_dec J J' with
        | left pf' => _              
        | right _  => None
      end
  end);
subst; apply Some; apply (@existT _ _ J'); apply op; assumption.
Defined.

Definition sigProd T (x y: sigT (raExp T) ) : option (sigT (raExp T)).
intros; refine (
  match x , y with
    | existT J R , existT J' R' => _
  end);
subst; apply Some; apply (@existT _ _ (J ++ J'));
apply prodExp; assumption.
Defined.

Fixpoint sql2RA (q: raExp') : option (sigT (raExp (fun _ => string))) :=
  match q with
    | varExp' s J => Some (existT _ J (@varExp _ J s))
    | prodExp' a b => match sql2RA a , sql2RA b with
                       | Some a' , Some b' => sigProd _ a' b' 
                       | _ , _ => None
                     end
    | interExp' a b => match sql2RA a , sql2RA b with
                        | Some a' , Some b' => sigBin _ a' b' (@interExp _)
                        | _ , _ => None
                      end
    | unionExp' a b => match sql2RA a , sql2RA b with
                        | Some a' , Some b' => sigBin _ a' b' (@unionExp _ )
                        | _ , _ => None
                      end
    | selectExp' q p => match sql2RA q with
                          | None => None
                          | Some a' => 
                            match a' with
                              | existT J x => 
                                match sql2RA' J p with
                                  | None => None
                                  | Some z => Some (existT _ _ (selectExp x z)) 
                                end
                            end
                        end
    | gprojExp' cols q => 
      match sql2RA q with
        | Some a' => 
          match a' with
            | existT J a => 
              match checkBounds cols J with
                | left pf => Some (existT _ _ (gprojExp pf a)) 
                | right _ => None
              end
          end
        | None => None
      end
  end.

End Z.

