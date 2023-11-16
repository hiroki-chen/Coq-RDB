(* Copyright (c) 2009, Harvard University
 * All rights reserved.
 *
 * Authors: Ryan Wisnesky, Gregory Malecha
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

Require Import RAInterface.
Require Import DBInterface.
Require Import SQL.
Require Import Ascii String.
Require Import Ynot.
Require Import List.
Require Import DataModel.
Require Import RelationalModel.
Require Import Optimizer.

Open Scope hprop_scope.
Open Scope stsep_scope.

Inductive DBCmd : Set :=
| DBQuery : raExp' -> DBCmd
| DBLoad  : forall I (s: string) (t: list (Tuple I)), DBCmd
| DBSave  : string -> string -> DBCmd.

Definition isSpace (ch:ascii) : bool :=
  match nat_of_ascii ch with
    | 9   => true
    | 13 => true
    | 10 => true
    | 32 => true
    | _ => false
  end.

Fixpoint rstrip (s : string) : string :=
  match s with
    | EmptyString => EmptyString
    | String a b => match rstrip b with 
                      | EmptyString => if isSpace a then EmptyString else String a EmptyString
                      | b => String a b
                    end
  end.

Fixpoint lstrip (s : string) : string :=
  match s with
    | EmptyString => EmptyString
    | String a b => if isSpace a then lstrip b else s
  end.

Definition strip (s : string) : string := lstrip (rstrip s).

Require Import String.
Definition getCmd : STsep __ (fun c: option DBCmd => __).
Require Import Charset Packrat.
Require Import DmlParser.
Require Import Basis.
Require Import SqlParser.
refine ( printStringLn "Enter Command [Load | Query | Save]" <@> _ ;;
         printString ">> " <@> _ ;;
         x <- readStringLn ;
         match strip x with
           | "Load" =>    printString   "File> "
                       ;; filename <- readStringLn 
                        ; data <- readFile (strip filename)
                        ; match data with
                            | None => 
                              printStringLn ("[!!] No such file '" ++ filename ++ "'")
                              ;; {{ Return None }}
                            | Some dml =>
                                is <- STRING_INSTREAM.instream_of_list_ascii (str2la (strip dml))
                              ; printStringLn ("""" ++ (strip dml) ++ """") <@> _ 
                             ;; z <- dml_parse is 0
                              ; match z with
                                  | Some (n, Some (s, existT J l)) => 
                                       INSTREAM.close is 
                                    ;; printStringLn ("[--] Table parsed '" ++ s ++ "'")
                                    ;; {{ Return (Some (DBLoad J s l)) }}

                                  | Some (_, None) =>
                                       INSTREAM.close is 
                                    ;; printStringLn "[--] Table parsed"
                                    ;; printStringLn "[!!] Type-check failed"
                                    ;; {{ Return None }}
                                  | _ =>
                                       INSTREAM.close is 
                                    ;; printStringLn "[!!] Bad parse"
                                    ;; {{ Return None }}
                                end
                          end
           | "Query" =>   printString "SQL> "
                       ;; str <- readStringLn 
                        ; is <- STRING_INSTREAM.instream_of_list_ascii (str2la (strip str))
                        ; z <- sql_parse is 0
                        ; match z with
                            | Some (n, x) =>
                                  INSTREAM.close is
                               ;; printStringLn "[--] Query Parsed"                      
                               ;; {{ Return (Some (DBQuery x)) }}

                            | _ =>
                                  INSTREAM.close is 
                               ;; printStringLn "[!!] Bad Query"
                               ;; {{ Return None }}
                          end
           | "Save" =>    printString "Table> "
                       ;; table <- readStringLn
                        ; printString "File> "
                       ;; file <- readStringLn
                        ; {{ Return (Some (DBSave (strip table) (strip file))) }}
           | _ =>   printStringLn ("[!!] Bad Command '" ++ (strip x) ++ "'")
                 ;; {{ Return None }}
         end )%string;
 unfold DML_correct;
 unfold SQL_correct;
 unfold Packrat.ans_correct;
  ( cbv beta; sep fail auto ).
Qed.

Definition forever : forall T (I : T -> hprop)
  (B :  forall t, STsep (I t) (fun x:T => I x)) t, 
  STsep (I t) (fun _:unit => (I t)  * [False]).
  intros. refine (
    SepFix I
        (fun t (_:unit) => I t * [False])
        (fun self t =>
          z <- B t ;
          {{self z }}
        ) t );
    solve [ sep fail auto ].
Qed.

Require Import BTreeRA.
Require Import FSetListNM.
Require Import BPlusTreeImpl.

Module Params : BTreeParams.
  Definition SIZE := 128.
  Definition Mk_Set I := @Make (Tuple I) (tupleOrd I).
  Definition BPT : forall (J:Typing), 
    BPlusTreeImplModel.bpt_map SIZE (value J) (tupleOrd J) (value_eq_ok J).
  Proof.
    intros. refine (BPlusTreeImpl _ _ (value J) (tupleOrd J) (value_eq_ok J)).
    unfold SIZE. omega.
    unfold SIZE. repeat constructor.
  Qed.
End Params.

Module engine := BTreeImpl Params.

Module top := ImperativeDB engine.

Definition forever' p := @forever 
  (sigT (fun x => prod Info (inhabited (Env top.F x)))) 
 (fun x => match x with
             | existT g (m, e) => 
                 e ~~ top.rep (G:=g) p e * [accurate m e]
           end).

Require Import Eqdep.
Open Scope string_scope.
Require Import Basis.
Open Scope stsepi_scope.

Require Import SetoidClass.

Definition proc1 (p: top.tx) (G: Ctx) m (E: [Env top.F G]) :
 STsep ( E ~~ top.rep p (G:=G) E * 
                     [accurate (F:=engine.F) m (G:=G) E]
         )
     (fun r : sigT (fun x1 => prod Info (inhabited (Env top.F x1)))  =>
        match r with
          | existT G (m, E) =>  E ~~ top.rep p (G:=G) E * [accurate m E]
        end).
 refine (fun p G m E =>
 c <- getCmd <@>  (E ~~ [accurate (F:=engine.F) m (G:=G) E] * top.rep p (G:=G) E) ;
 match c with
   | None => {{ Return (@existT Ctx (fun E => prod Info (inhabited (Env top.F E))) G (m, E))  
              <@>  (E ~~ [accurate (F:=engine.F) m (G:=G) E] * top.rep p (G:=G) E) }} 
   | Some w => 
     match w with 
       | DBQuery q => t <- @top.execQuery G m E p q ;
         match t with
           | None => {{ Return (@existT Ctx (fun E => prod Info (inhabited (Env top.F E))) G (m, E))  
             <@>  (E ~~ top.rep p (G:=G) E * [accurate (F:=engine.F) m (G:=G) E]) }} 
           | Some (existT j r) => 
             match sql2RA q as pf0 return sql2RA q = pf0 -> _ with
               | None => fun pf0 => {{ !!! }}
               | Some (existT J' e) => fun pf0 =>  
                 match typing_eq_dec j J' as pf1 return typing_eq_dec j J' = pf1 -> _ with
                   | right pf => fun pf1 => {{ !!! }}
                   | left pf => fun pf1 => _
                 end (refl_equal _)
             end (refl_equal _)
         end
         
       | DBLoad j s t => 
         m' <- @top.setTable G m E p j s t <@> ((E ~~ [accurate (F:=engine.F) m (G:=G) E])) ;
         {{ Return (@existT Ctx (fun x1 => prod Info (inhabited (Env top.F x1)))
                                           ((s, j) :: G)  (m', (E ~~~ (mkTbl top.F (I:=j) t, E)))) 
              <@>  (E ~~ [accurate (F:=engine.F) m (G:=G) E] * [@accurate engine.F m' ((s, j)::G) (mkTbl engine.F t, E) ] *  
                   (@top.rep p ((s, j)::G)) (mkTbl engine.F t, E) (* *
[(updInfo m s j (mkInfo (F:=F) (I:=j) (mkTbl F (I:=j) t)) = m')] *)
) }} 
       | DBSave tbl fn =>
         ser <- @top.serializeTable _ E p tbl <@> (E ~~ [accurate (F:=engine.F) m (G:=G) E]) ;
         match ser with 
           | None => printStringLn "No such table" <@> _
           | Some serialized =>
             success <- writeFile fn serialized <@> _ ;
             (if success then
                printStringLn "[--] Serialization successful"
              else
                printStringLn ("[--] Failed to write file '" ++ fn ++ "'")) <@> _ ;;
             printStringLn serialized <@> _
         end <@> (E ~~ [accurate (F:=engine.F) m (G:=G) E] * top.rep p (G:=G) E) ;;
         {{ Return (@existT Ctx (fun E => prod Info (inhabited (Env top.F E))) G (m, E))  
             <@>  (E ~~ [accurate (F:=engine.F) m (G:=G) E] * top.rep p (G:=G) E) }} 
     end
 end ) ; try sep fail auto.

 2: rewrite pf0; rewrite pf1; try sep fail auto.
 2: rewrite pf0; sep fail auto.
 rewrite pf0. rewrite pf1.
 refine (
   top.printTable (E ~~~ @cast1 J' j (fun x => DBRel (A:=x) (top.F x))
     (raDenote (F:=top.F) (inst (F:=top.F) (G:=G) E e)) (sym_eq pf)) (@cast1 J' j _ r (sym_eq pf)) <@> (E ~~ top.rep p (G:=G) E * [accurate (F:=engine.F) m (G:=G) E]) ;; 
   printStringLn "" <@> _ ;;
   top.clearTable (E ~~~ @cast1 J' j (fun x => DBRel (A:=x) (top.F x))
     (raDenote (F:=top.F) (inst (F:=top.F) (G:=G) E e)) (sym_eq pf)) (@cast1 J' j _ r (sym_eq pf))
   <@> (E ~~ top.rep p (G:=G) E *  [accurate (F:=engine.F) m (G:=G) E]) ;;
   {{ Return (@existT Ctx (fun x1 => prod Info (inhabited (Env top.F x1))) G (m, E))
     <@>  (E ~~ top.rep p (G:=G) E *  [accurate (F:=engine.F) m (G:=G) E] *
       match sql2RA q with
         | None => [False]
         | Some (existT J' e) => [ j = J']
       end
     ) }} ). 

 inhabiter. unpack_conc. subst E. 
 apply pack_injective in H0. rewrite <- H0. clear H0. clear x0.
 sep fail auto. generalize (raDenote (F:=top.F) (inst (F:=top.F) (G:=G) x e)). 
 generalize pf. rewrite <- pf. 
 intros. unfold cast1. unfold eq_rec_r. rewrite <- eq_rec_eq.
 rewrite <- eq_rec_eq. rewrite <- eq_rec_eq.
 sep fail auto.
 
 sep fail auto.
 sep fail auto.
 sep fail auto.

 2: sep fail auto.
 2: rewrite pf0; sep fail auto.

 Focus 2.
 rewrite pf0. intros. destruct v. sep fail auto.
 assert (x = G). congruence.
 subst x. destruct p0. apply inj_pair2 in H2.
   assert (i0 = E). congruence. assert (i = m). congruence.
   subst i. subst i0. unpack_conc. sep fail auto.

 sep fail auto.
Qed.

Definition emptyInfo : Info := 
 fun _ _ => MkInfo' true.

Definition main : STsep __ (fun r: unit => [False]).
 refine ( t <- top.init ;
          x <- @forever' t (fun x => match x with
                                       | existT G (m,r) => @proc1 t G m r
                                     end) 
 (existT (fun x => prod Info (inhabited (Env top.F x))) 
    nil  (emptyInfo, inhabits tt) )  ;
          {{ Return tt }} );
sep fail auto.
cut (accurate (F:=engine.F) emptyInfo (G:=nil) tt).
sep fail auto.
red.
intros.
unfold RelationalModel.lookup. simpl. reflexivity.
Qed.
