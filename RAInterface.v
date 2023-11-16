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

Require Import FSetInterfaceNM.
Require Import FSetListNM.
Require Import RelationalModel.
Require Import DataModel.
Require Import List.
Require Import SetoidClass.
Require Import Ascii.
Require Import Ynot.
Require Import Basis.
Require Import String.
Set Implicit Arguments.

Module Type RAInterface.

 Parameter F : forall (I: Typing), DBSet I.

 Parameter u : Typing -> Set.
 Parameter rep' : forall I, u I ->  DBRel (F I) -> hprop.
 
 Open Scope hprop_scope.
 
 Parameter impUnion : forall I (R1 R2: [DBRel (F I)])
    (p1 p2: u I), STsep (R1 ~~ R2 ~~ rep' p1 R1 * rep' p2 R2)
    (fun r:unit => R1 ~~ R2 ~~ 
      rep' p1 (union R1 R2) * rep' p2 R2).

 Parameter impInter : forall I (R1 R2: [DBRel (F I)])
    (p1 p2: u I), STsep (R1 ~~ R2 ~~ rep' p1 R1 * rep' p2 R2)
    (fun r: u I => R1 ~~ R2 ~~ 
      rep' p1 R1 * rep' p2 R2 * rep' r (inter R1 R2) ).

 Parameter impProd : forall I J (R1: [DBRel (F I)]) (R2: [DBRel (F J)])
    (p1: u I) (p2: u J), 
STsep (R1 ~~ R2 ~~ rep' p1 R1 * rep' p2 R2)
      (fun r: u (I++J) => R1 ~~ R2 ~~ 
      rep' p1 R1 * rep' p2 R2 * rep' r (prodRel R1 R2) ).

 Parameter impSelect : forall I f, Proper (equiv ==> equiv) f -> forall (R1: [DBRel (F I)])
    (p1: u I), STsep (R1 ~~ rep' p1 R1)
    (fun r: u I => R1 ~~
      rep' p1 R1 * rep' r (select f R1)).

 Parameter impProj : forall I l (pf: bounded I l) (R1: [DBRel (F I)]) 
   (p1: u I), STsep (R1 ~~ rep' p1 R1)
     (fun r: u (nthTyps pf) => R1 ~~ rep' p1 R1 * rep' r (gprojRel pf R1)).

 Parameter impDupl : forall I (R: [DBRel (F I)]) r,
  STsep (R ~~ rep' r R)
        (fun r': u I => R ~~ rep' r R * rep' r' R).

 (* this is probably not a good function to call *)
 Parameter impNew : forall I (R: DBRel (F I)),
   STsep (__)
         (fun r: u I => rep' r R).

 Parameter impFree : forall I (R: [DBRel (F I)]) p,
   STsep (R ~~ rep' p R )
         (fun _: unit => __).

 Parameter impDiff : forall J (R1 R2: [DBRel (F J)])
    (p1 p2: u J), STsep (R1 ~~ R2 ~~ rep' p1 R1 * rep' p2 R2)
    (fun r: u J => R1 ~~ R2 ~~ 
      rep' p1 R1 * rep' p2 R2 * rep' r (diff R1 R2) ).

 Parameter impMember : forall J (R1 : [DBRel (F J)])
    (p1: u J) k, STsep (R1 ~~ rep' p1 R1)
    (fun r: bool => R1 ~~
      rep' p1 R1 * [r = FSetInterfaceNM.mem k R1]).

 Parameter impPrint : forall I (R: [DBRel (F I)]) p,
   STsep (R ~~ rep' p R)
         (fun _: unit => R ~~ rep' p R).

 (** This probably needs a better type **)
 Parameter impSerialize : forall I (R: [DBRel (F I)]) p,
   STsep (R ~~ rep' p R)
         (fun _: string => R ~~ rep' p R).

 Parameter rep'_push : forall (I : Typing) (x : u I) (e e' : DBRel (F I)),
   e [=] e' -> rep' (I:=I) x e ==> rep' (I:=I) x e'.

End RAInterface.
