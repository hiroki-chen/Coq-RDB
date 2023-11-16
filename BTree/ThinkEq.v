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

Require Eqdep.

Module EqdepTheory := EqdepFacts.EqdepTheory(Eqdep.Eq_rect_eq).

(** Dependent Equality **)
Ltac eqdep := idtac;
  let th := idtac; 
    match goal with 
      | [ H' : context [ match ?e with 
                           | refl_equal => _
                         end ] |- _ ] => rewrite (EqdepTheory.UIP_refl _ _ e) in H'
      | [ H' : context [ eq_rect_r _ _ ?e _ ] |- _ ] =>
        rewrite (EqdepTheory.UIP_refl _ _ e) in H'; unfold eq_rect_r, eq_rect in H'; simpl in H'
      | [ H' : context [ eq_rect _ _ ?e _ ] |- _ ] =>
        rewrite (EqdepTheory.UIP_refl _ _ e) in H'; compute in H'
      | [ |- context [ match ?e with 
                         | refl_equal => _
                       end ] ] => rewrite (EqdepTheory.UIP_refl _ _ e)
      | [ |- context [ eq_rect_r _ _ ?e _ ] ] =>
        rewrite (EqdepTheory.UIP_refl _ _ e); unfold eq_rect_r, eq_rect; simpl
      | [ |- context [ eq_rect _ _ ?e _ ] ] =>
        rewrite (EqdepTheory.UIP_refl _ _ e); unfold eq_rect; simpl
    end
  in
  th; repeat th.

Ltac eqdep_hard e := 
  repeat match goal with
           | [ H : _, H' : _ |- _ ] => 
             match H with
               | e => generalize H'; clear H'
             end
         end;
  rewrite (EqdepTheory.UIP_refl _ _ e) in *.
