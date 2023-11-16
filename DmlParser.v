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

Require Import Ynot.
Require Import Charset Packrat.
Require Import List Ascii String.
Require Import DataModel.
Require Import Typ.

Set Implicit Arguments.
Set Strict Implicit.

(**
   TYPE    ::= "nat" | "unit" | "char" | "string" | "option" TYPE | "list" TYPE
   COLSIG  ::= TYPE
   TYPING  ::= COLSIG ( "," COLSIG )*

   VALUE   ::= <number> | "tt" | """ <string> """ | "None" | "Some" VALUE | "[" (VALUE ("," VALUE)* "]"
   TUPLE   ::= "(" VALUE ( "," VALUE) )* ")"
   DATA    ::= (TUPLE )*

   CREATE  ::= "CREATE" "TABLE" """ <ident> """ "SCHEMA" "(" TYPING ")" "VALUES" "{" DATA "}"
**)
Import Packrat.

Definition cls_alpha : CharClass AsciiCharset := Terminal AsciiCharset (ARange "a" "z").
Definition cls_Alpha : CharClass AsciiCharset := Terminal AsciiCharset (ARange "A" "Z").
Definition cls_digit : CharClass AsciiCharset := Terminal AsciiCharset (ARange "0" "9").
Definition cls_ws    : CharClass AsciiCharset := Group AsciiCharset 
  (" " :: (ascii_of_nat 9):: (ascii_of_nat 13) :: (ascii_of_nat 10) :: nil)%char.

Section Combinators.
  Variable base_ty : Set.
  Variable base_ty_denote : base_ty -> Set.
  Definition ty := @ty base_ty.
  Definition tyDenote : ty -> Set := @tyDenote AsciiCharset base_ty base_ty_denote.
  Definition term := @term AsciiCharset.

  Definition many ctx (T S : ty) (t: tyDenote T) (f : tyDenote S -> tyDenote T -> tyDenote T)
    (prin : term _ ctx S) (rec : term _ ctx T) : term _ ctx T :=
    (Alt (Map _ (fun a : tyDenote (Prod S T) => f (fst a) (snd a)) (Seq prin rec))
         (Map _ (fun _ => t) (@Epsilon AsciiCharset base_ty base_ty_denote ctx))).

  Definition many1 ctx (T S : ty) (t: tyDenote S -> tyDenote T)
    (f : tyDenote S -> tyDenote T -> tyDenote T)
    (prin : term _ ctx S) (rec : term _ ctx T) : term _ ctx T :=
    (Alt (Map _ (fun a:tyDenote (Prod S T) => f (fst a) (snd a)) (Seq prin rec))
         (Map _ (t) (prin))).

  Definition optional ctx (T : ty) (t : tyDenote T) (c : term base_ty_denote  ctx T) : term base_ty_denote ctx T :=
    Alt c (Map _ (fun _ => t) (@Epsilon AsciiCharset base_ty base_ty_denote ctx)).

End Combinators.


Inductive TyIndex : Set :=
| TyNat   : TyIndex
| TyType  : TyIndex
| TyValue : TyIndex
| TyString : TyIndex
| TyOption : ty TyIndex -> TyIndex
| TyScheme : TyIndex
| TyList  : ty TyIndex -> TyIndex.

Fixpoint IndexDenote (ty : TyIndex) : Set :=
  match ty with
    | TyNat    => nat
    | TyType   => typ
    | TyValue  => sigT typDenote
    | TyString => string
    | TyOption t => option (tyDenote IndexDenote t)
    | TyScheme => sigT (fun t:Typing => list (Tuple t))
    | TyList t => list (tyDenote IndexDenote t)
  end.

Definition term' := @term TyIndex IndexDenote.

Fixpoint litString ctx {T : ty TyIndex} (t : tyDenote _ T) (s : string) : term' ctx T :=
  match s with
    | EmptyString => (Map _ (fun _ => t) (@Epsilon AsciiCharset TyIndex IndexDenote ctx))
    | String a r => (Map _ (fun _ => t) (Seq (Lit AsciiCharset IndexDenote ctx a) (litString ctx t r)))
  end.

Definition Str ctx : term' ctx (Char TyIndex) -> term' ctx (Base TyString) -> term' ctx (Base TyString) :=
  @many1 _ _ ctx (Base TyString) (Char TyIndex) (fun a => String a EmptyString) String.

Definition Unit' := @Unit TyIndex.
Definition Char' := @Char TyIndex.

Definition Typing' := Base (TyList (Base TyType)).
Definition Tuple' := Base (TyList (Base TyValue)).
Definition Data' := Base (TyList Tuple').

Definition DML_ctx := 
       (Base (TyOption (Prod (Base TyString) (Base TyScheme))) ::
        (Base TyNat) :: (Base (TyList (Base (TyNat)))) :: (Base TyNat) :: Unit' :: Unit' ::
        (Base TyString) :: Char' ::
        Char' :: (Base TyString) ::
        (Base TyType)  :: Typing' :: Typing' ::
        (Base TyValue) :: Tuple' :: Tuple' :: Data' :: Data' :: nil)%type.

Notation "## c" := (@LitClass AsciiCharset TyIndex IndexDenote DML_ctx c%char) (at level 1) : grammar_scope.
Notation "e1 ^^ e2" := (@Seq AsciiCharset TyIndex IndexDenote _ _ _ e1 e2) (right associativity, at level 30) : grammar_scope.
Notation "e @@ f" := (@Map AsciiCharset TyIndex IndexDenote _ _ _ f e) (left associativity, at level 78) : grammar_scope.
Notation "e1 ||| e2" := (Alt e1 e2) (right associativity, at level 79) : grammar_scope.

Open Local Scope grammar_scope.

Definition Lit := @Lit AsciiCharset TyIndex IndexDenote.
Definition Map := @Map AsciiCharset TyIndex IndexDenote.
Definition Seq := @Seq AsciiCharset TyIndex IndexDenote.


Definition many'  := @many TyIndex IndexDenote DML_ctx.
Definition many1' := @many1 TyIndex IndexDenote DML_ctx.

Definition wrap s e T p :=
  @Map DML_ctx (Prod Char' (Prod T Char')) T
      (fun t => fst (snd t))
      ((Lit DML_ctx s) ^^ p ^^ (Lit DML_ctx e)).
Definition wrap_ws s e ws T p :=
  @Map DML_ctx (Prod (Prod Char' Unit') (Prod T (Prod Unit' Char'))) T
      (fun t => fst (snd t))
      ((Lit DML_ctx s ^^ ws) ^^ p ^^ (ws ^^ Lit DML_ctx e)).

Definition parens := wrap_ws "("%char ")"%char.
Definition quoted := wrap """"%char """"%char.
Definition bracketed := wrap_ws "{"%char "}"%char.
Definition Pad T := Prod Unit' (Prod T Unit').

Fixpoint enum ctx {T : ty TyIndex} (t : list (string * tyDenote _ T)) : term' ctx T :=
  match t with
    | nil => Void AsciiCharset IndexDenote ctx T
    | (str',v) :: r => (litString _ v str') ||| enum ctx r
  end.

Definition whitespace := @many1 TyIndex IndexDenote DML_ctx  Unit' Char' (fun _ => tt) (fun _ _ => tt)
  (LitClass _ DML_ctx cls_ws). 

(* mapM specialized to the option monad *)
Fixpoint mapMopt {A B : Type} (f : A -> option B) (l:list A) : option (list B) :=
  match l with
  | nil => Some nil
  | a :: t => match f a with
                | None => None
                | Some r => match mapMopt f t with
                              | None => None
                              | Some t' => Some (r :: t')
                            end
              end
  end.

Require Import SetoidDec.

Lemma typ_eq_dec (x y : typ) : {x = y} + {x <> y}.
Proof. decide equality. Qed.

Instance typ_eq_decd : EqDec (@eq_setoid typ).
Proof. red. intros. apply typ_eq_dec. Qed.

Definition convertTuple (T : list typ) (V : list (sigT typDenote)) 
  : option (Tuple T).
refine (fix  convertTuple (T : list typ) (V : list (sigT typDenote)) 
  : option (Tuple T)
  :=
  match T as T return option (Tuple T) with 
    | nil =>
      match V as V with
        | nil => Some tt
        | (existT actualty v::v') => None
      end
    | colty::t'  => 
      match V as V with
        | nil => None
        | (existT actualty v::v') => 
          match typ_eq_dec actualty colty with
            | left pfleft => 
              match convertTuple t' v' with 
                | None => None
                | Some r => _
              end
            | right pfright => None
          end
      end
  end).
  rewrite pfleft in v.
  refine (Some (v,r)).
Defined.

Definition convert' (T : list typ) (V : list (list (sigT typDenote))) : option (list (Tuple T))
  := mapMopt (convertTuple T) V.

Definition convert (T : list typ) (V : list (list (sigT typDenote))) : option (sigT (fun x => list (Tuple x)))
  := match (convert' T V) with
     | None => None
     | Some r => Some (existT _ _ r)
   end.

Definition DML_env :=
  gfix AsciiCharset IndexDenote DML_ctx
  (fun schema
       digit digits number ws ows
       string char
       string_char string_content
       type typing' typing
       value tuple' tuple data' data =>
    (* Query *)
    (@Map DML_ctx 
          (Prod (Prod Unit' Unit') (Prod Unit' (Prod (Pad (Base TyString))
            (Prod Unit' (Prod (Pad Typing') (Prod Unit' (Prod Unit' Data')))))))
          (Base (TyOption (Prod (Base TyString) (Base TyScheme))))
      (fun t =>
        let name   := fst (snd (fst (snd (snd t)))) in
        let typing := fst (snd (fst (snd (snd (snd (snd t)))))) in
        let data   := snd (snd (snd (snd (snd (snd (snd  t)))))) in
        match convert typing data with
          | None => None
          | Some v => Some (name, v)
        end)
      ((@litString DML_ctx Unit' tt "CREATE" ^^ ws) ^^
       @litString DML_ctx Unit' tt "TABLE"%string ^^ (ws ^^ quoted string ^^ ws) ^^
       @litString DML_ctx Unit' tt "SCHEMA"%string ^^ (ws ^^ parens ows typing ^^ ws) ^^
       @litString DML_ctx Unit' tt "VALUES"%string ^^ (ws ^^ bracketed ows data)),

    (* common parsers *)
    (@Map DML_ctx _ (Base TyNat)
      (fun t:tyDenote _ (Char TyIndex) => nat_of_ascii t - nat_of_ascii "0"%char)
      (LitClass _ DML_ctx cls_digit),
    (@many1' (Base (TyList (Base TyNat))) (Base TyNat)
              (fun x => x :: nil) (fun a b => a :: b)
              digit digits,
    (@Map DML_ctx (Base (TyList (Base TyNat))) (Base TyNat)
      (fun ls => fold_left (fun a x => a * 10 + x) ls 0)
      digits,
    (whitespace ws,
    (@optional _ _ DML_ctx Unit' tt ws,

    (Str char string,
    (    (LitClass _ DML_ctx cls_alpha) 
     ||| (LitClass _ DML_ctx cls_Alpha)
     ||| (LitClass _ DML_ctx cls_digit),

    (    (LitClass _ _ (Complement (Group AsciiCharset ("\"%char :: """"%char :: nil))))
     ||| (@Map DML_ctx (Prod Char' Char') Char'
            (fun cc => snd cc)
            (Lit _ "\"%char ^^
               (    (Lit _ "\"%char)
                ||| (@Map DML_ctx Char' Char' (fun _ => ascii_of_nat 13) (Lit _ "n"%char))
                ||| (@Map DML_ctx Char' Char' (fun _ => ascii_of_nat 9)  (Lit _ "t"%char))
                ||| (@Map DML_ctx Char' Char' (fun _ => ascii_of_nat 13) (Lit _ "r"%char))
                ||| (Lit _ """"%char)))),
    (@many' (Base TyString) Char'
              EmptyString (fun a b => String a b)
              string_char string_content,

    (* typing *)
    (    (@litString DML_ctx (Base TyType) nt "nat"%string)
     ||| (@litString DML_ctx (Base TyType) unt "unit"%string)
     ||| (@litString DML_ctx (Base TyType) boo "bool"%string)
     ||| (@litString DML_ctx (Base TyType) chr "char"%string)
     ||| (@litString DML_ctx (Base TyType) str "string"%string)
     ||| (@Map DML_ctx (Prod Unit' (Prod Unit' (Base TyType))) (Base TyType) (fun t => lst (snd (snd t)))
            (@litString DML_ctx Unit' tt "list"%string ^^ ws ^^ type))
     ||| (@Map DML_ctx (Prod Unit' (Prod Unit' (Base TyType))) (Base TyType) (fun t => opt (snd (snd t)))
            (@litString DML_ctx Unit' tt "option"%string ^^ ws ^^ type)),
    (@many' Typing' (Prod (Prod Unit' (Prod Char' Unit')) (Base TyType))
       nil (fun a b => (snd a) :: b)
       ((ows ^^ (Lit _ ","%char) ^^ ows) ^^ type) typing',
    (@optional _ _ DML_ctx Typing' nil (@Map DML_ctx (Prod (Base TyType) Typing') (Base (TyList (Base TyType))) (fun a => fst a :: snd a) (type ^^ typing')),

    (* values *)
    (    (@litString DML_ctx (Base TyValue) (existT typDenote unt tt) "tt"%string)
     ||| (@litString DML_ctx (Base TyValue) (existT typDenote boo true) "true"%string)
     ||| (@litString DML_ctx (Base TyValue) (existT typDenote boo false) "false"%string)
     ||| (@Map DML_ctx (Base TyNat) (Base TyValue) (fun x => existT typDenote nt x) number)
     ||| (@Map DML_ctx Char' (Base TyValue) (fun x => existT typDenote chr x)
            (wrap "'"%char "'"%char (string_char)))
     ||| (@Map DML_ctx (Base TyString) (Base TyValue) (fun x => existT typDenote str x)
            (quoted string))
     ||| (@Map DML_ctx (Prod Unit' (Prod Char' (Base TyType))) (Base TyValue)
            (fun t => existT typDenote (opt (snd (snd t))) None)
            (@litString DML_ctx Unit' tt "None"%string ^^ (Lit _ ":"%char) ^^ type))
     ||| (@Map DML_ctx (Prod Unit' (Prod Unit' (Base TyValue))) (Base TyValue)
            (fun t => match snd (snd t) with
                        | existT ty val => existT typDenote (opt ty) (Some val)
                      end)
            (@litString DML_ctx Unit' tt "Some"%string ^^ ws ^^ value)),

    (@many' Tuple' (Prod (Prod Unit' (Prod Char' Unit')) (Base TyValue))
       nil (fun a b => (snd a) :: b)
       ((ows ^^ (Lit _ ","%char) ^^ ows) ^^ value) tuple',
    (parens ows (@optional _ _ DML_ctx Tuple' nil (@Map DML_ctx (Prod (Base TyValue) Tuple') Tuple' (fun a => fst a :: snd a) (value ^^ tuple'))),

    (@many' Data' (Prod (Prod Unit' (Prod Char' Unit')) Tuple')
       nil (fun a b => (snd a) :: b)
       ((ows ^^ (Lit _ ","%char) ^^ ows) ^^ tuple) data',
    (@optional _ _ DML_ctx Data' nil (@Map DML_ctx (Prod Tuple' Data') Data' (fun a => fst a :: snd a) (tuple ^^ data')),
     tt))))))))))))))))))).

Open Local Scope hprop_scope.

Definition ParseType := option (string * sigT (fun x => list (Tuple x))).

Definition DML_correct (ins : StreamM.INSTREAM.instream_t ascii) (n : nat) (a : option (nat * ParseType)) :=
  ans_correct DML_env ins n [Var AsciiCharset IndexDenote DML_ctx 0]%inhabited a.

Definition dml_parse : forall (ins : StreamM.INSTREAM.instream_t ascii) (n : nat),
  STsep (StreamM.INSTREAM.rep ins n)
        (fun a : option (nat * ParseType) => DML_correct ins n a * rep_ans AsciiCharset ins n a).
  refine (mkparser (DML_env) (Var _ IndexDenote DML_ctx 0)).
Qed.

Require Export StreamM.
