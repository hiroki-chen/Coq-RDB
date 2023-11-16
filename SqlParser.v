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
Require Import SQL.
Require Import Peano_dec.
Require Import Typ.
 
Set Implicit Arguments.
Set Strict Implicit.

(**
   COLUMN  ::= <ident>
   COLUMNS ::= 
            |  COLUMN, COLUMNS
   TABLE   ::= <ident>

   TYPE    ::= "nat" | "bool" | "string" | "unit" | "char" | "option" TYPE | "list" TYPE
   TYPING  ::= TYPE ( "," TYPE )*

   QUERY   ::= "(" "SELECT" COLUMNS "FROM" QUERY ")"
            | "(" QUERY "WHERE" CONDITIONAL ")"
            | """ TABLE """ ":" "(" TYPING ")"
            | "(" QUERY "UNION" QUERY ")"
            | "(" QUERY "INTERSECT" QUERY ")"
            | "(" QUERY "CROSS" QUERY ")"
            | "(" QUERY ":" NUMBER "JOIN" QUERY ":" NUMBER "USING" "(" ("(" COLUMN "=" COLUMN ")")* ")"
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

Inductive SqlOp : Set :=
| SqlLt | SqlLe | SqlEq | SqlNe | SqlGt | SqlGe.

Inductive TyIndex : Set :=
| TyNat   : TyIndex
| TyAtomic : TyIndex
| TyQuery : TyIndex
| TyWhere : TyIndex
| TyOp    : TyIndex
| TyString : TyIndex
| TyType   : TyIndex
| TyValue  : TyIndex
| TyList  : ty TyIndex -> TyIndex.

Fixpoint IndexDenote (ty : TyIndex) : Set :=
  match ty with
    | TyNat    => nat
    | TyAtomic => atomicExp'
    | TyWhere  => whereExp'
    | TyQuery  => raExp'
    | TyOp     => SqlOp
    | TyString => string
    | TyType   => typ
    | TyValue  => sigT typDenote
    | TyList t => list (tyDenote IndexDenote t)
  end.

Definition opList : list (string * tyDenote IndexDenote (Base TyOp)) :=
  (("<", SqlLt) :: ("<=", SqlLe) :: 
   ("=", SqlEq) :: ("<>", SqlNe) :: 
   (">", SqlGt) :: (">=", SqlGe) :: nil)%string.

Definition term' := @term TyIndex IndexDenote.

Fixpoint litString ctx {T : ty TyIndex} (t : tyDenote _ T) (s : string) : term' ctx T :=
  match s with
    | EmptyString => (Map _ (fun _ => t) (@Epsilon AsciiCharset TyIndex IndexDenote ctx))
    | String a r => (Map _ (fun _ => t) (Seq (Lit AsciiCharset IndexDenote ctx a) (litString ctx t r)))
  end.

Definition Unit' := @Unit TyIndex.
Definition Char' := @Char TyIndex.
Definition Typing' := Base (TyList (Base TyType)).

Definition SQL_ctx := 
       ((Base TyQuery) ::
        (Base TyNat) :: (Base (TyList (Base (TyNat)))) :: (Base TyNat) :: Unit' :: Unit' ::
        (Char') :: (Base TyString) ::
        (** table **)
        (Base TyQuery) :: (Base TyType) :: Typing' :: Typing' ::
        (** project **)
        (Base TyQuery) :: (Base (TyList (Base TyNat))) ::
        (** intersect **)
        (Base TyQuery) ::
        (** union **)
        (Base TyQuery) ::
        (** product **)
        (Base TyQuery) ::
        (** join **)
        (Base TyQuery) :: (Prod (Base TyNat) (Base TyNat)) :: (Base (TyList (Prod (Base TyNat) (Base TyNat)))) ::
        (** where **)
        (Base TyQuery) :: (Base TyWhere) :: 
        (** atomics **)
        (Base TyValue) :: (Base TyAtomic) :: nil)%type.

Notation "## c" := (@LitClass AsciiCharset TyIndex IndexDenote SQL_ctx c%char) (at level 1) : grammar_scope.
Notation "e1 ^^ e2" := (@Seq AsciiCharset TyIndex IndexDenote _ _ _ e1 e2) (right associativity, at level 30) : grammar_scope.
Notation "e @@ f" := (@Map AsciiCharset TyIndex IndexDenote _ _ _ f e) (left associativity, at level 78) : grammar_scope.
Notation "e1 ||| e2" := (Alt e1 e2) (right associativity, at level 79) : grammar_scope.

Open Local Scope grammar_scope.

Definition Lit := @Lit AsciiCharset TyIndex IndexDenote.
Definition Map := @Map AsciiCharset TyIndex IndexDenote.
Definition Seq := @Seq AsciiCharset TyIndex IndexDenote.

Definition many' := @many TyIndex IndexDenote SQL_ctx.
Definition many1' := @many1 TyIndex IndexDenote SQL_ctx.

Definition wrap s e T p :=
  @Map SQL_ctx (Prod Char' (Prod T Char')) T
      (fun t => fst (snd t))
      ((Lit SQL_ctx s) ^^ p ^^ (Lit SQL_ctx e)).
Definition wrap_ws s e ws T p :=
  @Map SQL_ctx (Prod (Prod Char' Unit') (Prod T (Prod Unit' Char'))) T
      (fun t => fst (snd t))
      ((Lit SQL_ctx s ^^ ws) ^^ p ^^ (ws ^^ Lit SQL_ctx e)).

Definition parens  := wrap_ws "("%char ")"%char.
Definition squotes := wrap "'"%char "'"%char.
Definition dquotes := wrap """"%char """"%char.

Definition Pad T := Prod Unit' (Prod T Unit').
Definition Qop := Prod (Base TyQuery) (Prod (Pad Unit') (Base TyQuery)).
Definition WhereBop := Prod (Base TyWhere) (Prod (Pad Unit') (Base TyWhere)).
Definition WhereAop := Prod (Base TyAtomic) (Prod (Pad (Base TyOp)) (Base TyAtomic)).

Fixpoint enum ctx {T : ty TyIndex} (t : list (string * tyDenote _ T)) : term' ctx T :=
  match t with
    | nil => Void AsciiCharset IndexDenote ctx T
    | (str',v) :: r => (litString _ v str') ||| enum ctx r
  end.

Definition whitespace := @many1 TyIndex IndexDenote SQL_ctx  Unit' Char' (fun _ => tt) (fun _ _ => tt)
  (LitClass _ SQL_ctx cls_ws). 


Definition joinProject (a1 a2 : nat) (ls : list (nat * nat)) :=
  let filterBy := List.map (@snd nat nat) ls in
  let project := fun x : nat => match In_dec eq_nat_dec x filterBy with
                                  | left _ => false
                                  | _ => true
                                end 
  in                              
  (List.seq 0 a1 ++ List.map (fun x => a1 + x) (filter project (List.seq 0 a2)))%list.

Definition joinWhere (a1 : nat) (ls : list (nat * nat)) :=
  let terminals := List.map (fun x => compExp' (compareEq' (var' (fst x)) (var' (snd x + a1)))) ls in
  fold_left (fun acc c => andExp' acc c) terminals trueExp'.

Definition buildJoin Q1 A1 Q2 A2 equivs :=
  gprojExp' (joinProject A1 A2 equivs) (selectExp' (prodExp' Q1 Q2) (joinWhere A1 equivs)).

Definition SQL_env :=
  gfix AsciiCharset IndexDenote SQL_ctx
  (fun query
       digit digits number ws ows
       string_char string_content
       table type typing' typing
       project projs
       intersect
       union
       product
       join joinParam joinOn
       whereC cond const atomic =>
    (* Query *)
    (parens ows (table ||| project ||| intersect ||| union ||| product ||| whereC),

    (* common parsers **)
    (@Map SQL_ctx _ (Base TyNat)
      (fun t:tyDenote _ (Char TyIndex) => nat_of_ascii t - nat_of_ascii "0"%char)
      (LitClass _ SQL_ctx cls_digit),
    (@many1' (Base (TyList (Base TyNat))) (Base TyNat)
              (fun a => a :: nil) (fun a b => a :: b)
              digit digits,
    (@Map SQL_ctx (Base (TyList (Base TyNat))) (Base TyNat)
      (fun ls => fold_left (fun a x => a * 10 + x) ls 0)
      digits,
    (whitespace ws,
    (@optional _ _ SQL_ctx Unit' tt ws,

    (    (LitClass _ _ (Complement (Group AsciiCharset ("\"%char :: """"%char :: nil))))
     ||| (@Map SQL_ctx (Prod Char' Char') Char'
            (fun cc => snd cc) 
            (Lit _ "\"%char ^^ 
               (    (@Map SQL_ctx Char' Char' (fun _ => "\"%char) (Lit _ "\"%char))
                ||| (@Map SQL_ctx Char' Char' (fun _ => ascii_of_nat 13) (Lit _ "n"%char))
                ||| (@Map SQL_ctx Char' Char' (fun _ => ascii_of_nat 9) (Lit _ "t"%char))
                ||| (@Map SQL_ctx Char' Char' (fun _ => ascii_of_nat 13) (Lit _ "r"%char))
                ||| (@Map SQL_ctx Char' Char' (fun _ => """"%char) (Lit _ """"%char))))),
    (@many' (Base TyString) Char'
              EmptyString (fun a b => String a b)
              string_char string_content,

    (* table *)
    (@Map SQL_ctx (Prod (Base TyString) (Prod Char' Typing'))
                  (Base TyQuery)
      (fun t => varExp' (fst t) (snd (snd t)))
      (dquotes string_content ^^ Lit _ ":"%char ^^ parens ows typing),
    (    (@litString SQL_ctx (Base TyType) Typ.nt "nat"%string)
     ||| (@litString SQL_ctx (Base TyType) Typ.unt "unit"%string)
     ||| (@litString SQL_ctx (Base TyType) Typ.boo "bool"%string)
     ||| (@litString SQL_ctx (Base TyType) Typ.chr "char"%string)
     ||| (@litString SQL_ctx (Base TyType) Typ.str "string"%string)
     ||| (@Map SQL_ctx (Prod Unit' (Prod Unit' (Base TyType))) (Base TyType) (fun t => Typ.lst (snd (snd t)))
            (@litString SQL_ctx Unit' tt "list"%string ^^ ws ^^ type))
     ||| (@Map SQL_ctx (Prod Unit' (Prod Unit' (Base TyType))) (Base TyType) (fun t => Typ.opt (snd (snd t)))
            (@litString SQL_ctx Unit' tt "option"%string ^^ ws ^^ type)),
    (@many' Typing' (Prod (Prod Unit' (Prod Char' Unit')) (Base TyType))
       nil (fun a b => (snd a) :: b)
       ((ows ^^ (Lit _ ","%char) ^^ ows) ^^ type) typing',
    (@optional _ _ SQL_ctx Typing' nil (@Map SQL_ctx (Prod (Base TyType) Typing') (Base (TyList (Base TyType))) (fun a => fst a :: snd a) (type ^^ typing')),

    (* project *)
    (@Map SQL_ctx (Prod (Prod (Prod Unit' Unit') (Base (TyList (Base (TyNat)))))
                        (Prod (Prod Unit' (Prod Unit' Unit')) (Base TyQuery)))
                  (Base TyQuery)
      (fun t => gprojExp' (snd (fst t)) (snd (snd t)))
      ((((@litString SQL_ctx Unit' tt "SELECT") ^^ ws) ^^ projs) ^^
       ((ws ^^ (@litString SQL_ctx Unit' tt "FROM") ^^ ws) ^^ query)),

    (@many' (Base (TyList (Base TyNat))) (Base TyNat)
            nil (fun a b => a :: b)
            number projs,

    (* intersect *)
    (@Map SQL_ctx Qop (Base TyQuery)
       (fun t => interExp' (fst t) (snd (snd t)))
       (query ^^ (ws ^^ (@litString SQL_ctx Unit' tt "INTERSECT"%string) ^^ ws) ^^ query),

    (* union *)
    (@Map SQL_ctx Qop (Base TyQuery)
       (fun t => unionExp' (fst t) (snd (snd t)))
       (query ^^ (ws ^^ (@litString SQL_ctx Unit' tt "UNION"%string) ^^ ws) ^^ query),

    (* product *)
    (@Map SQL_ctx Qop (Base TyQuery)
       (fun t => prodExp' (fst t) (snd (snd t)))
       (query ^^ (ws ^^ (@litString SQL_ctx Unit' tt "CROSS"%string) ^^ ws) ^^ query),

    (* join *)
    (@Map SQL_ctx (Prod (Prod (Base TyQuery) (Prod Char' (Base TyNat))) (Prod (Pad Unit') 
                  (Prod (Prod (Base TyQuery) (Prod Char' (Base TyNat))) (Prod (Pad Unit') (Base (TyList (Prod (Base TyNat) (Base TyNat)))))))) (Base TyQuery)
       (fun t => 
         let q1 := fst t in
         let q2 := fst (snd (snd t)) in
         let jo := snd (snd (snd (snd t))) in
         buildJoin (fst q1) (snd (snd q1)) (fst q2) (snd (snd q2)) jo)
       ((query ^^ (Lit _ ":"%char) ^^ number) ^^ (ws ^^ (@litString SQL_ctx Unit' tt "JOIN"%string) ^^ ws) ^^
        (query ^^ (Lit _ ":"%char) ^^ number) ^^ (ws ^^ (@litString SQL_ctx Unit' tt "USING"%string) ^^ ws) ^^ joinOn),
    (@Map SQL_ctx (Prod (Base TyNat) (Prod Char' (Base TyNat))) (Prod (Base TyNat) (Base TyNat))
       (fun t => (fst t, snd (snd t)))
       (parens ows (number ^^ (Lit _ "="%char) ^^ number)),
    (@many' (Base (TyList (Prod (Base TyNat) (Base TyNat)))) (Prod (Base TyNat) (Base TyNat))
       nil (fun a b => a :: b)
       joinParam joinOn,

    (* where *)
    (@Map SQL_ctx (Prod (Base TyQuery)
                        (Prod (Pad Unit') (Base TyWhere))) (Base TyQuery)
       (fun t => selectExp' (fst t) (snd (snd t)))
       (query ^^ (ws ^^ (@litString SQL_ctx Unit' tt "WHERE"%string) ^^ ws) ^^ cond),
    (    (@litString SQL_ctx (Base TyWhere) trueExp' "TRUE"%string)
     ||| (@litString SQL_ctx (Base TyWhere) falseExp' "FALSE"%string)
     ||| (parens ows (@Map SQL_ctx (Prod (Prod Unit' Unit') (Base TyWhere)) (Base TyWhere) (fun t => notExp' (snd t))
                  ((@litString SQL_ctx Unit' tt "NOT"%string ^^ ws) ^^ cond)))
     ||| (parens ows (@Map SQL_ctx WhereBop (Base TyWhere) (fun t => andExp' (fst t) (snd (snd t)))
                  (cond ^^ (ws ^^ @litString SQL_ctx Unit' tt "AND"%string ^^ ws) ^^ cond)))
     ||| (parens ows (@Map SQL_ctx WhereBop (Base TyWhere) (fun t => orExp' (fst t) (snd (snd t)))
                  (cond ^^ (ws ^^ @litString SQL_ctx Unit' tt "OR"%string ^^ ws) ^^ cond)))
     ||| (parens ows (@Map SQL_ctx WhereAop (Base TyWhere)
                  (fun t =>
                    match fst (snd (fst (snd t))) with
                      | SqlLt => fun l r => compExp' (compareLt' l r)
                      | SqlLe => fun l r => notExp' (compExp' (compareGt' l r))
                      | SqlEq => fun l r => compExp' (compareEq' l r)
                      | SqlNe => fun l r => notExp' (compExp' (compareEq' l r))
                      | SqlGt => fun l r => compExp' (compareGt' l r)
                      | SqlGe => fun l r => notExp' (compExp' (compareLt' l r))
                    end (fst t) (snd (snd t)))
                  (atomic ^^ (ws ^^ @enum SQL_ctx (Base TyOp) opList ^^ ws) ^^ atomic))),
    (    (@litString SQL_ctx (Base TyValue) (existT _ unt tt) "tt"%string)
     ||| (@litString SQL_ctx (Base TyValue) (existT _ boo true) "true"%string)
     ||| (@litString SQL_ctx (Base TyValue) (existT _ boo false) "false"%string)
     ||| (@Map SQL_ctx (Base TyNat) (Base TyValue) (fun x => existT _ nt x) number)
     ||| (@Map SQL_ctx Char' (Base TyValue) (fun x => existT _ chr x)
            (wrap "'"%char "'"%char (string_char)))
     ||| (@Map SQL_ctx (Base TyString) (Base TyValue) (fun x => existT _ str x)
           (dquotes string_content))
     ||| (@Map SQL_ctx (Prod Unit' (Prod Char' (Base TyType))) (Base TyValue)
            (fun t => existT _ (opt (snd (snd t))) None)
            (@litString SQL_ctx Unit' tt "None"%string ^^ (Lit _ ":"%char) ^^ type))
     ||| (@Map SQL_ctx (Prod Unit' (Prod Unit' (Base TyValue))) (Base TyValue)
            (fun t => match snd (snd t) with
                        | existT ty val => existT typDenote (Typ.opt ty) (Some val)
                      end)
            (@litString SQL_ctx Unit' tt "Some"%string ^^ ws ^^ const)),
    (    (@Map SQL_ctx (Base TyValue) (Base TyAtomic) 
           (fun t => match t with
                       | existT t v => atom' t v
                     end) const 
     ||| (@Map SQL_ctx (Prod Char' (Base TyNat)) (Base TyAtomic) (fun x => var' (snd x))
           (Lit _ "$"%char ^^ number)),
    tt)))))))))))))))))))))))))).

Open Local Scope hprop_scope.

Definition SQL_correct (ins : StreamM.INSTREAM.instream_t ascii) (n : nat) (a : option (nat * raExp')) :=
  ans_correct SQL_env ins n [Var AsciiCharset IndexDenote SQL_ctx 0]%inhabited a.

Definition sql_parse : forall (ins : StreamM.INSTREAM.instream_t ascii) (n : nat),
  STsep (StreamM.INSTREAM.rep ins n)
        (fun a : option (nat * raExp') => SQL_correct ins n a * rep_ans AsciiCharset ins n a).
  refine (mkparser (SQL_env) (Var _ IndexDenote SQL_ctx 0)).
Qed.

Require Export StreamM.
