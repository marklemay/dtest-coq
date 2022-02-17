
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun.
Require Import AutosubstSsr ARS Context.
Require Import Program.Equality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* consider merging lump into term *)
Inductive term : Type :=
| Var (x : var)
| TT
| App (s t : term)
| Lamb (s : {bind term})
| Pi (s : term) (t : {bind term})
| Cast (s : term) (l : term)

| Lump (terms : list term) (t : term) (* TODO: cast just a singleton lump? *)
| assertEq (l r t : term) (p : path) (* TODO attach or remove type assertion? *)
| Arg (l : term)
| Bod (a :term) (l : term)


(* | Ap (a :term) (l : term) *)
(* TODO: app can just overload with ap *)
.

(* ... *)

Axiom Eq : (list term) -> term -> term -> term -> Prop.

(* endpoints *)
Reserved Notation "[ Gamma |- s ~= a :- A ]".


Inductive has_enpoint : list term -> term -> term -> term -> Prop :=
| ty_tt ctx :
  has_enpoint ctx TT TT TT
 (* | ty_var Gamma x :
  x < size Gamma ->
  [ Gamma |- Var x :- Gamma`_x ] *)
  (* has_enpoint ctx (Var x) (Var x) (lookup ...) *)
| ty_pi ctx A A' B B' :
  has_enpoint ctx A A' TT ->
  has_enpoint (A' :: ctx) B B' TT ->
  has_enpoint ctx (Pi A B) (Pi A' B') TT
  (*
| ty_fun Gamma A A' B B' b b' :
  has_enpoint ctx (Pi A B) (Pi A' B') TT ->
   has_enpoint ((Pi A' B').[ren (+1)] :: A' :: ctx) b b' B'.[ren (+1)] -> *)
   
(* | ty_app A' B' f f' a a' :
  has_enpoint ctx f f' (Pi A' B') ->
  has_enpoint ctx a a' A' ->
  has_enpoint ctx (App f a) (App f' a')  (B'.[a'/])  *)

| ty_cast ctx A' L B' a a' :
  has_enpoint ctx a a' A' ->

  has_enpoint ctx L A' TT ->
  has_enpoint ctx L B' TT ->
  ok ctx L ->

  has_enpoint ctx (Cast a L) (Cast a' L) B'

| ty_lump ctx l L A' B' a a' :
  Connected ctx l ->
  (* In l a -> *)
  has_enpoint ctx a a' A' ->
  ok ctx L ->
  has_enpoint ctx L A' TT -> (* redundnent? *)
  has_enpoint ctx L B' TT ->
  has_enpoint ctx (Lump l L) (Cast a' L) B'

| ty_assertEqL ctx a a' A' b b' B' C t p L :
  has_enpoint ctx a a' A' ->
  has_enpoint ctx b b' B' ->

  has_enpoint ctx t A' TT ->
  has_enpoint ctx t B' TT ->
  has_enpoint ctx t C TT ->
  ok ctx t ->

  has_enpoint ctx (assertEq a b t p) (Cast a' L) C 
  (* needs cast to allow local reduction behavior *)
  
| ty_assertEqR ctx a a' A' b b' B' C t p L :
  has_enpoint ctx a a' A' ->
  has_enpoint ctx b b' B' ->

  has_enpoint ctx t A' TT ->
  has_enpoint ctx t B' TT ->
  has_enpoint ctx t C TT ->
  ok ctx t ->

  has_enpoint ctx (assertEq a b t p) (Cast b' L) C 

| ty_Arg ctx AB A' B' :
  has_enpoint ctx AB (Pi A' B') TT ->
  has_enpoint ctx (Arg AB) A' TT
(* 
| ty_Arg ctx AB a a' A' B' :
  has_enpoint ctx AB (Pi A' B') TT ->
  has_enpoint ctx a a' A' ->
  has_enpoint ctx (Bod a AB)  (B'.[a'/]) TT *)

(* | ty_ap A' B' f f' a a' :
  has_enpoint ctx f f' (Pi A' B') ->
  has_enpoint ctx a a' A' ->
  has_enpoint ctx (Ap f a) (App f' a')  (B'.[a'/])  *)

| ty_conv ctx A B a a':
  Eq ctx A B TT ->
  has_enpoint ctx a a' A ->
  has_enpoint ctx a a' B

| tm_conv ctx A a a' b:
  Eq ctx a' b A ->
  has_enpoint ctx a a' A ->
  has_enpoint ctx a b A


(* where "[ Gamma |- s ~= a :- A ]" := (has_enpoint Gamma s a A). *)
with Connected : (list term) -> (list term) -> Prop :=
| Sing ctx a : Connected ctx (cons a nil)

| consCon ctx rest a a' A' b b' B'  : 
  Connected ctx rest ->
  (* In a rest -> *)
  has_enpoint ctx a a' A' ->
  has_enpoint ctx b b' B' ->
  Connected ctx (cons b rest)

(*  can you extract the type linkages from the terms *)
(*  possibly build this property directly into the has endpoint *)
with ok : (list term) -> (term) -> Prop :=
| VarOk ctx x : ok ctx (Var x) 
(* with condition x in ctx*)
| TTOk ctx : ok ctx TT
| AppOk ctx f a : ok ctx (App f a)
(*  TODO may need to make surte at least something matches up *)
(* | App ctx f f' A' B' a a' A' : 
has_enpoint ctx a a' A -> *)

(* | FunOk b : ok ctx b *)
(* expand ctx *)

(* | PiOk b : ... *)

| CastOk ctx a l :
    ok ctx a ->
    ok ctx l ->
    ok ctx (Cast a l)

| LumpOk ctx l L :
  ok ctx L ->
  (* (a -> In a l -> LumpOk ctx a) ->
  (a -> In a l -> Exists a' A' . has_enpoint ctx a a' A' -> has_enpoint ctx L A' TT ) *)
  Connected ctx l ->
  ok ctx (Lump l L)

| assertEqOk ctx a a' A' b b' B' t  (p : path) :
  has_enpoint ctx a a' A' ->
  has_enpoint ctx b b' B' ->

  has_enpoint ctx t A' TT ->
  has_enpoint ctx t B' TT->
  ok ctx t ->
  
  ok ctx (assertEq a b t p)
   
(* 
| Arg (l : term)
| Bod (a :term) (l : term) 
*) 
.

Definition ty (ctx : list term) (a : term) (A : term) := 
  has_enpoint ctx a a A.



