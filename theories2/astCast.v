
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun.
Require Import AutosubstSsr ARS Context.
Require Import Program.Equality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive path : Type  := (* mutually inductive? *)
| Here
| AObs : term -> path -> path
| BodTyObs : term -> path -> path
| ArgObs : term -> path -> path

(* consider merging lump into term *)
with term : Type :=
| Var (x : var)
| TT
| App (s t : term)
| Fun (s : {bind 2 of term})
| Pi (s : term) (t : {bind term})
| Cast (s : term) (l : term)

| Lump (terms : list term) (t : term)
(* TODO: cast just a singleton lump? *)
| assertEq (l r : term) (p : path) (* TODO attach type assertion? *)
| Arg (l : term)
| Bod (a :term) (l : term)
| Ap (a :term) (l : term).
(* TODO: app can just overload with ap *)

(* ... *)

Axiom Eq : (list term) -> term -> term -> term -> Prop.

(* endpoints *)
Reserved Notation "[ Gamma |- s ~= a :- A ]".

Axiom LumpOk : (list term) -> (term) -> Prop.

(* TODO: merge with above *)


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
  LumpOk ctx L ->
  has_enpoint ctx L A' TT ->
  has_enpoint ctx L B' TT ->
  has_enpoint ctx (Cast a L) (Cast a' L) B'

| ty_lump ctx l L A' B' a a' :
  Connected ctx l ->
  (* In l a -> *)
  has_enpoint ctx a a' A' ->
  LumpOk ctx L ->
  has_enpoint ctx L A' TT -> (* redundnent? *)
  has_enpoint ctx L B' TT ->
  has_enpoint ctx (Lump l L) (Cast a' L) B'

| ty_assertEqL ctx a a' A' b b' B' p :
  has_enpoint ctx a a' A' ->
  has_enpoint ctx b b' B' ->
  has_enpoint ctx (assertEq a b p) a' A' 
  
| ty_assertEqR ctx a a' A' b b' B' p :
  has_enpoint ctx a a' A' ->
  has_enpoint ctx b b' B' ->
  has_enpoint ctx (assertEq a b p) b' B' 

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

.

Definition ty (ctx : list term) (a : term) (A : term) := 
  has_enpoint ctx a a A.

Axiom extract_ty : term -> term.

Axiom Union : term -> term ->  term.

Inductive step : term -> term -> Prop :=
  (* beta reductions *)
  (* | step_beta b a :
      value a ->
      step (App (Fun b) a) (b.[Fun b,  a /]) *)
  
  | step_cast_beta b a l :
  (* value a -> *)
  step
    (App (Cast b l) a)
    (Cast (App b (Cast a (Arg l))) (Bod a l))

  | step_Lump_beta a ls L :
  (* value a -> *)
  step
    (App (Lump ls L) a)
    (Lump (map (fun x => App x a) ls) (Bod a L))

  | step_assert_beta b c p a :
  (* value a -> *)
  step
    (App (assertEq b c p) a)
    (assertEq (App b a) (App c a) (AObs a p)) 
(* 
  | step_cast_collapse a l l' :
    (* value a -> *)
    step
      (Cast (Cast a l) l')
      (Cast a (Union l l'))

  | step_Lump l l' L L' :
  (* value a L -> *)
  step
    (Lump (cons (Lump l L) l') L')
    (Lump (l ++ l') (Union L L' ))

  | step_Lump l l' L L' :
  (* value a L -> *)
  step
    (Lump (cons (Lump l L) l') L')
    (Lump (l ++ l') (Union L L' )) *)

.

Axiom Eq : (list term) -> term -> term -> term -> Prop.


