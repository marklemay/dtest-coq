
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
| ArgObs : path -> path
(* I would be happy to remove paths *)

(* consider merging lump into term *)
with term : Type :=
| Var (x : var)
| TT
| App (s t : term)
| Fun (s : {bind 2 of term})
| Pi (s : term) (t : {bind term})
| Cast (s : term) (l : term)

| Lump (terms : list term) (t : term) (* TODO: cast just a singleton lump? *)
| assertEq (l r t : term) (p : path) (* TODO attach type assertion? *)
| Arg (l : term)
| Bod (a :term) (l : term)
(* | Ap (a :term) (l : term) *)
(* TODO: app can just overload with ap *)
.

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

  has_enpoint ctx L A' TT ->
  has_enpoint ctx L B' TT ->
  LumpOk ctx L ->

  has_enpoint ctx (Cast a L) (Cast a' L) B'

| ty_lump ctx l L A' B' a a' :
  Connected ctx l ->
  (* In l a -> *)
  has_enpoint ctx a a' A' ->
  LumpOk ctx L ->
  has_enpoint ctx L A' TT -> (* redundnent? *)
  has_enpoint ctx L B' TT ->
  has_enpoint ctx (Lump l L) (Cast a' L) B'

| ty_assertEqL ctx a a' A' b b' B' C t p L :
  has_enpoint ctx a a' A' ->
  has_enpoint ctx b b' B' ->

  has_enpoint ctx t A' TT ->
  has_enpoint ctx t B' TT ->
  has_enpoint ctx t C TT ->
  LumpOk ctx t ->

  has_enpoint ctx (assertEq a b t p) (Cast a' L) C 
  (* needs cast to allow local reduction behavior *)
  
| ty_assertEqR ctx a a' A' b b' B' C t p L :
  has_enpoint ctx a a' A' ->
  has_enpoint ctx b b' B' ->

  has_enpoint ctx t A' TT ->
  has_enpoint ctx t B' TT ->
  has_enpoint ctx t C TT ->
  LumpOk ctx t ->

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

.

Definition ty (ctx : list term) (a : term) (A : term) := 
  has_enpoint ctx a a A.

Axiom extract_ty : term -> term.

Axiom Union : term -> term ->  term.

Inductive step : term -> term -> Prop :=
  (* beta reductions - app *)
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

  | step_assert_beta b c t p a :
  (* value a -> *)
  step
    (App (assertEq b c t p) a)
    (assertEq (App b a) (App c a) (Bod a t) (AObs a p))
    (* other reductions *)
  | step_cast_collapse a l l' :
    (* value ... -> *)
    step
      (Cast (Cast a l) l')
      (Cast a (Union l l'))
(* lump *)
  | step_Lump l l' L L' :
  (* value... -> *)
  (* TODO this does not only need to happen to the first element *)
  step
    (Lump (cons (Lump l L) l') L')
    (Lump (l ++ l') (Union L L' ))

  | step_Lump_cast a l' L L' :
    (* value ... -> *)
    (* TODO this does not only need to happen to the first element *)
    step
      (Lump (cons (Cast a L) l') L')
      (Lump (cons a l') (Union L L' ))
(* assert *)

| step_Assert_castL a b L L' o :
  step
  (assertEq (Cast a L) b L' o)
  (assertEq a b (Union L L') o)
  

  | step_Assert_castR a b L L' o :
  step
  (assertEq a (Cast b L) L' o)
  (assertEq a b (Union L L') o)

(* other reductions *)

(* Arg *)
  | step_Arg A B :
  step
    (Arg (Pi A B))
    A

  | step_Arg_Assert A B A' B' p:
  step
    (Arg (assertEq (Pi A B) (Pi A' B') TT p))
    (assertEq A A' TT (ArgObs p))

  | step_Arg_Lump ls:
  step
    (Arg (Lump ls TT))
    (Lump (map (Arg) ls) TT)

    (* Bod *)
  (* | step_Bod a A B :
  step
    (Bod a (Pi A B))
    (B.[a/]) *)

  (* | step_Bod_Assert a A B A' B' p:
  step
    (Bod a (assertEq (Pi A B) (Pi A' B') TT p))
    (assertEq (B.[a/]) (B'.[a/]) TT (BodTyObs a p)) *)

  | step_Bod_Lump a ls:
  step
    (Bod a (Lump ls TT))
    (Lump (map (Bod a) ls) TT)

  (* structrural rules *)
  (* ,,, *)
.


(* Assume Eq is a congruent equivelence that respects step.  And... *)
(* Axiom Casts_dont_matter ctx a a' L L' A' B : 
  has_enpoint ctx a a' A ->
  has_enpoint ctx L A' TT ->
  has_enpoint ctx L B TT ->
  LumpOk ctx L ->

  has_enpoint ctx L' A' TT ->
  has_enpoint ctx L' B TT ->
  LumpOk ctx L' ->

  Eq ctx (Cast a L) (Cast a L') B. *)

(* Axiom vacCast ctx a a' L L' A' B : 
  ty ctx a A 
  Eq ctx a (Cast a (cons A Nil)) A. *)


Lemma preservation ctx a a' A a2 : 
  has_enpoint ctx a a' A -> 
  step a a2 ->
  has_enpoint ctx a2 a' A.
Admitted.


