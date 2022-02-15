

From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun.
Require Import AutosubstSsr ARS Context.
Require Import Program.Equality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Require Import astCast.

Axiom extract_ty : term -> term.

Axiom Union : term -> term ->  term.

(* what if we union 2 terms that have different type interpertations
\ x . x : Nat -> Nat
\ x . x : Bool -> Bool
?
*)

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
  has_enpoint ctx a a' A ->   (* why isn't this importerd? *)
  step a a2 ->
  has_enpoint ctx a2 a' A.
Admitted.
