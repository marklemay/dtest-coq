

From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun.
Require Import AutosubstSsr ARS Context.
Require Import Program.Equality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Require Import ast.
Require Import smallstep.
Require Import confluence.
Require Import typing.
Require Import typesoundness.



(* typing, in a bidirectional style *)

Reserved Notation "[ Gamma |- s :-> A ]".

Reserved Notation "[ Gamma |- s <-: A ]".

Inductive type_infer : list term -> term -> term -> Prop :=
| ty_infer_Var ctx x : 
  x < size ctx ->
  [ ctx |- (Var x) :-> (ctx `_ x) ]
| ty_infer_TT ctx : 
  [ ctx |- TT :-> TT ]

| ty_infer_PI ctx A B : 
  [ ctx |- A <-: TT ] ->
  [ A :: ctx |- B <-: TT ] ->
  [ ctx |- Pi A B :-> TT ]

| ty_infer_app ctx A B f a :
  [ ctx |- f :-> Pi A B ] ->
  [ ctx |- a <-: A ] ->
  [ ctx |- App f a :-> B.[a/] ]

| ty_infer_cast ctx e t: (*TODO no check that t is a type? *)
  [ ctx |- e <-: t ] ->
  [ ctx |- Cast e t :-> t ]

where "[ ctx |- s :-> A ]" := (type_infer ctx s A) 

with type_checks : list term -> term -> term -> Prop :=
| ty_checks_fun ctx b A B :
   [ ctx |- Pi A B <-: TT ] ->
   [ (Pi A B).[ren (+1)] :: A :: ctx |- b <-: B.[ren (+1)] ] -> (* why +1 ? what is the orientation of gamma and the bound vars inside of it. seems more reasonable to do A+1 *)
   [ ctx |- Fun b <-: Pi A B ]
| ty_checks_conv ctx a A A' : 
   A === A' ->
   [ ctx |- a :-> A ] ->
   [ ctx |- a <-: A' ] 

where "[ ctx |- s <-: A ]" := (type_checks ctx s A)
.

(*TODO  type_infer is unique *)


(* bidirectional tying implies (TAS) typing *)

(* mutual induction *)
Theorem check_ty' : forall ctx n N,
[ ctx |- n <-: N ] -> [ ctx |- n :- N ].
Admitted.

Theorem infer_ty : forall ctx n N,
[ ctx |- n :-> N ] -> [ ctx |- n :- N ].
Proof.
  intros.
  induction H.
  apply ty_var.
  auto.
  apply ty_tt.
  apply check_ty' in H.
  apply check_ty' in H0.
  apply ty_pi. auto. auto.
  apply check_ty' in H0.
  exact: (ty_app IHtype_infer H0).
  apply check_ty' in H.
  apply ty_cast in H.
  auto.
Qed.


Theorem check_ty : forall ctx n N,
[ ctx |- n <-: N ] -> [ ctx |- n :- N ].
Proof.
  intros.
  induction H.
  apply ty_fun.
  auto.
  auto.
  apply infer_ty in H0.
  exact: (ty_conv H H0).
Qed.


Theorem type_soundnes : forall s t s',
[ [::] |- s :-> t ] ->
star step s s' -> not (Stuck s').
Proof.
  intros s.
  intros t.
  intros s'.
  intros H.
  apply infer_ty in H.
  exact: (type_soundness H).
Qed.
