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
Require Import preservation.
Require Import progress.


Lemma steps_psteps s t : star step s t -> star pstep s t.
Proof. 
  intros.
  induction H.
  apply starR.
  apply step_pstep in H0.
  apply (starSE IHstar H0).
Qed.


Theorem type_soundness : forall s t s',
[ [::] |- s :- t ] ->
star step s s' -> not (Stuck s').
Proof.
  intros.
  apply (steps_preservation ctx_nil H) in H0.
  apply progress in H0.
  destruct H0.
  unfold Stuck.
  unfold not.
  intros.
  destruct H1.
  auto.

  unfold Stuck.
  unfold not.
  intros.
  destruct H1.
  auto.
Qed.
