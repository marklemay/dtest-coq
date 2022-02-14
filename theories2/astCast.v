
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun.
Require Import AutosubstSsr ARS Context.
Require Import Program.Equality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive path : Type  := (* mutually inductive? *)
| Here
| AObs : path -> path
| BodTyObs : term -> path -> path
| ArgObs : term -> path -> path

(* consider merging lump into term *)
with term : Type :=
| Var (x : var)
| App (s t : term)
| Fun (s : {bind 2 of term})
| Pi (s : term) (t : {bind term})
| Cast (s : term) (l : term)

| Lump (terms : list term) (t : term)
| assertEq (l r : term) (p : path)
| Arg (l : term)
| Bod (a :term) (l : term)
| Ap (a :term) (l : term).
(* TODO: cast just a singleton lump? *)


(* seperated version *)

(* with assertEq : Type :=
| AssertEq (left right : term) (p : path)

with term : Type :=
| Var (x : var)
| LumpT (l : lump)  (* since equalities may need to be embedded in terms *)
| TT
| App (s t : term)
| Fun (s : {bind 2 of term})
| Pi (s : term) (t : {bind term})
| Cast (s : term) (l : lump)

with lump : Type :=
| TTL
| Lump (terms : list term) (asserts : list assertEq) (tyl : lump)
| Arg (l : lump)
| Bod (a :term) (l : lump)
| Ap (a :term) (l : lump). *)

Scheme path_mutual := Induction for path Sort Type
with term_mutual := Induction for term Sort Type.

Definition ids_term (v : var) : term := Var v.

Instance Ids_term : Ids term. 
  unfold Ids.
  apply ids_term.
Defined.

Axiom rename_term : (var -> var) -> (term) -> term.
(* Fixpoint rename_term (re : var -> var) (t : term) : term :=
  match t with
  | Var x => Var (re x)
  | TT => TT
  | App s t => App (rename_term re s) (rename_term re t)
  | Fun s => Fun (rename_term (iterate upren 2 re) s)
  | Pi s t => Pi (rename_term re s) (rename_term (upren re) t)
  | Cast s under over p => 
    let s := rename_term re s in
    let under := rename_term re under in
    let over := rename_term re over in
    let p := rename_path re p in
    Cast s under over p
  end

with rename_path (re : var -> var) (p : path) : path :=
  match p with
  | Here => Here
  | Aty p => Aty (rename_path re p)
  | BodTy t p =>
    let t := rename_term re t in
    let p := rename_path re p in
    BodTy t p
  end. *)

Instance Rename_term : Rename term. 
  unfold Rename.
  apply rename_term.
Defined.

Axiom subst_term : (var -> term) -> (term) -> term.
(* Fixpoint subst_term (sigma : var -> term) (s : term) : term :=
  match s as t return (annot term t) with
  | Var x => sigma x
  | TT => TT
  | App s1 s2 => App (subst_term sigma s1) (subst_term sigma s2)
  | Fun s0 => Fun (subst_term (upn 2 sigma) s0)
  | Pi s0 t => Pi (subst_term sigma s0) (subst_term (up sigma) t)
  | Cast s1 s2 s3 p =>
    let s1 := subst_term sigma s1 in
    let s2 := subst_term sigma s2 in
    let s3 := subst_term sigma s3 in
    let p := subst_path sigma p in
    Cast s1 s2 s3 p
  end

with subst_path (sigma : var -> term) (p : path) : path :=
  match p as t return (annot path p) with
  | Here => Here
  | Aty p => Aty (subst_path sigma p)
  | BodTy t p => 
    let t := subst_term sigma t in
    let p := subst_path sigma p in
    BodTy t p
  end. *)

Instance Subst_term : Subst term. 
  unfold Subst.
  apply subst_term.
Defined.

Axiom rename_subst : forall xi s, 
  rename xi s = s.[ren xi].

Axiom subst_id : forall s, s.[ids] = s.

Axiom ren_subst_comp : forall xi sigma s, 
  (rename xi s).[sigma] = s.[xi >>> sigma].
  
Axiom subst_ren_comp : forall sigma xi s,
  rename xi s.[sigma] = s.[sigma >>> rename xi].

Axiom subst_comp : forall (sigma tau : var -> term) (s : term),
  s.[sigma].[tau] = s.[sigma >> tau].


(* Instance substLemmas_term : SubstLemmas term.
  constructor.
  - apply rename_subst.
  - apply subst_id.
  - reflexivity.
  - apply subst_comp.
Qed. *)

(* Notation "p .[/ sigma ]" := (subst_path sigma p)
  (at level 2, sigma at level 200, left associativity,
    format "p .[/ sigma ]") : subst_scope. *)


(* helper tactic *)
(* Ltac fold_all :=
  fold subst_term;
  fold subst_path;
  fold Subst_term;
  fold subst. *)
