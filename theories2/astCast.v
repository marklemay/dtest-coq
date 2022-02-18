
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

| Lump (terms : list term)
 (* (t : term) TODO: cast just a singleton lump? *)
| assertEq (l r (* t *) : term)
| Arg (l : term)
| Bod (a :term) (l : term)
.

Instance Ids_term : Ids term. derive. Defined.
Instance Rename_term : Rename term. derive. Defined.
Instance Subst_term : Subst term. derive. Defined.
Instance substLemmas_term : SubstLemmas term. derive. Qed.

Inductive pstep : term -> term -> Prop :=
| psAppLam x x' y y' : 
  pstep x x'
  -> pstep y y'
  -> pstep (App (Lamb x') y') (x'.[y'/] )

| psAppCast f f' F F' a a' : 
  pstep f f'
  -> pstep F F'
  -> pstep a a'
  -> pstep 
    (App (Cast f F) a) 
    (Cast (App f' (Cast a' (Arg F'))) (Bod a' F'))

| psAppLump ls ls' a a' : 
  psteps ls ls'
  -> pstep a a'
  -> pstep 
    (App (Lump ls) a) 
    (Lump (map (fun x => App x a') ls'))

| psAppAssertEq b b' c c' a a' : 
  pstep b b'
  -> pstep c c'
  -> pstep a a'
    -> pstep 
      (App (assertEq b c) a) 
      (assertEq (App b' a') (App c' a'))

| psCastTT b b' : 
  pstep b b'
    -> pstep 
      (Cast b TT) 
      b'

(* let's see if we can get it to work without htis first *)
(* | psLumpflatten b b' : 
psteps b b'
  -> pstep 
    (Lump b)
    (List.flat_map (fun x => match x with
    | Lump l => l
    | y => cons y nil
    end
      ) b' ) *)
        
(* TODO supress repeated TT within lump *)

| pslumpTT b b' : 
  pstep b b'
    -> pstep 
      (Lump (cons TT nil))
      TT

| psassertEqTT :  pstep 
    (assertEq TT TT)
    TT

| psassertEqPi b b' c c' a a' d d' : 
   pstep b b'
   -> pstep a a'
   -> pstep c c'
   -> pstep d d'
   -> pstep
    (assertEq (Pi a b) (Pi c d))
    (Pi (assertEq a' c') (assertEq b' d'))

| psArgPi x x' y :
  pstep x x'
  -> pstep
    (Arg (Pi x y))
    x'

| psArgLump ls ls' : 
  psteps ls ls'
  -> pstep 
    (Arg (Lump ls))
    (Lump (map (fun x => Arg x) ls'))
  
| psbodPi x x' y a a' :
  pstep x x'
  -> pstep
    (Bod a (Pi y x))
    (x'.[a'/] )
  (* may need a cast here *)

| psbodLump ls ls' a a' : 
  psteps ls ls'
  -> pstep a a'
  -> pstep 
    (Arg (Lump ls))
    (Lump (map (fun x => Bod a' x) ls'))

(* | psAppLam x x' y y' : 
pstep x x'
-> pstep y y'
-> pstep (App (Lamb x') y') (x'.[y'/] ) *)

(* structrual *)
| psVar x : pstep x x
| psTT : pstep TT TT
| psApp x x' y y' : 
  pstep x x'
  -> pstep y y'
  -> pstep (App x y)  (App x' y')
| psLam x x' : 
  pstep x x'
  -> pstep (Lamb x)  (Lamb x')
| psPi x x' y y' : 
  pstep x x'
  -> pstep y y'
  -> pstep (Pi x y)  (Pi x' y')
| psCast x x' y y' : 
  pstep x x'
  -> pstep y y'
  -> pstep (Cast x y)  (Cast x' y')
| psLump x x': 
  psteps x x'
  -> pstep (Lump x)  (Lump x')
| psAssertEq x x' y y' : 
    pstep x x'
    -> pstep y y'
    -> pstep (assertEq x y)  (assertEq x' y')
| psArg x x' : 
  pstep x x'
  -> pstep (Arg x)  (Arg x')
| psBod x x' y y' : 
    pstep x x'
    -> pstep y y'
    -> pstep (Bod x y)  (Bod x' y')
  
with psteps : list term -> list term -> Prop :=
(* better way to do this? *)
| pssNil : psteps nil nil
| psscons x x' rest rest' :
  pstep x x' -> psteps rest rest' -> psteps (cons x rest) (cons x' rest')
.


(* ... *)

(* Axiom Eq : (list term) -> term -> term -> term -> Prop. *)

Axiom Eq : term -> term -> Prop. (* try and assume untyped for now *)

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

| ty_lamb ctx A A' B B' b b' :
  has_enpoint ctx (Pi A B) (Pi A' B') TT ->
   has_enpoint (A' :: ctx) b b' B' -> 
   has_enpoint ctx (Lamb b) (Lamb b') (Pi A' B')
   
| ty_app ctx A' B' f f' a a' :
  has_enpoint ctx f f' (Pi A' B') ->
  has_enpoint ctx a a' A' ->
  has_enpoint ctx (App f a) (App f' a')  (B'.[a'/]) 
| ty_cast ctx A' L B' a a' :
  has_enpoint ctx a a' A' ->

  has_enpoint ctx L A' TT ->
  has_enpoint ctx L B' TT ->
  (* ok ctx L -> *)
  has_enpoint ctx (Cast a L) (Cast a' L) B'



  (* perhaps simplified too much? *)
(* | ty_lump ctx L A' B' a a' :
  In a L ->
  has_enpoint ctx a a' A' ->
  has_enpoint ctx (Lump L) a' A' *)

| ty_assertEqL ctx a a' A' b:
  has_enpoint ctx a a' A' ->
  has_enpoint ctx (assertEq a b) a' A' 
  (* needs cast to allow local reduction behavior *)
  
| ty_assertEqR ctx a a' A' b:
  has_enpoint ctx a a' A' ->
  has_enpoint ctx (assertEq b a) a' A' 
  (* needs cast to allow local reduction behavior *)

| ty_Arg ctx AB A' B' :
  has_enpoint ctx AB (Pi A' B') TT ->
  has_enpoint ctx (Arg AB) A' TT

| ty_bod ctx AB a a' A' B' :
  has_enpoint ctx AB (Pi A' B') TT ->
  has_enpoint ctx a a' A' ->
  has_enpoint ctx (Bod a AB)  (B'.[a'/]) TT 
  
| ty_conv ctx A B a a' :
  Eq A B ->
  has_enpoint ctx a a' A ->
  has_enpoint ctx a a' B

| tm_conv ctx A a a' b :
  Eq a' b ->
  has_enpoint ctx a a' A ->
  has_enpoint ctx a b A
.





(* this is prob wong *)
(* insure a term is "connected" *)
Inductive ok : list term -> term -> Prop :=
| ok_TT ctx :
  ok ctx TT
(* any var in gamma is ok *)
 (* | ty_var Gamma x :
  x < size Gamma ->
  [ Gamma |- Var x :- Gamma`_x ] *)
  (* has_enpoint ctx (Var x) (Var x) (lookup ...) *)

(* 
| ok_pi ctx A B:
  (( A' : term) -> has_enpoint ctx A A' TT -> ok (A' :: ctx) B)
  -> ok ctx (Pi A B) *)

  (* ... *)
.

(* 
Definition ty (ctx : list term) (a : term) (A : term) := 
  has_enpoint ctx a a A.
 *)


