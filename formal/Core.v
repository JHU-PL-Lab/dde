Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Lia.
From Coq Require Import Strings.String Lists.List Arith.Arith.
From DDE Require Import Maps.
Import ListNotations.

(* slightly adjusted definition to more easily define notations *)
Inductive expr : Type :=
  | Appl (e1 : lexpr) (e2 : lexpr)
  | Val (v : val)
  | Ident (id : string)
with lexpr : Type := Lexpr (e : expr) (l : nat)
with val : Type := Fun (id : string) (e : lexpr).

Definition sigma : Type := list nat.

Inductive res : Type := Res (v : val) (l : nat) (s : sigma).

(* coherce strings into exprs via the Ident constructor *)
Coercion Ident : string >-> expr.

Declare Custom Entry lang.
Declare Scope lang_scope.

(* custom language syntax *)
Notation "<{ e }>" := e (at level 0, e custom lang at level 99) : lang_scope.
Notation "( x )" := x (in custom lang, x at level 99) : lang_scope.
Notation "x" := x (in custom lang at level 0, x constr at level 0) : lang_scope.
(* TODO: next level? *)
Notation "'fun' x -> e" :=
  (Fun x e)
    (in custom lang at level 20, e at level 30, right associativity) : lang_scope.
Notation "e1 <- e2" :=
  (Appl e1 e2)
    (* associativity doesn't matter here as e1 and e2 are lexprs *)
    (in custom lang at level 30, left associativity).
Notation "e @ l" :=
  (Lexpr e l)
    (in custom lang at level 15, no associativity) : lang_scope.
Notation "v @@ l" :=
  (Lexpr (Val v) l)
    (in custom lang at level 15, no associativity) : lang_scope.
(* TODO: meh syntax to make parser happy *)
Notation "#[ v , l , s ]" :=
  (Res v l s)
    (in custom lang at level 15, v at level 25, s at level 25, no associativity) : lang_scope.

Open Scope lang_scope.

Definition X : string := "x".
Definition Y : string := "y".
Definition Z : string := "z".
Definition M : string := "m".
Definition N : string := "n".

Example sample_ident := <{ X@1 }>.
Example sample_fun := <{ fun X -> X@1 }>.
Example sample_fun_lexpr := <{ (fun X -> X@1) @@ 2 }>.
Example sample_fun_lexpr' := <{ (fun X -> (fun Y -> X@1) @@ 2) @@ 3 }>.
Example sample_appl := <{ (X@1 <- X@2) @ 3}>.
Example sample_res := <{ #[fun X -> X@1, 2, nil] }>.

(* build mapping from label to label of enclosing function given a root lexpr *)
Fixpoint build_myfun (le : lexpr) (myfun_l : option nat) (myfun : partial_map nat) : partial_map nat :=
  match le with
  | <{ e @ l }> =>
    match e with
    | Val v =>
      match v with
      | <{ fun _ -> e' }> => build_myfun e' (Some l) (l !-> myfun_l; myfun)
      end
    | Ident _ => (l !-> myfun_l; myfun)
    | <{ e1 <- e2 }> => build_myfun e2 myfun_l (build_myfun e1 myfun_l myfun)
    end
  end.

(* Compute build_myfun <{ (fun X -> X@1 ) @@ 2 }> None empty. *)

(* build mapping from label to lexpr given a root lexpr *)
Fixpoint build_mylexpr (le : lexpr) (mylexpr : partial_map lexpr) : partial_map lexpr :=
  match le with
  | <{ e @ l }> =>
    match e with
    | Val v =>
      match v with
      | <{ fun _ -> e' }> => (l |-> le; build_mylexpr e' mylexpr)
      end
    | Ident _ => (l |-> le; mylexpr)
    | <{ e1 <- e2 }> => (l |-> le; build_mylexpr e2 (build_mylexpr e1 mylexpr))
    end
  end.

(* Compute build_mylexpr <{ (fun X -> X@1 ) @@ 2 }> empty. *)

(* custom syntax for evaluation; I try to mirror the written syntax as much as possible *)
Reserved Notation
         "{{ myfun , mylexpr , s }} |- e => r"
         (at level 40, e custom lang at level 99,
          myfun constr, mylexpr constr, s constr, r custom lang at level 99).

(* logic for DDE's concrete lambda calculus operational semantics *)
Inductive eval : lexpr -> sigma -> res -> partial_map nat -> partial_map lexpr -> Prop :=
  | E_Val : forall s v l myfun mylexpr,
    {{ myfun, mylexpr, s }} |- v@@l => #[v, l, s]
  (* TODO: forall sound? *)
  | E_Appl : forall e1 e2 l s r e l1 s1 myfun mylexpr x,
    {{ myfun, mylexpr, s }} |- e1 => #[fun x -> e, l1, s1] ->
    {{ myfun, mylexpr, l :: s }} |- e => r ->
    {{ myfun, mylexpr, s }} |- (e1 <- e2) @ l => r
  | E_VarLocal : forall (x : string) l s r myfun mylexpr e1 e2 l' e myfun_l,
    length s <> 0 ->
    (* hd will never give default *)
    mylexpr (hd 0 s) = Some <{ (e1 <- e2) @ l' }> ->
    myfun l = Some myfun_l ->
    mylexpr myfun_l = Some <{ (fun x -> e) @@ myfun_l }> ->
    {{ myfun, mylexpr, tl s }} |- e2 => r ->
    {{ myfun, mylexpr, s }} |- x@l => r
  | E_VarNonLocal : forall (x : string) l s r myfun mylexpr e1 e2 l2 e myfun_l x1 s1,
    length s <> 0 ->
    mylexpr (hd 0 s) = Some <{ (e1 <- e2) @ l2 }> ->
    myfun l = Some myfun_l ->
    mylexpr myfun_l = Some <{ (fun x1 -> e) @@ myfun_l }> ->
    x <> x1 ->
    {{ myfun, mylexpr, tl s }} |- e1 => #[fun x1 -> e, myfun_l, s1] ->
    {{ myfun, mylexpr, s1 }} |- x@myfun_l => r ->
    {{ myfun, mylexpr, s }} |- x@l => r

  where "{{ myfun , mylexpr , s }} |- e => r" := (eval e s r myfun mylexpr).

Hint Unfold build_myfun build_mylexpr update t_update : core.

Definition id_val :=
  <{ (fun X -> X@0) @@ 1 }>.
Definition id_val_myfun :=
  build_myfun id_val None empty.
Definition id_val_mylexpr :=
  build_mylexpr id_val empty.

(* simple value *)
Example val_correct :
  {{ id_val_myfun, id_val_mylexpr, [] }} |- id_val => #[fun X -> X@0, 1, []].
Proof.
  apply E_Val.
Qed.

Definition eg_loc :=
  <{ ((fun X -> X@0) @@ 1 <- (fun Y -> Y@2) @@ 3) @ 4 }>.
Definition eg_loc_myfun :=
  build_myfun eg_loc None empty.
Definition eg_loc_mylexpr :=
  build_mylexpr eg_loc empty.

(* local variable lookup *)
Example eg_loc_correct :
  {{ eg_loc_myfun, eg_loc_mylexpr, [] }} |- eg_loc => #[fun Y -> Y@2, 3, []].
Proof.
  eapply E_Appl.
  - apply E_Val.
  - eapply E_VarLocal.
    + auto.
    + unfold eg_loc_mylexpr, eg_loc. autounfold. reflexivity.
    + unfold eg_loc_myfun, eg_loc. autounfold. reflexivity.
    + unfold eg_loc_mylexpr, eg_loc. autounfold. reflexivity.
    + apply E_Val.
Qed.

(* non-local variable lookup *)
Definition eg_noloc :=
  <{ (((fun X -> (fun Y -> X@0) @@ 1) @@ 2
       <- (fun Z -> Z@3) @@ 4) @ 5
       <- (fun M -> M@6) @@ 7) @ 8 }>.
Definition eg_noloc_myfun :=
  build_myfun eg_noloc None empty.
Definition eg_noloc_mylexpr :=
  build_mylexpr eg_noloc empty.

Example eg_noloc_correct :
  {{ eg_noloc_myfun, eg_noloc_mylexpr, [] }} |- eg_noloc => #[fun Z -> Z@3, 4, []].
Proof.
  eapply E_Appl.
  - eapply E_Appl.
    + apply E_Val.
    + apply E_Val.
  - eapply E_VarNonLocal.
    + auto.
    + reflexivity.
    + reflexivity.
    + unfold eg_noloc_mylexpr, eg_noloc. autounfold. reflexivity.
    + intro contra. discriminate contra.
    (* N.B. that we re-do the application here, as expected from the rules *)
    + eapply E_Appl.
      * apply E_Val.
      * apply E_Val.
    + eapply E_VarLocal.
      * auto.
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * apply E_Val.
Qed.

(* TODO: auto-generate labels *)
