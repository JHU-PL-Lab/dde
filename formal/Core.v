Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Lia.
From Coq Require Import Strings.String Lists.List Arith.Arith.
From DDE Require Import Maps.
Import ListNotations.

Inductive expr : Type :=
  | Appl (e1 : lexpr) (e2 : lexpr)
  | Val (v : val)
  | Ident (id : string)
with lexpr : Type := Lexpr (e : expr) (l : nat)
with val : Type := Fun (id : string) (e : lexpr).

Definition sigma : Type := list nat.

Inductive res : Type := Res (v : val) (l : nat) (s : sigma).

Coercion Ident : string >-> expr.

Declare Custom Entry lang.
Declare Scope lang_scope.

Notation "<{ e }>" := e (at level 0, e custom lang at level 99) : lang_scope.
Notation "( x )" := x (in custom lang, x at level 99) : lang_scope.
Notation "x" := x (in custom lang at level 0, x constr at level 0) : lang_scope.
(* TODO: Next level? *)
Notation "'fun' x -> e" :=
  (Fun x e)
    (in custom lang at level 20, e at level 30, right associativity) : lang_scope.
Notation "e1 <- e2" :=
  (Appl e1 e2)
    (in custom lang at level 30, left associativity).
Notation "e @ l" :=
  (Lexpr e l)
    (in custom lang at level 15, no associativity) : lang_scope.
Notation "v @@ l" :=
  (Lexpr (Val v) l)
    (in custom lang at level 15, no associativity) : lang_scope.
(* TODO: Meh syntax to make parser happy *)
Notation "#[ v , l , s ]" :=
  (Res v l s)
    (in custom lang at level 15, v at level 25, s at level 25, no associativity) : lang_scope.

Open Scope lang_scope.

Definition X : string := "x".
Definition Y : string := "y".
Definition Z : string := "z".

Example sample_ident := <{ X@1 }>.
Example sample_fun := <{ fun X -> X@1 }>.
Example sample_fun_lexpr := <{ (fun X -> X@1) @@ 2 }>.
Example sample_fun_lexpr' := <{ (fun X -> (fun Y -> X@1) @@ 2) @@ 3 }>.
Example sample_appl := <{ (X@1 <- X@2) @ 3}>.
Example sample_res := <{ #[fun X -> X@1, 2, nil] }>.

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

Inductive eval : lexpr -> sigma -> res -> partial_map nat -> partial_map lexpr -> Prop :=
  | E_Val : forall s v l myfun mylexpr, eval <{ v @@ l }> s <{ #[v, l, s] }> myfun mylexpr
  (* TODO: forall sound? *)
  | E_Appl : forall e1 e2 l s r e l1 s1 myfun mylexpr x,
    eval e1 s <{ #[fun x -> e, l1, s1] }> myfun mylexpr ->
    eval e (l :: s) r myfun mylexpr ->
    eval <{ (e1 <- e2) @ l }> s r myfun mylexpr
  | E_VarLocal : forall (x : string) l s r myfun mylexpr e1 e2 l' e myfun_l,
    length s <> 0 ->
    (* TODO: hd default value sound? *)
    mylexpr (hd 0 s) = Some <{ (e1 <- e2) @ l' }> ->
    myfun l = Some myfun_l ->
    mylexpr myfun_l = Some <{ (fun x -> e) @@ myfun_l }> ->
    eval e2 (tl s) r myfun mylexpr ->
    eval <{ x@l }> s r myfun mylexpr.

Hint Unfold build_myfun build_mylexpr update t_update : core.

Definition id_val :=
  <{ (fun X -> X@0) @@ 1 }>.
Definition id_val_myfun :=
  build_myfun id_val None empty.
Definition id_val_mylexpr :=
  build_mylexpr id_val empty.

Example val_correct :
  eval id_val [] <{ #[fun X -> X@0, 1, []] }> id_val_myfun id_val_mylexpr.
Proof.
  apply E_Val.
Qed.

Definition id_appl :=
  <{ (((fun X -> X@0) @@ 1) <- ((fun Y -> Y@2) @@ 3)) @ 4 }>.
Definition id_appl_myfun :=
  build_myfun id_appl None empty.
Definition id_appl_mylexpr :=
  build_mylexpr id_appl empty.

Example appl_correct :
  eval id_appl [] <{ #[fun Y -> Y@2, 3, []] }> id_appl_myfun id_appl_mylexpr.
Proof.
  eapply E_Appl.
  - apply E_Val.
  - eapply E_VarLocal.
    + auto.
    + unfold id_appl_mylexpr, id_appl. autounfold. reflexivity.
    + unfold id_appl_myfun, id_appl. autounfold. reflexivity.
    + unfold id_appl_mylexpr, id_appl. autounfold. reflexivity.
    + apply E_Val.
Qed.
