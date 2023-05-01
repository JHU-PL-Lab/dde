From Coq Require Import Lists.List Arith.Arith.
Import ListNotations.
From DDE Require Import Maps.

Inductive expr : Type :=
  | Appl: lexpr -> lexpr -> expr
  | Val: val -> expr
  | Ident: string -> expr
with lexpr : Type := Lexpr : expr -> nat -> lexpr
with val : Type := Fun : string -> lexpr -> val.

Definition sigma : Type := list nat.

Inductive res : Type := Res : val -> nat -> sigma -> res.

Definition s_set : Type := list sigma.

Inductive res_S : Type := ResS : res -> s_set -> res_S.

Coercion Ident : string >-> expr.

Declare Custom Entry lang.
Declare Scope lang_scope.

(* custom language syntax *)
Notation "<{ e }>" := e (at level 0, e custom lang at level 99) : lang_scope.
Notation "( x )" := x (in custom lang at level 0, x at level 99) : lang_scope.
Notation "x" := x (in custom lang at level 0, x constr at level 0) : lang_scope.
Notation "'fun' x -> e" :=
  (Fun x e)
    (in custom lang at level 20, e at next level, right associativity) : lang_scope.
Notation "e1 <- e2" :=
  (Appl e1 e2)
    (* associativity doesn't matter here as e1 and e2 are lexprs *)
    (in custom lang at level 30, left associativity).
Notation "$ v" :=
  (Val v)
    (in custom lang at level 25) : lang_scope.
Notation "e @ l" :=
  (Lexpr e l)
    (in custom lang at level 15) : lang_scope.
Notation "[ v , l , s ]" :=
  (Res v l s)
    (in custom lang at level 99, v at next level, l at next level, s constr) : lang_scope.
Notation "res / S" :=
  (ResS res S)
    (in custom lang at level 99) : lang_scope.

#[local] Open Scope lang_scope.

Definition X : string := "x".
Definition Y : string := "y".
Definition Z : string := "z".
Definition M : string := "m".
Definition N : string := "n".

Definition myfun : Type := partial_map nat nat.
Definition mylexpr : Type := partial_map nat lexpr.

(* build mapping from label to label of enclosing function given a root lexpr *)
Fixpoint build_myfun (le : lexpr) (mf_l : option nat) (mf : myfun) : myfun :=
  match le with
  | <{ e @ l }> =>
    match e with
    | Val v =>
      match v with
      | <{ fun _ -> e' }> => build_myfun e' (Some l) (l !-> mf_l; mf)
      end
    | Ident _ => (l !-> mf_l; mf)
    | <{ e1 <- e2 }> => build_myfun e2 mf_l (build_myfun e1 mf_l mf)
    end
  end.

(* build mapping from label to lexpr given a root lexpr *)
Fixpoint build_mylexpr (le : lexpr) (ml : mylexpr) : mylexpr :=
  match le with
  | <{ e @ l }> =>
    match e with
    | Val v =>
      match v with
      | <{ fun _ -> e' }> => (l |-> le; build_mylexpr e' ml)
      end
    | Ident _ => (l |-> le; ml)
    | <{ e1 <- e2 }> => (l |-> le; build_mylexpr e2 (build_mylexpr e1 ml))
    end
  end.

Fixpoint prune_sigma (s : sigma) (k : nat) (acc : sigma) : sigma := 
  match s with
  | [] => acc
  | l :: ls =>
    if k =? 0 then acc
    else prune_sigma ls (k - 1) (l :: acc)
  end.

Reserved Notation
         "s / S '|-a' e => r"
         (at level 40, e custom lang at level 99, r custom lang at level 99,
          S at next level).

Inductive analyze : sigma -> s_set -> lexpr -> res_S -> Prop :=
  | E_Val : forall s S v l,
    s / S |-a ($v)@l => [ v, l, s ] / S
  | E_Appl : forall s S e1 e2 l rv Sv x e l1 s1 S1,
    s / S |-a e1 => [ fun x -> e, l1, s1 ] / S1 ->
    prune_sigma (l :: s) 2 [] / ((l :: s) :: S1) |-a e => rv / Sv ->
    s / S |-a (e1 <- e2) @ l => rv / Sv
  (* TODO: should s' be universally/exitentially quantified? *)
  | E_VarLocal : forall e1 e2 l' s S x l rv Sv mf mf_l e ml s',
    mf l = mf_l ->
    ml mf_l = Some <{ ($fun x -> e) @ mf_l }> ->
    ml l' = Some <{ (e1 <- e2) @ l' }> ->
    (exists s0, In s0 S /\ s0 = l' :: s ++ s') ->
    (s ++ s') / S |-a e2 => rv / Sv ->
    (l' :: s) / S |-a x@l => rv / Sv
  | E_VarNonLocal : forall e1 e2 l2 s S x l rv Sv mf x1 e ml l1 s1 S1,
    mf l = l1 ->
    ml l1 = Some <{ ($fun x1 -> e) @ l1 }> ->
    x <> x1 ->
    ml l2 = Some <{ (e1 <- e2) @ l2 }> ->
    s / S |-a e1 => [ fun x1 -> e, l1, s1] / S1 ->
    s1 / S1 |-a x@l1 => rv / Sv ->
    (l2 :: s) / S |-a x@l => rv / Sv

  where "s / S '|-a' e => r" := (analyze s S e r).

Close Scope lang_scope.
