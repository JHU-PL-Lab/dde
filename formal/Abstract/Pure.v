From Coq Require Import Arith.Arith.
From DDE.Common Require Import Lang.

Definition s_set : Type := list sigma.

#[local] Open Scope lang_scope.

Fixpoint prune_sigma (s : sigma) (k : nat) (acc : sigma) : sigma := 
  match s with
  | [] => acc
  | l :: ls =>
    if k =? 0 then acc
    else prune_sigma ls (k - 1) (l :: acc)
  end.

Definition prune_sigma_2 (s : sigma) : sigma :=
  prune_sigma s 2 [].

Reserved Notation
         "mf / ml / s / S '|-a' e => rv / Sv"
         (at level 40, e custom lang at level 99, rv custom lang at level 99,
          ml at next level, s at next level, S at next level, Sv constr).

Inductive analyze
  : myfun -> mylexpr -> sigma -> s_set -> lexpr -> res -> s_set -> Prop
:=
  | E_Val : forall mf ml s S v l,
    mf / ml / s / S |-a ($v)@l => [ v, l, s ] / S
  | E_Appl : forall mf ml s S e1 e2 l rv Sv x e l1 s1 S1,
    mf / ml / s / S |-a e1 => [ fun x *-> e, l1, s1 ] / S1 ->
    mf / ml / prune_sigma_2 (l :: s) / ((l :: s) :: S1) |-a e => rv / Sv ->
    mf / ml / s / S |-a (e1 <-* e2) @ l => rv / Sv
  (* TODO: should s' be universally/existentially quantified? *)
  | E_VarLocal : forall mf ml e1 e2 l' s S x l rv Sv mf_l e s',
    mf l = Some mf_l ->
    ml mf_l = Some <{ ($fun x *-> e) @ mf_l }> ->
    ml l' = Some <{ (e1 <-* e2) @ l' }> ->
    (exists s0, In s0 S /\ s0 = l' :: s ++ s') ->
    mf / ml / (s ++ s') / S |-a e2 => rv / Sv ->
    mf / ml / (l' :: s) / S |-a x@l => rv / Sv
  | E_VarNonLocal : forall mf ml e1 e2 l2 s S x l rv Sv x1 e l1 s1 S1,
    mf l = Some l1 ->
    ml l1 = Some <{ ($fun x1 *-> e) @ l1 }> ->
    x <> x1 ->
    ml l2 = Some <{ (e1 <-* e2) @ l2 }> ->
    mf / ml / s / S |-a e1 => [ fun x1 *-> e, l1, s1] / S1 ->
    mf / ml / s1 / S1 |-a x@l1 => rv / Sv ->
    mf / ml / (l2 :: s) / S |-a x@l => rv / Sv

  where "mf / ml / s / S '|-a' e => rv / Sv" := (analyze mf ml s S e rv Sv).

Definition Self : string := "self".
Definition self_fun := <{ $fun Self -> $fun N -> Self <- Self }>.

Definition eg_rec :=
  to_lexpr <{ self_fun <- self_fun <- $fun X -> X }>.
(* Compute eg_rec. *)
Definition eg_rec_mf := build_myfun eg_rec None empty.
Definition eg_rec_ml := build_mylexpr eg_rec empty.

(* TODO: find examples *)
Theorem analyze_nondeterministic :
  ~ forall mf ml s S e Sv rv1 rv2,
      mf / ml / s / S |-a e => rv1 / Sv ->
      mf / ml / s / S |-a e => rv2 / Sv ->
      rv1 = rv2.
Admitted.
