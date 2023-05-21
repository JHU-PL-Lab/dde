From DDE.Abstract Require Import Common.

#[local] Open Scope lang_scope.

Reserved Notation
         "mf ; ml ; s ; S '|-a' e => rv / Sv"
         (at level 40, e custom lang at level 99, rv at next level,
          ml at next level, s at next level, S at next level, Sv at next level).

Inductive analyze
  : myfun -> mylexpr -> sigma -> s_set -> lexpr -> res -> s_set -> Prop
:=
  | A_Val : forall mf ml s S v l,
    mf; ml; s; S |-a ($v)@l => (<v, l, s>) / S
  | A_Appl : forall mf ml s S e1 e2 l rv Sv x e l1 s1 S1,
    mf; ml; s; S |-a e1 => <fun x *-> e, l1, s1> / S1 ->
    mf; ml; prune_sigma2 (l :: s); ((l :: s) :: S1) |-a e => rv / Sv ->
    mf; ml; s; S |-a (e1 <-* e2) @ l => rv / Sv
  (* TODO: should s' be universally/existentially quantified? *)
  | A_VarLocal : forall mf ml e1 e2 l' s S x l rv Sv mf_l e s',
    mf l = Some mf_l ->
    ml mf_l = Some <{ ($fun x *-> e) @ mf_l }> ->
    ml l' = Some <{ (e1 <-* e2) @ l' }> ->
    (exists s0, In s0 S /\ s0 = l' :: s ++ s') ->
    mf; ml; (s ++ s'); S |-a e2 => rv / Sv ->
    mf; ml; (l' :: s); S |-a x@l => rv / Sv
  | A_VarNonLocal : forall mf ml e1 e2 l2 s S x l rv Sv x1 e l1 s1 S1,
    mf l = Some l1 ->
    ml l1 = Some <{ ($fun x1 *-> e) @ l1 }> ->
    x <> x1 ->
    ml l2 = Some <{ (e1 <-* e2) @ l2 }> ->
    mf; ml; s; S |-a e1 => <fun x1 *-> e, l1, s1> / S1 ->
    mf; ml; s1; S1 |-a x@l1 => rv / Sv ->
    mf; ml; (l2 :: s); S |-a x@l => rv / Sv

  where "mf ; ml ; s ; S '|-a' e => rv / Sv" := (analyze mf ml s S e rv Sv).

Definition Self : string := "self".

Definition self_fun := <{ $fun Self -> $fun N -> Self <- Self }>.
Definition eg_rec :=
  to_lexpr <{ self_fun <- self_fun <- $fun X -> X }>.
(* Compute eg_rec. *)
Definition eg_rec_mf := build_myfun eg_rec.
Definition eg_rec_ml := build_mylexpr eg_rec.

(* TODO: find examples *)
Theorem analyze_nondeterministic :
  ~ forall mf ml s S e Sv rv1 rv2,
      mf; ml; s; S |-a e => rv1 / Sv ->
      mf; ml; s; S |-a e => rv2 / Sv ->
      rv1 = rv2.
Admitted.
