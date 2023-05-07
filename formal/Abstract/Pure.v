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

Reserved Notation
         "s / S '|-a' e => rv / Sv"
         (at level 40, e custom lang at level 99, rv custom lang at level 99,
          S at next level, Sv constr).

Inductive analyze : sigma -> s_set -> lexpr -> res -> s_set -> Prop :=
  | E_Val : forall s S v l,
    s / S |-a ($v)@l => [ v, l, s ] / S
  | E_Appl : forall s S e1 e2 l rv Sv x e l1 s1 S1,
    s / S |-a e1 => [ fun x -> e, l1, s1 ] / S1 ->
    prune_sigma (l :: s) 2 [] / ((l :: s) :: S1) |-a e => rv / Sv ->
    s / S |-a (e1 <- e2) @ l => rv / Sv
  (* TODO: should s' be universally/existentially quantified? *)
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

  where "s / S '|-a' e => rv / Sv" := (analyze s S e rv Sv).

Definition eg_recursion :=
  <{ (((($fun X ->
      ($fun N ->
          (((X@0 <- X@1) @ 2) <- N@3) @ 4) @ 5) @ 6
      <- ($fun Y -> Y@7) @ 8) @ 9)
      <- ($fun Z -> Z@10) @ 11) @ 12 }>.

Theorem analyze_nondeterministic :
  ~ forall s S e Sv rv1 rv2,
      s / S |-a e => rv1 / Sv ->
      s / S |-a e => rv2 / Sv ->
      rv1 = rv2.
Admitted.
