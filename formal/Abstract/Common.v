From Coq Require Import Arith.Arith.
From DDE.Common Require Export Lang.

(* a set of call stacks *)
Definition S_set : Type := list sigma.

Class EqDec (A : Type) := {
  eq_dec: forall (x y : A), {x = y} + {x <> y}
}.

#[export] Instance EqDec_nat : EqDec nat := {
  eq_dec x y := eq_nat_dec x y
}.

#[export] Instance EqDec_sigam : EqDec sigma := {
  eq_dec x y := list_eq_dec eq_nat_dec x y
}.

#[export] Instance EqDec_S : EqDec S_set := {
  eq_dec x y := list_eq_dec (list_eq_dec eq_nat_dec) x y
}.

Definition nodup_cons {A : Type} {eq_dec_A : EqDec A} (x : A) (set : list A) : list A :=
  if in_dec eq_dec x set then set else x :: set.

Definition nodup_app {A : Type} {eq_dec_A : EqDec A}
                     (set1 : list A) (set2 : list A) : list A :=
  fold_right nodup_cons set2 set1.

Notation "x ~> set" := (nodup_cons x set)
  (at level 67, right associativity).
Notation "S1 |_| S2" := (nodup_app S1 S2)
  (at level 68, S2 at next level, no associativity).

Example eg_nodup_app : [1; 2; 3] |_| [2; 3; 4] = [1; 2; 3; 4].
Proof.
  reflexivity.
Qed.

Fixpoint prune_sigma (s : sigma) (k : nat) (acc : sigma) : sigma := 
  match s with
  | [] => acc
  | l :: ls =>
    if k =? 0 then acc
    else prune_sigma ls (k - 1) (l :: acc)
  end.

Definition prune_sigma2 (s : sigma) : sigma := prune_sigma s 2 [].
