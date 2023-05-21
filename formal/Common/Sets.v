From Coq Require Export Sets.Ensembles Sets.Powerset_Classical_facts Sets.Powerset_facts.
From DDE.Common Require Import Tactics.

Definition set (A : Type) : Type := Ensemble A.

Definition empty_set {A : Type} : set A := Empty_set A.

Definition add {A : Type} (S : set A) (x : A) : set A :=
  Add A S x.

Definition subtract {A : Type} (S : set A) (x : A) : set A :=
  Subtract A S x.

Definition union {A : Type} (S1 : set A) (S2 : set A) : set A :=
  Union A S1 S2.

Notation "x ~> S" := (add S x)
  (at level 67, right associativity).
Notation "S \ x" := (subtract S x)
  (at level 68, left associativity).
Notation "S1 |_| S2" := (union S1 S2)
  (at level 69, S2 at next level, no associativity).
Notation "x ? S" := (In _ S x)
  (at level 70, S at next level, no associativity).

Example eg_add := 1 ~> 2 ~> 3 ~> empty_set.
Example eg_sub := (1 ~> 2 ~> empty_set \ 1 \ 2) ~> empty_set.
Example eg_union := 1 ~> empty_set |_| empty_set.
Example eg_in := 1 ? 1 ~> empty_set \ 1.

Example eg_not_in : ~ eg_in.
Proof.
  unfold eg_in, "?", "~>", "\".
  intro Contra. inversion Contra.
  apply H0. inversion H.
  - contradiction.
  - assumption.
Qed.

(* overload standard library lemma to not disrupt notations *)
Lemma add_comm : forall {A : Type} (S : set A) (x y : A),
  x ~> y ~> S = y ~> x ~> S.
Proof.
  intros. apply Add_commutative.
Qed.
