From Coq Require Import Arith.Arith. Import Nat.

Definition total_map (A : Type) := nat -> A.

Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).

Definition t_update {A : Type} (m : total_map A)
                    (i : nat) (v : A) :=
  fun i' => if i =? i' then v else m i'.

Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity).

Notation "i '!->' v ';' m" := (t_update m i v)
                              (at level 100, v at next level, right associativity).

Lemma t_update_eq : forall (A : Type) (m : total_map A) i v,
  (i !-> v ; m) i = v.
Proof.
  intros A m x v. unfold t_update. rewrite eqb_refl. reflexivity.
Qed.

Theorem t_update_neq : forall (A : Type) (m : total_map A) i1 i2 v,
  i1 <> i2 ->
  (i1 !-> v ; m) i2 = m i2.
Proof.
  intros A m i1 i2 v Hneq.
  unfold t_update. apply eqb_neq in Hneq.
  rewrite Hneq. reflexivity.
Qed.

Definition partial_map (A : Type) := total_map (option A).

Definition empty {A : Type} : partial_map A :=
  t_empty None.

Definition update {A : Type} (m : partial_map A)
           (i : nat) (v : A) :=
  (i !-> Some v ; m).

Notation "i '|->' v ';' m" := (update m i v)
  (at level 100, v at next level, right associativity).

Notation "i '|->' v" := (update empty i v)
  (at level 100).
