(* overall design courtesy of Logical Foundations
  https://softwarefoundations.cis.upenn.edu/lf-current/Maps.html *)

From Coq Require Import Arith.Arith. Import Nat.
From Coq Require Export Strings.String.

Class Eqb (A : Type) := {
  eqb: A -> A -> bool
}.

#[global] Instance nat_Eqb : Eqb nat := {
  eqb x y := Nat.eqb x y
}.

#[global] Instance string_Eqb : Eqb string := {
  eqb x y := String.eqb x y
}.

Definition total_map (K : Type) (V : Type) := K -> V.

Definition t_empty {K : Type} {V : Type} (v : V) : total_map K V :=
  (fun _ => v).

Definition t_update {K : Type} {V : Type} {eqbk : Eqb K}
                    (m : total_map K V) (k : K) (v : V) : total_map K V :=
  fun k' => if eqb k k' then v else m k'.

Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity).

Notation "k '!->' v ; m" := (t_update m k v)
                              (at level 100, v at next level, right associativity).

Definition partial_map (K : Type) (V : Type) := total_map K (option V).

Definition empty {K : Type} {V : Type} : partial_map K V :=
  t_empty None.

Definition update {K : Type} {V : Type} {eqbk : Eqb K}
                  (m : partial_map K V) (k : K) (v : V) : partial_map K V :=
  (k !-> Some v ; m).

Notation "k '|->' v ; m" := (update m k v)
  (at level 100, v at next level, right associativity).

Notation "k '|->' v" := (update empty k v)
  (at level 100).
