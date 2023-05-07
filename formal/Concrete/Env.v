From DDE Require Import Maps.

Inductive expr : Type :=
  | Appl : expr -> expr -> expr
  | Val : val -> expr
  | Ident : string -> expr
with val : Type := Fun : string -> expr -> val.

Inductive res : Type := Res : val -> env -> res
with env : Type := Env : (partial_map string res) -> env.

Coercion Ident : string >-> expr.
#[nonuniform] Coercion Env : partial_map >-> env.

Declare Custom Entry lang.
Declare Scope lang_scope.

(* custom language syntax *)
Notation "<{ e }>" := e (at level 0, e custom lang at level 99) : lang_scope.
Notation "( x )" := x (in custom lang at level 0, x at level 99) : lang_scope.
(* TODO: implication of x constr at level 0? *)
Notation "x" := x (in custom lang at level 0, x constr at level 0) : lang_scope.
Notation "'fun' x -> e" :=
  (Fun x e)
    (in custom lang at level 20, e at next level, right associativity) : lang_scope.
Notation "e1 <- e2" :=
  (Appl e1 e2)
    (in custom lang at level 30, left associativity).
Notation "$ v" :=
  (Val v)
    (in custom lang at level 25) : lang_scope.
Notation "[ v , env ]" :=
  (Res v env)
    (in custom lang at level 15, v at next level, env constr) : lang_scope.

#[local] Open Scope lang_scope.

Definition X : string := "x".
Definition Y : string := "y".
Definition Z : string := "z".
Definition M : string := "m".
Definition N : string := "n".

Example sample_res := <{ [ fun Y -> Y, X |-> <{ [ fun Y -> Y, empty] }> ] }>.

Reserved Notation
         "env |- e => r"
         (at level 40, e custom lang at level 99, env constr, r custom lang at level 99).

Inductive eval : expr -> env -> res -> Prop :=
  | E_Val : forall E v,
    E |- $v => [ v, E ]
  | E_Appl : forall E e1 e2 r x e (E1 : partial_map string res) r2,
    E |- e1 => [ fun x -> e, E1 ] ->
    E |- e2 => r2 ->
    (x |-> r2; E1) |- e => r ->
    E |- e1 <- e2 => r
  | E_Var : forall (E : partial_map string res) x r,
    E x = Some r ->
    E |- x => r

  where "env |- e => r" := (eval e env r).

Example eg_val_correct :
  empty |- $fun X -> X => [ fun X -> X, empty ].
Proof.
  apply E_Val.
Qed.

Example eg_app_correct :
  empty |- $fun X -> X <- $fun Y -> Y => [ fun Y -> Y, empty ].
Proof.
  eapply E_Appl.
  - apply E_Val.
  - apply E_Val.
  - apply E_Var. unfold update, t_update. simpl. reflexivity.
Qed.
