From DDE.Abstract Require Import Common.

(* TODO: use set library *)
(* a set of labeled expression, stack pairs to stub cycles *)
Definition v_set : Type := list (lexpr * sigma).

(* a disjunction of possible analysis results *)
Definition disj : Type := list res.

#[local] Open Scope lang_scope.

Reserved Notation
         "mf ; ml ; s ; S ; V '|-aa' e => rc / Sv"
         (at level 40, e custom lang at level 99, rc constr at next level,
          ml at next level, s at next level, S at next level, V at next level,
          Sv constr).
          
(* union operation in Application *)
Reserved Notation
         "mf ; ml ; s ; S ; V |_A_| r1 => r2 + S2"
         (at level 40, r1 constr at level 99,
          ml at next level, s at next level, S at next level, V at next level,
          r2 constr at next level, S2 constr).

(* union operation in Var Local *)
Reserved Notation
         "mf ; ml ; s ; V ; l' ; e2 |_VL_| S => r2 + S2"
         (at level 40, S constr at level 99, e2 custom lang at level 99,
          ml at next level, s at next level, V at next level, l' at next level,
          r2 constr at next level, S2 constr).

Inductive analyze
  : myfun -> mylexpr -> sigma -> s_set -> v_set -> lexpr -> disj -> s_set -> Prop
:=
  | A_Val : forall mf ml s S V v l,
    mf; ml; s; S; V |-aa ($v)@l => [<{ [ v, l, s ] }>] / S
  | A_Appl : forall mf ml s S V e e' l r2 S2 r1 S1 ls ls_pruned,
    mf; ml; s; S; V |-aa e => r1 / S1 ->
    ls = (l :: s) ->
    ls_pruned = prune_sigma2 ls ->
    mf; ml; ls_pruned; (ls :: S); ((e, ls_pruned) :: V) |_A_| r1 => r2 + S2 ->
    mf; ml; s; S; V |-aa (e <-* e') @ l => r2 / S2
  | A_VarLocal : forall mf ml s0 S V x l r1 S1 l' s mf_l e e1 e2,
    s0 = (l' :: s) ->
    mf l = Some mf_l ->
    ml mf_l = Some <{ ($fun x *-> e) @ mf_l }> ->
    ml l' = Some <{ (e1 <-* e2) @ l' }> ->
    mf; ml; s; ((e, s0) :: V); l'; e2 |_VL_| S => r1 + S1 ->
    mf; ml; s0; S; V |-aa x@l => r1 / S1
  (* TODO: A_VarNonLocal *)

with union_appl : myfun -> mylexpr -> sigma -> s_set -> v_set -> disj -> disj -> s_set -> Prop :=
  | UA_Nil : forall mf ml s S V, mf; ml; s; S; V |_A_| [] => [] + []
  (* go through every disjunct to union the result *)
  | UA_Cons : forall mf ml s S V x1 e1 l1 s1 r1s r2 S2 r0 S0 r0s S0s,
    mf; ml; s; S; V |-aa e1 => r0 / S0 ->
    mf; ml; s; S; V |_A_| r1s => r0s + S0s ->
    r2 = r0 ++ r0s ->
    S2 = S0 ++ S0s ->
    mf; ml; s; S; V |_A_| <{ [ fun x1 *-> e1, l1, s1 ] }> :: r1s => r2 + S2

with union_varlocal : myfun -> mylexpr -> sigma -> v_set -> nat -> lexpr -> s_set -> disj -> s_set -> Prop :=
  | UVL_Nil : forall mf ml s V e2 l', mf; ml; s; V; l'; e2 |_VL_| [] => [] + []
  (* skip current stack s'' its top frame isn't l' *)
  | UVL_Cons_None : forall mf ml s V l' e2 s'' S r0s S0s,
    s'' = [] \/ (forall l'' s', l'' <> l' /\ s'' = l'' :: s') ->
    (* go through the rest of the stacks *)
    mf; ml; s; V; l'; e2 |_VL_| S => r0s + S0s ->
    mf; ml; s; V; l'; e2 |_VL_| (s'' :: S) => r0s + S0s
  (* matching stack to execute and union with *)
  | UVL_Cons_Some : forall mf ml s V l' e2 s'' S r1 S1 s' r0 S0 r0s S0s,
    (* a match! *)
    s'' = l' :: s ++ s' ->
    mf; ml; (s ++ s'); S; V |-aa e2 => r0 / S0 ->
    mf; ml; s; V; l'; e2 |_VL_| S => r0s + S0s ->
    r1 = r0 ++ r0s ->
    S1 = S0 ++ S0s ->
    mf; ml; s; V; l'; e2 |_VL_| (s'' :: S) => r1 + S1

  where "mf ; ml ; s ; S ; V '|-aa' e => rc / Sv" := (analyze mf ml s S V e rc Sv)
    and "mf ; ml ; s ; S ; V |_A_| r1 => r2 + S2" := (union_appl mf ml s S V r1 r2 S2)
    and "mf ; ml ; s ; V ; l' ; e2 |_VL_| S => r2 + S2" := (union_varlocal mf ml s V l' e2 S r2 S2).

(* simple function value *)
Definition eg_val := to_lexpr <{ $fun X -> X }>.
Definition eg_val_mf := build_myfun eg_val.
Definition eg_val_ml := build_mylexpr eg_val.

Example eg_val_correct :
  eg_val_mf; eg_val_ml; []; []; [] |-aa eg_val => [<{ [ fun X *-> X@0, 1, [] ] }>] / [].
Proof.
  apply A_Val.
Qed.

(* simple application involving a local variable lookup *)
Definition eg_loc := to_lexpr <{ ($fun X -> X) <- ($fun Y -> Y) }>.
(* Compute eg_loc. *)
Definition eg_loc_mf := build_myfun eg_loc.
Definition eg_loc_ml := build_mylexpr eg_loc.

Example eg_loc_correct :
  eg_loc_mf; eg_loc_ml; []; []; [] |-aa eg_loc => [<{ [ fun Y *-> Y@2, 3, [] ] }>] / [].
Proof.
  eapply A_Appl; try reflexivity.
  - apply A_Val.
  - eapply UA_Cons.
    + eapply A_VarLocal; try reflexivity.
      eapply UVL_Cons_Some.
      * reflexivity.
      * apply A_Val.
      * apply UVL_Nil.
      * reflexivity.
      * reflexivity.
    + apply UA_Nil.
    + reflexivity.
    + reflexivity.
Qed.

(* TODO: add examples to demonstrate UVL_Cons_None and A_VarNonLocal *)
