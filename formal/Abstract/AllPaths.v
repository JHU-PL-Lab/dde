From DDE.Abstract Require Import Common.

Definition v_set : Type := list (lexpr * sigma).

Definition disj : Type := list res.

#[local] Open Scope lang_scope.

Reserved Notation
         "mf / ml / s / S / V '|-aa' e => rc / Sv"
         (at level 40, e custom lang at level 99, rc constr at next level,
          ml at next level, s at next level, S at next level, V at next level,
          Sv constr).

(* TODO: use Record to declutter *)
Inductive analyze
  : myfun -> mylexpr -> sigma -> s_set -> v_set -> lexpr -> disj -> s_set -> Prop
:=
  | A_Val : forall mf ml s S V v l,
    mf / ml / s / S / V |-aa ($v)@l => [<{ [ v, l, s ] }>] / S
  | A_Appl : forall mf ml s S V e e' l r2 S2 r1 S1 ls ls_pruned,
    mf / ml / s / S / V |-aa e => r1 / S1 ->
    ls = (l :: s) ->
    ls_pruned = prune_sigma2 ls ->
    union_appl mf ml ls_pruned (S ++ [ls]) (V ++ [(e, ls_pruned)]) r1 r2 S2 ->
    mf / ml / s / S / V |-aa (e <-* e') @ l => r2 / S2
  | A_VarLocal : forall mf ml s0 S V x l r1 S1 l' s mf_l e e1 e2,
    s0 = (l' :: s) ->
    mf l = Some mf_l ->
    ml mf_l = Some <{ ($fun x *-> e) @ mf_l }> ->
    ml l' = Some <{ (e1 <-* e2) @ l' }> ->
    union_varlocal mf ml s l' S (V ++ [(e, s0)]) e2 r1 S1 ->
    mf / ml / s0 / S / V |-aa x@l => r1 / S1

with union_appl : myfun -> mylexpr -> sigma -> s_set -> v_set -> disj -> disj -> s_set -> Prop :=
  | UA_nil : forall mf ml s S V, union_appl mf ml s S V [] [] []
  | UA_cons : forall mf ml x1 e1 l1 s1 s S V r0 S0 rs r0s S0s,
    mf / ml / s / S / V |-aa e1 => r0 / S0 ->
    union_appl mf ml s S V rs r0s S0s ->
    union_appl mf ml s S V (<{ [ fun x1 *-> e1, l1, s1 ] }> :: rs) (r0 ++ r0s) (S0 ++ S0s)

with union_varlocal : myfun -> mylexpr -> sigma -> nat -> s_set -> v_set -> lexpr -> disj -> s_set -> Prop :=
  | UVL_nil : forall mf ml s l' V e, union_varlocal mf ml s l' [] V e [] []
  (* TODO cons but no match *)
  | UVL_cons : forall mf ml s l' s' S Vnew e2 r0 S0 r0s S0s,
    mf / ml / (s ++ s') / S / Vnew |-aa e2 => r0 / S0 ->
    union_varlocal mf ml s l' S Vnew e2 r0s S0s ->
    union_varlocal mf ml s l' ((l' :: s ++ s') :: S) Vnew e2 (r0 ++ r0s) (S0 ++ S0s)

  where "mf / ml / s / S / V '|-aa' e => rc / Sv" := (analyze mf ml s S V e rc Sv).
  
Definition eg_val := to_lexpr <{ $fun X -> X }>.
Definition eg_val_mf := build_myfun eg_val.
Definition eg_val_ml := build_mylexpr eg_val.

Example eg_val_correct :
  eg_val_mf / eg_val_ml / [] / [] / [] |-aa eg_val => [<{ [ fun X *-> X@0, 1, [] ] }>] / [].
Proof.
  apply A_Val.
Qed.

Definition eg_loc := to_lexpr <{ ($fun X -> X) <- ($fun Y -> Y) }>.
(* Compute eg_loc. *)
Definition eg_loc_mf := build_myfun eg_loc.
Definition eg_loc_ml := build_mylexpr eg_loc.

Example eg_loc_correct :
  eg_loc_mf / eg_loc_ml / [] / [] / [] |-aa eg_loc => [<{ [ fun Y *-> Y@2, 3, [] ] }>] / [].
Proof.
  eapply A_Appl.
  - apply A_Val.
  - reflexivity.
  - reflexivity.
  - rewrite <- app_nil_r.
    (* TODO: automate! *)
    replace [<{ [fun Y *-> Y @ 2, 3, []] }>] with ([<{ [fun Y *-> Y @ 2, 3, []] }>] ++ []) by reflexivity.
    eapply UA_cons.
    + eapply A_VarLocal.
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * simpl.
        replace [[4]] with ((4 :: [] ++ []) :: []) by reflexivity.
        rewrite <- app_nil_r.
        replace [<{ [fun Y *-> Y @ 2, 3, []] }>] with ([<{ [fun Y *-> Y @ 2, 3, []] }>] ++ []) by reflexivity.
        apply UVL_cons.
        -- apply A_Val.
        -- apply UVL_nil.
    + apply UA_nil.
Qed.
