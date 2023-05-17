From DDE.Abstract Require Import Common.

Definition v_set : Type := list (lexpr * sigma).

Definition disj : Type := list res.

#[local] Open Scope lang_scope.

Inductive Contains {A : Type} : list A -> list A -> Prop :=
  | Contains_nil : forall l2, Contains [] l2 
  | Contains_cons : forall x l1 l2,
    In x l2 ->
    Contains l1 l2 ->
    Contains (x :: l1) l2.

Reserved Notation
         "mf / ml / s / S / V '|-aa' e => rc / Sv"
         (at level 40, e custom lang at level 99, rc constr at next level,
          ml at next level, s at next level, S at next level, V at next level,
          Sv constr).

Section Analyze.

Variable analyze'
  : myfun -> mylexpr -> sigma -> s_set -> v_set -> lexpr -> disj -> s_set -> Prop.

Inductive analyze
  : myfun -> mylexpr -> sigma -> s_set -> v_set -> lexpr -> disj -> s_set -> Prop
:=
  | A_Id : forall mf ml s S V e rc Sv,
    analyze' mf ml s S V e rc Sv ->
    mf / ml / s / S / V |-aa e => rc / Sv
  | A_Val : forall mf ml s S V v l,
    mf / ml / s / S / V |-aa ($v)@l => [<{ [ v, l, s ] }>] / S
  | A_Appl : forall mf ml s S V e e' l r2 S2 r1 S1 l_app_s V_new,
    mf / ml / s / S / V |-aa e => r1 / S1 ->
    l_app_s = prune_sigma2 (l :: s) ->
    V_new = [(e, l_app_s)] ->
    (forall x1 e1 l1 s1 r0 S0,
      In <{ [ fun x1 *-> e1, l1, s1 ] }> r1 ->
      analyze' mf ml l_app_s ((l :: s) :: S1) (V ++ V_new) e1 r0 S0 ->
      Contains r0 r2 /\ Contains S0 S2) ->
    mf / ml / s / S / V |-aa (e <-* e') @ l => r2 / S2
  | A_VarLocal : forall mf ml s0 S V x l r1 S1 l' s mf_l e e1 e2 V_new,
    s0 = (l' :: s) ->
    mf l = Some mf_l ->
    ml mf_l = Some <{ ($fun x *-> e) @ mf_l }> ->
    ml l' = Some <{ (e1 <-* e2) @ l' }> ->
    V_new = [(e, s0)] ->
    (forall s' r0 S0,
      (*? /\ or ->: probably doesn't matter within a premise *)
      (exists s'', In s'' S /\ s'' = l' :: s ++ s') ->
      analyze' mf ml (s ++ s') S (V ++ V_new) e2 r0 S0 ->
      Contains r0 r1 /\ Contains S0 S1) ->
    mf / ml / s0 / S / V |-aa x@l => r1 / S1

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
  - intros.
    inversion H; inversion H1; subst; clear H; clear H1.
    apply A_Id in H0. inversion H0; subst; clear H0.
    + admit. (* gets stuck here *)
    + inversion H2. subst. clear H2.
      inversion H3. subst. clear H3.
      inversion H4. subst. clear H4.
      inversion H5. subst. clear H5.
Abort.

End Analyze.
