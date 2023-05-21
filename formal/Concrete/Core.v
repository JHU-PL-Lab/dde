From DDE.Common Require Import Lang Tactics.

#[local] Open Scope lang_scope.

(* custom syntax for evaluation, mirroring the written syntax
   as much as possible. Uses ';' instead of ',' so notation doesn't
   clash with that of Ltac's match goal. *)
Reserved Notation
         "mf ; ml ; s |- e => r"
         (at level 40, e custom lang at level 99, r at next level,
          ml at next level, s at next level).

(* logic for DDE's concrete lambda calculus operational semantics *)
Inductive eval : myfun -> mylexpr -> sigma -> lexpr -> res -> Prop :=
  | E_Val : forall s v l mf ml,
    mf; ml; s |- ($v)@l => <v, l, s>
  (* TODO: forall sound? *)
  | E_Appl : forall e1 e2 l s r x e l1 s1 mf ml,
    mf; ml; s |- e1 => <fun x *-> e, l1, s1> ->
    mf; ml; l :: s |- e => r ->
    mf; ml; s |- (e1 <-* e2) @ l => r
  | E_VarLocal : forall x l s r mf ml e1 e2 l' e mf_l,
    ml l' = Some <{ (e1 <-* e2) @ l' }> ->
    mf l = Some mf_l ->
    ml mf_l = Some <{ ($fun x *-> e) @ mf_l }> ->
    mf; ml; s |- e2 => r ->
    mf; ml; (l' :: s) |- x@l => r
  | E_VarNonLocal : forall x l s r mf ml e1 e2 l2 e l1 x1 s1,
    mf l = Some l1 ->
    ml l1 = Some <{ ($fun x1 *-> e) @ l1 }> ->
    x <> x1 ->
    ml l2 = Some <{ (e1 <-* e2) @ l2 }> ->
    mf; ml; s |- e1 => <fun x1 *-> e, l1, s1> ->
    mf; ml; s1 |- x@l1 => r ->
    mf; ml; (l2 :: s) |- x@l => r

  where "mf ; ml ; s |- e => r" := (eval mf ml s e r).

Definition id_val := to_lexpr <{ $fun X -> X }>.
Definition id_val_mf := build_myfun id_val.
Definition id_val_ml := build_mylexpr id_val.

(* simple value *)
Example eg_val_correct :
  id_val_mf; id_val_ml; [] |- id_val => <fun X *-> X@0, 1, []>.
Proof.
  apply E_Val.
Qed.

Definition eg_loc := to_lexpr <{ $fun X -> X <- $fun Y -> Y }>.
Definition eg_loc_mf := build_myfun eg_loc.
Definition eg_loc_ml := build_mylexpr eg_loc.

(* local variable lookup *)
(* N.B. that I'm intentionally not using automation to the greatest extent
   so that the proof can be better traced to see what's happening. Proof
   scripts can be almost entirely automated in our logic. *)
Example eg_loc_correct :
  eg_loc_mf; eg_loc_ml; [] |- eg_loc => <fun Y *-> Y@2, 3, []>.
Proof.
  eapply E_Appl.
  - apply E_Val.
  - eapply E_VarLocal; try reflexivity.
    apply E_Val.
Qed.

Definition eg_noloc :=
  to_lexpr <{ ($fun X -> $fun Y -> X) <- $fun Z -> Z <- $fun M -> M }>.
Definition eg_noloc_mf := build_myfun eg_noloc.
Definition eg_noloc_ml := build_mylexpr eg_noloc.

(* non-local variable lookup *)
Example eg_noloc_correct :
  eg_noloc_mf; eg_noloc_ml; [] |- eg_noloc => <fun Z *-> Z@3, 4, []>.
Proof with try reflexivity.
  eapply E_Appl.
  - eapply E_Appl.
    + apply E_Val.
    + apply E_Val.
  - eapply E_VarNonLocal...
    + discriminate.
    (* N.B. that we re-do the application here, as expected from the rules *)
    + eapply E_Appl.
      * apply E_Val.
      * apply E_Val.
    + eapply E_VarLocal...
      * apply E_Val.
Qed.

(* bad non-local variable lookup *)
Example eg_noloc_bad :
  ~ eg_noloc_mf; eg_noloc_ml; [] |- eg_noloc => <fun M *-> M@6, 7, []>.
Proof.
  intro Contra. invert Contra.
  invert H6. invert H8. invert H9. invert H7.
  - (* E_VarLocal *) invert H5. invert H6. invert H9.
  - (* E_VarNonLocal *) invert H3. invert H4. invert H9.
    invert H11. invert H6. invert H7.
    invert H12.
    + (* E_VarLocal *) invert H5. invert H6. invert H9.
      inversion H10.
    + (* E_VarNonLocal *) invert H3. invert H4.
      contradiction.
Qed.

Theorem eval_deterministic : forall mf ml s e r1 r2,
  mf; ml; s |- e => r1 ->
  mf; ml; s |- e => r2 ->
  r1 = r2.
Proof.
  intros. generalize dependent r2.
  induction H; intros.
  - (* E_Val *) invert H0. reflexivity.
  - (* E_Appl *) invert H1.
    apply IHeval1 in H9. invert H9. subst.
    apply IHeval2 in H10. assumption.
  - (* E_VarLocal *) invert H3.
    + (* E_VarLocal *) inject_all.
      apply IHeval in H14. assumption.
    + (* E_VarNonLocal *) congruence.
  - (* E_VarNonLocal *) invert H5.
    + (* E_VarLocal *) congruence.
    + (* E_VarNonLocal *) inject_all.
      apply IHeval1 in H17. invert H17.
      apply IHeval2 in H18. assumption.
Qed.
