Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String Lists.List Arith.Arith.
Import ListNotations.
From DDE Require Import Maps.

(* slightly adjusted grammar to more easily define notations *)
Inductive expr : Type :=
  | Appl: lexpr -> lexpr -> expr
  | Val: val -> expr
  | Ident: string -> expr
with lexpr : Type := Lexpr : expr -> nat -> lexpr
with val : Type := Fun : string -> lexpr -> val.

Definition sigma : Type := list nat.

Inductive res : Type := Res : val -> nat -> sigma -> res.

(* coerce strings into exprs via the Ident constructor *)
Coercion Ident : string >-> expr.

Declare Custom Entry lang.
Declare Scope lang_scope.

(* custom language syntax *)
Notation "<{ e }>" := e (at level 0, e custom lang at level 99) : lang_scope.
Notation "( x )" := x (in custom lang at level 0, x at level 99) : lang_scope.
Notation "x" := x (in custom lang at level 0, x constr at level 0) : lang_scope.
Notation "'fun' x -> e" :=
  (Fun x e)
    (in custom lang at level 20, e at next level, right associativity) : lang_scope.
Notation "e1 <- e2" :=
  (Appl e1 e2)
    (* associativity doesn't matter here as e1 and e2 are lexprs *)
    (in custom lang at level 30, left associativity).
Notation "$ v" :=
  (Val v)
    (in custom lang at level 25) : lang_scope.
Notation "e @ l" :=
  (Lexpr e l)
    (in custom lang at level 15) : lang_scope.
Notation "[ v , l , s ]" :=
  (Res v l s)
    (in custom lang at level 99, v at next level, l at next level, s constr) : lang_scope.

Open Scope lang_scope.

Definition X : string := "x".
Definition Y : string := "y".
Definition Z : string := "z".
Definition M : string := "m".
Definition N : string := "n".

Example sample_ident := <{ X@0 }>.
Example sample_fun := <{ fun X -> X@0 }>.
Example sample_fun_lexpr := <{ ($fun X -> X@0) @ 1 }>.
Example sample_fun_lexpr' := <{ ($fun X -> ($fun Y -> X@0) @ 1) @ 2 }>.
Example sample_appl := <{ (X@0 <- X@1) @ 2}>.
Example sample_res := <{ [ fun X -> X@0, 1, 0 :: [] ] }>.

(* TODO: auto-generate labels *)

Definition myfun : Type := partial_map nat nat.
Definition mylexpr : Type := partial_map nat lexpr.

(* build mapping from label to label of enclosing function given a root lexpr *)
Fixpoint build_myfun (le : lexpr) (mf_l : option nat) (mf : myfun) : myfun :=
  match le with
  | <{ e @ l }> =>
    match e with
    | Val v =>
      match v with
      | <{ fun _ -> e' }> => build_myfun e' (Some l) (l !-> mf_l; mf)
      end
    | Ident _ => (l !-> mf_l; mf)
    | <{ e1 <- e2 }> => build_myfun e2 mf_l (build_myfun e1 mf_l mf)
    end
  end.

(* Compute build_myfun <{ (fun X -> X@1 ) @@ 2 }> None empty. *)

(* build mapping from label to lexpr given a root lexpr *)
Fixpoint build_mylexpr (le : lexpr) (ml : mylexpr) : mylexpr :=
  match le with
  | <{ e @ l }> =>
    match e with
    | Val v =>
      match v with
      | <{ fun _ -> e' }> => (l |-> le; build_mylexpr e' ml)
      end
    | Ident _ => (l |-> le; ml)
    | <{ e1 <- e2 }> => (l |-> le; build_mylexpr e2 (build_mylexpr e1 ml))
    end
  end.

(* Compute build_mylexpr <{ (fun X -> X@1 ) @@ 2 }> empty. *)

(* custom syntax for evaluation, mirroring the written syntax
   as much as possible. Uses '/' instead of ',' so notation doesn't
   clash with that of Ltac's match goal. *)
Reserved Notation
         "mf / ml / s |- e => r"
         (at level 40, e custom lang at level 99, r custom lang at level 99,
          ml at next level, s at next level).

(* logic for DDE's concrete lambda calculus operational semantics *)
Inductive eval : lexpr -> sigma -> res -> myfun -> mylexpr -> Prop :=
  | E_Val : forall s v l mf ml,
    mf / ml / s |- ($v)@l => [ v, l, s ]
  (* TODO: forall sound? *)
  | E_Appl : forall e1 e2 l s r x e l1 s1 mf ml,
    mf / ml / s |- e1 => [ fun x -> e, l1, s1 ] ->
    mf / ml / l :: s |- e => r ->
    mf / ml / s |- (e1 <- e2) @ l => r
  | E_VarLocal : forall x l s r mf ml e1 e2 l' e mf_l,
    ml l' = Some <{ (e1 <- e2) @ l' }> ->
    mf l = Some mf_l ->
    ml mf_l = Some <{ ($fun x -> e) @ mf_l }> ->
    mf / ml / s |- e2 => r ->
    mf / ml / (l' :: s) |- x@l => r
  | E_VarNonLocal : forall x l s r mf ml e1 e2 l2 e l1 x1 s1,
    mf l = Some l1 ->
    ml l1 = Some <{ ($fun x1 -> e) @ l1 }> ->
    x <> x1 ->
    ml l2 = Some <{ (e1 <- e2) @ l2 }> ->
    mf / ml / s |- e1 => [ fun x1 -> e, l1, s1 ] ->
    mf / ml / s1 |- x@l1 => r ->
    (* TODO: inline premises *)
    mf / ml / (l2 :: s) |- x@l => r

  where "mf / ml / s |- e => r" := (eval e s r mf ml).

Hint Unfold build_myfun build_mylexpr update t_update : core.

Definition id_val :=
  <{ ($fun X -> X@0) @ 1 }>.
Definition id_val_mf :=
  build_myfun id_val None empty.
Definition id_val_ml :=
  build_mylexpr id_val empty.

(* simple value *)
Example eg_val_correct :
  id_val_mf / id_val_ml / [] |- id_val => [ fun X -> X@0, 1, [] ].
Proof.
  apply E_Val.
Qed.

Definition eg_loc :=
  <{ (($fun X -> X@0) @ 1 <- ($fun Y -> Y@2) @ 3) @ 4 }>.
Definition eg_loc_mf :=
  build_myfun eg_loc None empty.
Definition eg_loc_ml :=
  build_mylexpr eg_loc empty.

(* local variable lookup *)
(* N.B. that I'm intentionally not using automation to the greatest extent
   so that the proof can be better traced to see what's happening. Proof
   scripts can be almost entirely automated in our logic. *)
Example eg_loc_correct :
  eg_loc_mf / eg_loc_ml / [] |- eg_loc => [ fun Y -> Y@2, 3, [] ].
Proof.
  eapply E_Appl.
  - apply E_Val.
  - eapply E_VarLocal.
    + unfold eg_loc_ml, eg_loc. autounfold. reflexivity.
    + unfold eg_loc_mf, eg_loc. autounfold. reflexivity.
    + unfold eg_loc_ml, eg_loc. autounfold. reflexivity.
    + apply E_Val.
Qed.

Definition eg_noloc :=
  <{ ((($fun X -> ($fun Y -> X@0) @ 1) @ 2
      <- ($fun Z -> Z@3) @ 4) @ 5
      <- ($fun M -> M@6) @ 7) @ 8 }>.
Definition eg_noloc_mf :=
  build_myfun eg_noloc None empty.
Definition eg_noloc_ml :=
  build_mylexpr eg_noloc empty.

(* non-local variable lookup *)
Example eg_noloc_correct :
  eg_noloc_mf / eg_noloc_ml / [] |- eg_noloc => [ fun Z -> Z@3, 4, [] ].
Proof.
  eapply E_Appl.
  - eapply E_Appl.
    + apply E_Val.
    + apply E_Val.
  - eapply E_VarNonLocal.
    + reflexivity.
    + reflexivity.
    + discriminate.
    + reflexivity.
    (* N.B. that we re-do the application here, as expected from the rules *)
    + eapply E_Appl.
      * apply E_Val.
      * apply E_Val.
    + eapply E_VarLocal.
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * apply E_Val.
Qed.

Ltac map_lookup mymap prog :=
  match goal with
    H : mymap _ = _
    |- _ => unfold mymap, prog in H; autounfold in H; simpl in H;
            injection H as H; subst
  end.

(* bad non-local variable lookup *)
Example eg_noloc_bad :
  ~ eg_noloc_mf / eg_noloc_ml / [] |- eg_noloc => [ fun M -> M@6, 7, [] ].
Proof.
  intro contra.
  inversion contra. subst. clear contra.
  inversion H6. subst. clear H6.
  inversion H8. subst. clear H8.
  inversion H9. subst. clear H9.
  inversion H7; subst; clear H7.
  (* E_VarLocal *)
  - map_lookup eg_noloc_mf eg_noloc.
    map_lookup eg_noloc_ml eg_noloc.
    discriminate H9.
  (* E_VarNonLocal *)
  - map_lookup eg_noloc_ml eg_noloc.
    map_lookup eg_noloc_mf eg_noloc.
    map_lookup eg_noloc_ml eg_noloc.
    inversion H11. subst. clear H11.
    inversion H7. subst. clear H7.
    inversion H8. subst. clear H8.
    inversion H12; subst; clear H12.
    (* E_VarLocal *)
    + map_lookup eg_noloc_ml eg_noloc.
      map_lookup eg_noloc_mf eg_noloc.
      map_lookup eg_noloc_ml eg_noloc.
      inversion H10.
    (* E_VarNonLocal *)
    + map_lookup eg_noloc_ml eg_noloc.
      map_lookup eg_noloc_mf eg_noloc.
      map_lookup eg_noloc_ml eg_noloc.
      contradiction.
Qed.

Ltac injection_subst :=
  match goal with
    H1 : ?E = _,
    H2 : ?E = _
    |- _ => rewrite H1 in H2; injection H2 as H2; subst; clear H1
  end.

Theorem eval_deterministic : forall mf ml s e r1 r2,
  mf / ml / s |- e => r1 ->
  mf / ml / s |- e => r2 ->
  r1 = r2.
Proof.
  intros. generalize dependent r2. induction H; intros.
  (* E_Val *)
  - inversion H0. subst. reflexivity.
  (* E_Appl *)
  - inversion H1. subst. clear H1.
    apply IHeval1 in H9. injection H9 as H9. subst.
    apply IHeval2 in H10. assumption.
  (* E_VarLocal *)
  - inversion H3; subst; clear H3.
    (* E_VarLocal *)
    + repeat injection_subst. clear H2.
      apply IHeval in H14. assumption.
    (* E_VarNonLocal *)
    + congruence.
  (* E_VarNonLocal *)
  - inversion H5; subst; clear H5.
    (* E_VarLocal *)
    + congruence.
    (* E_VarNonLocal *)
    + repeat injection_subst.
      clear H3. clear H4.
      apply IHeval1 in H17. injection H17 as H17. subst.
      apply IHeval2 in H18. assumption.
Qed.

Close Scope lang_scope.
