From DDE.Abstract Require Import Common.
From DDE.Common Require Import Tactics.

Definition V_state : Type := lexpr * sigma.
(* a set of labeled expression + stack pairs to stub cycles *)
Definition V_set : Type := list V_state.
(* N.B. that we don't deduplicate V as we do for S because
  membership in V is sufficient for stubbing *)

(* a disjunction of possible analysis results *)
Definition disj : Type := list res.

#[local] Open Scope lang_scope.

Reserved Notation
         "mf / ml / s / S / V '|-aa' e => rc / Sv"
         (at level 40, e custom lang at level 99, rc at next level,
          ml at next level, s at next level, S at next level, V at next level).
          
(* union operation seen in Application *)
Reserved Notation
         "mf / ml / s / S / V '|_A_|' r1 => r2 + S2"
         (at level 40, r1 at level 99,
          ml at next level, s at next level, S at next level, V at next level,
          r2 at next level).

(* stack stitching union operation *)
Reserved Notation
         "mf / ml / S / V / l' / s / e2 '|_S_|' S' => r2 + S2"
         (at level 40, S' at level 99, e2 custom lang at level 99,
          ml at next level, S at next level, V at next level,
          l' at next level, s at next level, r2 at next level).

(* union operation seen in Var Non-Local *)
Reserved Notation
         "mf / ml / S / V / x / l1 '|_N_|' r1 => r2 + S2"
         (at level 40, r1 at level 99,
          ml at next level, S at next level, V at next level,
          x at next level, l1 at next level,
          r2 at next level).

Inductive analyze
  : myfun -> mylexpr -> sigma -> S_set -> V_set -> lexpr -> disj -> S_set -> Prop
:=
  | A_Val : forall mf ml s S V v l,
    mf / ml / s / S / V |-aa ($v)@l => [<v, l, s>] / S
  | A_Appl : forall mf ml s S V e e' l r2 S2 r1 S1 ls ls_pruned,
    mf / ml / s / S / V |-aa e => r1 / S1 ->
    ls = l :: s ->
    ls_pruned = prune_sigma2 ls ->
    mf / ml / ls_pruned / (ls ~> S1) / ((e, ls_pruned) :: V) |_A_| r1 => r2 + S2 ->
    mf / ml / s / S / V |-aa (e <-* e') @ l => r2 / S2
  | A_VarLocal : forall mf ml s0 S V x l r1 S1 l' s mf_l e e1 e2,
    s0 = l' :: s ->
    mf l = Some mf_l ->
    ml mf_l = Some <{ ($fun x *-> e) @ mf_l }> ->
    ml l' = Some <{ (e1 <-* e2) @ l' }> ->
    mf / ml / S / ((e, s0) :: V) / l' / s / e2 |_S_| S => r1 + S1 ->
    mf / ml / s0 / S / V |-aa x@l => r1 / S1
  | A_VarNonLocal : forall mf ml l2 s S V x l r2 S2 mf_l x1 e e1 e2 r1 S1,
    mf l = Some mf_l ->
    ml mf_l = Some <{ ($fun x1 *-> e) @ mf_l }> ->
    x <> x1 ->
    ml l2 = Some <{ (e1 <-* e2) @ l2 }> ->
    mf / ml / S / V / l2 / s / e1 |_S_| S => r1 + S1 ->
    mf / ml / S1 / V / x / mf_l |_N_| r1 => r2 + S2 ->
    mf / ml / (l2 :: s) / S / V |-aa x@l => r2 / S2
(* TODO: add Stub rules *)

with union_appl
  : myfun -> mylexpr -> sigma -> S_set -> V_set -> disj -> disj -> S_set -> Prop
:=
  | UA_Nil : forall mf ml s S V, mf / ml / s / S / V |_A_| [] => [] + []
  (* go through every disjunct to union the result *)
  | UA_Cons : forall mf ml s S V x1 e1 l1 s1 r1s r2 S2 r0 S0 r0s S0s,
    mf / ml / s / S / V |-aa e1 => r0 / S0 ->
    mf / ml / s / S / V |_A_| r1s => r0s + S0s ->
    r2 = r0 ++ r0s ->
    S2 = S0 |_| S0s ->
    mf / ml / s / S / V |_A_| <fun x1 *-> e1, l1, s1> :: r1s => r2 + S2

with union_stitch
  : myfun -> mylexpr -> sigma -> S_set -> V_set -> nat -> lexpr -> S_set -> disj -> S_set -> Prop
:=
  | ST_Nil : forall mf ml s S V e2 l',
    mf / ml / S / V / l' / s / e2 |_S_| [] => [] + []
  (* skip current stack s'' if its top frame isn't l' *)
  | ST_Cons_Skip : forall mf ml s S V l' e2 s'' S' r0s S0s,
    (forall l'' s', s'' = l'' :: s' -> l'' <> l') ->
    (* go through the rest of the stacks *)
    mf / ml / S / V / l' / s / e2 |_S_| S' => r0s + S0s ->
    mf / ml / S / V / l' / s / e2 |_S_| s'' :: S' => r0s + S0s
  (* matching stack to execute and union with *)
  | ST_Cons : forall mf ml s S V l' e2 s'' S' r1 S1 s' r0 S0 r0s S0s,
    (* a match! *)
    s'' = l' :: s ++ s' ->
    mf / ml / (s ++ s') / S / V |-aa e2 => r0 / S0 ->
    mf / ml / S / V / l' / s / e2 |_S_| S' => r0s + S0s ->
    r1 = r0 ++ r0s ->
    S1 = S0 |_| S0s ->
    mf / ml / S / V / l' / s / e2 |_S_| s'' :: S' => r1 + S1

with union_varnonlocal
  : myfun -> mylexpr -> S_set -> V_set -> expr -> nat -> disj -> disj -> S_set -> Prop
:=
  | UVN_Nil : forall mf ml S1 V x l1, mf / ml / S1 / V / x / l1 |_N_| [] => [] + []
  (* go through every disjunct to union the result *)
  | UVN_Cons : forall mf ml S1 V x l1 x1 e s1 r1s r2 S2 r0' S0' r0's S0's,
    mf / ml / s1 / S1 / V |-aa x@l1 => r0' / S0' ->
    mf / ml / S1 / V / x / l1 |_N_| r1s => r0's + S0's ->
    r2 = r0' ++ r0's ->
    S2 = S0' |_| S0's ->
    (* checking l1 is sufficient because we never relabel functions *)
    mf / ml / S1 / V / x / l1 |_N_| <fun x1 *-> e, l1, s1> :: r1s => r2 + S2

  where "mf / ml / s / S / V '|-aa' e => rc / Sv" :=
      (analyze mf ml s S V e rc Sv)
    and "mf / ml / s / S / V '|_A_|' r1 => r2 + S2" :=
      (union_appl mf ml s S V r1 r2 S2)
    and "mf / ml / S / V / l' / s / e2 '|_S_|' S' => r2 + S2" :=
      (union_stitch mf ml s S V l' e2 S' r2 S2)
    and "mf / ml / S / V / x / l1 '|_N_|' r1 => r2 + S2" :=
      (union_varnonlocal mf ml S V x l1 r1 r2 S2).

Scheme analyze_union_appl := Induction for union_appl Sort Prop
  with union_appl_analyze := Induction for analyze Sort Prop.

Scheme analyze_union_stitch := Induction for union_stitch Sort Prop
  with union_stitch_analyze := Induction for analyze Sort Prop.

Scheme analyze_union_varnonlocal := Induction for union_varnonlocal Sort Prop
with union_varnonlocal_analyze := Induction for analyze Sort Prop.

(* Check analyze_ind. *)
(* Check union_appl_analyze. *)

Fixpoint starts_with {A : Type} {eqb_A : Eqb A} (ls1 ls2 : list A) : bool :=
  match ls1, ls2 with
  | _, [] => true
  | [], _ => false
  | h1 :: t1, h2 :: t2 => (eqb h1 h2 && starts_with t1 t2)%bool
  end.

(* full automation *)
Ltac solve_analyze :=
  repeat match goal with
  | [|- context[_ ~> _]] => unfold prune_sigma2, "~>"; simpl

  | [|- _ / _ / _ / _ / _ |-aa (_ <-* _) @ _ => _ / _] => econstructor
  | [|- _ / _ / _ / _ / _ |-aa ($fun _ *-> _) @ _ => _ / _] => constructor
  | [|- analyze ?mf ?ml _ _ _ (Lexpr (Ident ?x) ?l) _ _] =>
    (* e.g., evaluate X to "x" *)
    let x := eval cbv in x in
    (* execute function *)
    match eval cbv in (mf l) with
    | Some ?mf_l =>
      match eval cbv in (ml mf_l) with
      | Some <{ ($fun x *-> _) @ _}> => eapply A_VarLocal
      | Some <{ ($fun _ *-> _) @ _}> => eapply A_VarNonLocal
      | _ => idtac
      end
    | _ => idtac
    end
  | [|- _ / _ / _ / _ / _ |-aa ?eg => _ / _] =>
    unfold eg, to_lexpr; simpl
  | [|- _ / _ / _ / _ / _ |_A_| ?r1 => _ + _] =>
    match r1 with
    | _ :: _ => econstructor
    | [] => constructor
    end
  | [|- _ / _ / _ / _ / ?l' / ?s / _ |_S_| ?S => _ + _] =>
    match S with
    | ?s'' :: _ =>
      match s'' with
      | l' :: ?s' =>
        tryif
          match eval cbv in (starts_with s' s)
            with true => idtac | false => fail
          end
        then eapply ST_Cons
        else eapply ST_Cons_Skip
      | _ :: _ => apply ST_Cons_Skip
      | [] => idtac "unreachable"
      end
    | [] => constructor
    end
  | [|- _ / _ / _ / _ / _ / _ |_N_| ?r1 => _ + _] =>
    match r1 with
    | _ :: _ => econstructor
    | [] => constructor
    end

  | [|- forall l'' s', _ = l'' :: s' -> l'' <> _] =>
    let H := fresh "H" in
    intros l'' s' H; invert H; intro; discriminate
  | [|- _ = _] => simpl; reflexivity
  | [|- _ <> _] => discriminate
  end.

(* Example eg : [1] = 1 :: [] ++ [].
Proof. *)

(* simple function value *)
Definition eg_val := to_lexpr <{ $fun X -> X }>.
Definition eg_val_mf := build_myfun eg_val.
Definition eg_val_ml := build_mylexpr eg_val.

Example eg_val_correct :
  eg_val_mf / eg_val_ml / [] / [] / [] |-aa eg_val => [<fun X *-> X@0, 1, []>] / [].
Proof.
  apply A_Val.
Qed.

(* simple application involving local variable lookup *)
Definition eg_loc := to_lexpr <{ ($fun X -> X) <- ($fun Y -> Y) }>.
(* Compute eg_loc. *)
Definition eg_loc_mf := build_myfun eg_loc.
Definition eg_loc_ml := build_mylexpr eg_loc.

Example eg_loc_correct :
  eg_loc_mf / eg_loc_ml / [] / [] / [] |-aa eg_loc => [<fun Y *-> Y@2, 3, []>] / [[4]].
Proof.
  solve_analyze.
Qed.

(* application involving non-local variable lookup *)
Definition eg_noloc1 :=
  to_lexpr <{ (($fun X -> $fun Y -> X)
                <- $fun Z -> Z)
                <- $fun N -> N }>.
(* Compute eg_noloc1. *)
Definition eg_noloc1_mf := build_myfun eg_noloc1.
Definition eg_noloc1_ml := build_mylexpr eg_noloc1.

Example eg_noloc1_correct :
  eg_noloc1_mf / eg_noloc1_ml / [] / [] / [] |-aa eg_noloc1 =>
    [<fun Z *-> Z@3, 4, []>] / [[8]; [5]].
Proof.
  solve_analyze.
Qed.

(* verbose version for stepping through *)
Example eg_noloc1_correct' :
  eg_noloc1_mf / eg_noloc1_ml / [] / [] / [] |-aa eg_noloc1 =>
    [<fun Z *-> Z@3, 4, []>] / [[8]; [5]].
Proof.
  eapply A_Appl.
  - eapply A_Appl.
    + apply A_Val.
    + reflexivity.
    + reflexivity.
    + eapply UA_Cons.
      * apply A_Val.
      * apply UA_Nil.
      * reflexivity.
      * reflexivity.
  - reflexivity.
  - reflexivity.
  - eapply UA_Cons.
    + eapply A_VarNonLocal.
      * reflexivity.
      * reflexivity.
      * discriminate.
      * reflexivity.
      * eapply ST_Cons.
        -- reflexivity.
        -- eapply A_Appl.
           ++ apply A_Val.
           ++ reflexivity.
           ++ reflexivity.
           ++ eapply UA_Cons.
              ** apply A_Val.
              ** apply UA_Nil.
              ** reflexivity.
              ** reflexivity.
        -- eapply ST_Cons_Skip.
           ++ intros. invert H. intro. discriminate.
           ++ apply ST_Nil.
        -- reflexivity.
        -- reflexivity.
      * simpl. eapply UVN_Cons.
        -- eapply A_VarLocal.
           ++ reflexivity.
           ++ reflexivity.
           ++ reflexivity.
           ++ reflexivity.
           ++ eapply ST_Cons_Skip.
              ** intros. invert H. intro. discriminate.
              ** eapply ST_Cons.
                --- reflexivity.
                --- apply A_Val.
                --- apply ST_Nil.
                --- reflexivity.
                --- reflexivity.
        -- apply UVN_Nil.
        -- simpl. reflexivity.
        -- simpl. reflexivity.
    + apply UA_Nil.
    + reflexivity.
    + reflexivity.
Qed.

Definition eg_noloc2 :=
  to_lexpr <{ ($fun X -> (($fun Y -> Y) <- X)) <- $fun Z -> Z }>.
(* Compute eg_noloc2. *)
Definition eg_noloc2_mf := build_myfun eg_noloc2.
Definition eg_noloc2_ml := build_mylexpr eg_noloc2.

Example eg_noloc2_correct :
  eg_noloc2_mf / eg_noloc2_ml / [] / [] / [] |-aa eg_noloc2 =>
    [<fun Z *-> Z@5, 6, []>] / [[3; 7]; [7]].
Proof.
  solve_analyze.
Qed.

Theorem deterministic : forall mf ml s S V e r1 S1 r2 S2,
  mf / ml / s / S / V |-aa e => r1 / S1 ->
  mf / ml / s / S / V |-aa e => r2 / S2 ->
  r1 = r2.
Proof.
  intros.
  generalize dependent r2.
  generalize dependent S2.
  induction H; intros.
  - invert H0. reflexivity.
  - subst. invert H3.
    apply IHanalyze in H5. subst.
    invert H2.
    + invert H15. reflexivity.
    + invert H15.
Abort.
