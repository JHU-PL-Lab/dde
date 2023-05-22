From DDE.Abstract Require Import Common.
From DDE.Common Require Import Tactics.

Definition V_state : Type := lexpr * sigma.
(* set of labeled expression + stack pairs to stub cycles *)
Definition V_set : Type := set V_state.
Definition empty_V : V_set := @empty_set V_state.

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
         "mf / ml / s / S / V / l' / e2 '|_V_|' S' => r2 + S2"
         (at level 40, S' at level 99, e2 custom lang at level 99,
          ml at next level, s at next level, S at next level, V at next level,
          l' at next level, r2 at next level).

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
    ls = (l :: s) ->
    ls_pruned = prune_sigma2 ls ->
    mf / ml / ls_pruned / (ls ~> S1) / ((e, ls_pruned) ~> V) |_A_| r1 => r2 + S2 ->
    mf / ml / s / S / V |-aa (e <-* e') @ l => r2 / S2
  | A_VarLocal : forall mf ml s0 S V x l r1 S1 l' s mf_l e e1 e2,
    s0 = (l' :: s) ->
    mf l = Some mf_l ->
    ml mf_l = Some <{ ($fun x *-> e) @ mf_l }> ->
    ml l' = Some <{ (e1 <-* e2) @ l' }> ->
    mf / ml / s / S / ((e, s0) ~> V) / l' / e2 |_V_| S => r1 + S1 ->
    mf / ml / s0 / S / V |-aa x@l => r1 / S1
  | A_VarNonLocal : forall mf ml l2 s S V x l r2 S2 mf_l x1 e e1 e2 r1 S1,
    mf l = Some mf_l ->
    ml mf_l = Some <{ ($fun x1 *-> e) @ mf_l }> ->
    x <> x1 ->
    ml l2 = Some <{ (e1 <-* e2) @ l2 }> ->
    mf / ml / s / S / V / l2 / e1 |_V_| S => r1 + S1 ->
    mf / ml / S1 / V / x / mf_l |_N_| r1 => r2 + S2 ->
    mf / ml / (l2 :: s) / S / V |-aa x@l => r2 / S2
(* TODO: add Stub rules *)

with union_appl
  : myfun -> mylexpr -> sigma -> S_set -> V_set -> disj -> disj -> S_set -> Prop
:=
  | UA_Nil : forall mf ml s S V, mf / ml / s / S / V |_A_| [] => [] + empty_S
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
    mf / ml / s / S / V / l' / e2 |_V_| empty_S => [] + empty_S
  (* skip current stack s'' if its top frame isn't l' *)
  | ST_Cons_Skip : forall mf ml s S V l' e2 S' r0s S0s s'',
    s'' ? S' ->
    (forall l'' s', s'' = l'' :: s' -> l'' <> l') ->
    (* go through the rest of the stacks *)
    mf / ml / s / S / V / l' / e2 |_V_| S' \ s'' => r0s + S0s ->
    mf / ml / s / S / V / l' / e2 |_V_| S' => r0s + S0s
  (* matching stack to execute and union with *)
  | ST_Cons : forall mf ml s S V l' e2 s'' S' r1 S1 s' r0 S0 r0s S0s,
    s'' ? S' ->
    (* a match! *)
    s'' = l' :: s ++ s' ->
    mf / ml / (s ++ s') / S / V |-aa e2 => r0 / S0 ->
    mf / ml / s / S / V / l' / e2 |_V_| S' \ s'' => r0s + S0s ->
    r1 = r0 ++ r0s ->
    S1 = S0 |_| S0s ->
    mf / ml / s / S / V / l' / e2 |_V_| S' => r1 + S1

with union_varnonlocal
  : myfun -> mylexpr -> S_set -> V_set -> expr -> nat -> disj -> disj -> S_set -> Prop
:=
  | UVN_Nil : forall mf ml S1 V x l1, mf / ml / S1 / V / x / l1 |_N_| [] => [] + empty_S
  (* go through every disjunct to union the result *)
  | UVN_Cons : forall mf ml S1 V x l1 x1 e s1 r1s r2 S2 r0' S0' r0's S0's,
    mf / ml / s1 / S1 / V |-aa x@l1 => r0' / S0' ->
    mf / ml / S1 / V / x / l1 |_N_| r1s => r0's + S0's ->
    r2 = r0' ++ r0's ->
    S2 = S0' |_| S0's ->
    (* checking l1 is sufficient because we never relabel functions *)
    mf / ml / S1 / V / x / l1 |_N_| <fun x1 *-> e, l1, s1> :: r1s => r2 + S2

  where "mf / ml / s / S / V '|-aa' e => rc / Sv" := (analyze mf ml s S V e rc Sv)
    and "mf / ml / s / S / V '|_A_|' r1 => r2 + S2" := (union_appl mf ml s S V r1 r2 S2)
    and "mf / ml / s / S / V / l' / e2 '|_V_|' S' => r2 + S2" := (union_stitch mf ml s S V l' e2 S' r2 S2)
    and "mf / ml / S / V / x / l1 '|_N_|' r1 => r2 + S2" := (union_varnonlocal mf ml S V x l1 r1 r2 S2).

Scheme analyze_mut := Induction for union_appl Sort Prop
with union_appl_mut := Induction for analyze Sort Prop.

(* Check analyze_ind. *)
(* Check union_appl_mut. *)

Ltac solve_analyze :=
  repeat match goal with
  | [|- _ / _ / _ / _ / _ |-aa (_ <-* _) @ _ => _ / _] => eapply A_Appl
  | [|- _ / _ / _ / _ / _ |-aa ($fun _ *-> _) @ _ => _ / _] => eapply A_Val
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
    | _ ++ _ => simpl; econstructor
    | [] => constructor
    end
  | [|- _ / _ / _ / _ / _ / ?l' / _ |_V_| ?S => _ + _] =>
    match S with
    | ?s ~> _ \ ?s => 
      let Contra := fresh "Contra" in
      let H := fresh "H" in
      rewrite <- Sub_Add_new by (intro Contra; invert Contra; invert H);
      solve_analyze
    (* TODO: implement decision procedure for union_stitch *)
    (* | ?s ~> _ =>
      match s with
      | l' :: _ => eapply ST_Cons
      | _ :: _ => eapply ST_Cons_Skip
      | [] => constructor
      end *)
    | empty_S => constructor
    end
  | [|- _ / _ / _ / _ / _ / _ |_N_| ?r1 => _ + _] =>
    match r1 with
    | _ :: _ => econstructor
    | _ ++ _ => simpl; econstructor
    | [] => constructor
    end
  | [|- _ ? _ ~> empty_S] => apply Union_intror; constructor
  | [|- context[_ |_| empty_S]] => simpl; rewrite Empty_set_zero_right
  | [H: _ ? empty_S |- _] => contradiction
  | [|- _ ? _ |_| empty_S ] =>
    apply Ensembles.Union_introl
  | [|- _ ? empty_S |_| _] =>
    apply Ensembles.Union_intror
  | [|- forall l'' s', _ = l'' :: s' -> l'' <> _] =>
    let H := fresh "H" in
    intros l'' s' H; invert H; intro; discriminate
  | [|- _ = _] => simpl; reflexivity
  | [|- _ <> _] => discriminate
  end.

(* simple function value *)
Definition eg_val := to_lexpr <{ $fun X -> X }>.
Definition eg_val_mf := build_myfun eg_val.
Definition eg_val_ml := build_mylexpr eg_val.

Example eg_val_correct :
  eg_val_mf / eg_val_ml / [] / empty_S / empty_V |-aa eg_val =>
    [<fun X *-> X@0, 1, []>] / empty_S.
Proof.
  apply A_Val.
Qed.

(* simple application involving local variable lookup *)
Definition eg_loc := to_lexpr <{ ($fun X -> X) <- ($fun Y -> Y) }>.
(* Compute eg_loc. *)
Definition eg_loc_mf := build_myfun eg_loc.
Definition eg_loc_ml := build_mylexpr eg_loc.
Definition eg_loc_S : S_set := Ensembles.Singleton sigma [4].

Example eg_loc_correct :
  eg_loc_mf / eg_loc_ml / [] / empty_S / empty_V |-aa eg_loc =>
    [<fun Y *-> Y@2, 3, []>] / eg_loc_S.
Proof.
  solve_analyze.
  eapply ST_Cons; solve_analyze.
  - auto with sets.
  - reflexivity.
Qed.

(* application involving non-local variable lookup *)
Definition eg_noloc :=
  to_lexpr <{ (($fun X -> $fun Y -> X)
                <- $fun Z -> Z)
                <- $fun N -> N }>.
(* Compute eg_noloc. *)
Definition eg_noloc_mf := build_myfun eg_noloc.
Definition eg_noloc_ml := build_mylexpr eg_noloc.
Definition eg_noloc_S := [8] ~> [5] ~> empty_S.

Example eg_noloc_correct :
  eg_noloc_mf / eg_noloc_ml / [] / empty_S / empty_V |-aa eg_noloc =>
    [<fun Z *-> Z@3, 4, []>] / eg_noloc_S.
Proof.
  solve_analyze.
  eapply ST_Cons; solve_analyze.
  - apply Union_intror. constructor.
  - solve_analyze.
    eapply ST_Cons_Skip; solve_analyze.
  - solve_analyze.
    (* deduplicate set *)
    rewrite Non_disjoint_union by auto with sets.
    eapply ST_Cons; solve_analyze.
    + auto with sets.
    + rewrite add_comm. solve_analyze.
      eapply ST_Cons_Skip; solve_analyze.
    + solve_analyze.
  - reflexivity.
Qed.

(* verbose version for stepping through *)
Example eg_noloc_correct' :
  eg_noloc_mf / eg_noloc_ml / [] / empty_S / empty_V |-aa eg_noloc =>
    [<fun Z *-> Z@3, 4, []>] / eg_noloc_S.
Proof.
  eapply A_Appl.
  - eapply A_Appl.
    + apply A_Val.
    + reflexivity.
    + reflexivity.
    + eapply UA_Cons; try rewrite Empty_set_zero_right.
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
        -- apply Union_intror. constructor.
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
        -- rewrite <- Sub_Add_new by (intro Contra; invert Contra; invert H).
           eapply ST_Cons_Skip.
           ++ apply Union_intror. constructor.
           ++ intros. invert H. intro. discriminate.
           ++ rewrite <- Sub_Add_new.
              ** apply ST_Nil.
              ** intro Contra. contradiction.
        -- reflexivity.
        -- simpl. repeat rewrite Empty_set_zero_right.
           rewrite Non_disjoint_union.
           ++ reflexivity.
           ++ apply Union_introl. apply Union_intror. constructor.
      * eapply UVN_Cons.
        -- eapply A_VarLocal.
           ++ reflexivity.
           ++ reflexivity.
           ++ reflexivity.
           ++ reflexivity.
           ++ eapply ST_Cons.
              ** apply Union_introl. apply Union_intror. constructor.
              ** reflexivity.
              ** apply A_Val.
              ** rewrite add_comm. rewrite <- Sub_Add_new.
                 eapply ST_Cons_Skip.
                 --- apply Union_intror. constructor.
                 --- intros. invert H. intro. discriminate.
                 --- rewrite <- Sub_Add_new.
                     +++ apply ST_Nil.
                     +++ intro Contra. contradiction.
                 --- intro Contra. invert Contra; invert H.
              ** simpl. reflexivity.
              ** rewrite Empty_set_zero_right. reflexivity.
        -- apply UVN_Nil.
        -- simpl. reflexivity.
        -- rewrite Empty_set_zero_right. reflexivity.
    + apply UA_Nil.
    + reflexivity.
    + rewrite Empty_set_zero_right. reflexivity.
Qed.

(* TODO: add examples to demonstrate ST_Cons_Skip *)
