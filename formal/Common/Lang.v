From Coq Require Export Lists.List.
Export ListNotations.
From DDE Require Export Maps.

(* slightly adjusted grammar to more easily define notations *)
Inductive expr : Type :=
  | Appl: expr -> expr -> expr
  | LAppl: lexpr -> lexpr -> expr
  | Val: val -> expr
  | Ident: string -> expr
with val : Type :=
  | Fun : string -> expr -> val
  | LFun : string -> lexpr -> val
with lexpr : Type := Lexpr : expr -> nat -> lexpr.

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
Notation "'fun' x '*->' le" :=
  (LFun x le)
    (in custom lang at level 20, le at next level, no associativity) : lang_scope.
Notation "e1 <- e2" :=
  (Appl e1 e2)
    (in custom lang at level 30, left associativity).
Notation "le1 '<-*' le2" :=
  (LAppl le1 le2)
    (* associativity doesn't matter here as le1 and le2 are lexprs *)
    (in custom lang at level 30, no associativity).
Notation "$ v" :=
  (Val v)
    (in custom lang at level 25) : lang_scope.
Notation "e @ l" :=
  (Lexpr e l)
    (in custom lang at level 15) : lang_scope.

Notation "< v , l , s >" :=
  (Res v l s)
    (at level 39, v custom lang at level 99,
      l at next level, s at next level) : lang_scope.

#[local] Open Scope lang_scope.

Definition X : string := "x".
Definition Y : string := "y".
Definition Z : string := "z".
Definition M : string := "m".
Definition N : string := "n".

(* assign a label to each expr, turning it into an lexpr. *)
Fixpoint assn (e : expr) (l : nat) : lexpr * nat :=
  match e with
  | <{ e1 <- e2 }> =>
    let (le1, l1) := assn e1 l in
    let (le2, l2) := assn e2 l1 in
    (<{ (le1 <-* le2) @ l2 }>, S l2)
  | <{ le1 <-* le2 }> => (le1, l) (* unreachable *)
  | <{ $v }> =>
    match v with
    | <{ fun x -> e' }> =>
      let (le', l') := assn e' l in
      (<{ ($fun x *-> le') @ l' }>, S l')
    | <{ fun _ *-> le' }> => (le', l) (* unreachable *)
    end
  | Ident _ => (<{ e @ l }>, S l)
  end.

(* assn will in practice only be used on expr's with no lexpr subcomponents *)
Inductive assn_prac : expr -> nat -> nat -> Prop :=
  | AP_Ident : forall x l,
    assn_prac (Ident x) l (S l)
  | AP_Appl : forall e1 e2 l l1' l2',
    assn_prac e1 l l1' ->
    assn_prac e2 l1' l2' ->
    assn_prac <{ e1 <- e2 }> l (S l2')
  | AP_Val : forall v l l' x e',
    v = <{ fun x -> e' }> ->
    assn_prac e' l l' ->
    assn_prac <{ $v }> l (S l').

(* for all possible realistic use cases, assn is sound in terms of
  correctly assigning labels *)
Theorem assn_sound : forall e l l',
  assn_prac e l l' ->
  l' = snd (assn e l).
Proof.
  intros. induction H.
  - reflexivity.
  - simpl.
    destruct (assn e1 l).
    simpl in IHassn_prac1. rewrite IHassn_prac1 in IHassn_prac2.
    destruct (assn e2 n).
    subst. reflexivity.
  - rewrite H. simpl.
    destruct (assn e' l).
    subst. reflexivity.
Qed.

Definition to_lexpr (e : expr) : lexpr := fst (assn e 0).

Example sample_fun := to_lexpr <{ $fun X -> X }>.
Example sample_fun' := to_lexpr <{ $fun X -> $fun Y -> X }>.
(* Compute sample_fun'. *)
Example sample_fun'' := to_lexpr <{ $fun X -> (X <- X) }>.
(* Compute sample_fun''. *)
Example sample_appl := to_lexpr <{ ($fun X -> X) <- ($fun X -> X) }>.
Example sample_appl' := to_lexpr <{ X <- X }>.
(* Compute sample_appl'. *)
Example sample_res := < fun X *-> X@0, 1, (2 :: []) >.

Definition myfun : Type := partial_map nat nat.
Definition mylexpr : Type := partial_map nat lexpr.

(* build mapping from label to label of enclosing function given a root lexpr *)
Definition build_myfun (le : lexpr) : myfun :=
  (fix aux (le : lexpr) (mf_l : option nat) (mf : myfun) : myfun :=
    match le with
    | <{ e @ l }> =>
      match e with
      | <{ $v }> =>
        match v with
        | <{ fun _ *-> le' }> => aux le' (Some l) (l !-> mf_l; mf)
        | <{ fun _ -> _ }> => mf (* unreachable *)
        end
      | Ident _ => (l !-> mf_l; mf)
      | <{ le1 <-* le2 }> => aux le2 mf_l (aux le1 mf_l mf)
      | <{ _ <- _ }> => mf (* unreachable *)
      end
    end) le None empty.

(* Compute build_myfun (to_lexpr <{ $fun X -> X }>) None empty. *)

(* build mapping from label to lexpr given a root lexpr *)
Definition build_mylexpr (le : lexpr) : mylexpr :=
  (fix aux (le : lexpr) (ml : mylexpr) : mylexpr :=
  match le with
  | <{ e @ l }> =>
    match e with
    | <{ $v }> =>
      match v with
      | <{ fun _ *-> le' }> => (l |-> le; aux le' ml)
      | <{ fun _ -> _ }> => ml (* unreachable *)
      end
    | Ident _ => (l |-> le; ml)
    | <{ le1 <-* le2 }> => (l |-> le; aux le2 (aux le1 ml))
    | <{ _ <- _ }> => ml (* unreachable *)
    end
  end) le empty.

(* Compute build_mylexpr (to_lexpr <{ $fun X -> X }>) empty. *)

(* TODO: prove properties of above functions,
  like number of labels must be number of expr's,
  and size of mylexpr must be number of lexpr's *)

#[export] Hint Unfold build_myfun build_mylexpr update t_update : core.
