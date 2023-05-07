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
    (in custom lang at level 20, le at next level, right associativity) : lang_scope.
Notation "e1 <- e2" :=
  (Appl e1 e2)
    (in custom lang at level 30, left associativity).
Notation "le1 '<-*' le2" :=
  (LAppl le1 le2)
    (* associativity doesn't matter here as le1 and le2 are lexprs *)
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

#[local] Open Scope lang_scope.

Definition X : string := "x".
Definition Y : string := "y".
Definition Z : string := "z".
Definition M : string := "m".
Definition N : string := "n".

(* assign a label to each expr, turning it into an lexpr. *)
Fixpoint assign_labels (e : expr) (l : nat) : lexpr * nat :=
  match e with
  | <{ e1 <- e2 }> =>
    let (le1, l1) := assign_labels e1 l in
    let (le2, l2) := assign_labels e2 l1 in
    (<{ (le1 <-* le2) @ l2 }>, S l2)
  | <{ le1 <-* le2 }> => (le1, l) (* unreachable *)
  | <{ $v }> =>
    match v with
    | <{ fun x -> e' }> =>
      let (le', l') := assign_labels e' l in
      (<{ ($fun x *-> le') @ l' }>, S l')
    | <{ fun _ *-> le' }> => (le', l) (* unreachable *)
    end
  | Ident _ => (<{ e @ l }>, S l)
  end.

Definition to_lexpr (e : expr) := fst (assign_labels e 0).

Example sample_fun := to_lexpr <{ $fun X -> X }>.
Example sample_fun' := to_lexpr <{ $fun X -> $fun Y -> X }>.
(* Compute sample_fun'. *)
Example sample_fun'' := to_lexpr <{ $fun X -> (X <- X) }>.
(* Compute sample_fun''. *)
Example sample_appl := to_lexpr <{ ($fun X -> X) <- ($fun X -> X) }>.
Example sample_appl' := to_lexpr <{ X <- X }>.
(* Compute sample_appl'. *)
Example sample_res := <{ [ fun X *-> X@0, 1, 2 :: [] ] }>.

Definition myfun : Type := partial_map nat nat.
Definition mylexpr : Type := partial_map nat lexpr.

(* build mapping from label to label of enclosing function given a root lexpr *)
Fixpoint build_myfun (le : lexpr) (mf_l : option nat) (mf : myfun) : myfun :=
  match le with
  | <{ e @ l }> =>
    match e with
    | <{ $v }> =>
      match v with
      | <{ fun _ *-> le' }> => build_myfun le' (Some l) (l !-> mf_l; mf)
      | <{ fun _ -> _ }> => mf (* unreachable *)
      end
    | Ident _ => (l !-> mf_l; mf)
    | <{ le1 <-* le2 }> => build_myfun le2 mf_l (build_myfun le1 mf_l mf)
    | <{ _ <- _ }> => mf (* unreachable *)
    end
  end.

(* Compute build_myfun (to_lexpr <{ $fun X -> X }>) None empty. *)

(* build mapping from label to lexpr given a root lexpr *)
Fixpoint build_mylexpr (le : lexpr) (ml : mylexpr) : mylexpr :=
  match le with
  | <{ e @ l }> =>
    match e with
    | <{ $v }> =>
      match v with
      | <{ fun _ *-> le' }> => (l |-> le; build_mylexpr le' ml)
      | <{ fun _ -> _ }> => ml (* unreachable *)
      end
    | Ident _ => (l |-> le; ml)
    | <{ le1 <-* le2 }> => (l |-> le; build_mylexpr le2 (build_mylexpr le1 ml))
    | <{ _ <- _ }> => ml (* unreachable *)
    end
  end.

(* Compute build_mylexpr (to_lexpr <{ $fun X -> X }>) empty. *)

(* TODO: prove properties of above functions,
  like number of labels must be number of expr's,
  and size of mylexpr must be number of lexpr's *)

#[export] Hint Unfold build_myfun build_mylexpr update t_update : core.
