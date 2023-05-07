From DDE Require Export Maps.
From Coq Require Export Lists.List.
Export ListNotations.

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

#[local] Open Scope lang_scope.

Definition X : string := "x".
Definition Y : string := "y".
Definition Z : string := "z".
Definition M : string := "m".
Definition N : string := "n".

(* TODO: auto-generate labels *)
Example sample_ident := <{ X@0 }>.
Example sample_fun := <{ fun X -> X@0 }>.
Example sample_fun_lexpr := <{ ($fun X -> X@0) @ 1 }>.
Example sample_fun_lexpr' := <{ ($fun X -> ($fun Y -> X@0) @ 1) @ 2 }>.
Example sample_appl := <{ (X@0 <- X@1) @ 2}>.
Example sample_res := <{ [ fun X -> X@0, 1, 0 :: [] ] }>.

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

#[export] Hint Unfold build_myfun build_mylexpr update t_update : core.
