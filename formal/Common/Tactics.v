Ltac invert H := inversion H; subst; clear H.

Ltac inject_all :=
  repeat match goal with
    H1 : ?E = _,
    H2 : ?E = _
    |- _ => rewrite H1 in H2; invert H2
  end.
