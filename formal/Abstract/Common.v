From Coq Require Import Arith.Arith.
From DDE.Common Require Export Lang.

Definition s_set : Type := list sigma.

Fixpoint prune_sigma (s : sigma) (k : nat) (acc : sigma) : sigma := 
  match s with
  | [] => acc
  | l :: ls =>
    if k =? 0 then acc
    else prune_sigma ls (k - 1) (l :: acc)
  end.

Definition prune_sigma2 (s : sigma) : sigma := prune_sigma s 2 [].
