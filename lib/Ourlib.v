Require Import Coqlib.

(** * Useful tactics *)
Ltac rewrite_hyps :=
  repeat
    match goal with
      H1 : ?a = _, H2: ?a = _ |- _ => rewrite H1 in H2; inv H2
    end.

Ltac trim H :=
  match type of H with
    ?a -> ?b => let x := fresh in assert a as x; [ clear H | specialize (H x); clear x]
  end.
