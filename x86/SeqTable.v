(** ** Tables *)
Require Import NArith Lists.List.

(** ** A table storing a sequence of elements. *)

Module SeqTable.

Definition t (V:Type) := list V.

Section WITHV.

  Context {V:Type}.

  Definition get (i:N) (tbl: t V) := 
    nth_error tbl (N.to_nat i).

  Fixpoint set_nat (i:nat) (v:V) (tbl: t V) :=
    match i, tbl with
    | O, h::l =>
      Some (v::l)
    | S i', h::l =>
      match set_nat i' v l with
      | None => None
      | Some l' => Some (h :: l')
      end
    | _, _ => None
    end.

  Definition set (i:N) (v: V) (tbl: t V) :=
    let i' := (N.to_nat i) in
    set_nat i' v tbl.

  Definition size (tbl:t V) :=
    length tbl.

End WITHV.

End SeqTable.
