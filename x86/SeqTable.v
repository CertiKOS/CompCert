(** ** Tables *)
Require Import NArith Lists.List.

(** ** A table storing a sequence of elements. 
       The index might start at a non-zero value. *)

Module Type SeqTableParams.
  Parameter V: Type.
  Parameter ofs: N.
End SeqTableParams.

Module SeqTable(P: SeqTableParams).

  Definition t := list (P.V).

  Definition idx i := (i - P.ofs)%N.

  Definition get (i:N) (tbl: t) := 
    nth_error tbl (N.to_nat (idx i)).

  Fixpoint set_nat (i:nat) (v:P.V) (tbl: t) :=
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

  Definition set (i:N) (v: P.V) (tbl: t) :=
    let i' := (N.to_nat (idx i)) in
    set_nat i' v tbl.

  Definition size (tbl:t) :=
    length tbl.

  Definition filter (f: P.V -> bool) (tbl: t) :=
    List.filter f tbl.

End SeqTable.
