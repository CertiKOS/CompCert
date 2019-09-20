(** ** Tables *)
Require Import PArith Lists.List.

(** A table storing a sequence of elements indexed by
    numbers 0, 1, 2, ..., and so on *)
Module SeqTable.

Definition t (V:Type) := list V.

(** The 0-th element cannot be accessed by using get;
    it is usually a dummy or undefined element *)
Definition get {V:Type} (i:Pos.t) (tbl:t V) := 
  let i' := (Pos.to_nat i) in
  nth_error tbl i'.

Definition size {V:Type} (tbl:t V) :=
  length tbl.

End SeqTable.