Require Import ZArith Integers Values.
Require Import Memdata Lists.List.

Definition encode_int_big (n:nat) (i: Z) : list byte :=
  rev (bytes_of_int n i).

Definition encode_int_little (n:nat) (i: Z) : list byte :=
  bytes_of_int n i.

Definition encode_int32 (i:Z) : list byte :=
  encode_int 4 i.

Definition n_zeros_bytes (n:nat) : list byte :=
  List.map (fun _ => Byte.zero) (seq 1 n).
