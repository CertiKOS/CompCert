Require Import String Coqlib Maps.
Require Import AST Integers.

(** * Raw Binary *)

Record program : Type := {
  prog_code : list byte;
  prog_data : list byte;
  prog_data_addr  : ptrofs;
  prog_data_size  : ptrofs;
  prog_code_addr  : ptrofs;
  prog_code_size  : ptrofs;
}.