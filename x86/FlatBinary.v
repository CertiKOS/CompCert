Require Import String Coqlib Maps.
Require Import AST Integers Floats Values Memory Events Smallstep.
Require Import Locations Stacklayout Conventions EraseArgs.
Require Import Num.
Require Import SegAsm FlatProgram.
Require Globalenvs.

(* An instruction is a list of bytes *)
Definition instruction := list byte.

Definition function := @FlatProgram.function instruction.
Definition gdef := @FlatProgram.gdef instruction data_info.

(* A program with binary representation of code and data *)
Definition program := @FlatProgram.program instruction data_info.