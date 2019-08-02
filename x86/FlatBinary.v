Require Import String Coqlib Maps.
Require Import AST Integers Floats Values Memory Events Smallstep.
Require Import Locations Stacklayout Conventions EraseArgs.
Require Import Num.
Require Import SegAsm FlatProgram.
Require Globalenvs.

(* An instruction is a list of bytes *)
Definition code_type := list byte.

Definition function := @FlatProgram.function code_type.
Definition gdef := @FlatProgram.gdef code_type data_info.

(* A program with binary representation of code and data *)
Definition program := @FlatProgram.program code_type data_info.
