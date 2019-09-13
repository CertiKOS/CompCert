(** Translation from RawAsm to RealAsm *)

Require Import Coqlib Errors.
Require Import AST Integers Floats Memdata.
Require Import Op Locations Mach Asm.

Local Open Scope string_scope.
Local Open Scope error_monad_scope.

Definition transf_function (f: Asm.function) : res Asm.function :=
  if func_no_jmp_rel_dec f then 
    OK f 
  else
    Error (msg "function contains jumps to relative offset").

Definition transf_fundef (f: Asm.fundef) : res Asm.fundef :=
  transf_partial_fundef transf_function f.

Definition transf_program (p: Asm.program) : res Asm.program :=
  transform_partial_program transf_fundef p.

