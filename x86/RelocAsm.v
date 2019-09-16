(* *******************  *)
(* Author: Yuting Wang  *)
(* Date:   Sep 13, 2019 *)
(* *******************  *)

(** * The language of relocatble assembly *)

Require Import Coqlib Maps Integers Values AST.
Require Import Globalenvs.
Require Import Asm RelocProgram.


(** Define the programs *)
Definition instr_with_info:Type := instruction * secblock * ident.

Definition code := list instr_with_info.

Module RelocAsmParams.
  
  Definition C:= code.
  Definition D:= unit.

End RelocAsmParams.

Module Prog := RelocProg(RelocAsmParams).
Export Prog.
