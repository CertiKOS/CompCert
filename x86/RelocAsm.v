(* *******************  *)
(* Author: Yuting Wang  *)
(* Date:   Sep 13, 2019 *)
(* *******************  *)

(** * The language of relocatble assembly *)

Require Import Coqlib Maps Integers Values AST.
Require Import Globalenvs.
Require Import Asm RelocAsmProgram.


(** Define the programs *)
Module RAsmParams.
  
  Definition I:= instruction.
  Definition D:= unit.

End RAsmParams.

Module Prog := RelocAsmProg(RAsmParams).
Import Prog.
