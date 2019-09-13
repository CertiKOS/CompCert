(* *******************  *)
(* Author: Yuting Wang  *)
(* Date:   Sep 13, 2019 *)
(* *******************  *)

(** * The language of relocatble binary *)

Require Import Coqlib Maps Integers Values AST.
Require Import Globalenvs.
Require Import Asm RelocProgram.


(** Define the programs *)
Definition code := list byte.

Module RelocBinParams.
  
  Definition C:= code.
  Definition D:= unit.

End RelocBinParams.

Module Prog := RelocProg(RelocBinParams).
Import Prog.
