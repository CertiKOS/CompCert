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

Definition globvar := AST.globvar (option (seclabel * list byte)).

Module RelocBinParams.
  
  Definition C:= code.
  Definition D:= option (seclabel * list byte).

End RelocBinParams.

Module Prog := RelocProg(RelocBinParams).
Export Prog.
