(* *******************  *)
(* Author: Yuting Wang  *)
(* Date:   Oct 3, 2019  *)
(* *******************  *)

Require Import Coqlib Integers AST Maps.
Require Import Errors.
Require Import Ascii String.

(** This an external function in ML for 
    finding the strings associated with the global symbols *)
Parameter find_symbol_pos : ident -> option (list positive).

