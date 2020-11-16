(* *******************  *)
(* Author: Yuting Wang  *)
(* Date:   Sep 19, 2019 *)
(* *******************  *)

Require Import Coqlib Integers AST Maps.
Require Import Events.
Require Import Asm.
Require Import Errors.
Require Import Memtype.
Require Import Globalenvs .
Require Import LocalLib.
Import ListNotations.

Set Implicit Arguments.

Local Open Scope error_monad_scope.

(** * Pad initialization data with spaces *)

(** This pass is necessary to make the sizes of global data correctly
aligned for memory injections *)

Definition compute_pad_size initd :=
  let sz := AST.init_data_list_size initd in
  (align sz alignw) - sz.

Definition transl_globvar (gv:globvar unit) :=
  let initd := gvar_init gv in
  let initd' := 
      match initd with
      | nil
      | [Init_space _] => initd
      | _ => 
        let psz := compute_pad_size initd in
        if zlt 0 psz then
          initd ++ [Init_space psz]
        else
          initd
      end in
  mkglobvar (gvar_info gv) initd' (gvar_readonly gv) (gvar_volatile gv).

Definition transf_globdef (gdef : ident * (globdef fundef unit)) :=
  let '(id, def) := gdef in
  let def' := 
      match def with
      | (Gvar v) => (Gvar (transl_globvar v))
      | _ => def
      end in
  (id, def').

Definition transf_program (p:program) :=
  {| prog_defs := map transf_globdef (prog_defs p);
     prog_public := prog_public p;
     prog_main := prog_main p |}.
