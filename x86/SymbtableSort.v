(* *******************  *)
(* Author: Zhenguo Yin  *)
(* Date:   Aug 17, 2020 *)
(* *******************  *)

Require Import Coqlib Integers AST Maps.
Require Import Asm.
Require Import Errors.
Require Import Memtype.
Require Import RelocProgram.
Require Import CheckDef.
Require Import LocalLib.
Require Globalenvs.
Import ListNotations.

Set Implicit Arguments.

Local Open Scope error_monad_scope.


Definition filter_local_symbe (symbe:symbentry) :=
  match symbentry_bind symbe with
  | bind_local => true
  | bind_global => false
  end.

Definition filter_global_symbe (symbe:symbentry) :=
  match symbentry_bind symbe with
  | bind_global => true
  | bind_local => false
  end.

(* *)
Definition transf_symbtable (symbt:symbtable)
  : symbtable:=
  let symb_local := List.filter filter_local_symbe symbt in
  let symb_global := List.filter filter_global_symbe symbt in
  symb_local ++ symb_global.
  
(** The full translation *)
Definition transf_program (p: program) : res program :=
  let symb_tbl := transf_symbtable (prog_symbtable p) in
  if list_norepet_dec ident_eq (List.map fst (prog_defs p))
  then
    if list_norepet_dec ident_eq (List.map symbentry_id (prog_symbtable p))
    then
      OK {| prog_defs := prog_defs p;
            prog_public := prog_public p;
            prog_main := prog_main p;
            prog_sectable := prog_sectable p;
            prog_strtable := prog_strtable p;
            prog_symbtable := symb_tbl;
            prog_reloctables := prog_reloctables p;
            prog_senv := prog_senv p;
         |}
             else
      Error (msg "Symbol entry identifiers repeat in symbol table")
  else
    Error (msg "Identifiers repeat in program definitions")
.
