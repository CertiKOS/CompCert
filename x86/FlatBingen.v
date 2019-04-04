Require Import Coqlib Integers AST Maps.
Require Import Asm MC Segment.
Require Import Errors.
Require Import FlatAsmBuiltin.
Require Import Memtype.
Require Import FlatAsmProgram FlatMCProgram FlatMC FlatBinary.
Require Import Hex.
Import ListNotations.
Import Hex.

Local Open Scope error_monad_scope.
Local Open Scope hex_scope.

Definition fmc_instr_encode (i: FlatMC.instruction) : res FlatBinary.instruction :=
  match i with
  | FMCjmp_l ofs =>
    OK (HByte{"E9"} :: nil)
  | _ =>
    Error (msg "FMC instruction not supported")
  end.


Definition transl_instr' (ii: FlatMC.instr_with_info) : res instruction :=
  let '(i, sz) := ii in
  fmc_instr_encode i.


(** Translation of a sequence of instructions in a function *)
Fixpoint transl_instrs (instrs: list FlatMC.instr_with_info) : res (list instruction) :=
  match instrs with
  | nil => OK nil
  | i::instrs' =>
    do instr <- transl_instr' i;
    do tinstrs' <- transl_instrs instrs';
    OK (instr :: tinstrs')
  end.

(** Tranlsation of a function *)
Definition transl_fun (f:@FlatMCProgram.function FlatMC.instr_with_info) : res function :=
  do code' <- transl_instrs (FlatMCProgram.fn_code f);
  OK (mkfunction (FlatMCProgram.fn_sig f) code').

Definition transl_globdef (def: (ident * option (@FlatMCProgram.gdef FlatMC.instr_with_info)) )
  : res (ident * option (@FlatMCProgram.gdef instruction)) :=
  let '(id,def) := def in
  match def with
  | Some (AST.Gfun (Internal f)) =>
    do f' <- transl_fun f;
      OK (id, Some (AST.Gfun (Internal f')))
  | Some (AST.Gfun (External f)) => 
    OK (id, Some (AST.Gfun (External f)))
  | Some (AST.Gvar v) =>
    OK (id, Some (AST.Gvar v))
  | None => OK (id, None)
  end.

Fixpoint transl_globdefs defs :=
  match defs with
  | nil => OK nil
  | def::defs' =>
    do tdef <- transl_globdef def;
    do tdefs' <- transl_globdefs defs';
    OK (tdef :: tdefs')
  end.


(** Translation of a program *)
Definition transf_program (p:FlatMC.program) : res program := 
  do defs <- transl_globdefs (FlatMCProgram.prog_defs p);
  OK (Build_program
        defs
        (prog_public p)
        (prog_main p)
        (prog_main_ofs p)
        (prog_data_addr p)
        (prog_data_size p)
        (prog_code_addr p)
        (prog_code_size p))
      .