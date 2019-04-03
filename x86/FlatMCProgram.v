Require Import String Coqlib Maps.
Require Import AST Integers.


(* Machine code programs with a flat memory space *)
Section FLATPROG.

Context {I: Type}.

Definition instr_with_info: Type := I * ptrofs.

Definition code := list instr_with_info.

Record function : Type := mkfunction { fn_sig: signature; fn_code: code; }.

Definition fundef := AST.fundef function.
Definition gdef := globdef fundef unit.

(* The Flat Machine Code Program *)
Record program : Type := {
  prog_defs: list (ident * option gdef);
  prog_public: list ident;
  prog_main: ident;
  prog_main_ofs: ptrofs;
  prog_data_addr: ptrofs;
  prog_data_size: ptrofs;
  prog_code_addr: ptrofs;
  prog_code_size: ptrofs;
}.

End FLATPROG.