Require Import String Coqlib Maps.
Require Import AST Integers.


(* Programs with a flat memory space *)
Section FLATPROG.

Context {C: Type}.
Context {D: Type}.

Definition code := C.

Record function : Type := mkfunction { fn_sig: signature; fn_code: code; fn_start: ptrofs; fn_size: ptrofs}.

Definition fundef := AST.fundef function.
Definition gdef := globdef fundef D.

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
