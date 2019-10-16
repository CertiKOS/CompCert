(* *******************  *)
(* Author: Xiangzhe Xu  *)
(* Date:   Oct 16, 2019 *)
(* *******************  *)




Require Import Coqlib Integers AST Maps.
Require Import Events.
Require Import Asm.
Require Import Errors.
Require Import Memtype.
Require Import Globalenvs .
Import ListNotations.

Local Open Scope error_monad_scope.


Definition transl_instr (i: instruction) (ofs:Z) (code:code) : res (list instruction) :=
  match i with
  |Psetcc c rd =>
   OK [Psetcc c rd; Pmovzb_rr rd rd]
  |_ =>
   OK [i] 
  end.


Definition acc_transl_instr c r i :=
  do r' <- r;
    let '(ofs, code) := r' in
    do i' <- transl_instr i ofs c;
      OK (ofs + instr_size i, (i' ++ code)).
  
Definition transl_code (c:code) : res code :=
  do rs <- 
     fold_left (acc_transl_instr c)
               c
               (OK (0, []));
  let '(_, c') := rs in
  OK (rev c').


Definition trans_function (f: function) :res function :=
  if func_no_jmp_rel_dec f then 
    do instrs <- transl_code (fn_code f);
      OK (mkfunction (fn_sig f) instrs (fn_stacksize f) (fn_pubrange f))
  else
    Error (msg "Some source function contains relative jumps").

Definition transf_fundef (f: Asm.fundef) : res Asm.fundef :=
  transf_partial_fundef trans_function f.

Definition transf_program (p: Asm.program) : res Asm.program :=
  transform_partial_program transf_fundef p.


