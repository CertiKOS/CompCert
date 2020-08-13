(* ******************** *)
(* Author: Xiangzhe Xu  *)
(*         Zhenguo Yin  *)
(* Date:   Aug 12, 2020 *)
(* ******************** *)
Require Import Coqlib Integers AST Maps.
Require Import Events.
Require Import Asm.
Require Import Errors.
Require Import Memtype.
Require Import Globalenvs .
Import ListNotations.

Local Open Scope error_monad_scope.

Definition transf_instr (i: instruction) : res (list instruction) :=
  match i with
  |Psetcc c rd =>
   OK [Pmovzb_rr rd rd; Psetcc c rd]
  |_ => OK [i] 
  end.

Definition acc_transl_instr (r:res code) (i:instruction) :=
  do acc_i <- r;
  do i' <- transf_instr i;
  OK (acc_i ++ i').
  
Definition transl_code (c:code) : res code :=
  do code <- fold_left acc_transl_instr c (OK []);
  OK (code).

Definition transf_function (f: function) : res function :=
  (* make sure that code can not have relative jumps*)
  if func_no_jmp_rel_dec f then
    do fn_code' <- transl_code (fn_code f);
    OK {|
        fn_sig := fn_sig f;
        fn_code := fn_code';
        fn_stacksize := fn_stacksize f;
        fn_pubrange := fn_pubrange f;
      |}
  else
    Error [MSG "Code contains relative jumps"].

Definition transf_fundef (f: Asm.fundef) : res Asm.fundef :=
  transf_partial_fundef transf_function f.

Definition transf_program (p: Asm.program) : res Asm.program :=
  transform_partial_program transf_fundef p.
