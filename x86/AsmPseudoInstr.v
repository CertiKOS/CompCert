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
Require Import Globalenvs.
Require Import AsmLabelNew.
Import ListNotations.

Local Open Scope error_monad_scope.

Definition neg_cond (cond:testcond) :=
  match cond with
  | Cond_e => Cond_ne
  | Cond_ne => Cond_e
  | Cond_b => Cond_ae
  | Cond_be => Cond_a
  | Cond_ae => Cond_b
  | Cond_a => Cond_be
  | Cond_l => Cond_ge
  | Cond_le => Cond_g
  | Cond_ge => Cond_l
  | Cond_g => Cond_le
  | Cond_p => Cond_np
  | Cond_np => Cond_p
  end.
  
Definition transf_instr (i: instruction) : res (list instruction) :=
  match i with
  | Psetcc c rd =>
   OK [Pmovzb_rr rd rd; Psetcc c rd]
  | Pjcc2 cond1 cond2 lbl =>
    let lbl' := new_label tt in
    let i1 := Pjcc (neg_cond cond1) lbl' in
    let i2 := Pjcc cond2 lbl in
    let i3 :=  Plabel lbl' in
    OK ([i1]++[i2]++[i3])
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
