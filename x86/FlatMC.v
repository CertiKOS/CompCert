Require Import String Coqlib Maps.
Require Import AST Integers Floats Values Memory Events Smallstep.
Require Import Locations Stacklayout Conventions EraseArgs.
Require Import Num.
Require Import Asm FlatMCProgram.
Require Globalenvs.

Inductive scale : Type :=
| Scale1 | Scale2 | Scale4 | Scale8.

Inductive addrmode: Type :=
| Addrmode (base: option ireg)
           (index: option (ireg * scale))
           (disp: ptrofs).
            
Inductive instruction : Type :=
  | FMCjmp_l (ofs: ptrofs)
  | FMCjcc (c: testcond) (ofs: ptrofs)
  | FMCshortcall (ofs: ptrofs) (sg: signature) 
  | FMCleal (rd: ireg) (a:addrmode)
  | FMCxorl_r (rd: ireg)
  | FMCaddl_ri (rd: ireg) (n:int)
  | FMCsubl_ri (rd: ireg) (n:int)
  | FMCsubl_rr (rd r1: ireg)
  | FMCmovl_ri (rd: ireg) (n:int)
  | FMCmov_rr (rd r1: ireg)
  | FMCmovl_rm (rd: ireg) (a: addrmode)
  | FMCmovl_mr (a: addrmode) (rs: ireg)
  | FMCmov_rs (rd:ireg) (ofs: ptrofs) 
  | FMCmov_rm_a (rd: ireg) (a: addrmode)
  | FMCmov_mr_a (a: addrmode) (r1: ireg)
  | FMCtestl_rr (r1 r2: ireg)
  | FMCret
  | FMCimull_rr (rd r1: ireg)
  | FMCimull_ri (rd: ireg) (n: int)
  | FMCcmpl_rr (r1 r2: ireg)
  | FMCcmpl_ri (r1:ireg) (n:int)
  | FMCcltd
  | FMCidivl (r1: ireg)
  | FMCsall_ri (rd:ireg) (n:int)
  | FMCnop.

Definition instr_with_info: Type := instruction * ptrofs.

(* The Flat Machine Code Program *)
Definition program := @FlatMCProgram.program instr_with_info.

