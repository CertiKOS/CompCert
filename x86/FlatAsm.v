Require Import String Coqlib Maps.
Require Import AST Integers Floats Values Memory Events Smallstep.
Require Import Locations Stacklayout Conventions EraseArgs.
Require Import Num.
Require Import SegAsm Asm FlatProgram.
Require Globalenvs.

Inductive scale : Type :=
| Scale1 | Scale2 | Scale4 | Scale8.

Inductive addrmode: Type :=
| Addrmode (base: option ireg)
           (index: option (ireg * scale))
           (disp: ptrofs).
            
Inductive instruction : Type :=
  | Fjmp_l (ofs: ptrofs)
  | Fjcc (c: testcond) (ofs: ptrofs)
  | Fshortcall (ofs: ptrofs) (sg: signature) 
  | Fleal (rd: ireg) (a:addrmode)
  | Fxorl_r (rd: ireg)
  | Faddl_ri (rd: ireg) (n:int)
  | Fsubl_ri (rd: ireg) (n:int)
  | Fsubl_rr (rd r1: ireg)
  | Fmovl_ri (rd: ireg) (n:int)
  | Fmov_rr (rd r1: ireg)
  | Fmovl_rm (rd: ireg) (a: addrmode)
  | Fmovl_mr (a: addrmode) (rs: ireg)
  | Fmov_rm_a (rd: ireg) (a: addrmode)
  | Fmov_mr_a (a: addrmode) (r1: ireg)
  | Ftestl_rr (r1 r2: ireg)
  | Fret
  | Fimull_rr (rd r1: ireg)
  | Fimull_ri (rd: ireg) (n: int)
  | Fcmpl_rr (r1 r2: ireg)
  | Fcmpl_ri (r1:ireg) (n:int)
  | Fcltd
  | Fidivl (r1: ireg)
  | Fsall_ri (rd:ireg) (n:int)
  | Fnop.

Definition instr_with_info: Type := instruction * ptrofs.

Definition function := @FlatProgram.function instr_with_info.
Definition gdef := @FlatProgram.gdef instr_with_info data_info.

(* The Flat Machine Code Program *)
Definition program := @FlatProgram.program instr_with_info data_info.

