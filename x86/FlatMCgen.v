Require Import Coqlib Integers AST Maps.
Require Import Asm MC Segment.
Require Import Errors.
Require Import FlatAsmBuiltin.
Require Import Memtype.
Require Import FlatAsmProgram FlatMCProgram FlatMC.
Import ListNotations.

Local Open Scope error_monad_scope.


Definition SMAP_TYPE := segid_type -> option ptrofs.


Section WITH_SEG_MAP.

Variable smap: SMAP_TYPE.

Definition transl_scale (s:Z) : res scale :=
  match s with
  | 1 => OK Scale1
  | 2 => OK Scale2
  | 4 => OK Scale4
  | 8 => OK Scale8
  | _ => Error (msg "Translation of scale failed")
  end.

Definition transl_addr_mode (m: addrmode') : res addrmode :=
  match m with
  | Addrmode' b ofs (sid, sofs) =>
    do index <-
         match ofs with
         | None => OK None
         | Some (r,scale) => 
           do sc <- transl_scale scale;
             OK (Some (r, sc))
         end;
    do disp <- 
       match smap sid with
       | None => Error (msg "Invalid segment found during address mode translation")
       | Some disp => OK (Ptrofs.add disp sofs)
       end;
    OK (Addrmode b index disp)
  end.

Definition transl_instr (i: MC.instruction) : res instruction :=
  match i with
  | MCjmp_l ofs => OK (FMCjmp_l ofs)
  | MCjcc c ofs => OK (FMCjcc c ofs)
  | MCshortcall ofs sg => OK (FMCshortcall ofs sg)
  | MCleal ofs a => 
    do a' <- transl_addr_mode a;
      OK (FMCleal ofs a')
  | MCAsminstr (Paddl_ri rd n) =>
    OK (FMCaddl_ri rd n)
  | MCAsminstr (Psubl_ri rd n) =>
    OK (FMCsubl_ri rd n)
  | MCAsminstr (Psubl_rr rd r1) =>
    OK (FMCsubl_rr rd r1)
  | MCAsminstr (Pmovl_ri rd n) =>
    OK (FMCmovl_ri rd n)
  | MCAsminstr (Pmov_rr rd r1) =>
    OK (FMCmov_rr rd r1)
  | MCmovl_rm rd a =>
    do a' <- transl_addr_mode a;
      OK (FMCmovl_rm rd a')
  | MCmovl_mr a rs =>
    do a' <- transl_addr_mode a;
      OK (FMCmovl_mr a' rs)
  | MCmov_rs rd (sid,sofs) =>
    do ofs <- 
       match smap sid with
       | None => Error (msg "Invalid segment in the argument of MCmov_rs")
       | Some ofs => OK (Ptrofs.add ofs sofs)
       end;
      OK (FMCmovl_rm rd (Addrmode None None ofs))
  | MCmov_rm_a rd a =>
    do a' <- transl_addr_mode a;
      OK (FMCmov_rm_a rd a')
  | MCmov_mr_a a rs =>
    do a' <- transl_addr_mode a;
      OK (FMCmov_mr_a a' rs)
  | MCAsminstr (Ptestl_rr r1 r2) =>
    OK (FMCtestl_rr r1 r2)
  | MCAsminstr (Pret) =>
    OK FMCret 
  | MCAsminstr (Pimull_rr rd r1) =>
    OK (FMCimull_rr rd r1)
  | MCAsminstr (Pimull_ri rd n) =>
    OK (FMCimull_ri rd n)
  | MCAsminstr (Pcmpl_rr r1 r2) =>
    OK (FMCcmpl_rr r1 r2)
  | MCAsminstr (Pcmpl_ri r1 n) =>
    OK (FMCcmpl_ri r1 n)
  | MCAsminstr (Pcltd) =>
    OK FMCcltd
  | MCAsminstr (Pidivl r1) =>
    OK (FMCidivl r1)
  | MCAsminstr (Psall_ri rd n) =>
    OK (FMCsall_ri rd n)
  | MCAsminstr (Plabel l) =>
    OK FMCnop
  | _ => Error (msg "Instruction not supported")
  end.

Definition transl_instr' (ii: MC.instr_with_info) : res instr_with_info :=
  let '(i, sb, fid) := ii in
  do i' <- transl_instr i;
    OK (i', segblock_size sb).

(** Translation of a sequence of instructions in a function *)
Fixpoint transl_instrs (instrs: list MC.instr_with_info) : res (list instr_with_info) :=
  match instrs with
  | nil => OK nil
  | i::instrs' =>
    do instr <- transl_instr' i;
    do tinstrs' <- transl_instrs instrs';
    OK (instr :: tinstrs')
  end.

(** Tranlsation of a function *)
Definition transl_fun (f:@FlatAsmProgram.function MC.instruction) : res function :=
  do code' <- transl_instrs (FlatAsmProgram.fn_code f);
  let sb := (FlatAsmProgram.fn_range f) in
  match smap (segblock_id sb) with
  | None =>
    Error (msg "Segment block of a function is unkown")
  | Some ofs => 
    OK (mkfunction (FlatAsmProgram.fn_sig f) code' 
                   (Ptrofs.add ofs (segblock_start sb))
                   (segblock_size sb))
  end.


Definition transl_globdef (def: (ident * option (@FlatAsmProgram.gdef MC.instruction) * segblock)) 
  : res (ident * option (@FlatMCProgram.gdef FlatMC.instr_with_info)) :=
  let '(id,def,sb) := def in
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

End WITH_SEG_MAP.


Definition seg_map : SMAP_TYPE :=
  fun sid =>
    if peq sid code_segid then Some Ptrofs.zero
    else 
    if peq sid data_segid then Some Ptrofs.zero
    else
    None.

(** Translation of a program *)
Definition transf_program (p:MC.program) : res program := 
  do defs <- transl_globdefs seg_map (FlatAsmProgram.prog_defs p);
  OK (Build_program
        defs
        (FlatAsmProgram.prog_public p)
        (FlatAsmProgram.prog_main p)
        Ptrofs.zero
        Ptrofs.zero
        (segsize (data_seg p))
        Ptrofs.zero
        (segsize (code_seg p)))
      .