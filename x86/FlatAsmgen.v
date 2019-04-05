Require Import Coqlib Integers AST Maps.
Require Import Asm TransSegAsm Segment.
Require Import Errors.
Require Import SegAsmBuiltin.
Require Import Memtype.
Require Import SegAsmProgram FlatProgram FlatAsm.
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

Definition transl_instr (i: TransSegAsm.instruction) : res instruction :=
  match i with
  | Sjmp_l ofs => OK (Fjmp_l ofs)
  | Sjcc c ofs => OK (Fjcc c ofs)
  | Sshortcall ofs sg => OK (Fshortcall ofs sg)
  | Sleal ofs a => 
    do a' <- transl_addr_mode a;
      OK (Fleal ofs a')
  | SAsminstr (Paddl_ri rd n) =>
    OK (Faddl_ri rd n)
  | SAsminstr (Psubl_ri rd n) =>
    OK (Fsubl_ri rd n)
  | SAsminstr (Psubl_rr rd r1) =>
    OK (Fsubl_rr rd r1)
  | SAsminstr (Pmovl_ri rd n) =>
    OK (Fmovl_ri rd n)
  | SAsminstr (Pmov_rr rd r1) =>
    OK (Fmov_rr rd r1)
  | Smovl_rm rd a =>
    do a' <- transl_addr_mode a;
      OK (Fmovl_rm rd a')
  | Smovl_mr a rs =>
    do a' <- transl_addr_mode a;
      OK (Fmovl_mr a' rs)
  | Smov_rs rd (sid,sofs) =>
    do ofs <- 
       match smap sid with
       | None => Error (msg "Invalid segment in the argument of MCmov_rs")
       | Some ofs => OK (Ptrofs.add ofs sofs)
       end;
      OK (Fmovl_rm rd (Addrmode None None ofs))
  | Smov_rm_a rd a =>
    do a' <- transl_addr_mode a;
      OK (Fmov_rm_a rd a')
  | Smov_mr_a a rs =>
    do a' <- transl_addr_mode a;
      OK (Fmov_mr_a a' rs)
  | SAsminstr (Ptestl_rr r1 r2) =>
    OK (Ftestl_rr r1 r2)
  | SAsminstr (Pret) =>
    OK Fret 
  | SAsminstr (Pimull_rr rd r1) =>
    OK (Fimull_rr rd r1)
  | SAsminstr (Pimull_ri rd n) =>
    OK (Fimull_ri rd n)
  | SAsminstr (Pcmpl_rr r1 r2) =>
    OK (Fcmpl_rr r1 r2)
  | SAsminstr (Pcmpl_ri r1 n) =>
    OK (Fcmpl_ri r1 n)
  | SAsminstr (Pcltd) =>
    OK Fcltd
  | SAsminstr (Pidivl r1) =>
    OK (Fidivl r1)
  | SAsminstr (Psall_ri rd n) =>
    OK (Fsall_ri rd n)
  | SAsminstr (Plabel l) =>
    OK Fnop
  | _ => Error (msg "Instruction not supported")
  end.

Definition transl_instr' (ii: TransSegAsm.instr_with_info) : res instr_with_info :=
  let '(i, sb, fid) := ii in
  do i' <- transl_instr i;
    OK (i', segblock_size sb).

(** Translation of a sequence of instructions in a function *)
Fixpoint transl_instrs (instrs: list TransSegAsm.instr_with_info) : res (list instr_with_info) :=
  match instrs with
  | nil => OK nil
  | i::instrs' =>
    do instr <- transl_instr' i;
    do tinstrs' <- transl_instrs instrs';
    OK (instr :: tinstrs')
  end.

(** Tranlsation of a function *)
Definition transl_fun (f:TransSegAsm.function) : res function :=
  do code' <- transl_instrs (SegAsmProgram.fn_code f);
  let sb := (SegAsmProgram.fn_range f) in
  match smap (segblock_id sb) with
  | None =>
    Error (msg "Segment block of a function is unkown")
  | Some ofs => 
    OK (mkfunction (SegAsmProgram.fn_sig f) code' 
                   (Ptrofs.add ofs (segblock_start sb))
                   (segblock_size sb))
  end.


Definition transl_globdef (def: (ident * option TransSegAsm.gdef) * segblock) 
  : res (ident * option FlatAsm.gdef) :=
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
Definition transf_program (p:TransSegAsm.program) : res program := 
  do defs <- transl_globdefs seg_map (SegAsmProgram.prog_defs p);
  OK (Build_program
        defs
        (SegAsmProgram.prog_public p)
        (SegAsmProgram.prog_main p)
        Ptrofs.zero
        Ptrofs.zero
        (segsize (data_seg p))
        Ptrofs.zero
        (segsize (code_seg p)))
      .