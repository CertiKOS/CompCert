(* *******************  *)
(* Author: Yuting Wang  *)
(* Date:   Sep 16, 2019 *)
(* *******************  *)

(** * Generation of the relocation table and references to it *)

Require Import Coqlib Integers AST Maps.
Require Import Asm.
Require Import Errors.
Require Import Memtype.
Require Import RelocProgram.
Require Import SeqTable.
Import ListNotations.

Set Implicit Arguments.

Local Open Scope error_monad_scope.

(** ** Translation of instructions *)

Definition addrmode_reloc_offset (a:addrmode) : res Z :=
  match a with 
  | Addrmode _ _ (inr _) => OK (addrmode_size_aux a)
  | _ => Error (msg "Calculation of the relocation offset for addrmode fails: displacement is a constant")
  end. 

(** Calculate the starting offset of the bytes
    that need to be relocated in an instruction *)
Definition instr_reloc_offset (i:instruction) : res Z :=
  match i with
  | Pmov_rs _ _ => OK 2
  | Pcall (inr _) _ => OK 1
  | Pjmp (inr _) _ => OK 1
  | Pleal rd a =>
    do aofs <- addrmode_reloc_offset a;
    OK (1 + aofs)
  | Pmovl_rm _ a =>
    do aofs <- addrmode_reloc_offset a;
    OK (1 + aofs)
  | Pmovl_mr a _ =>
    do aofs <- addrmode_reloc_offset a;
    OK (1 + aofs)
  | Pmov_rm_a _ a =>
    do aofs <- addrmode_reloc_offset a;
    OK (1 + aofs)
  | Pmov_mr_a a _ =>
    do aofs <- addrmode_reloc_offset a;
    OK (1 + aofs)
  | _ => Error (msg "Calculation of addenddum failed: Instruction not supported yet by relocation")
  end.

(** Calculate the addendum of an instruction *)
Definition instr_addendum (i:instruction) : res Z :=
  do ofs <- instr_reloc_offset i;
  OK (ofs - (instr_size i)).


(** Compute the relocation entry of an instruction with a relative reference *)
Definition compute_instr_rel_relocentry (sofs:Z) (i:instruction) (symb:ident)  :=
  do iofs <- instr_reloc_offset i;
  do addend <- instr_addendum i;
  OK {| reloc_offset := sofs + iofs; 
        reloc_type := reloc_rel;
        reloc_symb := (SymbIndex.interp symb);
        reloc_addend := addend |}.

(** Compute the relocation entry of an instruction with an absolute reference *)
Definition compute_instr_abs_relocentry (sofs:Z) (i:instruction) (addend:Z) (symb:ident) :=
  do iofs <- instr_reloc_offset i;
  OK {| reloc_offset := sofs + iofs; 
        reloc_type := reloc_abs;
        reloc_symb := (SymbIndex.interp symb);
        reloc_addend := addend |}.

(** Compute the relocation entry of an instruciton with 
    an addressing mode whose displacement is (id + offset) *)
Definition compute_instr_disp_relocentry (sofs: Z) (i:instruction) (disp: ident*ptrofs) :=
  let '(symb,addend) := disp in
  compute_instr_abs_relocentry sofs i (Ptrofs.unsigned addend) symb.


Definition transl_instr_with_addrmode (rtbl:reloctable) 
           (sofs:Z) (i: instruction) rb ss disp (cstr:addrmode -> instruction) :=
    do e <- compute_instr_disp_relocentry sofs i disp;
    let next_rid := RelocIndex.deinterp' (N.of_nat (length rtbl)) in
    let instr' := cstr (Addrmode rb ss (inr (next_rid,Ptrofs.zero))) in
    OK (e :: rtbl, instr').


Definition transl_instr (sofs:Z) (rtbl:reloctable) (i: instruction) : res (reloctable * instruction) :=
  let next_rid := RelocIndex.deinterp' (N.of_nat (length rtbl)) in
  match i with
    Pallocframe _ _ _
  | Pfreeframe _ _
  | Pload_parent_pointer _ _ => Error (msg "Source program contains pseudo instructions")
  | Pjmp_l _
  | Pjcc _ _
  | Pjcc2 _ _ _
  | Pjmptbl _ _ => Error (msg "Source program contains jumps to labels")
  | Pjmp (inr id) sg => 
    do e <- compute_instr_rel_relocentry sofs i id;
    let i' := Pjmp (inr next_rid) sg in
    OK (e :: rtbl, i')
  | Pcall (inr id) sg =>
    do e <- compute_instr_rel_relocentry sofs i id;
    let i' := Pcall (inr next_rid) sg in
    OK (e :: rtbl, i')
  | Pmov_rs rd id => 
    do e <- compute_instr_abs_relocentry sofs i 0 id;
    let i' := Pmov_rs rd next_rid in
    OK (e :: rtbl, i')

  | Pmovl_rm rd (Addrmode rb ss (inr disp)) =>
    transl_instr_with_addrmode rtbl sofs i rb ss disp
                               (fun a => Pmovl_rm rd a)

  | Pmovq_rm rd a =>
    Error (msg "Relocation failed: instruction not supported yet")
  | Pmovl_mr (Addrmode rb ss (inr disp)) rs =>
    transl_instr_with_addrmode rtbl sofs i rb ss disp
                               (fun a => Pmovl_mr a rs)
  | Pmovq_mr a rs =>
    Error (msg "Relocation failed: instruction not supported yet")
  | Pmovsd_fm rd a =>
    Error (msg "Relocation failed: instruction not supported yet")
  | Pmovsd_mf a r1 =>
    Error (msg "Relocation failed: instruction not supported yet")
  | Pmovss_fm rd a =>
    Error (msg "Relocation failed: instruction not supported yet")
  | Pmovss_mf a r1 =>
    Error (msg "Relocation failed: instruction not supported yet")
  | Pfldl_m a =>               (**r [fld] double precision *)
    Error (msg "Relocation failed: instruction not supported yet")
  | Pfstpl_m a =>             (**r [fstp] double precision *)
    Error (msg "Relocation failed: instruction not supported yet")
  | Pflds_m a =>               (**r [fld] simple precision *)
    Error (msg "Relocation failed: instruction not supported yet")
  | Pfstps_m a =>              (**r [fstp] simple precision *)
    Error (msg "Relocation failed: instruction not supported yet")
  (** Moves with conversion *)
  | Pmovb_mr a rs =>    (**r [mov] (8-bit int) *)
    Error (msg "Relocation failed: instruction not supported yet")
  | Pmovw_mr a rs =>    (**r [mov] (16-bit int) *)
    Error (msg "Relocation failed: instruction not supported yet")
  | Pmovzb_rm rd a =>
    Error (msg "Relocation failed: instruction not supported yet")
  | Pmovsb_rm rd a =>
    Error (msg "Relocation failed: instruction not supported yet")
  | Pmovzw_rm rd a =>
    Error (msg "Relocation failed: instruction not supported yet")
  | Pmovsw_rm rd a =>
    Error (msg "Relocation failed: instruction not supported yet")
  (** Integer arithmetic *)
  | Pleal rd (Addrmode rb ss (inr disp))  =>
    transl_instr_with_addrmode rtbl sofs i rb ss disp
                               (fun a => Pleal rd a)
  | Pleaq rd a =>
    Error (msg "Relocation failed: instruction not supported yet")
  (** Saving and restoring registers *)
  | Pmov_rm_a rd (Addrmode rb ss (inr disp)) =>  (**r like [Pmov_rm], using [Many64] chunk *)
    transl_instr_with_addrmode rtbl sofs i rb ss disp
                               (fun a => Pmov_rm_a rd a)
  | Pmov_mr_a (Addrmode rb ss (inr disp)) rs =>   (**r like [Pmov_mr], using [Many64] chunk *)
    transl_instr_with_addrmode rtbl sofs i rb ss disp
                               (fun a => Pmov_mr_a a rs)
  | Pmovsd_fm_a rd a => (**r like [Pmovsd_fm], using [Many64] chunk *)
    Error (msg "Relocation failed: instruction not supported yet")
  | Pmovsd_mf_a a r1 =>  (**r like [Pmovsd_mf], using [Many64] chunk *)
    Error (msg "Relocation failed: instruction not supported yet")
  | _ =>
    OK (rtbl, i)
  end.


Definition acc_instrs r i := 
  do r' <- r;
  let '(sofs, rtbl, code) := r' in
  do ri <- transl_instr sofs rtbl i;
  let '(rtbl', i') := ri in
  OK (sofs + instr_size i, rtbl',  i' :: code).

Definition transl_code (c:code) : res (reloctable * code) :=
  do rs <- 
     fold_left acc_instrs c (OK (0, [], []));
  let '(_, rtbl', c') := rs in
  OK (rev rtbl', rev c').


(** ** Translation of global variables *)

Definition transl_init_data (dofs:Z) (rtbl:reloctable) 
           (d:init_data) : (reloctable * init_data) :=
  let next_rid := RelocIndex.deinterp' (N.of_nat (length rtbl)) in
  match d with
  | Init_addrof id ofs =>
    let e := {| reloc_offset := dofs;
                reloc_type := reloc_abs;
                reloc_symb := (SymbIndex.interp id);
                reloc_addend := Ptrofs.unsigned ofs;
             |} in
    let d' := Init_addrof next_rid (Ptrofs.zero) in
    (e :: rtbl, d')
  | _ => 
    (rtbl, d)
  end.

(** Tranlsation of a list of initialization data and generate
    relocation entries *)

Definition acc_init_data r d := 
  let '(dofs, rtbl, l) := r in
  let '(rtbl', d') := transl_init_data dofs rtbl d in
  (dofs + init_data_size d, rtbl', d' :: l).

Definition transl_init_data_list (l:list init_data) : (reloctable * list init_data) :=
  let '(_, rtbl, l') :=
      fold_left acc_init_data l (0, [], []) in
  (rev rtbl, rev l').


(** ** Translation of the program *)

Definition transl_section (sec:section) : res ((option reloctable) * section) :=
  match sec with
  | sec_text code =>
    do r <- transl_code code;
    let '(rtbl, code) := r in
    OK (Some rtbl, sec_text code)
  | sec_data l =>
    let '(rtbl, l') := transl_init_data_list l in
    OK (Some rtbl, sec_data l')
  | _ => 
    OK (None, sec)
  end.
 
Definition acc_sections r sec := 
  do r' <- r;
  let '(rtbls, stbl, si) := r' in
  do rs <- transl_section sec;
  let '(rtbl, sec') := rs in
  match SecIndex.deinterp si with
  | None => OK (rtbls, sec' :: stbl, N.succ si)
  | Some sec_idx =>
    let rtbls' := 
        match rtbl with
        | None => rtbls
        | Some rtbl => PTree.set sec_idx rtbl rtbls
        end in
    OK (rtbls', sec' :: stbl, N.succ si)
  end.

Definition transl_sectable (stbl: sectable) :=
  do r <- 
     fold_left acc_sections stbl
     (OK (PTree.empty reloctable, [], 0%N));
  let '(rtbls, stbl, _) := r in
  OK (rtbls, rev stbl).
   
  

Definition transf_program (p:program) : res program :=
  do rs <- transl_sectable (prog_sectable p);
  let '(rtbls, stbl) := rs in
  OK {| prog_defs := p.(prog_defs);
        prog_public := p.(prog_public);
        prog_main := p.(prog_main);
        prog_sectable := stbl;
        prog_strtable := prog_strtable p;
        prog_symbtable := p.(prog_symbtable);
        prog_reloctables := rtbls;
        prog_senv := p.(prog_senv);
     |}.
