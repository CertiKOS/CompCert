(* *******************  *)
(* Author: Yuting Wang  *)
(* Date:   Sep 16, 2019 *)
(* *******************  *)

(** * Generation of the relocation table and references to it *)

Require Import Coqlib Integers AST Maps.
Require Import Asm.
Require Import Errors.
Require Import Memtype.
Require Import RelocProgram RelocAsm.
Import ListNotations.

Set Implicit Arguments.

Local Open Scope error_monad_scope.

(** ** Translation of instructions and functions *)

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
Definition compute_instr_rel_relocentry (slbl:seclabel) (i:instruction) (symb:ident)  :=
  let '(sid, sofs) := slbl in
  do iofs <- instr_reloc_offset i;
  do addend <- instr_addendum i;
  OK {| reloc_offset := sofs + iofs; 
        reloc_type := reloc_rel;
        reloc_symb := symb;
        reloc_addend := addend |}.

(** Compute the relocation entry of an instruction with an absolute reference *)
Definition compute_instr_abs_relocentry (slbl: seclabel) (i:instruction) (addend:Z) (symb:ident) :=
  let '(sid, sofs) := slbl in
  do iofs <- instr_reloc_offset i;
  OK {| reloc_offset := sofs + iofs; 
        reloc_type := reloc_abs;
        reloc_symb := symb;
        reloc_addend := addend |}.

(** Compute the relocation entry of an instruciton with 
    an addressing mode whose displacement is (id + offset) *)
Definition compute_instr_disp_relocentry (slbl: seclabel) (i:instruction) (disp: ident*ptrofs) :=
  let '(symb,addend) := disp in
  compute_instr_abs_relocentry slbl i (Ptrofs.unsigned addend) symb.


Definition transl_instr_with_addrmode (rtbl:reloctable) (next_rid:ident) 
           (slbl:seclabel) (i: instruction) rb ss disp (cstr:addrmode -> instruction) :=
    do e <- compute_instr_disp_relocentry slbl i disp;
    let instr' := cstr (Addrmode rb ss (inr (next_rid,Ptrofs.zero))) in
    OK (PTree.set next_rid e rtbl, Psucc next_rid, (instr', slbl)).

Definition transl_instr_with_info (rtbl:reloctable) (next_rid:ident)
           (ii: instr_with_info) : res (reloctable * ident * instr_with_info) :=
  let '(i,slbl) := ii in
  match i with
    Pallocframe _ _ _
  | Pfreeframe _ _
  | Pload_parent_pointer _ _ => Error (msg "Source program contains pseudo instructions")
  | Pjmp_l _
  | Pjcc _ _
  | Pjcc2 _ _ _
  | Pjmptbl _ _ => Error (msg "Source program contains jumps to labels")
  | Pjmp (inr id) sg => 
    do e <- compute_instr_rel_relocentry slbl i id;
    let ii' := (Pjmp (inr next_rid) sg, slbl) in
    OK (PTree.set next_rid e rtbl, Psucc next_rid, ii')
  | Pcall (inr id) sg =>
    do e <- compute_instr_rel_relocentry slbl i id;
    let ii' := (Pcall (inr next_rid) sg, slbl) in
    OK (PTree.set next_rid e rtbl, Psucc next_rid, ii')
  | Pmov_rs rd id => 
    do e <- compute_instr_abs_relocentry slbl i 0 id;
    let ii' := (Pmov_rs rd next_rid, slbl) in
    OK (PTree.set next_rid e rtbl, Psucc next_rid, ii')

  | Pmovl_rm rd (Addrmode rb ss (inr disp)) =>
    transl_instr_with_addrmode rtbl next_rid slbl i rb ss disp
                               (fun a => Pmovl_rm rd a)

  | Pmovq_rm rd a =>
    Error (msg "Relocation failed: instruction not supported yet")
  | Pmovl_mr (Addrmode rb ss (inr disp)) rs =>
    transl_instr_with_addrmode rtbl next_rid slbl i rb ss disp
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
    transl_instr_with_addrmode rtbl next_rid slbl i rb ss disp
                               (fun a => Pleal rd a)
  | Pleaq rd a =>
    Error (msg "Relocation failed: instruction not supported yet")
  (** Saving and restoring registers *)
  | Pmov_rm_a rd (Addrmode rb ss (inr disp)) =>  (**r like [Pmov_rm], using [Many64] chunk *)
    transl_instr_with_addrmode rtbl next_rid slbl i rb ss disp
                               (fun a => Pmov_rm_a rd a)
  | Pmov_mr_a (Addrmode rb ss (inr disp)) rs =>   (**r like [Pmov_mr], using [Many64] chunk *)
    transl_instr_with_addrmode rtbl next_rid slbl i rb ss disp
                               (fun a => Pmov_mr_a a rs)
  | Pmovsd_fm_a rd a => (**r like [Pmovsd_fm], using [Many64] chunk *)
    Error (msg "Relocation failed: instruction not supported yet")
  | Pmovsd_mf_a a r1 =>  (**r like [Pmovsd_mf], using [Many64] chunk *)
    Error (msg "Relocation failed: instruction not supported yet")
  | _ =>
    OK (rtbl, next_rid, (i,slbl))
  end.


Definition transl_func (rtbl:reloctable) (next_rid:ident) (f: function) 
  : res (reloctable * ident * function) :=
  do rs <- 
     fold_right (fun ii r =>
                   do r' <- r;
                   let '(rtbl, next_id, code) := r' in
                   do ri <- transl_instr_with_info rtbl next_id ii;
                   let '(rtbl', next_id', ii') := ri in
                   OK (rtbl', next_id', ii' :: code)) 
     (OK (rtbl, next_rid, [])) (fn_code f);
  let '(rtbl', next_rid', code) := rs in
  OK (rtbl', next_rid', mkfunction (fn_sig f) code (fn_stacksize f) (fn_pubrange f)).

Definition transf_fundef (rtbl:reloctable) (next_rid:ident) (fd: fundef) 
  : res (reloctable * ident * fundef) :=
  match fd with
  | External _ => OK (rtbl, next_rid, fd)
  | Internal f =>
    do r <- transl_func rtbl next_rid f;
    let '(rtbl', next_rid', f') := r in
    OK (rtbl', next_rid', Internal f')
  end.

Definition transf_fundefs (defs: list (ident * option gdef))
  : res (reloctable * list (ident * option gdef)) :=
  do r <-
      fold_right (fun '(id, def) r =>
                    do r' <- r;
                    let '(rtbl, next_rid, l) := r' in
                    match def with
                    | Some (Gfun fd) => 
                      do rg <- transf_fundef rtbl next_rid fd;
                      let '(rtbl', next_rid', fd') := rg in
                      OK (rtbl', next_rid', (id, Some (Gfun fd'))::l)
                    | _ =>
                      OK (rtbl, next_rid, (id, def)::l)
                    end
                 )
                 (OK (PTree.empty relocentry, 1%positive, nil))
                 defs;
  let '(rtbl, _, defs') := r in
  OK (rtbl, defs').

(** ** Translation of global variables *)

Definition transl_init_data (rtbl:reloctable) (next_rid:ident)
           (dofs:Z) (d:init_data) : (reloctable * ident * init_data) :=
  match d with
  | Init_addrof id ofs =>
    let e := {| reloc_offset := dofs;
                reloc_type := reloc_abs;
                reloc_symb := id;
                reloc_addend := Ptrofs.unsigned ofs;
             |} in
    let d' := Init_addrof next_rid (Ptrofs.zero) in
    (PTree.set next_rid e rtbl, Psucc next_rid, d')
  | _ => 
    (rtbl, next_rid, d)
  end.

(** Tranlsation of a list of initialization data and generate
    relocation entries. It takes as input the relocation table, the next
    available id for the relocation entries, the offset of data 
    in the data section and the list of init data *)

Definition transl_init_data_list (rtbl:reloctable) (next_rid:ident)
           (dofs:Z) (l:list init_data) : (reloctable * ident * Z * list init_data) :=
  fold_right (fun d '(rtbl, next_id, dofs, l) =>
                let '(rtbl', next_id', d') := transl_init_data rtbl next_id dofs d in
                (rtbl', next_id', (dofs + init_data_size d), d' :: l))
             (rtbl, next_rid, dofs, []) l.

Definition transf_globvar (rtbl:reloctable) (next_rid:ident) (gv:globvar) :=
  match gv.(gvar_init) with
  | nil
  | [Init_space _] => OK (rtbl, next_rid, gv)
  | _ => 
    match gv.(gvar_info) with
    | None => Error (msg "Relocation of global variable fails: no section label found")
    | Some (sid,ofs) =>
      let '(rtbl', next_rid', _, l) := 
          transl_init_data_list rtbl next_rid ofs gv.(gvar_init) in
      OK (rtbl', next_rid', mkglobvar gv.(gvar_info) l gv.(gvar_readonly) gv.(gvar_volatile))
    end
  end.
    
Definition transf_globvars (defs: list (ident * option gdef))
  : res (reloctable * list (ident * option gdef)) :=
  do r <-
      fold_right (fun '(id, def) r =>
                    do r' <- r;
                    let '(rtbl, next_rid, l) := r' in
                    match def with
                    | Some (Gvar v) => 
                      do rg <- transf_globvar rtbl next_rid v;
                      let '(rtbl', next_rid', v') := rg in
                      OK (rtbl', next_rid', (id, Some (Gvar v'))::l)
                    | _ =>
                      OK (rtbl, next_rid, (id, def)::l)
                    end
                 )
                 (OK (PTree.empty relocentry, 1%positive, nil))
                 defs;
  let '(rtbl, _, defs') := r in
  OK (rtbl, defs').

(** ** Translation of the program *)

Definition transf_program (p:program) : res program :=
  let defs := prog_defs p in
  do rf <- transf_fundefs defs;
  let '(frtbl, defs1) := rf in
  do rv <- transf_globvars defs1;
  let '(vrtbl, defs2) := rv in
  let reloctables := 
      PTree.set sec_code_id frtbl 
                (PTree.set sec_data_id vrtbl 
                           (PTree.empty reloctable)) in
  OK {| prog_defs := defs1;
        prog_public := p.(prog_public);
        prog_main := p.(prog_main);
        prog_sectable := p.(prog_sectable);
        prog_symbtable := p.(prog_symbtable);
        prog_reloctables := reloctables;
        prog_senv := p.(prog_senv);
     |}.