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


Section WITH_SYMB_INDEX_MAP.

Variable (symb_index_map: symb_index_map_type).

(** Compute the relocation entry of an instruction with a relative reference *)
Definition compute_instr_rel_relocentry (sofs:Z) (i:instruction) (symb:ident) :=
  do iofs <- instr_reloc_offset i;
  do addend <- instr_addendum i;
  match PTree.get symb symb_index_map with
  | None => Error [MSG "Cannot find the index for symbol: "; POS symb]
  | Some idx =>
    OK {| reloc_offset := sofs + iofs; 
          reloc_type := reloc_rel;
          reloc_symb := idx;
          reloc_addend := addend |}
  end.

(** Compute the relocation entry of an instruction with an absolute reference *)
Definition compute_instr_abs_relocentry (sofs:Z) (i:instruction) (addend:Z) (symb:ident)  :=
  do iofs <- instr_reloc_offset i;
  match PTree.get symb symb_index_map with
  | None => Error [MSG "Cannot find the index for symbol: "; POS symb]
  | Some idx => 
    OK {| reloc_offset := sofs + iofs; 
          reloc_type := reloc_abs;
          reloc_symb := idx;
          reloc_addend := addend |}
  end.

(** Compute the relocation entry of an instruciton with 
    an addressing mode whose displacement is (id + offset) *)
Definition compute_instr_disp_relocentry (sofs: Z) (i:instruction) (disp: ident*ptrofs) :=
  let '(symb,addend) := disp in
  compute_instr_abs_relocentry sofs i (Ptrofs.unsigned addend) symb.


Definition transl_instr (sofs:Z) (i: instruction) : res (list relocentry) :=
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
    OK [e]
  | Pcall (inr id) sg =>
    do e <- compute_instr_rel_relocentry sofs i id;
    OK [e]
  | Pmov_rs rd id => 
    do e <- compute_instr_abs_relocentry sofs i 0 id;
    OK [e]
  | Pmovl_rm rd (Addrmode rb ss (inr disp)) =>
    do e <- compute_instr_disp_relocentry sofs i disp;
    OK [e]
  | Pmovq_rm rd a =>
    Error (msg "Relocation failed: instruction not supported yet")
  | Pmovl_mr (Addrmode rb ss (inr disp)) rs =>
    do e <- compute_instr_disp_relocentry sofs i disp;
    OK [e]
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
    do e <- compute_instr_disp_relocentry sofs i disp;
    OK [e]
  | Pleaq rd a =>
    Error (msg "Relocation failed: instruction not supported yet")
  (** Saving and restoring registers *)
  | Pmov_rm_a rd (Addrmode rb ss (inr disp)) =>  (**r like [Pmov_rm], using [Many64] chunk *)
    do e <- compute_instr_disp_relocentry sofs i disp;
    OK [e]
  | Pmov_mr_a (Addrmode rb ss (inr disp)) rs =>   (**r like [Pmov_mr], using [Many64] chunk *)
    do e <- compute_instr_disp_relocentry sofs i disp;
    OK [e]
  | Pmovsd_fm_a rd a => (**r like [Pmovsd_fm], using [Many64] chunk *)
    Error (msg "Relocation failed: instruction not supported yet")
  | Pmovsd_mf_a a r1 =>  (**r like [Pmovsd_mf], using [Many64] chunk *)
    Error (msg "Relocation failed: instruction not supported yet")
  | _ =>
    OK []
  end.


Definition acc_instrs r i :=
  do (sofs, rtbl) <- r;
  do ri <- transl_instr sofs i;
  OK (sofs + instr_size i, ri ++ rtbl).

Definition transl_code (c:code) : res reloctable :=
  do (_, rtbl) <- fold_left acc_instrs c (OK (0, []));
  OK rtbl.

(** ** Translation of global variables *)

Definition transl_init_data (dofs:Z) (d:init_data) : res reloctable :=
  match d with
  | Init_addrof id ofs =>
    match symb_index_map ! id with
    | None =>
      Error [MSG "Cannot find the index for symbol: "; POS id]
    | Some idx =>
      let e := {| reloc_offset := dofs;
                  reloc_type := reloc_abs;
                  reloc_symb := idx;
                  reloc_addend := Ptrofs.unsigned ofs;
               |} in
      OK [e]
    end
  | _ =>
    OK []
  end.

(** Tranlsation of a list of initialization data and generate
    relocation entries *)

Definition acc_init_data r d :=
  do r' <- r;
  let '(dofs, rtbl) := r' in
  do ri <- transl_init_data dofs d;
  OK (dofs + init_data_size d, ri ++ rtbl).

Definition transl_init_data_list (l:list init_data) : res reloctable :=
  do rs <-
      fold_left acc_init_data l (OK (0, []));
  let '(_, rtbl) := rs in
  OK rtbl.


(** ** Translation of the program *)

Definition transl_sectable (stbl: sectable) :=
  match SeqTable.get sec_code_id stbl with
  | Some (sec_text code) =>
    match transl_code code with
    | Error e => Error e
    | OK codereloctable =>
      match SeqTable.get sec_data_id stbl with
      | Some (sec_data l) =>
        match transl_init_data_list l with
        | Error e => Error e
        | OK datareloctable =>
          OK (codereloctable, datareloctable)
        end
      | _ => Error (msg "Expected data section to be a sec_data")
      end
    end
  | _ => Error (msg "Expected code section to be a sec_text")
  end.

Definition id_eliminate (i:instruction):res (instruction):=
    match i with
  | Pjmp (inr id) sg =>
    OK (Pjmp (inr xH) sg)
  | Pcall (inr id) sg =>
    OK (Pcall (inr xH) sg)
  | Pmov_rs rd id =>
    OK (Pmov_rs rd xH)
  | Pmovl_rm rd (Addrmode rb ss (inr disp)) =>
    let '(id, ptrofs) := disp in
    OK (Pmovl_rm rd (Addrmode rb ss (inr (xH,ptrofs))))
  | Pmovl_mr (Addrmode rb ss (inr disp)) rs =>
    let '(id, ptrofs) := disp in
    OK (Pmovl_mr (Addrmode rb ss (inr (xH, ptrofs))) rs)
  (** Integer arithmetic *)
  | Pleal rd (Addrmode rb ss (inr disp))  =>
    let '(id, ptrofs) := disp in
    OK (Pleal rd (Addrmode rb ss (inr (xH, ptrofs))))
  (** Saving and restoring registers *)
  | Pmov_rm_a rd (Addrmode rb ss (inr disp)) =>  (**r like [Pmov_rm], using [Many64] chunk *)
    let '(id, ptrofs) := disp in
    OK (Pmov_rm_a rd (Addrmode rb ss (inr (xH, ptrofs))))
  | Pmov_mr_a (Addrmode rb ss (inr disp)) rs =>   (**r like [Pmov_mr], using [Many64] chunk *)
    let '(id, ptrofs) := disp in
    OK (Pmov_mr_a (Addrmode rb ss (inr (xH, ptrofs))) rs)
  | _ =>
    OK i
    end.

Definition acc_id_eliminate r i :=
  do r' <- r;
  do i' <- id_eliminate i;
    OK(i::r').

Definition transl_code' (c:code): res (code) :=
  do r <- fold_left acc_id_eliminate c (OK []);
    OK (rev r).

Definition transl_sectable' (stbl: sectable): res sectable :=
  match stbl with
    [sec_null; sec_text code; sec_data l] =>
    do code' <- transl_code' code;
    OK [sec_null; sec_text code'; sec_data l]
  | _ => Error (msg "Expected section table to be [null; text; data]")
  end.

End WITH_SYMB_INDEX_MAP.

Definition transf_program (p:program) : res program :=
  let map := gen_symb_index_map (p.(prog_symbtable)) in
  do (codereloc, datareloc) <- transl_sectable map (prog_sectable p);
    do sec' <- transl_sectable' (prog_sectable p);
  OK {| prog_defs := prog_defs p;
        prog_public := prog_public p;
        prog_main := prog_main p;
        prog_sectable := sec';
        prog_strtable := prog_strtable p;
        prog_symbtable := prog_symbtable p;
        prog_reloctables := Build_reloctable_map codereloc datareloc;
        prog_senv := prog_senv p;
     |}.
