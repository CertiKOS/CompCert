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

Definition addrmode_reloc_offset (a:addrmode) : Z :=
  addrmode_size_aux a.

(** Calculate the starting offset of the bytes
    that need to be relocated in an instruction *)
Definition instr_reloc_offset (i:instruction) : res Z :=
  match i with
  | Pmov_rs _ _ => OK 2
  | Pcall (inr _) _ => OK 1
  | Pjmp (inr _) _ => OK 1
  | Pjmp_m a
  | Pleal _ a
  | Pmovl_rm _ a
  | Pmovl_mr a _
  | Pmov_rm_a _ a
  | Pmov_mr_a a _
  | Pfldl_m a
  | Pfstpl_m a
  | Pflds_m a
  | Pfstps_m a
  | Pmovb_mr a _
  | Pmovb_rm _ a =>
    let aofs := addrmode_reloc_offset a in
    OK (1 + aofs)
  | Pmovw_mr a _
  | Pmovw_rm _ a
  | Pmovzb_rm _ a
  | Pmovsb_rm _ a
  | Pmovzw_rm _ a
  | Pmovsw_rm _ a =>
    let aofs := addrmode_reloc_offset a in
    OK (2 + aofs)
  | Pmovsd_fm _ a
  | Pmovsd_mf a _
  | Pmovss_fm _ a
  | Pmovss_mf a _
  | Pmovsq_rm _ a
  | Pmovsq_mr a _              
  | Pxorpd_fm _ a
  | Pxorps_fm _ a
  | Pandpd_fm _ a
  | Pandps_fm _ a =>
    let aofs := addrmode_reloc_offset a in
    OK (3 + aofs)
  | _ => Error [MSG "Calculation of relocation offset failed: Either there is no possible relocation location or the instruction ";
              MSG (instr_to_string i); MSG " is not supported yet by relocation"]
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
  | Pjmp_m (Addrmode rb ss (inr disp)) =>
    do e <- compute_instr_disp_relocentry sofs i disp;
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
    Error [MSG "Relocation failed: "; MSG (instr_to_string i); MSG " not supported yet"]   
  | Pmovl_mr (Addrmode rb ss (inr disp)) rs =>
    do e <- compute_instr_disp_relocentry sofs i disp;
    OK [e]
  | Pmovq_mr a rs =>
    Error [MSG "Relocation failed: "; MSG (instr_to_string i); MSG " not supported yet"]
  | Pmovsd_fm rd (Addrmode rb ss (inr disp)) =>
    do e <- compute_instr_disp_relocentry sofs i disp;
    OK [e]
  | Pmovsd_mf (Addrmode rb ss (inr disp)) r1 =>
    do e <- compute_instr_disp_relocentry sofs i disp;
    OK [e]
  | Pmovss_fm rd (Addrmode rb ss (inr disp)) =>
    do e <- compute_instr_disp_relocentry sofs i disp;
    OK [e]
  | Pmovss_mf (Addrmode rb ss (inr disp)) r1 =>
    do e <- compute_instr_disp_relocentry sofs i disp;
    OK [e]
  | Pfldl_m (Addrmode rb ss (inr disp)) => (**r [fld] double precision *)
    do e <- compute_instr_disp_relocentry sofs i disp;
    OK [e]
  | Pfstpl_m (Addrmode rb ss (inr disp)) => (**r [fstp] double precision *)
    do e <- compute_instr_disp_relocentry sofs i disp;
    OK [e]
  | Pflds_m (Addrmode rb ss (inr disp)) => (**r [fld] simple precision *)
    do e <- compute_instr_disp_relocentry sofs i disp;
    OK [e]
  | Pfstps_m (Addrmode rb ss (inr disp)) => (**r [fstp] simple precision *)
    do e <- compute_instr_disp_relocentry sofs i disp;
    OK [e]
  | Pxorpd_fm rd (Addrmode rb ss (inr disp)) =>
    do e <- compute_instr_disp_relocentry sofs i disp;
    OK [e]
  | Pxorps_fm rd (Addrmode rb ss (inr disp)) =>
    do e <- compute_instr_disp_relocentry sofs i disp;
    OK [e]
  | Pandpd_fm rd (Addrmode rb ss (inr disp)) =>
    do e <- compute_instr_disp_relocentry sofs i disp;
    OK [e]
  | Pandps_fm rd (Addrmode rb ss (inr disp)) =>
    do e <- compute_instr_disp_relocentry sofs i disp;
    OK [e]
    (** Moves with conversion *)
  | Pmovb_mr (Addrmode rb ss (inr disp)) rs =>    (**r [mov] (8-bit int) *)
    do e <- compute_instr_disp_relocentry sofs i disp;
    OK [e]
  | Pmovb_rm rd (Addrmode rb ss (inr disp)) =>    (**r [mov] (8-bit int) *)
    do e <- compute_instr_disp_relocentry sofs i disp;
    OK [e]       
  | Pmovw_mr (Addrmode rb ss (inr disp)) rs =>    (**r [mov] (16-bit int) *)
    do e <- compute_instr_disp_relocentry sofs i disp;
    OK [e]
  | Pmovw_rm rd (Addrmode rb ss (inr disp)) =>    (**r [mov] (16-bit int) *)
    do e <- compute_instr_disp_relocentry sofs i disp;
    OK [e]
  | Pmovzb_rm rd (Addrmode rb ss (inr disp)) =>
    do e <- compute_instr_disp_relocentry sofs i disp;
    OK [e]
  | Pmovsb_rm rd (Addrmode rb ss (inr disp)) =>
    do e <- compute_instr_disp_relocentry sofs i disp;
    OK [e]
  | Pmovzw_rm rd (Addrmode rb ss (inr disp)) =>
    do e <- compute_instr_disp_relocentry sofs i disp;
    OK [e]
  | Pmovsw_rm rd (Addrmode rb ss (inr disp)) =>
    do e <- compute_instr_disp_relocentry sofs i disp;
    OK [e]
  | Pmovsq_rm frd (Addrmode rb ss (inr disp)) =>
    do e <- compute_instr_disp_relocentry sofs i disp;
    OK [e]
  | Pmovsq_mr (Addrmode rb ss (inr disp)) frs =>
    do e <- compute_instr_disp_relocentry sofs i disp;
    OK [e]
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
    Error [MSG "Relocation failed:"; MSG (instr_to_string i); MSG "not supported yet"]
  | Pmovsd_mf_a a r1 =>  (**r like [Pmovsd_mf], using [Many64] chunk *)
    Error [MSG "Relocation failed:"; MSG (instr_to_string i); MSG "not supported yet"]
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
  match SecTable.get sec_code_id stbl with
  | Some (sec_text code) =>
    match transl_code code with
    | Error e => Error e
    | OK codereloctable =>
      match SecTable.get sec_data_id stbl with
      | Some (sec_data l) =>
        match transl_init_data_list l with
        | Error e => Error e
        | OK datareloctable =>
          match SecTable.get sec_rodata_id stbl with
          | Some (sec_rodata l') =>
            match transl_init_data_list l' with
            | Error e => Error e
            | OK rodatareloctable =>
              OK (codereloctable, datareloctable, rodatareloctable)
            end
          |_ => Error (msg "Expected rodata section to be a sec_rodata")
          end
        end
      | _ => Error (msg "Expected data section to be a sec_data")
      end
    end
  | _ => Error (msg "Expected code section to be a sec_text")
  end.

Fixpoint ok_builtin_arg {A} (ba: builtin_arg A) : bool :=
  match ba with
  | BA_addrglobal _ _
  | BA_loadglobal _ _ _ => false
  | BA_splitlong ba1 ba2 => ok_builtin_arg ba1 && ok_builtin_arg ba2
  | _ => true
  end.

Definition unsupported i :=
  match i with
  | Pmovq_rm _ _
  | Pmovq_mr _ _
  | Pmovsd_fm_a _ _
  | Pmovsd_mf_a _ _
  | Pleaq _ _
    => true
  | Pbuiltin _ args _ =>
    negb (forallb ok_builtin_arg args)
  | _ => false
  end.


Definition id_eliminate (i:instruction):res (instruction):=
  if unsupported i
  then Error [MSG "unsupported instruction: "; MSG (instr_to_string i); MSG " in id_eliminate"]
  else 
    match i with
  | Pjmp (inr id) sg =>
    OK (Pjmp (inr xH) sg)
  | Pjmp_m (Addrmode rb ss (inr disp)) =>
    let '(id, ptrofs) := disp in
    OK (Pjmp_m (Addrmode rb ss (inr (xH,ptrofs))))
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
  | Pfldl_m (Addrmode rb ss (inr disp)) =>
    let '(id, ptrofs) := disp in
    OK (Pfldl_m (Addrmode rb ss (inr (xH, ptrofs))))
  | Pfstpl_m (Addrmode rb ss (inr disp)) =>
    let '(id, ptrofs) := disp in
    OK (Pfstpl_m (Addrmode rb ss (inr (xH, ptrofs))))
  | Pflds_m (Addrmode rb ss (inr disp)) =>
    let '(id, ptrofs) := disp in
    OK (Pflds_m (Addrmode rb ss (inr (xH, ptrofs))))
  | Pfstps_m (Addrmode rb ss (inr disp)) =>
    let '(id, ptrofs) := disp in
    OK (Pfstps_m (Addrmode rb ss (inr (xH, ptrofs))))
  | Pmovsd_fm rd (Addrmode rb ss (inr disp)) =>
    let '(id, ptrofs) := disp in
    OK (Pmovsd_fm rd (Addrmode rb ss (inr (xH, ptrofs))))
  | Pmovsd_mf (Addrmode rb ss (inr disp)) rs =>
    let '(id, ptrofs) := disp in
    OK (Pmovsd_mf (Addrmode rb ss (inr (xH, ptrofs))) rs)
  | Pmovss_fm rd (Addrmode rb ss (inr disp)) =>
    let '(id, ptrofs) := disp in
    OK (Pmovss_fm rd (Addrmode rb ss (inr (xH, ptrofs))))
  | Pmovss_mf (Addrmode rb ss (inr disp)) rs =>
    let '(id, ptrofs) := disp in
    OK (Pmovss_mf (Addrmode rb ss (inr (xH, ptrofs))) rs)
  | Pxorpd_fm rd (Addrmode rb ss (inr disp)) =>
    let '(id, ptrofs) := disp in
    OK (Pxorpd_fm rd (Addrmode rb ss (inr (xH, ptrofs))))
  | Pxorps_fm rd (Addrmode rb ss (inr disp)) =>
    let '(id, ptrofs) := disp in
    OK (Pxorps_fm rd (Addrmode rb ss (inr (xH, ptrofs))))
  | Pandpd_fm rd (Addrmode rb ss (inr disp)) =>
    let '(id, ptrofs) := disp in
    OK (Pandpd_fm rd (Addrmode rb ss (inr (xH, ptrofs))))
  | Pandps_fm rd (Addrmode rb ss (inr disp)) =>
    let '(id, ptrofs) := disp in
    OK (Pandps_fm rd (Addrmode rb ss (inr (xH, ptrofs))))
  (** Moves with conversion *)
  | Pmovb_mr (Addrmode rb ss (inr disp)) rs =>
    let '(id, ptrofs) := disp in
    OK (Pmovb_mr (Addrmode rb ss (inr (xH, ptrofs))) rs)
  | Pmovb_rm rd (Addrmode rb ss (inr disp)) =>
    let '(id, ptrofs) := disp in
    OK (Pmovb_rm rd (Addrmode rb ss (inr (xH, ptrofs))))
  | Pmovw_mr (Addrmode rb ss (inr disp)) rs =>
    let '(id, ptrofs) := disp in
    OK (Pmovw_mr (Addrmode rb ss (inr (xH, ptrofs))) rs)
  | Pmovw_rm rd (Addrmode rb ss (inr disp)) =>
    let '(id, ptrofs) := disp in
    OK (Pmovw_rm rd (Addrmode rb ss (inr (xH, ptrofs))))
  | Pmovzb_rm rd (Addrmode rb ss (inr disp)) =>
    let '(id, ptrofs) := disp in
    OK (Pmovzb_rm rd (Addrmode rb ss (inr (xH, ptrofs))))
  | Pmovsb_rm rd (Addrmode rb ss (inr disp)) =>
    let '(id, ptrofs) := disp in
    OK (Pmovsb_rm rd (Addrmode rb ss (inr (xH, ptrofs))))
  | Pmovzw_rm rd (Addrmode rb ss (inr disp)) =>
    let '(id, ptrofs) := disp in
    OK (Pmovzw_rm rd (Addrmode rb ss (inr (xH, ptrofs))))
  | Pmovsw_rm rd (Addrmode rb ss (inr disp)) =>
    let '(id, ptrofs) := disp in
    OK (Pmovsw_rm rd (Addrmode rb ss (inr (xH, ptrofs))))
  | Pmovsq_rm rd (Addrmode rb ss (inr disp)) =>
    let '(id, ptrofs) := disp in
    OK (Pmovsq_rm rd (Addrmode rb ss (inr (xH, ptrofs))))
  | Pmovsq_mr (Addrmode rb ss (inr disp)) rs =>
    let '(id, ptrofs) := disp in
    OK (Pmovsq_mr (Addrmode rb ss (inr (xH, ptrofs))) rs)
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
    OK(i'::r').

Definition transl_code' (c:code): res (code) :=
  do r <- fold_left acc_id_eliminate c (OK []);
    OK (rev r).

Local Open Scope string_scope.
Definition print_section (s: section) :=
  match s with
  | sec_text _ => "text"
  | sec_data _ => "data"
  | sec_rodata _ => "rodata"
  | sec_bytes _ => "bytes"
  end.

Fixpoint print_sectable (stbl: sectable) :=
  match stbl with
  | [] => ""
  | s::r => String.append (print_section s) (String.append ";" (print_sectable r))
  end.

Definition transl_sectable' (stbl: sectable): res sectable :=
  match stbl with
    [sec_rodata l'; sec_data l; sec_text code] =>
    do code' <- transl_code' code;
    if zlt (code_size code') Ptrofs.max_unsigned
    then OK [sec_rodata l'; sec_data l; sec_text code']
    else Error (msg "code_size transl_sectable'")
  | _ => Error (msg "Expected section table to be [text; data], got " ++ msg (print_sectable stbl))
  end.



End WITH_SYMB_INDEX_MAP.

Definition transf_program (p:program) : res program :=
  let map := gen_symb_index_map (p.(prog_symbtable)) in
  do r <- transl_sectable map (prog_sectable p);
  let '(codereloc, datareloc, rodatareloc) := r in
  do sec' <- transl_sectable' (prog_sectable p);
  if list_norepet_dec ident_eq (List.map fst (prog_defs p))
  then
    if list_norepet_dec ident_eq (List.map symbentry_id (prog_symbtable p))
    then
    OK {| prog_defs := prog_defs p;
          prog_public := prog_public p;
          prog_main := prog_main p;
          prog_sectable := sec';
          prog_strtable := prog_strtable p;
          prog_symbtable := prog_symbtable p;
          prog_reloctables := Build_reloctable_map codereloc datareloc rodatareloc;
          prog_senv := prog_senv p;
       |}
    else
      Error (msg "Symbol entry identifiers repeat in symbol table")
  else
    Error (msg "Identifiers repeat in program definitions")
.
