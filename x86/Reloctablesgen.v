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

(* 
Definition instr_reloc_offset (i:instruction) : res Z :=
  match i with
  | Pmov_rs _ _ => OK 2
  | Pcall (inr _) _ => OK 1
  | Pjmp (inr _) _ => OK 1
  | Pleal _ a
  | Pmovl_rm _ a
  | Pmovl_mr a _
  | Pmov_rm_a _ a
  | Pmov_mr_a a _ =>
    let aofs := addrmode_reloc_offset a in
    OK (1 + aofs)
  | _ => Error (msg "In reloctablesgen1: Calculation of relocation offset failed: Either there is no possible relocation location or the instruction is not supported yet by relocation")
  end. *)

  Definition instr_reloc_offset (i:instruction) : res Z :=
  match i with
  | Pmov_rs _ _ => OK 2
  | Pcall (inr _) _ => OK 1
  | Pjmp (inr _) _ => OK 1
  | Pleal rd a =>
    let aofs := addrmode_reloc_offset a in
    OK (1 + aofs)
  | Pmovl_rm _ a =>
    let aofs := addrmode_reloc_offset a in
    OK (1 + aofs)
  | Pmovl_mr a _ =>
    let aofs := addrmode_reloc_offset a in
    OK (1 + aofs)
  | Pmov_rm_a _ a =>
    let aofs := addrmode_reloc_offset a in
    OK (1 + aofs)
  | Pmov_mr_a a _ =>
    let aofs := addrmode_reloc_offset a in
      OK (1 + aofs)
  | Pmovsd_fm_a frd a
  | Pmovsd_fm frd a =>
    let aofs := addrmode_reloc_offset a in
      OK (3 + aofs)
  | Pmovsd_mf_a a fr1
  | Pmovsd_mf a fr1 =>
    let aofs := addrmode_reloc_offset a in
      OK (3 + aofs)
  | Pmovss_fm frd a =>
    let aofs := addrmode_reloc_offset a in
      OK (3 + aofs)
  | Pmovss_mf a fr1 =>
    let aofs := addrmode_reloc_offset a in
      OK (3 + aofs)
  | Pfldl_m a =>
    let aofs := addrmode_reloc_offset a in
      OK (1 + aofs)
  | Pfstpl_m a =>
    let aofs := addrmode_reloc_offset a in
      OK (1 + aofs)
  | Pflds_m a =>
    let aofs := addrmode_reloc_offset a in
      OK (1 + aofs)
  | Pfstps_m a =>
    let aofs := addrmode_reloc_offset a in
      OK (1 + aofs)
  | Pmovb_mr a rs =>
    let aofs := addrmode_reloc_offset a in
      OK (1 + aofs)
  | Pmovw_mr a rs =>
    let aofs := addrmode_reloc_offset a in
      OK (2 + aofs)
  | Pmovzb_rm rd a =>
    let aofs := addrmode_reloc_offset a in
      OK (2 + aofs)
  | Pmovzw_rm rd a =>
    let aofs := addrmode_reloc_offset a in
      OK (2 + aofs)
  | Pmovsb_rm rd a =>
    let aofs := addrmode_reloc_offset a in
      OK (2 + aofs)
  | Pmovsw_rm rd a =>
    let aofs := addrmode_reloc_offset a in
      OK (2 + aofs)   
  (* | Pmovsb_rm rd a =>
    let aofs := addrmode_reloc_offset a in
      OK (2 + aofs)                    *)
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



Definition transl_instr' (sofs:Z) (i: instruction) : res (list relocentry) :=
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
  (** Moves with conversion *)
  | Pmovb_mr (Addrmode rb ss (inr disp)) rs =>    (**r [mov] (8-bit int) *)
    do e <- compute_instr_disp_relocentry sofs i disp;
      OK [e]
  | Pmovw_mr (Addrmode rb ss (inr disp)) rs =>    (**r [mov] (16-bit int) *)
    do e <- compute_instr_disp_relocentry sofs i disp;
      OK [e]
  | Pmovzb_rm rd (Addrmode rb ss (inr disp)) =>
    do e <- compute_instr_disp_relocentry sofs i disp;
      OK [e]
  | Pmovsb_rm rd (Addrmode rb ss (inr disp)) =>
    do e <- compute_instr_disp_relocentry sofs i disp;
      OK [e]
  (* Error [MSG "Relocation failed: "; MSG (instr_to_string i); MSG " not supported yet"] *)
  | Pmovzw_rm rd (Addrmode rb ss (inr disp)) =>
    do e <- compute_instr_disp_relocentry sofs i disp;
      OK [e]    
  | Pmovsw_rm rd (Addrmode rb ss (inr disp)) =>
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
  | Pmovsd_fm_a rd (Addrmode rb ss (inr disp)) => (**r like [Pmovsd_fm], using [Many64] chunk *)
    do e <- compute_instr_disp_relocentry sofs i disp;
      OK [e]
  | Pmovsd_mf_a (Addrmode rb ss (inr disp)) r1 =>  (**r like [Pmovsd_mf], using [Many64] chunk *)
    do e <- compute_instr_disp_relocentry sofs i disp;
      OK [e]
  | _ =>
    OK []
  end.


Definition ready_for_proof (i: instruction) : bool :=
  match i with
  | Pjmp_l_rel jofs => true
  | Pjcc_rel c jofs => true
  | Pcall (inr id) _ => true
  | Pleal rd a => true
  | Pxorl_r rd => true
  | Paddl_ri rd n => true
  | Psubl_ri rd n => true
  | Psubl_rr rd r1 => true
  | Pmovl_ri rd n => true
  | Pmov_rr rd r1 => true
  | Pmovl_rm rd a => true
  | Pmovl_mr a rs => true
  | Pmov_rm_a rd a => true
  | Pmov_mr_a a rs => true
  | Pmov_rs rd id => true
  | Ptestl_rr r1 r2 => true
  | Pret => true
  | Pimull_rr rd r1 => true
  | Pimull_ri rd n => true
  | Pcmpl_rr r1 r2 => true
  | Pcmpl_ri r1 n => true
  | Pcltd => true
  | Pidivl r1 => true
  | Psall_ri rd n => true
  | Plabel _ => true
  | Pnop => true
  | _ => false
  end.

Section TRANSL_INSTR.
  Variable more_inst:bool.
  
  Definition transl_instr (sofs:Z) (i: instruction) : res (list relocentry) :=
    if more_inst then
      transl_instr' sofs i
    else if ready_for_proof i then
           transl_instr' sofs i
         else
           Error[MSG (instr_to_string i);MSG" not ready for relocation"].







(* 
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
  end. *)



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
          OK (codereloctable, datareloctable)
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
  (* | Pmovsd_fm_a _ _
  | Pmovsd_mf_a _ _ *)
  (* | Pmovsb_rm _ _ *)
  (* | Pmovzw_rm _ _
  | Pmovsw_rm _ _ *)
  | Pleaq _ _
    => true
  | Pbuiltin _ args _ =>
    negb (forallb ok_builtin_arg args)
  | _ => false
  end.

Definition id_eliminate' (i:instruction):res (instruction):=
  if unsupported i
  then Error (msg "unsupported instruction in id_eliminate")
  else 
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
    (** Moves with conversion *)
    | Pmovb_mr (Addrmode rb ss (inr disp)) rs =>
      let '(id, ptrofs) := disp in
      OK (Pmovb_mr (Addrmode rb ss (inr (xH, ptrofs))) rs)
    | Pmovzb_rm rd (Addrmode rb ss (inr disp)) =>
      let '(id, ptrofs) := disp in
      OK (Pmovzb_rm rd (Addrmode rb ss (inr (xH, ptrofs))))
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
    | Pmovsd_fm_a rd (Addrmode rb ss (inr disp)) => (**r like [Pmovsd_fm], using [Many64] chunk *)
      let '(id, ptrofs) := disp in
      OK (Pmovsd_fm_a rd (Addrmode rb ss (inr (xH, ptrofs))))
    | Pmovsd_mf_a (Addrmode rb ss (inr disp)) r1 =>  (**r like [Pmovsd_mf], using [Many64] chunk *)
      let '(id, ptrofs) := disp in
      OK (Pmovsd_mf_a (Addrmode rb ss (inr (xH, ptrofs))) r1)
    | Pmovzw_rm rd (Addrmode rb ss (inr disp)) =>
      let '(id, ptrofs) := disp in
      OK (Pmovzw_rm rd (Addrmode rb ss (inr (xH, ptrofs))))

    | Pmovsw_rm rd (Addrmode rb ss (inr disp)) =>
      let '(id, ptrofs) := disp in
      OK (Pmovsw_rm rd (Addrmode rb ss (inr (xH, ptrofs))))
    | _ =>
      OK i
    end.

Definition id_eliminate (i:instruction):res (instruction):=
  if more_inst then
    id_eliminate' i
  else if ready_for_proof i then
         id_eliminate' i
       else
         Error[MSG (instr_to_string i);MSG" not ready for id_eliminate"].
    


(* Definition id_eliminate (i:instruction):res (instruction):= *)
  (* if unsupported i *)
  (* then Error (msg "unsupported instruction in id_eliminate") *)
  (* else  *)
  (*   match i with *)
  (* | Pjmp (inr id) sg => *)
  (*   OK (Pjmp (inr xH) sg) *)
  (* | Pcall (inr id) sg => *)
  (*   OK (Pcall (inr xH) sg) *)
  (* | Pmov_rs rd id => *)
  (*   OK (Pmov_rs rd xH) *)
  (* | Pmovl_rm rd (Addrmode rb ss (inr disp)) => *)
  (*   let '(id, ptrofs) := disp in *)
  (*   OK (Pmovl_rm rd (Addrmode rb ss (inr (xH,ptrofs)))) *)
  (* | Pmovl_mr (Addrmode rb ss (inr disp)) rs => *)
  (*   let '(id, ptrofs) := disp in *)
  (*   OK (Pmovl_mr (Addrmode rb ss (inr (xH, ptrofs))) rs) *)
  (* (** Integer arithmetic *) *)
  (* | Pleal rd (Addrmode rb ss (inr disp))  => *)
  (*   let '(id, ptrofs) := disp in *)
  (*   OK (Pleal rd (Addrmode rb ss (inr (xH, ptrofs)))) *)
  (* (** Saving and restoring registers *) *)
  (* | Pmov_rm_a rd (Addrmode rb ss (inr disp)) =>  (**r like [Pmov_rm], using [Many64] chunk *) *)
  (*   let '(id, ptrofs) := disp in *)
  (*   OK (Pmov_rm_a rd (Addrmode rb ss (inr (xH, ptrofs)))) *)
  (* | Pmov_mr_a (Addrmode rb ss (inr disp)) rs =>   (**r like [Pmov_mr], using [Many64] chunk *) *)
  (*   let '(id, ptrofs) := disp in *)
  (*   OK (Pmov_mr_a (Addrmode rb ss (inr (xH, ptrofs))) rs) *)
  (* | _ => *)
  (*   OK i *)
  (*   end. *)

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
  | sec_bytes _ => "bytes"
  end.

Fixpoint print_sectable (stbl: sectable) :=
  match stbl with
  | [] => ""
  | s::r => String.append (print_section s) (String.append ";" (print_sectable r))
  end.

Definition transl_sectable' (stbl: sectable): res sectable :=
  match stbl with
    [sec_data l; sec_text code] =>
    do code' <- transl_code' code;
    if zlt (code_size code') Ptrofs.max_unsigned
    then OK [sec_data l; sec_text code']
    else Error (msg "code_size transl_sectable'")
  | _ => Error (msg "Expected section table to be [text; data], got " ++ msg (print_sectable stbl))
  end.

End TRANSL_INSTR.

End WITH_SYMB_INDEX_MAP.

Definition transf_program(more_inst:bool) (p:program) : res program :=
  let map := gen_symb_index_map (p.(prog_symbtable)) in
  do (codereloc, datareloc) <- transl_sectable map more_inst (prog_sectable p);
  do sec' <- transl_sectable' more_inst (prog_sectable p);
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
          prog_reloctables := Build_reloctable_map codereloc datareloc;
          prog_senv := prog_senv p;
       |}
    else
      Error (msg "Symbol entry identifiers repeat in symbol table")
  else
    Error (msg "Identifiers repeat in program definitions")
.
