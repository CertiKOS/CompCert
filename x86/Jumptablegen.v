(* *******************  *)
(* Author: Zhenguo Yin  *)
(* Date:   Aug 04, 2020 *)
(* *******************  *)
Require Import Coqlib Integers AST Maps.
Require Import Events.
Require Import Asm.
Require Import Errors.
Require Import Memtype.
Require Import RelocProgram.
Require Import Globalenvs.
Require Import SymbolString.
Require Import LocalLib.
Import ListNotations.

Set Implicit Arguments.

Local Open Scope error_monad_scope.

Definition jumptable : Type := (ident * option gdef) * list symbentry.

Definition labelofstoSymbol (ofsLst: Z) : symbentry :=
  let id := create_label_ident tt in
  {|symbentry_id := id;
    symbentry_bind := bind_local;
    symbentry_type := symb_notype;
    symbentry_value := ofsLst;
    symbentry_secindex := secindex_normal sec_code_id;
    symbentry_size := 0;
  |}.

Section WITH_SECS_SIZE.
  Variables (rodata: list init_data).
  
Definition transl_instr (i: instruction) (ofs:Z) :
  res (instruction * option (ident * list init_data * list symbentry)) :=
  let sz := instr_size i in
  match i with
  | Pjmptbl_rel r ofsLst =>
    let id := create_jump_table_ident tt in
    let addrLst := map (Zplus ((sz + ofs))) ofsLst in
    let symbLst := map labelofstoSymbol addrLst in
    let idLst := map (fun e => symbentry_id e) symbLst in
    let dataLst := map (fun id => Init_addrof id Ptrofs.zero) idLst in
    let disp := (id, Ptrofs.repr(0)) in
    let lblMem := (Addrmode None (Some(r,4)) (inr disp)) in
    let i' := Pjmp_m lblMem in
    OK (i', Some (id, dataLst, symbLst))
  | _ => OK(i, None)
  end.

Definition acc_instrs (r: res(Z * list instruction * list init_data * list symbentry))
           (i:instruction) :=
  do rs <- r;
  let '(acc_ofs, acc_code, acc_jmp_data, acc_jmp_symbl) := rs in
  do (i', res) <- transl_instr i acc_ofs;
  let code' := acc_code ++ [i'] in
  let ofs' := acc_ofs + instr_size i in
  match res with
  | Some jmp_tbl =>
    let '(tbl_id, tbl_data, lbl_symbl) := jmp_tbl in
    let tbl_e :=
        {|symbentry_id := tbl_id;
          symbentry_bind := bind_local;
          symbentry_type := symb_data;
          symbentry_value := init_data_list_size rodata +
                             init_data_list_size acc_jmp_data;
          symbentry_secindex := secindex_normal sec_rodata_id;
          symbentry_size := init_data_list_size tbl_data;
        |} in
    let jmp_data' := acc_jmp_data ++ tbl_data in
    let jmp_symbl' := acc_jmp_symbl ++ [tbl_e] ++ lbl_symbl in
    OK (ofs', code', jmp_data', jmp_symbl')
  | None =>
    OK (ofs', code', acc_jmp_data, acc_jmp_symbl)
  end.

(** Translation of a sequence of instructions in a function *)
Definition transl_code (c:code) : res (code * list init_data * list symbentry) :=
  do r <- fold_left acc_instrs c (OK(0,[],[],[]));
  let '(_, code, data, symb) := r in
  OK (code, data, symb).

End WITH_SECS_SIZE.

Definition compute_pad_size initd :=
  let sz := AST.init_data_list_size initd in
  (align sz alignw) - sz.
  
(** Generation of list of jump tables *)
Definition gen_jump_table (sctbl: sectable) (sytbl: symbtable)
  : res (sectable*symbtable) :=
  match sctbl with
  | [sec_rodata rdl; sec_data dl; sec_text code] =>
    (* translation of code to generate defs*)
    do r <- transl_code rdl code;
    let '(code', jmp_dl, jmp_syl) := r in
    (* pad jmpdl *)
    let psz := compute_pad_size jmp_dl in
    let jmp_dl_pad :=
        if zlt 0 psz then
          jmp_dl ++ [Init_space psz]
        else
          jmp_dl in
    let rdl' := rdl ++ jmp_dl_pad in
    let sytbl' := sytbl ++ jmp_syl in
    OK ([sec_rodata rdl'; sec_data dl; sec_text code'], sytbl')
  | _ => Error (msg "Expected the section table to be [sec_rodata; sec_data; sec_text]")
  end.
  
Definition transf_program (p: program) : res program :=
  do r <- gen_jump_table (prog_sectable p) (prog_symbtable p);
  let (sctabl, sytabl) := r in
  OK {| prog_defs := prog_defs p;
        prog_public := prog_public p;
        prog_main := prog_main p;
        prog_sectable := sctabl;
        prog_strtable := prog_strtable p;
        prog_symbtable := sytabl;
        prog_reloctables := prog_reloctables p;
        prog_senv := prog_senv p
     |}.
