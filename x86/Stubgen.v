(* *******************  *)
(* Author: Yuting Wang  *)
(* Date:   Sep 19, 2019 *)
(* *******************  *)

(** * Generation of the stub code *)

Require Import Coqlib Integers AST Maps.
Require Import Asm.
Require Import Errors.
Require Import RelocProgram Encode.
Require Import SeqTable.
Require Import Hex Bits.
Import Hex Bits.
Import ListNotations.


Set Implicit Arguments.

Local Open Scope error_monad_scope.
Local Open Scope hex_scope.
Local Open Scope bits_scope.

Definition create_start_stub : list byte := 
  let call_main_bytes := 
      (HB["E8"] :: zero_bytes 4) in             (* call   main *)
  let startsub := 
    [HB["89"]; HB["C3"];                                 (* mov    %eax,%ebx *)
     HB["B8"]; HB["01"]; HB["00"]; HB["00"]; HB["00"];   (* mov    $0x1,%eax *)
     HB["CD"]; HB["80"]]                                 (* int    $0x80 *)
  in
  call_main_bytes ++ startsub.

Definition create_start_stub_relocentry (main_symb:ident) (codesize:Z) : relocentry :=
  {| reloc_offset := codesize + 1; (** Points to the *main* symbol in * call main *  *)
     reloc_type   := reloc_rel;
     reloc_symb   := SymbIndex.interp main_symb;
     reloc_addend := -4
  |}.


Fixpoint find_symb (id:ident) (stbl:symbtable) : res Z := 
  match stbl with 
  | nil => Error (msg "cannot find the 'main' symbol")
  | e::l => 
    match symbentry_id e with
    | None => 
      do i <- find_symb id l;
      OK (i+1)
    | Some id' => 
      if ident_eq id id' then OK 0
      else do i <- find_symb id l;
        OK (i+1)
    end
  end.

Fixpoint find_symb' (id:ident) (stbl:symbtable) : res positive :=
  do i <- find_symb id stbl;
  if zlt i 1 
  then Error (msg "cannot find the 'main' symbol")
  else OK (Z.to_pos i).

(** ** Transformation of the program *)
Definition expand_code_section (sec:section) (instrs: list byte) :=
  match sec_type sec with 
  | sec_text =>
    do info' <- 
       match sec_info_ty sec as t 
             return interp_sec_info_type t -> res (interp_sec_info_type t)
       with
       | sec_info_byte => fun i => OK (i ++ instrs)
       | _ => fun i => Error (msg "Expandtion of section failed: section does not contain bytes")
       end (sec_info sec);
    let isz := Z.of_nat (length instrs) in
    OK {| sec_type := sec_type sec;
          sec_size := sec_size sec + isz;
          sec_info_ty := sec_info_ty sec;
          sec_info := info' |}
  | _ =>
    Error (msg "Expandtion of section failed: section does not contain instructions")
  end.

Definition append_reloc_entry (t: reloctable) (e:relocentry) :=
  (t ++ [e]).


Definition transf_program (p:program) : res program :=
  do main_symb <- find_symb' (prog_main p) (prog_symbtable p);
  match SeqTable.get (SecIndex.interp sec_code_id) (prog_sectable p) with
  | None => Error (msg "No .text section found")
  | Some txt_sec =>
    do txt_sec' <- expand_code_section txt_sec create_start_stub;
    let e := create_start_stub_relocentry main_symb (sec_size txt_sec) in
    do rtbl' <- 
       match PTree.get sec_code_id (prog_reloctables p) with
       | None => Error (msg "Cannot find the relocation table for .text")
       | Some rtbl => 
         OK (append_reloc_entry rtbl e)
       end;
    match SeqTable.set (SecIndex.interp sec_code_id) txt_sec' (prog_sectable p)
    with
    | Some stbl =>
      let rtbls := PTree.set sec_code_id rtbl' (prog_reloctables p) in
      let p':=
          {| prog_defs := prog_defs p;
            prog_public := prog_public p;
            prog_main := prog_main p;
            prog_sectable := stbl;
            prog_strtable := prog_strtable p;
            prog_symbtable := prog_symbtable p;
            prog_reloctables := rtbls;
            prog_senv := prog_senv p;
         |} in
      let len := (length (prog_sectable p')) in
      if beq_nat len 3 then
        OK p'
      else
        Error [MSG "In SymtableEncode: Number of sections is incorrect (not 3): "; POS (Pos.of_nat len)]
    | _ =>
      Error (msg "Update of code section and its relocation table fails")
    end
  end.
    