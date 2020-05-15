(* *******************  *)


(* *******************  *)

(** * Encoding of the relocation tables into sections *)

Require Import Coqlib Integers AST Maps.
Require Import Asm.
Require Import Errors.
Require Import RelocProgram Encode.
Require Import SeqTable Memdata.
Require Import Hex Bits.
Import Hex Bits.
Import ListNotations.

Set Implicit Arguments.

Local Open Scope error_monad_scope.
Local Open Scope hex_scope.
Local Open Scope bits_scope.

(** Relocation entry definition:

    typedef struct {
      Elf32_Addr     r_offset;
      Elf32_Word     r_info;
    }
*)

Definition encode_reloctype (t:reloctype) :=
  match t with
  | reloc_null => 0     (* R_386_NONE *)
  | reloc_abs  => 1     (* R_386_32 *)
  | reloc_rel  => 2     (* R_386_PC32 *)
  end.


Definition encode_reloc_info (t:reloctype) (symb:N) : list byte :=
  let te := encode_reloctype t in
  let se := Z.of_N symb in
  encode_int32 (se * (Z.pow 2 8) + te).

Definition encode_relocentry (e:relocentry) : list byte :=
  let r_offset_bytes := encode_int32 (reloc_offset e) in
  let r_info_bytes := encode_reloc_info (reloc_type e) (reloc_symb e) in
  (r_offset_bytes ++ r_info_bytes).

Definition encode_reloctable (t:reloctable) : list byte :=
    fold_right (fun e bytes => (encode_relocentry e) ++ bytes)
             [] t.

Definition create_reloctable_section (t:reloctable) : section :=
  let bytes := encode_reloctable t in
  sec_bytes bytes.
  

Definition create_reloctables_sections p : list section :=
  [create_reloctable_section (reloctable_data (prog_reloctables p));
     create_reloctable_section (reloctable_code (prog_reloctables p))].

(** Transforma the program *)
Definition transf_program p : res program :=
  let s := create_reloctables_sections p in
  let sect := prog_sectable p ++ s in
  if beq_nat (length sect) 7 then
    OK {| prog_defs := prog_defs p;
          prog_public := prog_public p;
          prog_main := prog_main p;
          prog_sectable := (prog_sectable p) ++ s;
          prog_strtable := (prog_strtable p);
          prog_symbtable := prog_symbtable p;
          prog_reloctables := prog_reloctables p;
          prog_senv := prog_senv p;
       |}
  else Error [].
