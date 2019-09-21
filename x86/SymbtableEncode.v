(* *******************  *)
(* Author: Yuting Wang  *)
(* Date:   Sep 21, 2019 *)
(* *******************  *)

(** * Encoding of the symbol table into a section *)

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


(** Symbol entry definition:

   typedef struct {
   Elf32_Word     st_name;
   Elf32_Addr     st_value;
   Elf32_Word     st_size;
   unsigned char  st_info;
   unsigned char  st_other;
   Elf32_Half     st_shndx;
   } Elf32_Sym

*)

Definition encode_symbtype (t:symbtype) :=
  match t with
  | symb_func => 2
  | symb_data => 1
  | symb_notype => 0
  end.

Definition symb_glob_bind := 1.

Definition encode_glob_symb_info (t:symbtype) := 
  symb_glob_bind * (Z.pow 2 4) + encode_symbtype t.

Definition encode_secindex (i:secindex) :=
  let shn_comm := HZ["FFF2"] in
  let shn_undef := 0 in 
  let v := 
      match i with
      | secindex_comm => shn_comm
      | secindex_undef => shn_undef
      | secindex_normal p => Z.pos p
      end in
  encode_int 2 v.

Definition encode_symbentry (e:symbentry) : list byte :=
  let st_name_bytes := zero_bytes 4 in (** Symbol names are not filled in yet at this point *)
  let st_value_bytes := encode_int32 (symbentry_value e) in
  let st_size_bytes := encode_int32 (symbentry_size e) in
  let st_info_bytes := 
      bytes_of_int 1 (encode_glob_symb_info (symbentry_type e)) in
  let st_other_bytes := [Byte.repr 0] in
  let st_shndx_bytes := encode_secindex (symbentry_secindex e) in
  (st_name_bytes ++ st_value_bytes ++ st_size_bytes ++
   st_info_bytes ++ st_other_bytes ++ st_shndx_bytes).
  
Definition encode_symbtable (t:symbtable) : list byte :=
  fold_right (fun '(_,e) bytes => (encode_symbentry e) ++ bytes)
             [] t.

Definition create_symbtable_section (t:symbtable) : section :=
  let bytes := encode_symbtable t in
  {| sec_type := sec_symbtbl;
     sec_size := Z.of_nat (length bytes);
     sec_info_ty := sec_info_byte;
     sec_info := bytes;
  |}.

(** Transform the program *)
Definition transf_program p : program :=
  let t := prog_symbtable p in
  let s := create_symbtable_section t in
  {| prog_defs := prog_defs p;
     prog_public := prog_public p;
     prog_main := prog_main p;
     prog_sectable := (prog_sectable p) ++ [s];
     prog_symbtable := prog_symbtable p;
     prog_reloctables := (prog_reloctables p);
     prog_senv := prog_senv p;
  |}.