(* *******************  *)
(* Author: Yuting Wang  *)
(* Date:   Sep 23, 2019 *)
(* *******************  *)

(** * Generation of the section header string table *)
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


(** The default shstrtab is '.data .text .symtab .reladata .relatext .shstrtab .strtab ' *)
Local Open Scope string_byte_scope.
Definition data_str := HB["00"] :: SB[".data"].
Definition text_str := HB["00"] :: SB[".text"].
Definition symtab_str := HB["00"] :: SB[".symtab"].
Definition reladata_str := HB["00"] :: SB[".reladata"].
Definition relatext_str := HB["00"] :: SB[".relatext"].
Definition shstrtab_str := HB["00"] :: SB[".shstrtab"].
Definition strtab_str := HB["00"] :: SB[".strtab"].


Definition default_shstrtab := 
  data_str ++ 
  text_str ++
  symtab_str ++
  reladata_str ++
  relatext_str ++
  shstrtab_str ++
  strtab_str ++ [HB["00"]].

Definition shstrtab_sec_size := Z.of_nat (length (default_shstrtab)).

Definition data_str_ofs := 1.
Definition text_str_ofs := data_str_ofs + (Z.of_nat (length data_str)).
Definition symtab_str_ofs := text_str_ofs + (Z.of_nat (length text_str)).
Definition reladata_str_ofs := symtab_str_ofs + (Z.of_nat (length symtab_str)).
Definition relatext_str_ofs := reladata_str_ofs + (Z.of_nat (length reladata_str)).
Definition shstrtab_str_ofs := relatext_str_ofs + (Z.of_nat (length relatext_str)).
Definition strtab_str_ofs := shstrtab_str_ofs + (Z.of_nat (length shstrtab_str)).


Definition create_shstrtab_section :=
  {| sec_type := sec_strtbl;
     sec_size := Z.of_nat (List.length default_shstrtab);
     sec_info_ty := sec_info_byte;
     sec_info := default_shstrtab;
  |}.

Definition transf_program (p:program) : res program :=
  let sec := create_shstrtab_section in
  OK {| prog_defs := p.(prog_defs);
        prog_public := p.(prog_public);
        prog_main := p.(prog_main);
        prog_sectable := p.(prog_sectable) ++ [sec];
        prog_strtable := p.(prog_strtable);
        prog_symbtable := p.(prog_symbtable);
        prog_reloctables := p.(prog_reloctables);
        prog_senv := p.(prog_senv);
     |}.