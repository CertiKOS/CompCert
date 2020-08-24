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


(** The default shstrtab is '.data .text .symtab .rela.data .rela.text .shstrtab .strtab ' *)
Local Open Scope string_byte_scope.
Definition bss_str := SB[".bss"] ++ [HB["00"]].
Definition rodata_str := SB[".rodata"] ++ [HB["00"]].
Definition data_str := SB[".data"] ++ [HB["00"]].
Definition text_str := SB[".text"] ++ [HB["00"]].
Definition symtab_str := SB[".symtab"] ++ [HB["00"]].
Definition relabss_str := SB[".rela.bss"] ++ [HB["00"]].
Definition relarodata_str := SB[".rela.rodata"] ++ [HB["00"]].
Definition reladata_str := SB[".rela.data"] ++ [HB["00"]].
Definition relatext_str := SB[".rela.text"] ++ [HB["00"]].
Definition shstrtab_str := SB[".shstrtab"] ++ [HB["00"]].
Definition strtab_str := SB[".strtab"] ++ [HB["00"]].


Definition default_shstrtab :=
  [HB["00"]] ++
  bss_str ++
  rodata_str ++
  data_str ++
  text_str ++
  symtab_str ++
  relabss_str ++
  relarodata_str ++
  reladata_str ++
  relatext_str ++
  shstrtab_str ++
  strtab_str.

Definition shstrtab_sec_size := Z.of_nat (length (default_shstrtab)).

Definition bss_str_ofs := 1.
Definition rodata_str_ofs := bss_str_ofs + (Z.of_nat (length bss_str)).
Definition data_str_ofs := rodata_str_ofs + (Z.of_nat (length rodata_str)).
Definition text_str_ofs := data_str_ofs + (Z.of_nat (length data_str)).
Definition symtab_str_ofs := text_str_ofs + (Z.of_nat (length text_str)).
Definition relabss_str_ofs := symtab_str_ofs + (Z.of_nat (length symtab_str)).
Definition relarodata_str_ofs := relabss_str_ofs + (Z.of_nat (length relabss_str)).
Definition reladata_str_ofs := relarodata_str_ofs + (Z.of_nat (length relarodata_str)).
Definition relatext_str_ofs := reladata_str_ofs + (Z.of_nat (length reladata_str)).
Definition shstrtab_str_ofs := relatext_str_ofs + (Z.of_nat (length relatext_str)).
Definition strtab_str_ofs := shstrtab_str_ofs + (Z.of_nat (length shstrtab_str)).

Definition create_shstrtab_section :=
  sec_bytes default_shstrtab.

Definition transf_program (p:program) : res program :=
  let sec := create_shstrtab_section in
  if beq_nat (length (prog_sectable p)) 11%nat then
  OK {| prog_defs := p.(prog_defs);
        prog_public := p.(prog_public);
        prog_main := p.(prog_main);
        prog_sectable := p.(prog_sectable) ++ [sec];
        prog_strtable := p.(prog_strtable);
        prog_symbtable := p.(prog_symbtable);
        prog_reloctables := prog_reloctables p;
        prog_senv := p.(prog_senv);
     |} else Error (msg "Not enough sections before shstr table encoding").
