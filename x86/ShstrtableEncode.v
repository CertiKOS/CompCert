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
Definition data_str := SB[".data"] ++ [HB["00"]].
Definition text_str := SB[".text"] ++ [HB["00"]].
Definition symtab_str := SB[".symtab"] ++ [HB["00"]].
Definition reladata_str := SB[".rela.data"] ++ [HB["00"]].
Definition relatext_str := SB[".rela.text"] ++ [HB["00"]].
Definition shstrtab_str := SB[".shstrtab"] ++ [HB["00"]].
Definition strtab_str := SB[".strtab"] ++ [HB["00"]].


Definition default_shstrtab :=
  [HB["00"]] ++
  data_str ++
  text_str ++
  symtab_str ++
  reladata_str ++
  relatext_str ++
  shstrtab_str ++
  strtab_str.

Definition shstrtab_sec_size := Z.of_nat (length (default_shstrtab)).

Definition data_str_ofs := 1.
Definition text_str_ofs := data_str_ofs + (Z.of_nat (length data_str)).
Definition symtab_str_ofs := text_str_ofs + (Z.of_nat (length text_str)).
Definition reladata_str_ofs := symtab_str_ofs + (Z.of_nat (length symtab_str)).
Definition relatext_str_ofs := reladata_str_ofs + (Z.of_nat (length reladata_str)).
Definition shstrtab_str_ofs := relatext_str_ofs + (Z.of_nat (length relatext_str)).
Definition strtab_str_ofs := shstrtab_str_ofs + (Z.of_nat (length shstrtab_str)).

Definition create_shstrtab_section :=
  sec_bytes default_shstrtab.

Definition transf_program (p:program) : res program :=
  let sec := create_shstrtab_section in
  if beq_nat (length (prog_sectable p)) 7%nat then
  OK {| prog_defs := p.(prog_defs);
        prog_public := p.(prog_public);
        prog_main := p.(prog_main);
        prog_sectable := p.(prog_sectable) ++ [sec];
        prog_strtable := p.(prog_strtable);
        prog_symbtable := p.(prog_symbtable);
        prog_reloctables := prog_reloctables p;
        prog_senv := p.(prog_senv);
     |} else Error (msg "Not enough sections before shstr table encoding").
