(* *******************  *)
(* Author: Author C  *)
(* Date:   Sep 23, 2019 *)
(* *******************  *)

(** * Generation of the string table *)
Require Import Coqlib Integers AST Maps.
Require Import Asm.
Require Import Errors.
Require Import RelocProgram Encode.
Require Import SeqTable Memdata.
Require Import SymbolString.
Require Import Hex Bits.
Import Hex Bits.
Import ListNotations.
Require Import SymbtableEncode StrtableEncode ShstrtableEncode ReloctablesEncode.
Set Implicit Arguments.

Local Open Scope error_monad_scope.
Local Open Scope hex_scope.
Local Open Scope bits_scope.



Definition transf_program (p:program) : res program :=
  let symbols := fold_right acc_symbols [] (prog_symbtable p) in
  do r <- get_strings_map_bytes symbols;
    let '(strmap, sbytes) := r in
    let strsec := create_strtab_section sbytes in
    do symsec <- create_symbtable_section strmap (prog_symbtable p);
      let datarelocsec := create_reloctable_section (reloctable_data (prog_reloctables p)) in
      let coderelocsec := create_reloctable_section (reloctable_code (prog_reloctables p)) in
      let shstrsec := create_shstrtab_section in
      let p' :=
          {| prog_defs := p.(prog_defs);
             prog_public := p.(prog_public);
             prog_main := p.(prog_main);
             prog_sectable :=
               p.(prog_sectable) ++ [strsec; symsec; datarelocsec; coderelocsec; shstrsec];
             prog_strtable := strmap;
             prog_symbtable := p.(prog_symbtable);
             prog_reloctables := prog_reloctables p;
             prog_senv := p.(prog_senv);
          |} in
      let len := (length (prog_sectable p')) in
      if beq_nat len 8 then
        OK p'
      else
        Error [MSG "In TablesEncode: number of sections is incorrect (not 8): "; POS (Pos.of_nat len)].

