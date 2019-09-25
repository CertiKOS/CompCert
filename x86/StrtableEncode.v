(* *******************  *)
(* Author: Yuting Wang  *)
(* Date:   Sep 23, 2019 *)
(* *******************  *)

(** * Generation of the string table *)
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


(** This an external function in ML for 
    finding the strings associated with the global symbols *)
Parameter find_symbol_string_bytes : ident -> res (list byte).

Definition get_strings_map_bytes (symbols: list ident) : res (PTree.t Z * list byte) :=
  do idbytes <-
     fold_right (fun id r =>
                   do idbytes <- r;
                   do bytes <- find_symbol_string_bytes id;
                   OK ((id, HB["00"] :: bytes) :: idbytes)) (OK []) symbols;
  let '(strmap, _) := fold_left (fun '(map,sz) '(id, bytes) => 
                                   let map' := PTree.set id (sz+1) map in
                                   let sz'  := sz + Z.of_nat(length bytes) in
                                   (map', sz'))
                                idbytes (PTree.empty Z, 0) in
  let sbytes := fold_right (fun '(id,bytes) acc => bytes ++ acc) [] idbytes in
  OK (strmap, sbytes ++ [HB["00"]]).
                             
Definition create_strtab_section (strs: list byte) :=
  {| sec_type := sec_strtbl;
     sec_size := Z.of_nat (List.length strs);
     sec_info_ty := sec_info_byte;
     sec_info := strs
  |}.

Definition transf_program (p:program) : res program :=
  let symbols := 
      fold_right (fun e ids => 
                    match symbentry_id e with
                    | None => ids
                    | Some id => id :: ids
                    end) [] (prog_symbtable p) in
  do r <- get_strings_map_bytes symbols;
  let '(strmap, sbytes) := r in
  let strsec := create_strtab_section sbytes in
  let p' :=
      {| prog_defs := p.(prog_defs);
        prog_public := p.(prog_public);
        prog_main := p.(prog_main);
        prog_sectable := p.(prog_sectable) ++ [strsec];
        prog_strtable := strmap;
        prog_symbtable := p.(prog_symbtable);
        prog_reloctables := p.(prog_reloctables);
        prog_senv := p.(prog_senv);
     |} in
  let len := (length (prog_sectable p')) in
  if beq_nat len 4 then
    OK p'
  else
    Error [MSG "In Strtablegen: number of sections is incorrect (not 4): "; POS (Pos.of_nat len)].