(* *******************  *)
(* Author: Pierre Wilke  *)
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

Record valid_relocentry (e: relocentry) :=
  {
    reloc_offset_range: 0 <= reloc_offset e < 2 ^ 32;
    reloc_symb_range: Z.of_N (reloc_symb e) < two_p 24;
    reloc_addend_range: 0 = reloc_addend e;
  }.

Definition valid_relocentry_dec: forall re, {valid_relocentry re} + {~ valid_relocentry re}.
Proof.
  intros.
  destruct (intv_dec 0 (2 ^ 32) (reloc_offset re)).
  destruct (zlt (Z.of_N (reloc_symb re)) (two_p 24)).
  destruct (zeq 0 (reloc_addend re)).
  left; constructor; auto.
  all: right; inversion 1; congruence.
Defined.

Definition reloctables_ok_dec: forall rtbls,
    {forall id, Forall valid_relocentry ((get_reloctable id) rtbls) }
    + {~ forall id, Forall valid_relocentry ((get_reloctable id) rtbls) }.
Proof.
  intros.
  destruct (Forall_dec _ (valid_relocentry_dec) (get_reloctable RELOC_CODE rtbls)).
  destruct (Forall_dec _ (valid_relocentry_dec) (get_reloctable RELOC_DATA rtbls)).
  left; destruct id; auto.
  right; intro A; apply n; auto.
  right; intro A; apply n; auto.
Defined.

Require Import SymbtableDecode.

Definition valid_secindex_dec: forall si, {valid_secindex si} + {~valid_secindex si}.
Proof.
  destruct si. 2-3: left; constructor.
  destruct (zlt 0 (Z.of_N idx)). destruct (zlt (Z.of_N idx) (HZ[ "FFF2"])).
  left; constructor; auto.
  all: right; inversion 1; omega.
Defined.

Definition valid_symbentry_dec: forall strmap se, {valid_symbentry strmap se} + {~ valid_symbentry strmap se}.
Proof.
  intros.
  destruct (intv_dec 0 (two_p 32) (symbentry_size se)).
  destruct (intv_dec 0 (two_p 32) (symbentry_value se)).
  destruct (strmap ! (symbentry_id se)) as [si|] eqn:STR.
  destruct (intv_dec 0 (two_p 32) si).
  destruct (valid_secindex_dec (symbentry_secindex se)).
  left; constructor; eauto.
  all: right; inversion 1; try congruence.
  destruct valid_symbentry_id as (si' & EQ & RNG). rewrite STR in EQ; inv EQ. congruence.
  destruct valid_symbentry_id as (si' & EQ & RNG). rewrite STR in EQ; inv EQ.
Defined.

Definition forall_valid_symbentry_dec:
  forall strmap symt,
    {Forall (valid_symbentry strmap) symt} + {~ Forall (valid_symbentry strmap) symt}.
Proof.
  intros. apply Forall_dec. apply valid_symbentry_dec.
Qed.

Lemma strtable_empty_dec strt : {strt = Maps.PTree.empty Z } + {strt <> Maps.PTree.empty Z }.
Proof.
  intros. destruct strt. left; reflexivity.
  right; inversion 1.
Defined.

Lemma norepet_symbs_dec symt:
  {list_norepet (map symbentry_id symt)} + {~list_norepet (map symbentry_id symt)}.
Proof.
  apply list_norepet_dec. apply ident_eq.
Defined.


Parameter dump_reloctables: reloctable_map -> res program.
Axiom dump_reloctables_error: forall r, dump_reloctables r = Error [MSG "Reloctables not OK"].

Definition transf_program (p:program) : res program :=
  let symbols := fold_right acc_symbols [] (prog_symbtable p) in
  do r <- get_strings_map_bytes symbols;
  let '(idbytes, strmap, sbytes) := r in
  if forall_valid_symbentry_dec strmap (prog_symbtable p) then
    if strtable_empty_dec (prog_strtable p) then
      if norepet_symbs_dec (prog_symbtable p) then
        if reloctables_ok_dec (prog_reloctables p) then
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
          if beq_nat len 7 then
            OK p'
          else
            Error [MSG "In TablesEncode: number of sections is incorrect (not 7): "; POS (Pos.of_nat len)]
        else dump_reloctables (prog_reloctables p)
      else Error [MSG "Symbol ids repeat."]
    else Error [MSG "Empty strings."]
  else Error [MSG "Invalid symbentries"].
