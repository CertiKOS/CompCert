(* *******************  *)
(* Author: Pierre Wilke  *)
(* Date:  Jan 7, 2020  *)
(* *******************  *)

(** * The semantics of relocatable program after string table, section header string
table and symbol table encoding *)


Require Import Coqlib Maps AST Integers Values.
Require Import Events Floats Memory Smallstep.
Require Import Asm RelocProgram RawAsm Globalenvs.
Require Import Stacklayout Conventions EraseArgs.
Require Import Linking SeqTable Errors.
Require Import SymbtableDecode StrtableDecode ShstrtableDecode ReloctablesDecode.
Require RelocProgSemantics2.

Local Open Scope error_monad_scope.
Import ListNotations.


Section WITHEXTERNALCALLS.
Context `{external_calls_prf: ExternalCalls}.

Definition decode_tables (p:program) : res program :=
  match prog_sectable p with
    srodata :: sdata :: scode :: strsec :: symsec :: rodatarelocsec :: datarelocsec :: coderelocsec :: shstrsec :: nil =>
    do rds <- decode_reloctable_section rodatarelocsec;
    do ds <- decode_reloctable_section datarelocsec;
    do cs <- decode_reloctable_section coderelocsec;
    do (symbs, strmap) <- decode_strtable_section strsec;
    do syms <- decode_symtable_section strmap symsec;
      OK {|
          prog_defs := prog_defs p;
          prog_public := prog_public p;
          prog_main := prog_main p;
          prog_sectable := [srodata; sdata; scode];
          prog_symbtable := syms;
          prog_strtable := PTree.empty Z;
          prog_reloctables := {| reloctable_code := cs; reloctable_data := ds; reloctable_rodata := rds|};
          prog_senv := prog_senv p;
        |}
  | _ => Error (msg "Expected 9 sections [rodata,data,code,str,symb,relrodata, reldata,relcode,shstr]")
  end.

Inductive initial_state (prog: program) (rs: regset) (s: state): Prop :=
| initial_state_intro: forall prog',
    decode_tables prog = OK prog' ->
    RelocProgSemantics2.initial_state prog' rs s ->
    initial_state prog rs s.

Definition semantics (p: program) (rs: regset) :=
  RelocProgSemantics2.semantics   match decode_tables p with
                                  | OK p => p
                                  | _ => p
                                  end rs.

(** Determinacy of the semantics. *)

Lemma semantics_determinate: forall p rs, determinate (semantics p rs).
Proof.
  intros.
  apply RelocProgSemantics2.semantics_determinate.
Qed.

Theorem reloc_prog_receptive p rs:
  receptive (semantics p rs).
Proof.
  unfold semantics.
  apply RelocProgSemantics2.reloc_prog_receptive.
Qed.

End WITHEXTERNALCALLS.
