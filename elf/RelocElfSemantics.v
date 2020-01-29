(* *******************  *)
(* Author: Pierre Wilke  *)
(* Date:  Jan 28, 2020  *)
(* *******************  *)

(** * The semantics of relocatable ELF program *)


Require Import Coqlib Maps AST Integers Values.
Require Import Events Floats Memory Smallstep.
Require Import Asm RelocProgram RawAsm Globalenvs.
Require Import Stacklayout Conventions EraseArgs.
Require Import Linking SeqTable Errors.
Require Import RelocProgSemantics3.
Require Import RelocElf.

Local Open Scope error_monad_scope.


Section WITHEXTERNALCALLS.
Context `{external_calls_prf: ExternalCalls}.

Definition reloc_program_of_elf_program (p:RelocElf.elf_file) : RelocProgram.program :=
  {|
      RelocProgram.prog_defs := prog_defs p;
      RelocProgram.prog_public := prog_public p;
      RelocProgram.prog_main := prog_main p;
      RelocProgram.prog_senv := prog_senv p;

      prog_sectable := sec_null :: map sec_bytes (elf_sections p);
      prog_symbtable := nil;
      prog_strtable := PTree.empty Z;
      prog_reloctables := {| reloctable_code := nil;
                             reloctable_data := nil
                          |};

    |}.

Definition semantics (p: elf_file) (rs: regset) :=
  RelocProgSemantics3.semantics (reloc_program_of_elf_program p) rs.

(** Determinacy of the semantics. *)

Lemma semantics_determinate: forall p rs, determinate (semantics p rs).
Proof.
  intro ef. apply RelocProgSemantics3.semantics_determinate.
Qed.

Theorem reloc_prog_receptive p rs:
  receptive (semantics p rs).
Proof.
  apply RelocProgSemantics3.reloc_prog_receptive.
Qed.

End WITHEXTERNALCALLS.
