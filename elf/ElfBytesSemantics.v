(* *******************  *)
(* Author: Pierre Wilke  *)
(* Date:  Jun 22, 2020  *)
(* *******************  *)

(** * The semantics of ELF binary programs   *)


Require Import Coqlib Maps AST Integers Values.
Require Import Events Floats Memory Smallstep.
Require Import Asm RelocProgram RawAsm Globalenvs.
Require Import Stacklayout Conventions EraseArgs.
Require Import Linking SeqTable Errors.
Require Import RelocElf RelocElfSemantics.
Require Import DecodeRelocElf.

Local Open Scope error_monad_scope.


Section WITHEXTERNALCALLS.
Context `{external_calls_prf: ExternalCalls}.

Definition semantics l p senv (rs: regset) :=
  match decode_elf_file l p senv with
  | OK ef =>
    RelocElfSemantics.semantics ef rs
  | Error _ =>
    Semantics (state:=state)
      (fun ge s1 t s2 => False)
      (fun s => False)
      (fun s r => False)
      (Genv.globalenv p)
  end.

(** Determinacy of the semantics. *)

Lemma semantics_determinate: forall l p senv rs, determinate (semantics l p senv rs).
Proof.
  intros.
  unfold semantics. destr.
  apply RelocElfSemantics.semantics_determinate.
  constructor; try red; simpl; intros; easy.
Qed.

Theorem reloc_prog_receptive l p senv rs:
  receptive (semantics l p senv rs).
Proof.
  unfold semantics. destr.
  apply RelocElfSemantics.reloc_prog_receptive.
  constructor; try red; simpl; intros; easy.
Qed.

End WITHEXTERNALCALLS.
