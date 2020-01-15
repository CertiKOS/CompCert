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


Section WITHEXTERNALCALLS.
Context `{external_calls_prf: ExternalCalls}.

Definition decode_tables (p:program) : res program :=
  do p <- ShstrtableDecode.transf_program_inv p;
    do p <- ReloctablesDecode.transf_program_inv p;
    do p <- SymbtableDecode.transf_program_inv p;
    do p <- StrtableDecode.transf_program_inv p; OK p.

Inductive initial_state (prog: program) (rs: regset) (s: state): Prop :=
| initial_state_intro: forall prog',
    decode_tables prog = OK prog' ->
    RelocProgSemantics2.initial_state prog' rs s ->
    initial_state prog rs s.

Definition semantics (p: program) (rs: regset) :=
  Semantics_gen RelocProgSemantics1.step
                (initial_state p rs) RelocProgSemantics1.final_state
                (RelocProgSemantics1.globalenv p)
                (RelocProgSemantics1.genv_senv (RelocProgSemantics1.globalenv p)).


(** Determinacy of the semantics. *)

Lemma semantics_determinate: forall p rs, determinate (semantics p rs).
Proof.
  intros.
  constructor; simpl; auto.
  - intros; eapply (sd_determ (RelocProgSemantics2.semantics_determinate p rs)); eauto.
  - intros; eapply (sd_traces (RelocProgSemantics2.semantics_determinate p rs)); eauto.
  - intros s1 s2 H H0. inv H; inv H0.
    assert (prog' = prog'0) by congruence. subst.
    intros; eapply (sd_initial_determ (RelocProgSemantics2.semantics_determinate prog'0 rs)); eauto.
  - intros; eapply (sd_final_nostep (RelocProgSemantics2.semantics_determinate p rs)); eauto.
  - intros; eapply (sd_final_determ (RelocProgSemantics2.semantics_determinate p rs)); eauto.
Qed.

Theorem reloc_prog_receptive p rs:
  receptive (semantics p rs).
Proof.
  destruct (RelocProgSemantics2.reloc_prog_receptive p rs).
  split; auto.
Qed.

End WITHEXTERNALCALLS.
