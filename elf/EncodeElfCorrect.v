Require Import ElfBytesSemantics.
Require Import Smallstep.
Require Import EncodeRelocElf DecodeRelocElf.
Require Import RelocElf.
Require Import Coqlib Errors.

Definition match_prog : elf_file -> (list Integers.Byte.int * Asm.program * Globalenvs.Senv.t) -> Prop :=
  fun p p' => encode_elf_file p = OK p'.

Section PRES.

Variable prog: elf_file.
Variable tprog_bytes: list Integers.Byte.int.
Variable tprog_prog: Asm.program.
Variable tprog_senv: Globalenvs.Senv.t.

Hypothesis TRANSF: match_prog prog (tprog_bytes, tprog_prog, tprog_senv).

Context `{external_calls_prf: Events.ExternalCalls}.

Lemma encode_elf_correct:
  forall rs, forward_simulation (RelocElfSemantics.semantics prog rs)
                                (ElfBytesSemantics.semantics tprog_bytes tprog_prog tprog_senv rs).
Proof.
  unfold match_prog in TRANSF.
  unfold ElfBytesSemantics.semantics. intros.
  erewrite decode_encode_elf_file; eauto.
  apply forward_simulation_step with (match_states := eq); intuition subst; eauto.
Qed.

End PRES.
