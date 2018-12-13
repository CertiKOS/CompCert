Require Import GameSemantics.
Require Import Compiler.
Require Import Errors.

Definition clight p :=
  Behavior.strat (Clight.semantics2 p).

Definition asm p :=
  Behavior.strat (Asm.semantics p).

Lemma compcert_correct p tp :
  transf_clight_program p = OK tp ->
  ATS.ref cc_compcert cc_compcert (asm tp) (clight p).
Proof.
  intros Htp.
  eapply Behavior.strat_sim.
  eapply transf_clight_program_correct; auto.
Qed.

