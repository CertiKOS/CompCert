(* ********************* *)
(* Author: Yuting Wang   *)
(* Date:   Oct 31, 2019  *)
(* ********************* *)

(** * Syntactic equality bewteen relocatble programs *)

Require Import Coqlib Maps Integers Values AST.
Require Import Globalenvs SeqTable Asm.
Require Import RelocProgram.
Require Import Permutation.

Definition symbtable_syneq (s1 s2: symbtable) : Prop :=
  Permutation s1 s2.
               

Lemma symbtable_syneq_refl: forall t,
    symbtable_syneq t t.
Proof.
  unfold symbtable_syneq.
  intros. 
  apply Permutation_refl; eauto.
Qed.

Lemma symbtable_syneq_symm: forall t1 t2,
    symbtable_syneq t1 t2 -> symbtable_syneq t2 t1.
Proof.
  unfold symbtable_syneq.
  intros. 
  apply Permutation_sym; eauto.
Qed.

Lemma symbtable_syneq_trans: forall t1 t2 t3,
    symbtable_syneq t1 t2 -> symbtable_syneq t2 t3 ->
    symbtable_syneq t1 t3.
Proof.
  unfold symbtable_syneq.
  intros. 
  eapply Permutation_trans; eauto.
Qed.


Definition reloc_prog_syneq (p tp: program) : Prop :=
  Permutation (prog_defs p) (prog_defs tp) 
  /\ prog_main p = prog_main tp
  /\ prog_public p = prog_public tp
  /\ prog_sectable p = prog_sectable tp
  /\ symbtable_syneq (prog_symbtable p) (prog_symbtable tp)
  /\ prog_strtable p = prog_strtable tp
  /\ prog_reloctables p = prog_reloctables tp.
  

Lemma reloc_prog_syneq_refl: forall t,
    reloc_prog_syneq t t.
Proof.
  unfold reloc_prog_syneq.
  intros. 
  split. apply Permutation_refl.
  intuition.
Qed.

Lemma reloc_prog_syneq_symm: forall t1 t2,
    reloc_prog_syneq t1 t2 -> reloc_prog_syneq t2 t1.
Proof.
  unfold reloc_prog_syneq.
  intros. 
  intuition.
Qed.

Lemma reloc_prog_syneq_trans: forall t1 t2 t3,
    reloc_prog_syneq t1 t2 -> reloc_prog_syneq t2 t3 ->
    reloc_prog_syneq t1 t3.
Proof.
  unfold reloc_prog_syneq.
  intros. 
  intuition try congruence.
  eapply Permutation_trans; eauto.
  eapply symbtable_syneq_trans; eauto.
Qed.


Definition match_prog p tp :=
  reloc_prog_syneq p tp.

Lemma transf_program_match:
  forall p tp, reloc_prog_syneq p tp -> match_prog p tp.
Proof.
  intros. subst. red. 
  auto.
Qed.

Require Import Values Memory Events Smallstep.
Require Import RealAsm RelocProgram RelocProgSemantics.

Section PRESERVATION.

Existing Instance inject_perm_all.
Context `{external_calls_prf: ExternalCalls}.

Local Existing Instance mem_accessors_default.


Variable p: program.
Variable tp: program.

Let ge := globalenv p.
Let tge := globalenv tp.

Hypothesis TRANSF: match_prog p tp.

Axiom transf_program_correct:
  forall rs, forward_simulation (semantics p rs) (semantics tp rs).
Proof.

End PRESERVATION.
