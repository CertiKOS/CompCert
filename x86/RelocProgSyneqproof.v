(* *******************  *)
(* Author: Yuting Wang  *)
(* Date:   Dec 2, 2019 *)
(* *******************  *)

Require Import Coqlib Errors.
Require Import Integers Floats AST Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Op Locations Mach Conventions Asm RealAsm.
Require Import RelocProgram RelocProgSemantics.
Require Import RelocProgSyneq.
Import ListNotations.
Require AsmFacts.

Definition match_prog p tp :=
  reloc_prog_syneq p tp.

Lemma transf_program_match:
  forall p tp, reloc_prog_syneq p tp -> match_prog p tp.
Proof.
  intros. subst. red. 
  auto.
Qed.


Section PRESERVATION.

Variable p: program.
Variable tp: program.

Let ge := globalenv p.
Let tge := globalenv tp.

Hypothesis TRANSF: match_prog p tp.

Lemma transf_program_correct:
  forall rs, forward_simulation (semantics p rs) (semantics tp rs).
Proof.
Admitted.

End PRESERVATION.
