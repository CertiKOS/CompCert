(* *******************  *)
(* Author: Yuting Wang  *)
(* Date:   Dec 2, 2019 *)
(* *******************  *)

Require Import Coqlib Errors.
Require Import Integers Floats AST Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Op Locations Mach Conventions Asm RealAsm.
Require Import Symbtablegen.
Require Import RelocProgram RelocProgSemantics.
Import ListNotations.
Require AsmFacts.

Definition match_prog p tp :=
  transf_program p = OK tp.

Lemma transf_program_match:
  forall p tp, transf_program p = OK tp -> match_prog p tp.
Proof.
  intros. subst. red. 
  auto.
Qed.


Section PRESERVATION.
  Existing Instance inject_perm_all.
Context `{external_calls_prf: ExternalCalls}.

Local Existing Instance mem_accessors_default.


Variable prog: Asm.program.
Variable tprog: program.

Let ge := Genv.globalenv prog.
Let tge := globalenv tprog.

Hypothesis TRANSF: match_prog prog tprog.

Axiom transf_program_correct:
  forall rs, forward_simulation (RealAsm.semantics prog rs) (semantics tprog rs).


End PRESERVATION.
