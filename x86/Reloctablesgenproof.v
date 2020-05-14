(* *******************  *)
(* Author: Author C *)
(* Date:   Jan 30, 2020 *)
(* *******************  *)

Require Import Coqlib Errors.
Require Import Integers Floats AST Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Op Locations Mach Conventions Asm RealAsm.
Require Import RelocProgram RelocProgSemantics RelocProgSemantics1.
Require Import Reloctablesgen.
Import ListNotations.

Definition match_prog p tp :=
  transf_program p = OK tp.

Lemma transf_program_match:
  forall p tp, transf_program p = OK tp -> match_prog p tp.
Proof.
  unfold match_prog; intuition.
Qed.

Section PRESERVATION.
  Existing Instance inject_perm_all.
Context `{external_calls_prf: ExternalCalls}.

Local Existing Instance mem_accessors_default.


Variables prog tprog: RelocProgram.program.

Hypothesis TRANSF: match_prog prog tprog.


End PRESERVATION.

Require Import RelocLinking RelocLinking1.

Axiom reloctablesgen_transflink : @TransfLink _ _ RelocLinking.Linker_reloc_prog RelocLinking1.Linker_reloc_prog match_prog.
