(* ******************** *)
(* Author: Zhenguo Yin  *)
(* Date:   Sep 21, 2020 *)
(* ******************** *)

Require Import Coqlib Errors.
Require Import Integers Floats AST Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Op Locations Mach Conventions Asm RealAsm.
Require Import AsmFloatLiteral.
Import ListNotations.
Require AsmFacts.

Definition match_prog (p tp:Asm.program) :=
  exists tp',
    transf_program p = tp' /\
    (* add defs *)
    (* prog_defs tp = prog_defs tp' /\ *)
    prog_public tp = prog_public tp' /\
    prog_main tp = prog_main tp'.

Lemma transf_program_match:
  forall p tp, transf_program p = tp -> match_prog p tp.
Proof.
  unfold match_prog. intros. exists tp; intuition.
Qed.

Section PRESERVATION.
  Existing Instance inject_perm_all.
Context `{external_calls_prf: ExternalCalls}.

Local Existing Instance mem_accessors_default.


Variable prog: Asm.program.
Variable tprog: Asm.program.

Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Hypothesis TRANSF: match_prog prog tprog.

Lemma transf_program_correct:
  forall rs, forward_simulation (semantics prog rs) (semantics tprog rs).
Proof.
Admitted.


End PRESERVATION.