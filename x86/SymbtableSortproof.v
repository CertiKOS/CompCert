(* ******************** *)
(* Author: Zhenguo Yin  *)
(* Date:   Sep 21, 2020 *)
(* ******************** *)

Require Import Coqlib Errors.
Require Import Integers Floats AST Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Op Locations Mach Conventions Asm RealAsm.
Require Import RelocProgram RelocProgSemantics.
Require Import SymbtableSort.
Import ListNotations.
Require AsmFacts.

Definition match_prog (p tp:program) :=
  exists tp',
    transf_program p = OK tp' /\
    prog_public tp = prog_public tp' /\
    prog_main tp = prog_main tp' /\
    prog_strtable tp = prog_strtable tp' /\
    prog_reloctables tp = prog_reloctables tp' /\
    prog_senv tp = prog_senv tp'.

Lemma transf_program_match:
  forall p tp, transf_program p = OK tp -> match_prog p tp.
Proof.
  unfold match_prog. intros. exists tp; intuition.
Qed.

Require Import RelocLinking.
Instance symbtablesort_transflink : @TransfLink _ _ RelocLinking.Linker_reloc_prog RelocLinking.Linker_reloc_prog match_prog.
Proof.
  Admitted.

Section PRESERVATION.

Variable prog: RelocProgram.program.
Variable tprog: RelocProgram.program.

Let ge := RelocProgSemantics.globalenv prog.
Let tge := RelocProgSemantics.globalenv tprog.

Hypothesis TRANSF: match_prog prog tprog.

Lemma transf_program_correct:
  forall rs, forward_simulation (RelocProgSemantics.semantics prog rs) (RelocProgSemantics.semantics tprog rs).
Proof.
Admitted.


End PRESERVATION.
