(* *******************  *)
(* Author: Yuting Wang  *)
(* Date:   Oct 30, 2019 *)
(* *******************  *)

(** * Preservation of semantics under the permutation of definitions for RealAsm *)
Require Import Coqlib Errors.
Require Import Integers Floats AST.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Permutation.
Require Import Asm RealAsm.

(** matching modulo the permutation of definitions *)

Definition match_prog {F V} (p tp: AST.program F V) :=
  Permutation (prog_defs p) (prog_defs tp) 
  /\ prog_main p = prog_main tp
  /\ prog_public p = prog_public tp.

Lemma transf_program_match:
  forall F V (p: AST.program F V), match_prog p p.
Proof.
  intros. red. 
  repeat (split; auto).
Qed.

(** Preservation of semantics under permutation *)
Section PRESERVATION.

Context `{external_calls_prf: ExternalCalls}.

Variable prog: Asm.program.
Variable tprog: Asm.program.
Hypothesis TRANSF: match_prog prog tprog.

Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Theorem transf_program_correct:
  forward_simulation (RealAsm.semantics prog (Pregmap.init Vundef))
                     (RealAsm.semantics tprog (Pregmap.init Vundef)).
Admitted.

End PRESERVATION.
