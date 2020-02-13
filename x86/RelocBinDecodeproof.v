(* *******************  *)
(* Author: Xiangzhe Xu  *)
(* Date:   Feb 12, 2020 *)
(* *******************  *)
Require Import Coqlib Integers AST Maps.
Require Import Asm.
Require Import Errors.
Require Import Memtype.
(* Require Import FlatProgram FlatAsm FlatBinary. *)
Require Import Hex Bits Memdata Integers Floats AST Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Import ListNotations.
Import Hex Bits.
Require Import RelocBingen RelocProgram SeqTable Encode.
Require Import Reloctablesgen.
Require Import RelocBinDecode RelocBingen RelocProgSemantics1 RelocProgSemantics2.
Local Open Scope error_monad_scope.
Local Open Scope hex_scope.
Local Open Scope bits_scope.


Definition match_prog (p tp: program) :=
  transf_program p = OK tp.

Lemma transf_program_match:
  forall p tp, transf_program p = OK tp -> match_prog p tp.
Proof.
  intros p tp HTrans.
  unfold match_prog.
  auto.
Qed.


Section PRESERVATION.
  Existing Instance inject_perm_all.
  Context `{external_calls_prf: ExternalCalls}.

Variable prog : program.
Variable tprog : program.

Let ge := globalenv prog.
Let tge := globalenv tprog.

Hypothesis TRANSF: match_prog prog tprog.


Inductive match_states : Asm.state -> Asm.state -> Prop :=
|match_states_intro m rs:
   match_states (Asm.State rs m) (Asm.State rs m).


(* Theorem step_simulation: *)
(*   forall S1 t S2, RelocProgSemantics1.step ge S1 t S2 -> *)
(*                   forall S1' (MS: match_states S1 S1'), *)
(*                     (exists S2', RelocProgSemantics2.step tge S1' t S2' /\ match_states S2 S2'). *)


End PRESERVATION.


