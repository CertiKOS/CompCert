(* *******************  *)
(* Author: Yuting Wang  *)
(* Date:   Dec 2, 2019 *)
(* *******************  *)

Require Import Coqlib Errors.
Require Import Integers Floats AST Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Op Locations Mach Conventions Asm RealAsm.
Require Import PadNops.
Import ListNotations.
Require AsmFacts.

Definition match_prog (p tp:Asm.program) :=
  match_program (fun _ f tf => tf = transf_fundef f) eq p tp.

Lemma transf_program_match:
  forall p tp, transf_program p = tp -> match_prog p tp.
Proof.
  intros. subst. red. 
  eapply match_transform_program; eauto.
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

Inductive match_states : Asm.state -> Asm.state -> Prop :=
|match_states_intro m rs:
   match_states (Asm.State rs m) (Asm.State rs m).

Theorem step_simulation:
  forall S1 t S2, step ge S1 t S2 ->
                  forall S1' (MS: match_states S1 S1'),
                    (exists S2', step tge S1' t S2' /\ match_states S2 S2').
Proof.
  destruct 1; intros; inv MS.
  
  - (* Internal Step *)
    exists (State rs' m'). split; [|constructor].
    eapply exec_step_internal with (f0:= transl_function f) (i0:=i); eauto.
    generalize (Genv.find_funct_ptr_transf TRANSF _ H0); eauto.
    admit.
    erewrite <- exec_instr_same; eauto.
    admit.
    admit.

  - (* Builtin step *)
    admit.

  - (* External Step *)
    admit.

Admitted.

Lemma transf_initial_states:
  forall st1 rs, initial_state prog rs st1 ->
         exists st2, initial_state tprog rs st2 /\ match_states st1 st2.
Proof.
  intros st1 rs HInit.
  exists st1.
  inv HInit.
  split.
  + econstructor.
    generalize (Genv.init_mem_transf TRANSF H).
    eauto.
    inv H0.
    econstructor; eauto.
    setoid_rewrite (match_program_main TRANSF); eauto.
    generalize (Genv.find_symbol_transf TRANSF (prog_main prog)).
    intros HFind.
    rewrite <- H1.
    auto.
  + destruct st1. constructor.
Qed.


Lemma transf_final_states:
  forall st1 st2 r,
  match_states st1 st2 -> final_state st1 r -> final_state st2 r.
Proof.
  intros st1 st2 r MS HFinal.
  inversion HFinal.
  inversion MS.
  econstructor.
  rewrite <- H1 in H3.
  inversion H3. auto.
  rewrite <- H1 in H3.
  inversion H3.
  auto.
Qed.

Lemma transf_program_correct:
  forall rs, forward_simulation (semantics prog rs) (semantics tprog rs).
Proof.
  intro rs.
  apply forward_simulation_step with match_states.
  + intros id. unfold match_prog in TRANSF.
    generalize (Genv.senv_match TRANSF). intros SENV_EQ.
    red in SENV_EQ.
    destruct SENV_EQ as (S1 & S2 & S3 & S4). auto.
  + simpl. intros s1 Hinit.
    exploit transf_initial_states; eauto.
  + simpl. intros s1 s2 r MS HFinal. eapply transf_final_states; eauto.
  + simpl. intros s1 t s1' STEP s2 MS.
    edestruct step_simulation as (STEP' & MS' ); eauto.
Qed.
  

Lemma transl_fun_pres_stacksize: forall f tf,
    transl_function f = tf -> 
    Asm.fn_stacksize f = Asm.fn_stacksize tf.
Proof.
  intros f tf HFunc.
  unfold transl_function in HFunc.
  subst.
  simpl. auto.
Qed.

End PRESERVATION.
