Require compcert.backend.RTLgenproof.
Require CminorSelX.
Require RTLX.

Import Coqlib.
Import Memory.
Import SmallstepX.
Import Globalenvs.
Import Events.
Import RTLgen.
Export RTLgenproof.

Section WITHCONFIG.
Context `{external_calls_prf: ExternalCalls}.

Variable prog: CminorSel.program.
Variable tprog: RTL.program.
Hypothesis TRANSL: transl_program prog = Errors.OK tprog.
Variable fn_stack_requirements: AST.ident -> Z.

Let MATCH_PROG: match_prog prog tprog.
Proof.
  apply transf_program_match; auto.
Qed.

Let ge : CminorSel.genv := Genv.globalenv prog.
Let tge : RTL.genv := Genv.globalenv tprog.

Lemma transl_initial_states:
  forall i m sg args,
  forall S, CminorSelX.initial_state fn_stack_requirements prog i m sg args S ->
  exists R, RTLX.initial_state fn_stack_requirements tprog i m sg args R /\ match_states S R.
Proof.
  inversion 1; subst.
  exploit function_ptr_translated; eauto.
  destruct 1 as [? [? ?]].
  esplit.
  split.
  econstructor.
  erewrite symbols_preserved; eauto.
  eassumption.
  symmetry. eapply sig_transl_function; eauto.
  constructor; auto.
  constructor.
  refine (val_lessdef_refl _).
  apply Mem.extends_refl.
  apply stack_equiv_refl; auto.
Qed.

Lemma transl_final_states:
  forall sg,
  forall S R r,
  match_states S R -> CminorSelX.final_state sg S r -> final_state_with_extends (RTLX.final_state sg) R r.
Proof.
  inversion 2; subst.
  inv H.
  inv MS.
  edestruct Mem.unrecord_stack_block_extends as (m2' & USB' & EXT'); eauto.
  econstructor.
  econstructor; eauto.
  assumption.
  assumption.
Qed.

Theorem transf_program_correct:
  forall i m sg args,
  forward_simulation
    (CminorSelX.semantics fn_stack_requirements prog i m sg args)
    (semantics_with_extends (RTLX.semantics fn_stack_requirements tprog i m sg args))
.
Proof.
  intros.
  eapply forward_simulation_star_wf with (order := lt_state) (match_states := fun s1 s2 => match_states s1 s2 /\ RTL.stack_inv s2).
  - apply senv_preserved; auto.
  - simpl; intros s1 IS. edestruct transl_initial_states as (s2 & IS2 & MS); eauto.
    exists s2; split; eauto using RTLX.initial_stack_inv.
  - simpl; intros s1 s2 r (MS & SI) FS; eapply transl_final_states; eauto.
  - apply lt_state_wf. 
  - simpl; intros s1 t s1' STEP s2 (MS & SI).
    edestruct transl_step_correct as (s2' & STEPS & MS'); eauto.
    eexists; split; eauto. split; auto.
    destruct STEPS as [STEPS | [STEPS _]]; auto.
    eapply inv_plus; eauto. apply RTL.stack_inv_inv.
    eapply inv_star; eauto. apply RTL.stack_inv_inv.
Qed.

End WITHCONFIG.
