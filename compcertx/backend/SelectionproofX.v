Require compcert.backend.Selectionproof.
Require CminorSelX.
Require CminorX.
Require SmallstepX.
Require EventsX.

Import Coqlib.
Import Errors.
Import AST.
Import Globalenvs.
Import EventsX.
Import SmallstepX.
Import SelectLong.
Export Selectionproof.

Section WITHCONFIG.
Context `{ external_calls_prf: ExternalCalls }.
Context `{i64_helpers_correct: !SplitLongproof.I64HelpersCorrect mem}.

Section TRANSF.

Variable prog: Cminor.program.
Variable tprog: CminorSel.program.
Hypothesis TRANF: Selection.sel_program prog = OK tprog.

Variable fn_stack_requirements: ident -> Z.

Let MATCH_PROG: match_prog prog tprog.
Proof. apply transf_program_match; auto. Qed.

Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Variable m: mem.

Lemma sel_initial_states:
  forall i sg args,
  forall S, CminorX.initial_state fn_stack_requirements prog i m sg args S ->
  exists R, CminorSelX.initial_state fn_stack_requirements tprog i m sg args R /\ match_states prog tprog S R.
Proof.
  inversion 1; subst.
  exploit function_ptr_translated; eauto.
  destruct 1 as (? & ? & FIND & FMATCH & FLINK).
  esplit. split. econstructor.
   erewrite symbols_preserved; eauto.
   eassumption.
   symmetry. eapply sig_function_translated; eauto.
  econstructor; eauto.
  constructor.
  refine (val_lessdef_refl _).
  apply Mem.extends_refl.
  apply stack_equiv_refl; auto.
Qed.

Lemma sel_final_states:
  forall sg,
  forall S R r,
  match_states prog tprog S R -> CminorX.final_state sg S r -> final_state_with_extends (CminorSelX.final_state sg) R r.
Proof.
  intros. inv H0. inv H.
  apply match_call_cont_cont in MC.
  destruct MC as (? & ? & MC).
  edestruct Mem.unrecord_stack_block_extends as (m2' & USB' & EXT'); eauto.
  inv MC.
  econstructor; eauto.
  econstructor; eauto.
Qed.

Lemma initial_stack_inv:
  forall i sg args s2,
    CminorSelX.initial_state fn_stack_requirements tprog i m sg args s2 ->
    CminorSel.stack_inv s2.
Proof.
  intros i sg args s2 IS; inv IS.
  econstructor.
  rewrite_stack_blocks. constructor. easy.
  simpl; constructor.
Qed.

Theorem transf_program_correct:
  forall i sg args,
  forward_simulation
    (CminorX.semantics fn_stack_requirements prog i m sg args)
    (semantics_with_extends (CminorSelX.semantics fn_stack_requirements tprog i m sg args))
.
Proof.
  intros.
  apply forward_simulation_opt with (match_states := fun s1 s2 => match_states prog tprog s1 s2 /\ CminorSel.stack_inv s2) (measure := measure).
  - apply senv_preserved; auto.
  - simpl. intros s1 IS. edestruct sel_initial_states as (s2 & IS2 & MS2); eauto.
    exists s2; split; eauto. split; eauto using initial_stack_inv.
  - simpl. intros s1 s2 r (MS & _) FS.
    eapply sel_final_states; eauto.
  - simpl; intros s1 t s1' STEP s2 (MS & IS).
    edestruct sel_step_correct as [(s2' & STEP' & MS2)|(DEC & NOTRACE & MS2)]; eauto.
    left; eexists; split; eauto. split; eauto using CminorSel.stack_inv_inv.
Qed.

End TRANSF.

End WITHCONFIG.
