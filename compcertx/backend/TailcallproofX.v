Require compcert.backend.Tailcallproof.
Require RTLX.
Require SmallstepX.

Import Coqlib.
Import Errors.
Import AST.
Import Values.
Import Memory.
Import Events.
Import SmallstepX.
Import Globalenvs.
Import Tailcall.
Export Tailcallproof.

Section WITHCONFIG.
Context `{external_calls_prf: ExternalCalls}.

Variable prog: RTL.program.
Let tprog := transf_program prog.

Let MATCH_PROG: match_prog prog tprog.
Proof. apply transf_program_match; auto. Qed.

Let ge : RTL.genv := Genv.globalenv prog.
Let tge: RTL.genv := Genv.globalenv tprog.

Variable fsr: ident -> Z.
Variable init_m: mem.
Hypothesis init_m_inject_neutral: Mem.inject_neutral (Mem.nextblock init_m) init_m.
Hypothesis genv_next_init_m: Ple (Genv.genv_next ge) (Mem.nextblock init_m).

Variable args: list val.
Hypothesis args_inj: Val.inject_list (Mem.flat_inj (Mem.nextblock init_m)) args args.

Lemma sizes_refl:
  forall s,
    StackInj.sizes (flat_frameinj (length s)) s s.
Proof.
  induction s; simpl; intros; econstructor; simpl; eauto.
  left. omega.
Qed.

Lemma transf_initial_states:
  forall i sg,
  forall S, RTLX.initial_state fsr prog i init_m sg args S ->
  exists R, RTLX.initial_state fsr tprog i init_m sg args R /\ match_states' prog init_m S R.
Proof.
  intros. inv H.
  exploit funct_ptr_translated; eauto. intros.
  exists (RTL.Callstate nil (transf_fundef f) args (Mem.push_new_stage init_m) (fsr i)); split.
  econstructor; eauto.
  unfold tprog. erewrite symbols_preserved; eauto.
  symmetry. eapply sig_preserved; eauto.
  econstructor. econstructor; eauto.
  - econstructor.
  - apply Mem.push_new_stage_inject.
    apply Mem.neutral_inject. exact init_m_inject_neutral.
  - simpl. rewrite_stack_blocks. econstructor; simpl.
    apply sizes_refl. eauto. left. omega.
  - split.
    + unfold Mem.flat_inj; intros; apply pred_dec_true. fold ge in H0. xomega.
    + unfold Mem.flat_inj. intros b1 b2 delta FI PLT. destr_in FI.
  - red; intros; congruence.
  - repeat split.
    + constructor; rewrite_stack_blocks.
      constructor; easy.
      simpl. constructor.
    + constructor; rewrite_stack_blocks.
      constructor; easy.
      simpl. constructor.
    + red. simpl. unfold stack_blocks_of_state. simpl.
      constructor.
    + red. simpl. rewnb. xomega.
    + red. simpl. rewnb. xomega.
Qed.

Lemma transf_final_states:
  forall sg,
  forall st1 st2 r, 
  match_states' prog init_m st1 st2 -> RTLX.final_state sg st1 r ->
  final_state_with_inject (RTLX.final_state sg) init_m st2 r.
Proof.
  intros sg st1 st2 r MS FS. inv FS. inv MS. inv H.
  inv MS.
  edestruct Mem.unrecord_stack_block_inject_parallel as (m2' & USB' & EXT'); eauto.
  econstructor. 4: eauto. all: eauto.
  constructor; auto.
Qed.

Theorem transf_program_correct:
  forall i sg,
  forward_simulation 
    (RTLX.semantics fsr prog i init_m sg args)
    (semantics_with_inject (RTLX.semantics fsr tprog i init_m sg args) init_m).
Proof.
  intros.
  eapply forward_simulation_opt with (measure := measure); eauto.
  apply senv_preserved; auto.
  apply transf_initial_states.
  apply transf_final_states.
  - intros s1 t s1' STEP1 s2 MS1. inv MS1. simpl in *.
    destruct H0 as (MSA1 & MSA2 & SPV1 & MGE1 & MGE2).
    exploit transf_step_correct; eauto.
    intros [(s2' & STEP & MS)|(MES & TR & MS)]; [left|right].
    + eexists; split; eauto.
      econstructor; eauto.
      repeat split.
      eapply RTL.stack_inv_inv; eauto.
      eapply RTL.stack_inv_inv; eauto.
      eapply sp_valid_step; eauto.
      eapply nextblock_inv_step. 3: eauto. all: eauto.
      eapply nextblock_inv_step. 3: eauto. all: eauto.
    + repeat split; eauto.
      eapply RTL.stack_inv_inv; eauto.
      eapply sp_valid_step; eauto.
      eapply nextblock_inv_step. 3: eauto. all: eauto.
Qed.

End WITHCONFIG.
