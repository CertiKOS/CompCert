Require compcert.backend.Mach2Mach2.
Require MachX.

Import Coqlib Memory.
Require Import SmallstepX.
Import Globalenvs Events.
Export Mach2Mach2.

Section WITHCONFIG.
Context `{external_calls_prf: ExternalCalls}.

Variable prog: Mach.program.
Variable fn_stack_requirements: AST.ident -> Z.

Let ge := Genv.globalenv prog.

Variable m: mem.
(* Hypothesis init_mem_simple_stack: *)
(*   Forall (fun l => length l = 1)%nat (Mem.stack_adt m). *)

(* Hypothesis init_mem_shape: *)
(*   Forall *)
(*     (fun t : list frame_adt => *)
(*        match t with *)
(*        | nil => False *)
(*        | fr :: nil => match frame_adt_blocks fr with *)
(*                      | nil => False *)
(*                      | (_, _) :: nil => True *)
(*                      | (_, _) :: _ :: _ => False *)
(*                      end *)
(*        | fr :: _ :: _ => False *)
(*        end) (Mem.stack_adt m). *)

Variable sg: AST.signature.
Hypothesis init_sp_has_stackinfo:
  Mach.init_sp_stackinfo sg (Mem.stack m).

(* Hypothesis frame_correct: *)
(*   forall (fb : Values.block) (f : Mach.function), *)
(*     Genv.find_funct_ptr ge fb = Some (AST.Internal f) -> frame_size (Mach.fn_frame f) = Mach.fn_stacksize f. *)

Lemma stack_equiv_refl s:
  stack_equiv s s.
Proof.
  induction s; simpl; constructor; auto.
Qed.

Lemma transl_initial_states:
  forall init_rs i args,
  forall S, MachX.initial_state init_rs prog i sg args m S ->
  exists R, MachX.initial_state init_rs prog i sg args m R /\ match_states S R.
Proof.
  inversion 1; subst.
  esplit.
  split.
  econstructor. eauto. eauto.
  constructor. apply Mem.extends_refl; auto.
  constructor.
  apply stack_equiv_refl.
Qed.

Lemma val_lessdef_get_pair:
  forall sg rs rs',
    (forall r, val_lessdef (rs r) (rs' r)) ->
    val_lessdef (MachX.get_pair sg rs) (MachX.get_pair sg rs').
Proof.
  induction sg0; simpl; intros; eauto.
  eapply Values.Val.longofwords_lessdef; eauto.
Qed.

Lemma transl_final_states:
  forall init_rs,
  forall S R r,
  match_states S R -> MachX.final_state init_rs sg S r -> final_state_with_extends (MachX.final_state init_rs sg) R r.
Proof.
  intros init_rs S R r MS FS.
  inv FS. inv MS.
  edestruct Mem.unrecord_stack_block_extends as (m2' & USB' & UNCH'); eauto.
  econstructor.
  econstructor.
  reflexivity.
  intros; eapply Values.Val.lessdef_trans. apply CALLEE_SAVE. auto. eauto. eauto.
  assumption.
  eapply val_lessdef_get_pair; eauto.
Qed.

Hypothesis frame_correct:
  forall (b : Values.block) (f : Mach.function),
  Genv.find_funct_ptr ge b = Some (AST.Internal f) -> 0 < Mach.fn_stacksize f.

Theorem transf_program_correct:
  forall rao init_rs init_ra i args (IRANU: init_ra <> Values.Vundef),
  forward_simulation
    (MachX.semantics rao Mach.invalidate_frame1 init_rs init_ra prog i sg args m)
    (semantics_with_extends (MachX.semantics rao Mach.invalidate_frame2 init_rs init_ra prog i sg args m)).
Proof.
  intros.
  eapply forward_simulation_step with
      (match_states := fun s1 s2 => match_states s1 s2
                                 /\ Mach.call_stack_consistency ge sg (Mem.stack m) s1
                                 /\ Mach.has_code rao ge s1
                                 /\ Mach.call_stack_consistency ge sg (Mem.stack m) s2
                                 /\ Mach.has_code rao ge s2).
  - reflexivity. 
  - simpl; intros s1 IS. edestruct transl_initial_states as (s2 & IS2 & MS); eauto.
    exists s2; split; [|split]; eauto. repeat split.
    inv IS. repeat (constructor; try red; try rewrite_stack_blocks); simpl; auto.
    inv IS. constructor. constructor.
    inv IS2. repeat (constructor; try red; try rewrite_stack_blocks); simpl; auto.
    inv IS2. constructor. constructor.
  - simpl; intros s1 s2 r (MS & CSC1 & HC1 & CSC2 & HC2) FS; eapply transl_final_states; eauto.
  - simpl; intros s1 t s1' STEP s2 (MS & CSC1 & HC1 & CSC2 & HC2).
    edestruct step_correct as (s2' & STEPS & MS'); eauto.
    eexists; split; eauto. repeat split; auto.
    eapply Mach.csc_step; eauto.
    unfold Mach.invalidate_frame1. inversion 1; subst; auto.
    unfold Mach.invalidate_frame1. inversion 1; subst; auto.
    eapply Mach.has_code_step; eauto.
    eapply Mach.csc_step; eauto.
    unfold Mach.invalidate_frame2. intros. rewrite_stack_blocks. simpl. intro A; rewrite A; simpl; auto.
    unfold Mach.invalidate_frame2. intros. inv H0. red. rewrite_stack_blocks. simpl.
    intros A. constructor; simpl.
    easy.
    eapply Mach.has_code_step; eauto.
Qed.

End WITHCONFIG.
