Require Asmgenproof.
Require SmallstepX.
Require EventsX.
Require AsmX.
Require MachX.

Import Coqlib.
Import Integers.
Import AST.
Import Values.
Import Memory.
Import Globalenvs.
Import EventsX.
Import SmallstepX.
Import Locations.
Import Conventions.
Import MachX.
Import AsmX.
Import Asmgen.
Export Asmgenproof.

Section PRESERVATION.
Context `{external_calls_prf: ExternalCalls}.

Variable prog: Mach.program.
Variable tprog: Asm.program.
Hypothesis TRANSF: transf_program prog = Errors.OK tprog.

Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Let MATCH_PROG := transf_program_match _ _ TRANSF.

Lemma genv_next_preserved:
  Genv.genv_next tge = Genv.genv_next ge.
Proof.
  eapply senv_preserved. eauto.
Qed.

Variables
   (init_asm_rs: Asm.regset)
   (m: mem)
   (i: ident)
   (b: block)
   (Hsymb: Genv.find_symbol (Genv.globalenv tprog) i = Some b)
   (HPC: init_asm_rs PC = Vptr b Ptrofs.zero)
   (HSP_NOT_VUNDEF: init_asm_rs SP <> Vundef)
   (HRA_NOT_VUNDEF: init_asm_rs RA <> Vundef)
.

Definition init_mach_rs: Mach.regset := (fun r => init_asm_rs (preg_of r)).
Definition init_sp := current_sp (Mem.stack m).
Hypothesis init_sp_reg : init_asm_rs RSP = init_sp.
Let init_ra := init_asm_rs RA.

Lemma extcall_arg_match:
  forall m l v,
  Mach.extcall_arg init_mach_rs m init_sp l v ->
  Asm.extcall_arg init_asm_rs m l v.
Proof.
  intros. inv H.
  constructor.
  unfold load_stack in H0.
  econstructor. eauto. rewrite init_sp_reg. assumption.
Qed.

Lemma extcall_arg_pair_match:
  forall m l v,
  Mach.extcall_arg_pair init_mach_rs m init_sp l v ->
  Asm.extcall_arg_pair init_asm_rs m l v.
Proof.
  intros. inv H; constructor; eauto using extcall_arg_match.
Qed.

Lemma extcall_args_match:
  forall m ll vl,
  list_forall2 (Mach.extcall_arg_pair init_mach_rs m init_sp) ll vl ->
  list_forall2 (Asm.extcall_arg_pair init_asm_rs m) ll vl.
Proof.
  induction 1; intros; constructor; auto using extcall_arg_pair_match.
Qed.

Lemma extcall_arguments_match:
  forall m sg args,
  Mach.extcall_arguments init_mach_rs m init_sp sg args ->
  Asm.extcall_arguments init_asm_rs m sg args.
Proof.
  unfold Mach.extcall_arguments, Asm.extcall_arguments; intros.
  eapply extcall_args_match; eauto.
Qed.

Lemma extcall_arg_match_inv:
  forall m,
  forall l v,
  Asm.extcall_arg init_asm_rs m l v ->
  Mach.extcall_arg init_mach_rs m (init_asm_rs RSP) l v.
Proof.
  intros. inv H.
  constructor.
  econstructor. eauto.
Qed.

Lemma extcall_arg_pair_match_inv:
  forall m,
  forall l v,
  Asm.extcall_arg_pair init_asm_rs m l v ->
  Mach.extcall_arg_pair init_mach_rs m (init_asm_rs RSP) l v.
Proof.
  intros. inv H; constructor; eauto using extcall_arg_match_inv.
Qed.

Lemma extcall_args_match_inv:
  forall m ll vl,
  list_forall2 (Asm.extcall_arg_pair init_asm_rs m) ll vl ->
  list_forall2 (Mach.extcall_arg_pair init_mach_rs m (init_asm_rs RSP)) ll vl.
Proof.
  induction 1; intros; constructor; auto using extcall_arg_pair_match_inv.
Qed.

(* Lemma machregs_type: *)
(*   AsmX.wt_regset init_asm_rs -> *)
(*   forall r, *)
(*     Val.has_type (init_mach_rs r) *)
(*                  (Machregs.mreg_type r). *)
(* Proof. *)
(*   unfold AsmX.wt_regset. intros. *)
(*   unfold init_mach_rs. *)
(*   generalize (H (preg_of r)). *)
(*   destruct r; simpl; try destr; try tauto. *)
(* Qed. *)

Lemma init_sp_type: Val.has_type (init_asm_rs RSP) Tptr.
Proof.
  rewrite init_sp_reg. unfold init_sp, current_sp, current_frame_sp.
  repeat destr; auto using Val.Vnullptr_has_type, Val.Vptr_has_type.
Qed.

Hypothesis init_sp_not_undef:
  init_sp <> Vundef.

Lemma transf_initial_states:
  forall sg args,
  forall st1, MachX.initial_state init_mach_rs prog i sg args m st1 ->
              exists st2, AsmX.initial_state init_asm_rs tprog i sg args m st2 /\
                          match_states prog init_ra st1 st2.
Proof.
  intros sg args.
  inversion 1; subst. 
  generalize Hb.
  esplit. split.
  - econstructor; eauto.
    apply extcall_arguments_match; eauto.
  - constructor.
    + constructor.
    + apply Mem.extends_refl.
    + constructor.
      * rewrite_stack_blocks. rewrite init_sp_reg.
        reflexivity.
      * rewrite_stack_blocks. simpl. unfold init_sp in init_sp_not_undef. auto.
      * rewrite_stack_blocks. simpl. generalize init_sp_type. rewrite init_sp_reg.
        unfold init_sp. auto.
      * intro. apply Val.lessdef_refl.
    + erewrite symbols_preserved in Hsymb; eauto. congruence.
    + reflexivity.
    + tauto.
    + reflexivity.
Qed.

Lemma parent_sp_tl_current_sp:
  forall l,
    l <> nil ->
    parent_sp l = current_sp (tl l).
Proof.
  destruct l; simpl; auto. congruence.
Qed.

Lemma transf_final_states:
  forall sg,
  forall st1 st2 r
    (MATCH: match_states prog init_ra st1 st2)
    (CSC: call_stack_consistency ge sg (Mem.stack m) st1)
    (FINAL: MachX.final_state init_mach_rs sg st1 r),
    final_state_with_extends (AsmX.final_state init_asm_rs sg) st2 r.
Proof.
  intros.
  inv FINAL.
  inv MATCH.
  inv STACKS.
  inv AG.
  econstructor.
  econstructor.
  symmetry; assumption.
  rewrite init_sp_reg. rewrite agree_sp. unfold init_sp.
  inv CSC. inv CallStackConsistency.
  rewrite parent_sp_tl_current_sp. congruence.
  intro EQ; rewrite EQ in agree_sp_def. simpl in agree_sp_def. congruence.
  reflexivity.
  assumption.
  intros. eapply Val.lessdef_trans. eapply CALLEE_SAVE. assumption. auto.
  congruence.
  unfold loc_external_result.
  generalize (loc_result sg). induction r; simpl; auto.
  apply Val.longofwords_lessdef; auto.
Qed.

Hypothesis init_ra_type: Val.has_type (init_asm_rs RA) Tptr.

Lemma init_sp_zero: forall (b0 : block) (o : ptrofs), init_sp = Vptr b0 o -> o = Ptrofs.zero.
Proof.
  unfold init_sp, current_sp, current_frame_sp.
  intros b0 o.
  repeat destr; inversion 1.
Qed.

Hypothesis genv_frames_ok:
 forall (fb : block) (f : Mach.function),
 Genv.find_funct_ptr (Genv.globalenv prog) fb = Some (Internal f) ->
 0 < Mach.fn_stacksize f
.

Lemma list_forall2_eq:
  forall {A: Type} (l1 l2: list A),
    list_forall2 (fun a b => a = b) l1 l2 ->
    l1 = l2.
Proof.
  induction 1; simpl; f_equal; eauto.
Qed.

Variable sg: signature.

Hypothesis init_sp_has_stackinfo:
  init_sp_stackinfo sg (Mem.stack m).

Hypothesis init_ra_is_after_call:
  (forall (b0 : block) (o : ptrofs),
   init_ra = Vptr b0 o ->
   forall f : fundef,
   Genv.find_funct_ptr (Genv.globalenv tprog) b0 = Some f -> is_after_call f (Ptrofs.unsigned o)).

Theorem transf_program_correct:
  forall args,
    forward_simulation
    (MachX.semantics (Asmgenproof0.return_address_offset) Mach.invalidate_frame2 init_mach_rs init_ra prog i sg args m)
    (semantics_with_extends (AsmX.semantics init_asm_rs tprog i sg args m)).
Proof.
  intros args.
  eapply forward_simulation_star with (measure := measure)
                                        (match_states := fun s1 s2 => match_states prog init_ra s1 s2
                                                                   /\ has_code (Asmgenproof0.return_address_offset) ge s1
                                                                   /\ call_stack_consistency ge sg (Mem.stack m) s1).
  - eapply senv_preserved; eauto.
  - simpl; intros s1 IS. edestruct transf_initial_states as (st2 & IS2 & MS); eauto.
    exists st2; split; auto. repeat split; auto.
    inv IS. constructor. constructor.
    inv IS. constructor. rewrite_stack_blocks. constructor. reflexivity. simpl. auto.
    simpl; auto.
    red; rewrite_stack_blocks; constructor. auto.
  - intros s1 s2 r (MS & HC & CSC) FS.
    eapply transf_final_states; eauto.
  - simpl; intros s1 t s1' STEP s2 (MS & HC & CSC).
    edestruct step_simulation with (init_ra0 := init_ra) as [(s2' & STEPS & MS')|(LT & EMPTY & MS')]; eauto.
    red; split; auto.
    left; exists s2'; split; eauto. split; auto. split; auto. eapply has_code_step; eauto. eapply csc_step; eauto.
    unfold invalidate_frame2. intros. rewrite_stack_blocks. intro A; rewrite A; simpl; auto.
    unfold invalidate_frame2. intros. red in H0 |- *. rewrite_stack_blocks. intro A; rewrite A in H0; inv H0. constructor; auto.
    right; split; auto. split; auto. split; auto. split; auto.
    eapply has_code_step; eauto. eapply csc_step; eauto.
    unfold invalidate_frame2. intros. rewrite_stack_blocks. intro A; rewrite A; simpl; auto.
    unfold invalidate_frame2. intros. red in H0 |- *. rewrite_stack_blocks. intro A; rewrite A in H0; inv H0. constructor; auto.
Qed.

End PRESERVATION.
