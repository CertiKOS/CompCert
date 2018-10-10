Require compcert.backend.Stackingproof.
Require MachX.
Require SmallstepX.

Import Coqlib.
Import Integers.
Import AST.
Import ValuesX.
Import MemoryX.
Import Globalenvs.
Require Import EventsX.
Import SmallstepX.
Import Locations.
Require Import LinearX.
Import Lineartyping.
Import MachX.
Import Stacking.
Export Stackingproof.

Section WITHCONFIG.
Context `{external_calls_prf: ExternalCalls}.
Variable (return_address_offset : function -> code -> ptrofs -> Prop).

Variable prog: Linear.program.
Variable tprog: Mach.program.
Hypothesis TRANSF: transf_program prog = Errors.OK tprog.

Let MATCH_PROG : match_prog prog tprog.
Proof.
  apply transf_program_match; auto.
Qed.

Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma genv_next_preserved:
  Genv.genv_next tge = Genv.genv_next ge.
Proof.
  eapply senv_preserved; eauto.
Qed.

Lemma extcall_arg_push:
  forall rs m sp l v,
    extcall_arg rs m sp l v ->
    extcall_arg rs (Mem.push_new_stage m) sp l v.
Proof.
  induction 1; simpl; intros; econstructor; eauto.
  unfold load_stack in *.
  rewrite Mem.push_new_stage_loadv; auto.
Qed.

Lemma extcall_arg_pair_push:
  forall rs m sp p v,
    extcall_arg_pair rs m sp p v ->
    extcall_arg_pair rs (Mem.push_new_stage m) sp p v.
Proof.
  induction 1; simpl; constructor; eauto using extcall_arg_push.
Qed.


Variables
  (init_mach_rs: Mach.regset)
  (init_m: mem)
.

Definition init_sp: val := current_sp (Mem.stack init_m).

Lemma init_sp_ofs_zero:
  forall b o, init_sp = Vptr b o -> o = Ptrofs.zero.
Proof.
  intros b o; unfold init_sp, current_sp, current_frame_sp.
  repeat destr; inversion 1.
Qed.

Definition init_linear_rs: Locations.Locmap.t :=
    fun ros =>
      match ros with
        | R r => init_mach_rs r
        | S Outgoing ofs ty =>
          match load_stack init_m init_sp ty (Ptrofs.repr (Stacklayout.fe_ofs_arg + 4 * ofs)) with
            | Some v => v
            | None => Vundef
          end
        | _ => Vundef
      end.

Lemma extcall_arg_eq l v:
  Mach.extcall_arg init_mach_rs init_m init_sp l v ->
  v = init_linear_rs l.
Proof.
  intro H.
  inv H; auto.
  unfold init_linear_rs.
  rewrite H0.
  reflexivity.
Qed.

Lemma extcall_arg_pair_eq l v:
  Mach.extcall_arg_pair init_mach_rs init_m init_sp l v ->
  v = Locmap.getpair l init_linear_rs.
Proof.
  inversion 1; subst; eauto using extcall_arg_eq.
  simpl.
  f_equal; auto using extcall_arg_eq.
Qed.

Lemma extcall_args_eq:
  forall ll vl,
    list_forall2 (Mach.extcall_arg_pair init_mach_rs init_m init_sp) ll vl
  -> vl = map (fun r => Locmap.getpair r init_linear_rs) ll.
Proof.
  induction 1; simpl.
   reflexivity.
  f_equal; eauto using extcall_arg_pair_eq.
Qed.

Lemma extcall_arg_init_linear_rs:
  forall la,
    list_forall2 (extcall_arg_pair init_mach_rs init_m init_sp) la (map (fun r => Locmap.getpair r init_linear_rs) la) ->
    forall l, In l (regs_of_rpairs la) ->
    extcall_arg init_mach_rs init_m init_sp l (init_linear_rs l).
Proof.

  induction la; simpl; inversion 1; subst.
   tauto.
  intros l H0.
  apply in_app_iff in H0.
  destruct H0 as [ H0 | ] ; auto.
  inv H3.
  + destruct H0; try contradiction.
    subst.
    auto.
  + simpl in H0.
    destruct H0.
    - subst. auto.
      inv H2; constructor; auto.
      unfold init_linear_rs. destr. 
    - destruct H0; try contradiction.
      subst.
      inv H6; constructor; auto.
      unfold init_linear_rs. rewrite H0. reflexivity.
Qed.

Variables
  (init_ra: val)
  (sg: signature)
  (args: list val)
  (Hargs: extcall_arguments init_mach_rs init_m init_sp sg args)
  (Hinject_neutral: Mem.inject_neutral (Mem.nextblock init_m) init_m)
  (Hgenv_next: Ple (Genv.genv_next tge) (Mem.nextblock init_m))
.

Hypothesis init_mach_rs_inj:
  forall r, Val.inject (Mem.flat_inj (Mem.nextblock init_m)) (init_mach_rs r) (init_mach_rs r).

(* Variable init_linear_m: mem. *)
(* Hypothesis init_linear_free_extcall_arg: free_extcall_args init_sp init_m (regs_of_rpairs (Conventions1.loc_arguments sg)) = Some init_linear_m. *)

Lemma init_sp_int: Val.has_type init_sp Tptr.
Proof.
  unfold init_sp, current_sp, current_frame_sp;
    repeat destr;
    auto using Val.Vnullptr_has_type, Val.Vptr_has_type.
Qed.

Context `{memory_model_x: !Mem.MemoryModelX mem}.

Lemma init_sp_valid:
  forall (b : block) (o : ptrofs),
    init_sp = Vptr b o -> Mem.valid_block init_m b.
Proof.
  unfold init_sp, current_sp, current_frame_sp.
  intros b o.
  repeat destr; inversion 1. subst.
  eapply Mem.in_frames_valid. rewrite Heqs.
  rewrite in_stack_cons; left.
  red. rewrite Heqo0. simpl. unfold get_frame_blocks. rewrite Heql.
  left; reflexivity.
Qed.

Lemma extcall_arg_slot_change_reg:
  forall rs rs' m sl o t sp v,
    extcall_arg rs m sp (S sl o t) v ->
    extcall_arg rs' m sp (S sl o t) v.
Proof.
  intros rs rs' m sl o t sp v EA; inv EA; constructor; auto.
Qed.

Hypothesis args_bnds:   4 * Conventions1.size_arguments sg <= Ptrofs.max_unsigned.

Variable i: ident.

Hypothesis init_sp_has_stackinfo:
  forall f b,
    Genv.find_symbol ge i = Some b ->
    Genv.find_funct_ptr ge b = Some f ->
    init_sp_stackinfo (Linear.funsig f) (Mem.stack init_m).

Lemma transf_initial_states:
  forall s
         (INIT: LinearX.initial_state (Stackingproof.fn_stack_requirements tprog) init_linear_rs prog i sg args init_m s),
    exists s',
      MachX.initial_state init_mach_rs tprog i sg args init_m s' /\
      match_states_inv
        return_address_offset
        prog tprog
        init_ra
        init_linear_rs sg
        (Mem.stack init_m)
        init_m
        s s'.
Proof.
  intros. inv INIT.
  exploit function_ptr_translated; eauto.
  destruct 1 as [tf [Htf TRANS]].
  esplit.
  split.
  - econstructor.
    erewrite symbols_preserved; eauto.
    assumption.
  - constructor. econstructor; eauto.
    + econstructor; eauto.
    + eexists; split; eauto.
      apply Genv.find_invert_symbol; auto.
      erewrite symbols_preserved; eauto.
    + unfold init_linear_rs. red. eauto.
    + red. unfold Mem.flat_inj.
      intros.
      destruct plt; intuition congruence.
    + rewnb. xomega.
    + unfold Stackingproof.init_sp.
      unfold block_prop. destr. unfold Mem.flat_inj.
      apply pred_dec_true; auto.
      apply Mem.in_frames_valid.
      revert Heqv. unfold current_sp. destr. inversion 1.
      unfold current_frame_sp.
      repeat destr; inversion 1. subst.
      rewrite in_stack_cons; left.
      eapply in_frame_in_frames; eauto.
      eapply in_frame'_in_frame; red; rewrite Heql; left; reflexivity.
    + red. unfold Mem.flat_inj.
      intros b' o' EQ b1 b2 delta1 delta2.
      repeat destr.
    +
      Require Import Separation.
      Open Scope sep_scope.

      unfold stack_contents. rewrite sep_pure. split; auto.
      repeat split.
      * simpl. rewrite_stack_blocks. simpl.
        apply Mem.push_new_stage_inject. eapply Mem.neutral_inject. assumption.
      * simpl.
        red; intros.
        red in Hargs.
        exploit extcall_arg_init_linear_rs; eauto. intro EA.
        apply extcall_arg_push in EA.
        eexists; split.
        eapply extcall_arg_slot_change_reg. eauto.
        Opaque Z.mul.
        simpl.
        destruct sl; auto.
        unfold load_stack.
        destruct (Mem.loadv (chunk_of_type ty) init_m
                            (Val.offset_ptr init_sp (Ptrofs.repr (4 * of)))) eqn:?; auto.
        destruct init_sp; try discriminate.
        exploit Mem.loadv_inject.
        eapply Mem.neutral_inject. eassumption.
        eassumption.
        simpl. econstructor.
        unfold Mem.flat_inj. destruct (plt b0 (Mem.nextblock init_m)). reflexivity.
        destruct n.
        eapply Mem.valid_access_valid_block.
        eapply Mem.valid_access_implies.
        eapply Mem.load_valid_access. unfold load_stack, Val.offset_ptr in Heqo. eexact Heqo.
        constructor.
        rewrite Ptrofs.add_zero.
        reflexivity.
        destruct 1 as [? [? ?]].
        unfold load_stack, Val.offset_ptr in Heqo.
        rewrite Heqo in H0. inv H0.
        assumption.
      * simpl.
        exists (Mem.nextblock init_m).
        rewnb. split; auto using Ple_refl.
        constructor.
        -- intros b0 H.
           unfold Mem.flat_inj.
           destruct (plt _ _); auto; contradiction.
        -- intros b1 b2 delta H H1.
           unfold Mem.flat_inj in H.
           destruct (plt _ _); congruence.
        -- intros id b0 H.
           apply Genv.genv_symb_range in H.
           fold ge in H.
           rewrite <- genv_next_preserved in H.
           xomega.
        -- intros id b0 H.
           apply Genv.find_funct_ptr_iff in H.
           apply Genv.genv_defs_range in H.
           fold ge in H.
           rewrite <- genv_next_preserved in H.
           xomega.
        -- intros id b0 H.
           apply Genv.find_var_info_iff in H.
           apply Genv.genv_defs_range in H.
           fold ge in H.
           rewrite <- genv_next_preserved in H.
           xomega.
      * red. simpl. easy.
    + apply stack_equiv_refl; auto.
    + constructor; eauto. rewnb; xomega. constructor.
    + constructor. constructor.
    + constructor. rewrite_stack_blocks.
      simpl. constructor; eauto.
      rewrite_stack_blocks. constructor. auto.
Qed.

Lemma transf_final_states:
  forall s s' r
    (MATCH: match_states_inv
              return_address_offset
              prog tprog
              init_ra
              init_linear_rs sg
              (Mem.stack init_m)
              init_m
              s s')
    (FIN: LinearX.final_state init_linear_rs sg s r),
    final_state_with_inject (MachX.final_state init_mach_rs sg) init_m s' r.
Proof.
  intros.
  inv FIN.
  inv MATCH; try congruence.
  inv MS.
  inv STACKS; try congruence.
  edestruct Mem.unrecord_stack_block_inject_parallel_flat as (m2' & USB' & INJ').
  apply sep_proj2 in SEP. apply mconj_proj1 in SEP. apply SEP. eauto.
  econstructor.
  econstructor. 
  reflexivity.
  { (* Callee-save registers. *)
    intros.
    refine (_ (AGLOCS (R r) _)).
    simpl. intro REW.
    eapply Mem.val_inject_flat_inj_lessdef.
    eapply val_inject_incr_recip.
    rewrite <- REW.
    eapply AGREGS. 
    eapply init_mach_rs_inj.
    auto.
    unfold Conventions1.destroyed_at_call in H.
    Opaque all_mregs.
    rewrite filter_In in H.
    generalize (all_mregs_complete r). intro.
    destruct (Conventions1.is_callee_save r); tauto.
  }
  eauto.
  apply INCR_init. apply INCR_sep.
  eauto.
  generalize (Conventions1.loc_result sg).
  destruct r; simpl; eauto using Val.longofwords_inject.
Qed.

Hypothesis wt_init_mach_rs:
  forall r, Val.has_type (init_mach_rs r) (mreg_type r).

Lemma wt_init_linear_rs:
  wt_locset init_linear_rs.
Proof.
  red.
  destruct l.
  simpl; auto.
  destruct sl; try (constructor; fail).
  unfold init_linear_rs, load_stack.
  case_eq (
      Mem.loadv (chunk_of_type ty) init_m
                (Val.offset_ptr init_sp
                                (Ptrofs.repr (Stacklayout.fe_ofs_arg + 4 * pos)))
    ); try (constructor; fail).
  destruct init_sp; try discriminate.
  unfold Val.offset_ptr, Mem.loadv.
  intros.
  exploit Mem.load_type; eauto.
  destruct ty; simpl; tauto.
Qed.

Theorem wt_initial_state:
  forall i,
  forall S, LinearX.initial_state (Stackingproof.fn_stack_requirements tprog) init_linear_rs prog i sg args init_m S ->
       Lineartyping.wt_state init_linear_rs S.
Proof.
  induction 1.
  exploit Genv.find_funct_ptr_inversion; eauto.
  destruct 1.
  econstructor.
  apply wt_callstack_nil.
  eapply wt_init_linear_rs.
  eapply wt_prog. eassumption. eassumption.
  apply wt_init_linear_rs.
Qed.

Hypothesis return_address_offset_exists:
  forall f sg ros c,
  is_tail (Mcall sg ros :: c) (fn_code f) ->
  exists ofs, return_address_offset f c ofs.

Hypothesis init_ra_int:
  Val.has_type init_ra Tptr.


Hypothesis init_ra_not_undef:
  init_ra <> Vundef.


Theorem transf_program_correct:
  forward_simulation
    (LinearX.semantics (Stackingproof.fn_stack_requirements tprog) init_linear_rs prog i sg args init_m)
    (semantics_with_inject (MachX.semantics return_address_offset invalidate_frame1 init_mach_rs init_ra tprog i sg args init_m) init_m)
.
Proof.
  set (ms :=
         fun s s' =>
           Lineartyping.wt_state init_linear_rs s /\
           match_states_inv return_address_offset prog tprog init_ra init_linear_rs sg
                            (Mem.stack init_m) init_m s s').
  intros.
  eapply forward_simulation_plus with (match_states := ms).
  - apply senv_preserved; auto.
  - intros. simpl in *.
    exploit transf_initial_states; eauto. intros [st2 [A B]].
    exists st2; split; auto. split; auto.
    generalize wt_initial_state; intro WIS.
    inversion H; subst.
    eapply WIS; eauto.
  - intros. destruct H. eapply transf_final_states; eauto.
  - intros. destruct H0.
    exploit transf_step_correct'; eauto.
    eapply Stackingproof.stacking_frame_correct. eauto.
    intros b o. unfold Stackingproof.init_sp, current_sp, current_frame_sp.
    repeat destr; inversion 1.
    eauto.
    intros [s2' [A B]].
    exists s2'; split. exact A. split.
    eapply step_type_preservation; eauto.
    eapply wt_prog. eassumption.
    simpl in *. eassumption.
    assumption.
Qed.

End WITHCONFIG.
