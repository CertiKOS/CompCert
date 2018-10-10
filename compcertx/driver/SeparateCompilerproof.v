
(** We do NOT import compcert.driver.Compiler, because we do NOT want
to depend on passes that are unsupported (e.g. CompCert C) *)

(** I can list the passes of CompCert backwards by heart! *)

Require SeparateCompiler.
Require AsmgenproofX.
Require MachX2Mach2X.
Require StackingproofX.
Require CleanupLabelsproofX.
Require LinearizeproofX.
Require TunnelingproofX.
Require AllocproofX.
Require DeadcodeproofX.
Require ConstpropproofX.
Require CSEproofX.
Require RenumberproofX.
Require InliningproofX.
Require TailcallproofX.
Require RTLgenproofX.
Require SelectionproofX.
Require CminorgenproofX.
Require CshmgenproofX.
Require RTLtypingX.

Import Coqlib.
Import String.
Import Errors.
Import AST.
Import Values.
Import MemoryX.
Import Globalenvs.
Import ComposePasses.
Import Events.
Import SmallstepX.
Import Conventions1.
Import Asm.
Import SeparateCompiler.

Local Open Scope string_scope.

(** * Semantic preservation *)

(** We prove that the [transf_program] translations preserve semantics
  by constructing the following simulations:
- Forward simulations from [Cstrategy] / [Cminor] / [RTL] to [Asm]
  (composition of the forward simulations for each pass).
- Backward simulations for the same languages
  (derived from the forward simulation, using receptiveness of the source
  language and determinacy of [Asm]).
- Backward simulation from [Csem] to [Asm]
  (composition of two backward simulations).

These results establish the correctness of the whole compiler! *)

Section WITHCONFIG.
Context mem `{external_calls_prf : ExternalCalls mem}
        `{memory_model_x: !Mem.MemoryModelX mem}.

Context {i64_helpers: SplitLongproof.I64HelpersCorrect mem}.

Variables
  (p: Clight.program) (p2: RTL.program)
  (TRANSL_TO_RTL: transf_clight_program_to_rtl p = OK p2)

  (** For Inlining, we need a parameter which contains functions to inline. We do not care here
      how it is computed, as long as it is sound with the intermediate representation p2.
      It can be very well instantiated with [PTree.empty _] to disable function inlining. *)
.

Let fenv := Inlining.funenv_program p2.


Ltac rew_genv_next :=
  lazymatch goal with
  | |- context [Genv.genv_next (Genv.globalenv ?p)] =>
    match goal with
    | H: Cminorgen.transl_program ?p = OK _ |- _ =>
      rewrite <- (Cminorgenproof.genv_next_preserved _ _ (Cminorgenproof.transf_program_match _ _ H))
    | H: Selection.sel_program ?p = OK _ |- _ =>
      rewrite <- (Selectionproof.genv_next_preserved _ _ (Selectionproof.transf_program_match _ _ H))
    | H: RTLgen.transl_program ?p = OK _ |- _ =>
      rewrite <- (RTLgenproof.genv_next_preserved _ _ (RTLgenproof.transf_program_match _ _ H))
    | H := Tailcall.transf_program ?p |- _ =>
           rewrite <- (Tailcallproof.genv_next_preserved _ _ (Tailcallproof.transf_program_match p)); fold H
         | H: InliningX.transf_program _ ?p = OK _ |- _ =>
           rewrite <- (Inliningproof.genv_next_preserved _ _ (Inliningproof.transf_program_match _ _ H))
         | H := Renumber.transf_program ?p |- _ =>
                rewrite <- (Renumberproof.genv_next_preserved _ _ (Renumberproof.transf_program_match p)); fold H
              | H := ConstpropX.transf_program ?p |- _ =>
                     rewrite <- (ConstpropproofX.genv_next_preserved p); fold H
                   | H: CSEX.transf_program ?p = OK _ |- _ =>
                     rewrite <- (CSEproofX.genv_next_preserved _ _ H)
                   | H: DeadcodeX.transf_program ?p = OK _ |- _ =>
                     rewrite <- (DeadcodeproofX.genv_next_preserved _ _ H)
                   | H: Allocation.transf_program ?p = OK _ |- _ =>
                     rewrite <- (Allocproof.genv_next_preserved _ _ (Allocproof.transf_program_match _ _ H))
                   | H := Tunneling.tunnel_program ?p |- _ =>
                          rewrite <- (Tunnelingproof.genv_next_preserved _ _ (Tunnelingproof.transf_program_match p)); fold H
                        | H: Linearize.transf_program ?p = OK _ |- _ =>
                          rewrite <- (Linearizeproof.genv_next_preserved _ _ (Linearizeproof.transf_program_match _ _ H))
                        | H := CleanupLabels.transf_program ?p |- _ =>
                               rewrite <- (CleanupLabelsproof.genv_next_preserved _ _ (CleanupLabelsproof.transf_program_match p)); fold H
    end
  end.

Lemma transf_clight_to_linear_correct:
    forall fn_stack_requirements
      (tp: Linear.program)
      (TRANSL_TO_LINEAR: transf_rtl_program_to_linear fenv p2 = OK tp)
      m
      (INJECT_NEUTRAL: Mem.inject_neutral (Mem.nextblock m) m)
      (GENV_NEXT: Ple (Genv.genv_next (Genv.globalenv tp)) (Mem.nextblock m))
      args
      (args_inj: Val.inject_list (Mem.flat_inj (Mem.nextblock m)) args args)
      sg
      init_linear_rs
      (Hargs_val:   args = map (fun r : rpair Locations.loc => Locations.Locmap.getpair r init_linear_rs) (loc_arguments sg))
 
      (Hargs_type:
         Val.has_type_list
           (map (fun r : rpair Locations.loc => Locations.Locmap.getpair r init_linear_rs) (loc_arguments sg))
           (sig_args sg))
      i
    ,
      forward_simulation
        (ClightX.semantics (fn_stack_requirements) p i m sg args)
        (semantics_with_inject (LinearX.semantics fn_stack_requirements init_linear_rs tp i sg args m) m).
  Proof.
    intros.
    unfold fenv in *.
    revert TRANSL_TO_RTL; unfold transf_clight_program_to_rtl; simpl.
    caseEq (Cshmgen.transl_program p); simpl; try congruence; intros p01 EQ01.
    caseEq (Cminorgen.transl_program p01); simpl; try congruence; intros p02 EQ02.
    caseEq (Selection.sel_program p02); simpl; try congruence; intros p1 EQ03.
    caseEq (RTLgen.transl_program p1); simpl; try congruence; intros p11 EQ11.
    intro.
    inv TRANSL_TO_RTL.
    revert TRANSL_TO_LINEAR; unfold transf_rtl_program_to_linear; simpl.
    set (p2 := Tailcall.transf_program p11) in *.
    caseEq (InliningX.transf_program (Inlining.funenv_program p2) p2); simpl; try congruence; intros p3 EQ3.
    set (p31 := Renumber.transf_program p3) in *.
    set (p32 := ConstpropX.transf_program p31) in *.
    set (p33 := Renumber.transf_program p32) in *.
    caseEq (CSEX.transf_program p33); simpl; try congruence; intros p34 EQ34.
    caseEq (DeadcodeX.transf_program p34); simpl; try congruence; intros p35 EQ35.
    caseEq (Allocation.transf_program p35); simpl; try congruence; intros p4 EQ4.
    set (p5 := Tunneling.tunnel_program p4) in *.
    caseEq (Linearize.transf_program p5); simpl; try congruence; intros p6 EQ6.
    set (p7 := CleanupLabels.transf_program p6) in *.
    intro EQTP.
    inv EQTP.
    eapply compose_forward_simulations.
    apply CshmgenproofX.transl_program_correct. eassumption.
    eapply compose_forward_simulations.
    apply CminorgenproofX.transl_program_correct. eassumption.
    assumption.
    {

        repeat rew_genv_next; eauto.
    }
    assumption.
    eapply compose_forward_simulations.
    {
      apply forward_simulation_extends_right_inject.
      apply SelectionproofX.transf_program_correct. eauto.
    }
    eapply compose_forward_simulations.
    {
      apply forward_simulation_extends_right_inject.
      apply RTLgenproofX.transf_program_correct. eassumption.
    }
    eapply compose_forward_simulations.
    {
      eapply forward_simulation_inject_right.
      apply TailcallproofX.transf_program_correct; auto.
      repeat rew_genv_next; eauto.
    }
    eapply compose_forward_simulations.
    {
      eapply forward_simulation_inject_right.
      eapply InliningproofX.transf_program_correct; eauto.
      fold p2. repeat rew_genv_next; eauto.
    }
    eapply forward_simulation_extends_right_inject.
    eapply compose_forward_simulations.
    eapply RenumberproofX.transf_program_correct.
    eapply compose_forward_simulations.
    eapply ConstpropproofX.transf_program_correct; eauto.
    {
      fold p31.
      repeat rew_genv_next; eauto.
    }
    eapply forward_simulation_extends_right.
    eapply compose_forward_simulations.
    eapply RenumberproofX.transf_program_correct.
    eapply compose_forward_simulations.
    {
      eapply CSEproofX.transf_program_correct; eauto.
      {
        fold p31. fold p32. fold p33.
        repeat rew_genv_next; eauto.
      }
    }
    eapply compose_forward_simulations.
    eapply forward_simulation_extends_right.
    eapply DeadcodeproofX.transf_program_correct; eauto.
    {
      repeat rew_genv_next; eauto.
    }
    eapply forward_simulation_extends_right.
    eapply compose_forward_simulations.
    {
      apply AllocproofX.transf_program_correct. eassumption.
      reflexivity.
      eassumption.
    }
    eapply compose_forward_simulations.
    {
      apply forward_simulation_extends.
      apply TunnelingproofX.transf_program_correct.
    }
    eapply compose_forward_simulations.
    {
      apply forward_simulation_extends.
      apply LinearizeproofX.transf_program_correct. eassumption.
    }
    apply forward_simulation_extends.
    apply CleanupLabelsproofX.transf_program_correct.
  Qed.

  Lemma plt_eq_eq:
    forall a b, (forall c, Plt c a <-> Plt c b) -> a = b.
  Proof.
    intros.
    destruct (plt a b). specialize (H a). rewrite <- H in p0. xomega.
    destruct (plt b a). specialize (H b). rewrite H in p0. xomega. xomega.
  Qed.

  Definition fn_stack_requirements (tp: Asm.program) (id: ident) : Z :=
    match Globalenvs.Genv.find_symbol (Globalenvs.Genv.globalenv tp) id with
    | Some b =>
      match Globalenvs.Genv.find_funct_ptr (Globalenvs.Genv.globalenv tp) b with
      | Some (Internal f) => Asm.fn_stacksize f
      | _ => 0
      end
    | None => 0
    end.

  Lemma match_program_no_more_functions:
    forall {F1 V1 F2 V2}
      `{Linking.Linker F1} `{Linking.Linker V1}
      Mf Mv
      (p1: AST.program F1 V1) (p2: AST.program F2 V2),
      Linking.match_program Mf Mv p1 p2 ->
      forall b,
        Globalenvs.Genv.find_funct_ptr (Globalenvs.Genv.globalenv p1) b = None ->
        Globalenvs.Genv.find_funct_ptr (Globalenvs.Genv.globalenv p2) b = None.
  Proof.
    intros.
    generalize (Globalenvs.Genv.find_def_match_2 H1 b).
    inversion 1.
    - destruct (Globalenvs.Genv.find_funct_ptr (Globalenvs.Genv.globalenv p0) b) eqn:?; auto.
      apply Globalenvs.Genv.find_funct_ptr_iff in Heqo. congruence.
    - destruct (Globalenvs.Genv.find_funct_ptr (Globalenvs.Genv.globalenv p0) b) eqn:?; auto.
      apply Globalenvs.Genv.find_funct_ptr_iff in Heqo. rewrite Heqo in H5.  inv H5.
      inv H6.
      symmetry in H4.
      apply Globalenvs.Genv.find_funct_ptr_iff in H4. congruence.
  Qed.

  Definition funsig (f: Asm.fundef) : signature :=
    match f with
      External ef => ef_sig ef
    | Internal f => fn_sig f
    end.

  Theorem transf_clight_program_correct:
    forall
      tp
      (TRANSL_TO_ASM: transf_rtl_program fenv p2 = OK tp)
      m init_asm_rs
      (ASM_INVARIANT: AsmX.asm_invariant (Genv.globalenv tp) init_asm_rs m)
      args sg
      (EXTCALL_ARGS: Asm.extcall_arguments init_asm_rs m sg args)
      i b
      (Hsymb:  Genv.find_symbol (Genv.globalenv tp) i = Some b)
      (SIGNATURE: forall f, Genv.find_funct_ptr (Genv.globalenv tp) b = Some f -> sg = funsig f)
      (INITSP: StackingproofX.init_sp m = init_asm_rs RSP)
      (PC_VAL: init_asm_rs PC = Values.Vptr b Integers.Ptrofs.zero)
      (RA_NOT_VUNDEF: init_asm_rs RA <> Vundef)
      (ARGSSIZE: 4 * size_arguments sg <= Integers.Ptrofs.max_unsigned)
      (ARGSTYPE:  Val.has_type_list
                    (map
                       (fun r =>
                          Locations.Locmap.getpair
                            r
                            (StackingproofX.init_linear_rs
                               (AsmgenproofX.init_mach_rs init_asm_rs)
                               m))
                       (loc_arguments sg))
                    (sig_args sg))
      (StackInfo: Mach.init_sp_stackinfo sg (Mem.stack m))
      (RaCorrect:   forall (b0 : block) (o : Integers.Ptrofs.int),
          init_asm_rs RA = Vptr b0 o ->
          forall f : fundef,
            Genv.find_funct_ptr (Genv.globalenv tp) b0 = Some f ->
            is_after_call f (Integers.Ptrofs.unsigned o)
      ),
      forward_simulation
        (ClightX.semantics (fn_stack_requirements tp) p i m sg args)
        (semantics_with_inject (AsmX.semantics init_asm_rs tp i sg args m) m).
  Proof.
    intros.
    rewrite <- transf_rtl_program_to_linear_to_asm_correct in TRANSL_TO_ASM.
    simpl in TRANSL_TO_ASM.
    destruct (transf_rtl_program_to_linear fenv p2) as [p7 | ] eqn:LINEAR; try discriminate.
    simpl in TRANSL_TO_ASM.
    unfold transf_linear_program in TRANSL_TO_ASM.
    simpl in TRANSL_TO_ASM.
    revert TRANSL_TO_ASM.
    caseEq (Stacking.transf_program p7); simpl; try congruence; intros p8 EQ8.
    intro EQTP.
    inv ASM_INVARIANT.
    inv inv_inject_neutral.
    assert
      (Ple (Genv.genv_next (Genv.globalenv p7)) (Mem.nextblock m))
      as LE.
    {
      erewrite <- StackingproofX.genv_next_preserved; eauto.
      erewrite <- AsmgenproofX.genv_next_preserved; eauto.
    }
    (* from C to linear *)
    assert (forward_simulation
              (ClightX.semantics (fn_stack_requirements tp) p i m sg args)
              (semantics_with_inject (LinearX.semantics (fn_stack_requirements tp) (StackingproofX.init_linear_rs (AsmgenproofX.init_mach_rs init_asm_rs) m) p7 i sg args m) m))
      as C_to_linear.
    {
      eapply transf_clight_to_linear_correct.
      assumption.
      assumption.
      assumption.
      eapply AsmX.extcall_args_inject_neutral; eauto.
      eapply StackingproofX.extcall_args_eq. rewrite INITSP. eapply AsmgenproofX.extcall_args_match_inv. eassumption.
      assumption.
    }

  (* finally, connect with the remaining part *)
  eapply compose_forward_simulations.
  eassumption.
  eapply SmallstepX.forward_simulation_inject_right.
  eapply compose_forward_simulations.
  {
    replace (fn_stack_requirements tp) with (Stackingproof.fn_stack_requirements p8).
    apply StackingproofX.transf_program_correct. eassumption.
    rewrite INITSP. apply AsmgenproofX.extcall_args_match_inv. assumption.
    assumption.
    erewrite <- AsmgenproofX.genv_next_preserved; eauto.
    intros; eapply inv_reg_inject_neutral.
    assumption.
    {
      intros f b0.
      erewrite <- Stackingproof.symbols_preserved. 2: apply Stackingproof.transf_program_match; eauto.
      erewrite <- Asmgenproof.symbols_preserved. 2: apply Asmgenproof.transf_program_match; eauto.
      rewrite Hsymb. intro SYMB; inv SYMB.
      intros FFPlinear.
      edestruct Stackingproof.function_ptr_translated as (fmach & FFPmach & TFstacking); eauto using Stackingproof.transf_program_match.
      edestruct Asmgenproof.functions_translated as (fasm & FFPasm & TFasmgen); eauto using Asmgenproof.transf_program_match.
      replace (Linear.funsig f) with (funsig fasm). exploit SIGNATURE; eauto. intro; subst. eauto.
      clear - TFstacking TFasmgen.
      erewrite <- Stackingproof.sig_preserved; eauto.
      unfold Asmgen.transf_fundef, Asmgen.transf_function in TFasmgen.
      destruct fmach; simpl in *; monadInv TFasmgen.
      monadInv EQ. repeat destr_in EQ1. unfold Asmgen.transl_function in EQ0. monadInv EQ0. inv EQ1.
      destr_in EQ2. inv EQ2. reflexivity.
      reflexivity.
    }
    {
      unfold AsmgenproofX.init_mach_rs.
      intros.
      red in inv_reg_wt.
      unfold AsmX.typ_of_preg in inv_reg_wt.
      specialize (inv_reg_wt (preg_of r)).
      rewrite (AsmX.mreg_of_complete r) in inv_reg_wt. auto.
    }
    apply Asmgenproof.return_address_exists.
    generalize (inv_reg_wt RA). unfold AsmX.typ_of_preg. simpl. eauto. auto.
    apply Axioms.functional_extensionality. intro id.
    unfold Stackingproof.fn_stack_requirements, fn_stack_requirements.
    erewrite Asmgenproof.symbols_preserved. 2: apply Asmgenproof.transf_program_match; eauto.
    destr.
    destr. 
    eapply Asmgenproof.functions_translated in Heqo0.
    2: apply Asmgenproof.transf_program_match; eauto.
    destruct Heqo0 as (tf & FFP & TF); rewrite FFP.
    destruct f; simpl in *; monadInv TF; auto.
    unfold Asmgen.transf_function in EQ. monadInv EQ. destr_in EQ1. inv EQ1.
    unfold Asmgen.transl_function in EQ0. monadInv EQ0. destr_in EQ1. inv EQ1. simpl. auto.
    eapply match_program_no_more_functions in Heqo0; eauto. rewrite Heqo0. auto.
    apply Asmgenproof.transf_program_match; eauto.
  }
  eapply compose_forward_simulations.
  apply forward_simulation_extends_inject.
  apply forward_simulation_extends_right.
  {
    apply MachX2Mach2X.transf_program_correct; auto.
    eapply Stackingproof.stacking_frame_correct.
    eapply Stackingproof.transf_program_match. eauto.    
  }
  apply forward_simulation_extends_inject.
  apply forward_simulation_extends_right.
  eapply AsmgenproofX.transf_program_correct. eassumption.
  eassumption.
  assumption.
  assumption.
  rewrite <- INITSP.  reflexivity.
  {
    unfold AsmgenproofX.init_sp. inv StackInfo. simpl.
    unfold current_frame_sp. simpl.
    inv PRIV. congruence.
  }
  apply inv_reg_wt.
  eapply Stackingproof.stacking_frame_correct.
  eapply Stackingproof.transf_program_match. eauto.
  auto.
  auto.
  Qed.

End WITHCONFIG.
