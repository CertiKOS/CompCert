Require Import Coqlib.
Require Import Maps.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Linking.
Require Import ModuleSemantics.
Require Clight.

Coercion Clight.genv_genv : Clight.genv >-> Genv.t.

(** * Clight syntactic composition theorem *)

Section CLIGHT_EQUIV.
  Context (sge tge: Clight.genv).

  Hypothesis cenv_equiv:
    Clight.genv_cenv tge = Clight.genv_cenv sge.

  Hypothesis genv_symb_equiv:
    Genv.genv_symb tge = Genv.genv_symb sge.

  Lemma find_symbol_equiv id:
    Genv.find_symbol tge id = Genv.find_symbol sge id.
  Proof.
    unfold Genv.find_symbol.
    congruence.
  Qed.

  Lemma assign_loc_equiv ty m b ofs v m':
    Clight.assign_loc sge ty m b ofs v m' ->
    Clight.assign_loc tge ty m b ofs v m'.
  Proof.
    destruct 1;
    solve [econstructor; rewrite ?cenv_equiv; eauto].
  Qed.

  Lemma eval_expr_lvalue_equiv e le m:
    (forall exp v,
      Clight.eval_expr sge e le m exp v ->
      Clight.eval_expr tge e le m exp v) /\
    (forall exp b ofs,
      Clight.eval_lvalue sge e le m exp b ofs ->
      Clight.eval_lvalue tge e le m exp b ofs).
  Proof.
    apply Clight.eval_expr_lvalue_ind;
    solve [
      intros;
      erewrite <- ?cenv_equiv;
      econstructor;
      rewrite ?cenv_equiv, ?find_symbol_equiv;
      eauto
    ].
  Qed.

  Lemma eval_expr_equiv e le m exp v:
    Clight.eval_expr sge e le m exp v ->
    Clight.eval_expr tge e le m exp v.
  Proof.
    edestruct eval_expr_lvalue_equiv; eauto.
  Qed.

  Lemma eval_lvalue_equiv e le m exp b ofs:
    Clight.eval_lvalue sge e le m exp b ofs ->
    Clight.eval_lvalue tge e le m exp b ofs.
  Proof.
    edestruct eval_expr_lvalue_equiv; eauto.
  Qed.

  Lemma eval_exprlist_equiv e le m exp tyl vl:
    Clight.eval_exprlist sge e le m exp tyl vl ->
    Clight.eval_exprlist tge e le m exp tyl vl.
  Proof.
    induction 1;
    solve [econstructor; eauto using eval_expr_equiv].
  Qed.

  Lemma blocks_of_env_equiv e:
    Clight.blocks_of_env tge e = Clight.blocks_of_env sge e.
  Proof.
    unfold Clight.blocks_of_env, Clight.block_of_binding.
    rewrite cenv_equiv.
    reflexivity.
  Qed.

  Lemma function_entry2_equiv f vargs m e le m':
    Clight.function_entry2 sge f vargs m e le m' ->
    Clight.function_entry2 tge f vargs m e le m'.
  Proof.
    destruct 1; constructor; eauto.
    revert H2; clear - cenv_equiv.
    induction 1; econstructor; eauto.
    rewrite cenv_equiv; eauto.
  Qed.
End CLIGHT_EQUIV.

Section CLIGHT_UNLINK.
  Context (ps: nlist Clight.program).
  Context (pt: Clight.program).
  Context (Hpt: link_list ps = Some pt).

  Let I := { p : Clight.program | nIn p ps }.
  Let L := fun i : I => Clight.semantics2 (proj1_sig i).
  Let Ls := Clight.semantics2 pt.
  Let Lt := HComp.semantics (Smallstep.symbolenv Ls) L.

  Let sge := Smallstep.globalenv Ls.
  Let tge := Smallstep.globalenv Lt.

  Hypothesis cenv_link:
    forall i, Clight.genv_cenv (tge i) = Clight.genv_cenv sge.

  Hypothesis genv_symb_link:
    forall i, Genv.genv_symb (tge i) = Genv.genv_symb sge.

  Hypothesis genv_defs_unlink:
    forall i id sdef,
      (Genv.genv_defs sge) ! id = Some sdef ->
      exists tdef,
        (Genv.genv_defs (tge i)) ! id = Some tdef /\
        linkorder tdef sdef.

  Lemma find_funct_unlink_call vf sfd ty i:
    Genv.find_funct sge vf = Some sfd ->
    Clight.type_of_fundef sfd = ty ->
    exists tfd,
      Genv.find_funct (tge i) vf = Some tfd /\
      linkorder tfd sfd /\
      Clight.type_of_fundef tfd = ty.
  Admitted.

  Lemma find_funct_unlink_switch vf fd:
    Genv.find_funct sge vf = Some fd ->
    exists i,
      Genv.find_funct (tge i) vf = Some fd.
  Admitted.

  Lemma find_funct_ptr_internal_unlink_switch b fd:
    Genv.find_funct_ptr sge b = Some (Ctypes.Internal fd) ->
    exists i,
      Genv.find_funct_ptr (tge i) b = Some (Ctypes.Internal fd).
  Admitted.

  (** Matching states. Per the definitions above, the state of the
    target machine is a stack where each entry designates a module,
    and a Clight state for that module. The source machine is simply
    the Clight state for the linked program. The outside of the source
    state matches the topmost state in the target, however .. *)

  Inductive match_states: state Ls -> state Lt -> Prop :=
    | match_state f s k e le m i ki stk:
        match_cont k ki stk ->
        match_states
          (Clight.State f s k e le m)
          (existT _ i (Clight.State f s ki e le m) :: stk)
    | match_callstate sfd tfd vargs k m i ki stk:
        linkorder tfd sfd ->
        match_cont k ki stk ->
        match_states
          (Clight.Callstate sfd vargs k m)
          (existT _ i (Clight.Callstate tfd vargs ki m) :: stk)
    | match_returnstate vres k m i ki stk:
        match_cont k ki stk ->
        match_states
          (Clight.Returnstate vres k m)
          (existT _ i (Clight.Returnstate vres ki m) :: stk)

  with match_cont: Clight.cont -> Clight.cont -> _ -> Prop :=
    | match_kstop:
        match_cont Clight.Kstop Clight.Kstop nil
    | match_kseq stmt k ki stk:
        match_cont k ki stk ->
        match_cont
          (Clight.Kseq stmt k)
          (Clight.Kseq stmt ki) stk
    | match_kloop1 stmt1 stmt2 k ki stk:
        match_cont k ki stk ->
        match_cont
          (Clight.Kloop1 stmt1 stmt2 k)
          (Clight.Kloop1 stmt1 stmt2 ki) stk
    | match_kloop2 stmt1 stmt2 k ki stk:
        match_cont k ki stk ->
        match_cont
          (Clight.Kloop2 stmt1 stmt2 k)
          (Clight.Kloop2 stmt1 stmt2 ki) stk
    | match_kswitch k ki stk:
        match_cont k ki stk ->
        match_cont
          (Clight.Kswitch k)
          (Clight.Kswitch ki) stk
    | match_kcall id f e le k ki stk:
        match_cont k ki stk ->
        match_cont
          (Clight.Kcall id f e le k)
          (Clight.Kcall id f e le ki) stk
    | match_cons k ki stk i f vargs m:
        Clight.is_call_cont k ->
        match_cont k ki stk ->
        match_cont
          k
          (Clight.Kstop) (existT _ i (Clight.Callstate f vargs ki m) :: stk).

  Lemma match_call_cont k ki stk:
    match_cont k ki stk ->
    match_cont
      (Clight.call_cont k)
      (Clight.call_cont ki) stk.
  Proof.
    clear.
    induction 1; simpl; eauto; try solve [constructor; eauto].
    - replace (Clight.call_cont k) with k in * by (destruct k; tauto).
      constructor; eauto.
  Qed.

  Hint Constructors match_cont.
  Hint Resolve match_call_cont.

  Lemma match_is_call_cont k ki stk:
    match_cont k ki stk ->
    Clight.is_call_cont k ->
    Clight.is_call_cont ki.
  Proof.
    destruct 1; simpl; eauto.
  Qed.

  Lemma match_find_label k ki stk lbl c s k':
    Clight.find_label lbl c k = Some (s, k') ->
    match_cont k ki stk ->
    exists ki',
      Clight.find_label lbl c ki = Some (s, ki') /\
      match_cont k' ki' stk.
  Proof.
  (*
    intros Hk H.
    revert k ki stk s k' Hk H.
    induction c; simpl; eauto; intros.
    - edestruct (Clight.find_label _ _ (Clight.Kseq c2 k)) eqn:H1.
      + inv H.
        edestruct IHc1; [ | eauto ..]. eauto.
        rewrite H; eauto.
      + simpl in H1.
        constructor; eauto.
   *)
  Admitted.

  Hypothesis same_senv:
    forall i, Senv.equiv sge (tge i).

  (** The following tactic uses the hypotheses and lemmas defined
    above to discharge the [exists s2', target step /\ related]
    subgoals of the simulation, assuming we have destructed the source
    step and the simulation relation. *)
  Ltac target_step :=
    try (edestruct match_find_label as (? & ? & ?); [ solve [eauto] .. | ]);
    try (edestruct find_funct_unlink_call as (?&?&?&?); [ eassumption.. | ]);
    eexists; split;
      [ apply plus_one;
        apply Res.step_internal;
        apply FComp.step_intro;
        econstructor;
        rewrite
          ?(blocks_of_env_equiv sge);
        eauto using
          eval_expr_equiv,
          eval_lvalue_equiv,
          eval_exprlist_equiv,
          assign_loc_equiv,
          external_call_symbols_preserved,
          match_is_call_cont,
          function_entry2_equiv
      | econstructor;
        eauto ].

  Lemma step_unlink s1 t s1' s2:
    Step Ls s1 t s1' ->
    match_states s1 s2 ->
    exists s2',
      Plus Lt s2 t s2' /\
      match_states s1' s2'.
  Proof.
    intros Hs1 Hs.

    (* First, destruct the source step. *)
    destruct Hs1;

    (* Next we inverse [match_state], and any [match_cont] that can be
      inversed productively. It is important to do this at this stage
      because the components involved in the target continuation may
      be needed when we instantiate [s2']. *)
    inv Hs;
    repeat match goal with
      | H: match_cont _ _ _ |- _ =>
        inv H; [ | contradiction (* is_call_cont *)]
      | H: linkorder ?tfd (_ _) |- _ =>
        inv H
    end;

    (* Most cases can be discharged by the [target_step] script. *)
    try solve [target_step].

    - (* Call to another module *)
      admit.

    - (* Return into another module *)
      admit.
  Admitted.

  Lemma initial_state_unlink w q1 q2 s1:
    match_query 1 w q1 q2 ->
    initial_state Ls q1 s1 ->
    exists s2,
      initial_state Lt q2 s2 /\
      match_states s1 s2.
  Proof.
    intros Hq.
    apply match_query_cc_id in Hq; subst.
    intros [id b f targs tres tcc vargs m ge' Hm Hb Hf Hvargs].
    edestruct find_funct_ptr_internal_unlink_switch as [i Hbi]; eauto.
    eexists (existT _ i (Clight.Callstate _ vargs Clight.Kstop m) :: nil).
    split.
    + apply Res.initial_state_intro.
      apply FComp.initial_state_intro.
      eapply Clight.initial_state_intro; eauto.
      * destruct (same_senv i) as (Hnextblock & _).
        change (Genv.genv_next _) with (Senv.nextblock (tge i)).
        rewrite Hnextblock.
        assumption.
      * destruct (same_senv i) as (_ & Hsymb & _).
        change (Genv.find_symbol _) with (Senv.find_symbol (tge i)).
        rewrite Hsymb.
        assumption.
    + apply match_callstate.
      * apply linkorder_refl.
      * apply match_kstop.
  Qed.

  Lemma external_unlink s1 s2 q1:
    match_states s1 s2 ->
    at_external Ls s1 q1 ->
    exists (wA : world 1) (q2 : query li_c),
      match_query 1 wA q1 q2 /\
      at_external Lt s2 q2 /\
      (forall r1 r2 s1',
          match_reply 1 wA r1 r2 ->
          after_external Ls s1 r1 s1' ->
          exists s2',
            after_external Lt s2 r2 s2' /\
            match_states s1' s2').
  Proof.
  Admitted.

  Lemma final_unlink w s1 s2 r1:
    match_states s1 s2 ->
    final_state Ls s1 r1 ->
    exists r2,
      match_reply 1 w r1 r2 /\
      final_state Lt s2 r2.
  Proof.
  Admitted.

  Lemma unlink:
    forward_simulation cc_id cc_id Ls Lt.
  Proof.
    eapply forward_simulation_plus with (fun _ => match_states).
    - reflexivity.
    - eauto using initial_state_unlink.
    - eauto using external_unlink.
    - eauto using final_unlink.
    - eauto using step_unlink.
  Qed.
End CLIGHT_UNLINK.
