Require Import LogicalRelations.
Require Import Linking.
Require Import GameSemantics.
Require Import Composition.
Require Import Values.
Require Import LanguageInterface.
Require Import AST.
Require Import Globalenvs.
Require Import Asm.
Require Import RTS.
Require Import ModuleSemantics.
Require Import Smallstep.
Require Import OptionRel.

Definition asm p : modsem (li_asm -o li_asm) :=
  Behavior.of (Asm.semantics p).

Require Import Maps.
Require Import List.
Require Import BoolRel.

Global Existing Instance Genv.Linker_genv.

Record Senv_le ge1 ge2 : Prop :=
  {
    Senv_le_find_symbol i:
      option_le eq (Senv.find_symbol ge1 i) (Senv.find_symbol ge2 i);
    Senv_le_public_symbol i:
      leb (Senv.public_symbol ge1 i) (Senv.public_symbol ge2 i);
    Senv_le_block_is_volatile i:
      option_le eq (Senv.block_is_volatile ge1 i) (Senv.block_is_volatile ge2 i);
  }.

Section GENV_REL.
  Context {F V} `{LF: Linker F} `{LV: Linker V} `{FI: FundefIsInternal F}.

  Global Instance find_symbol_linkorder:
    Monotonic
      (@Genv.find_symbol F V)
      (linkorder ++> - ==> option_le eq).
  Proof.
    intros ge1 ge2 Hge i. simpl in *.
    unfold Genv.find_symbol, Genv.find_def.
    destruct ((Genv.genv_defs ge1) ! i) as [gd1 | ] eqn:Hf1; try rauto.
    edestruct (Genv.linkorder_genv_defs Hge) as (gd2 & Hgd2 & Hgd & Hgdnp); eauto.
    rewrite Hgd2. rauto.
  Qed.

  Global Instance find_symbol_linkorder_params:
    Params (@Genv.find_symbol) 2.

  Global Instance find_funct_ptr_linkorder:
    Monotonic
      (@Genv.find_funct_ptr F V)
      (linkorder ++> - ==> option_le linkorder).
  Proof.
    intros ge1 ge2 Hge b. simpl in *.
    unfold Genv.find_funct_ptr, Genv.find_def.
    destruct Block.ident_of as [i | ]; try constructor.
    destruct ((Genv.genv_defs ge1) ! i) as [[f1|v1] | ] eqn:Hf1; try constructor.
    edestruct (Genv.linkorder_genv_defs Hge) as (gd2 & Hgd2 & Hgd & Hgdnp); eauto.
    inversion Hgd; clear Hgd; subst.
    rewrite Hgd2. rauto.
  Qed.

  Global Instance find_funct_ptr_linkorder_params:
    Params (@Genv.find_funct_ptr) 2.

  Global Instance find_var_info_linkorder:
    Monotonic
      (@Genv.find_var_info F V)
      (linkorder ++> - ==> option_le linkorder).
  Proof.
    intros ge1 ge2 Hge b. simpl in *.
    unfold Genv.find_var_info, Genv.find_def.
    destruct Block.ident_of as [i | ]; try constructor.
    destruct ((Genv.genv_defs ge1) ! i) as [[f1|v1] | ] eqn:Hf1; try constructor.
    edestruct (Genv.linkorder_genv_defs Hge) as (gd2 & Hgd2 & Hgd & Hgdnp); eauto.
    inversion Hgd; clear Hgd; subst.
    rewrite Hgd2. rauto.
  Qed.

  Global Instance find_var_info_linkorder_params:
    Params (@Genv.find_var_info) 2.

  Global Instance Genv_to_senv_le:
    Monotonic (@Genv.to_senv F V) (linkorder ++> Senv_le).
  Proof.
    intros ge1 ge2 Hge.
    split; simpl; intros i.
    - unfold Genv.find_symbol, Genv.find_def.
      destruct ((Genv.genv_defs ge1) ! i) as [gd1 | ] eqn:Hb; [ | constructor].
      edestruct (Genv.linkorder_genv_defs Hge) as (gd2 & Hgd2 & Hgd & _); eauto.
      rewrite Hgd2. rauto.
    - unfold Genv.public_symbol, Genv.find_symbol, Genv.find_def.
      destruct ((Genv.genv_defs ge1) ! i) as [gd1 | ] eqn:Hb; [ | constructor].
      edestruct (Genv.linkorder_genv_defs Hge) as (gd2 & Hgd2 & Hgd & _); eauto.
      rewrite Hgd2. unfold Coqlib.proj_sumbool.
      destruct (in_dec _ _ (_ ge1)) as [Hin | _]; try rauto.
      eapply Genv.linkorder_genv_public in Hin; eauto.
      destruct (in_dec _ _ (_ ge2)) as [_ | Hnotin]; try contradiction.
      reflexivity.
    - unfold Genv.block_is_volatile.
      repeat rstep.
      destruct H1. simpl. reflexivity.
  Qed.

  Global Instance genv_to_senv_params:
    Params (@Genv.to_senv) 1.

  (** * [eval_builtin_args] *)

  Global Instance genv_symbol_address_linkorder:
    Monotonic
      (@Genv.symbol_address F V)
      (linkorder ++> - ==> - ==> Val.lessdef).
  Proof.
    intros ge1 ge2 Hge id ofs.
    unfold Genv.symbol_address.
    repeat rstep; subst; constructor.
  Qed.

  Global Instance genv_symbol_address_linkorder_params:
    Params (@Genv.symbol_address) 3.

  Global Instance senv_symbols_address_inject:
    Monotonic
      (@Senv.symbol_address)
      (Senv_le ++> - ==> - ==> Val.lessdef).
  Proof.
    intros ge1 ge2 Hge i ofs.
    unfold Senv.symbol_address.
    pose proof (Senv_le_find_symbol ge1 ge2 Hge i).
    repeat rstep; subst; constructor.
  Qed.

  (*
  Global Instance eval_builtin_arg_rel {F V} R w:
    Monotonic
      (@eval_builtin_arg)
      (forallr -, Senv_le ++> - ==> - ==> - ==> - ==> set_le eq).
       (- ==> eq) ++>
       Val.inject (mi R w) ++> match_mem R w ++> - ==> set_le (Val.inject (mi R w))).
  Proof.
    intros A ge1 ge2 Hge f1 f2 Hf v1 v2 Hv m1 m2 Hm arg r Hr.
    revert v2 Hv.
    induction Hr; intros ? ?;
    try (transport_hyps; eexists; split; [constructor; eauto | rauto]).
    - edestruct IHHr1 as (vhi' & Hvhi' & Hvhi); eauto.
      edestruct IHHr2 as (vlo' & Hvlo' & Hvlo); eauto.
      eexists. split; [ constructor; eauto | rauto ].
    - edestruct IHHr1 as (va1 & Hva1 & Hva1'); eauto.
      edestruct IHHr2 as (va2 & Hva2 & Hva2'); eauto.
      eexists. split; [ constructor; eauto | rauto ].
  Qed.

  Hint Extern 1 (Transport _ _ _ _ _) =>
    set_le_transport @eval_builtin_arg : typeclass_instances.

  Global Instance eval_builtin_args_rel {F V} R w:
    Monotonic
      (@eval_builtin_args)
      (forallr -, (psat (genv_valid R w)) !! (@Genv.to_senv F V) ++>
       (- ==> Val.inject (mi R w)) ++>
       Val.inject (mi R w) ++> match_mem R w ++> - ==>
       set_le (Val.inject_list (mi R w))).
  Proof.
    unfold eval_builtin_args.
    repeat rstep.
    intros vl Hvl.
    induction Hvl.
    - eexists; split; constructor; eauto.
    - destruct IHHvl as (? & ? & ?).
      transport H3.
      eexists; split; constructor; eauto.
  Qed.

  Hint Extern 1 (Transport _ _ _ _ _) =>
    set_le_transport @eval_builtin_args : typeclass_instances.
*)


End GENV_REL.

Axiom external_call_empty :
  forall id sg ge vargs m t vres m',
    ~ Events.external_functions_sem id sg ge vargs m t vres m'.

Axiom inline_assembly_sem_empty : (* XXX admit: or assert compatibility w/ linkorder *)
  forall text sg ge vargs m t vres m',
    ~ Events.inline_assembly_sem text sg ge vargs m t vres m'.

Global Instance genv_block_is_volatile_linkorder:
  Monotonic
    (@Genv.block_is_volatile fundef unit)
    (linkorder ++> - ==> option_le eq).
Proof.
  intros ge1 ge2 Hge b.
  unfold Genv.block_is_volatile.
  repeat rstep.
  destruct H1. simpl. reflexivity.
Qed.

Global Instance genv_block_is_volatile_linkorder_params:
  Params (@Genv.block_is_volatile) 2.

Global Instance eventval_match_linkorder:
  Monotonic (@Events.eventval_match) (Senv_le ++> - ==> - ==> - ==> impl).
Proof.
  intros ge1 ge2 Hge ev ty v H.
  destruct H; constructor.
  - pose proof (Senv_le_public_symbol ge1 ge2 Hge id).
    rewrite H in H1. simpl in H1. auto.
  - destruct (Senv_le_find_symbol ge1 ge2 Hge id); congruence.
Qed.

Global Instance eventval_list_match_linkorder:
  Monotonic (@Events.eventval_list_match) (Senv_le ++> - ==> - ==> - ==> impl).
Proof.
  intros ge1 ge2 Hge ev ty v H.
  induction H; constructor; eauto.
  eapply eventval_match_linkorder; eauto.
Qed.

Lemma external_call_linkorder (ge1 ge2: Asm.genv) ef vargs m t vres m' :
  linkorder ge1 ge2 ->
  Events.external_call ef ge1 vargs m t vres m' ->
  Events.external_call ef ge2 vargs m t vres m'.
Proof.
  intros Hge H.
  destruct ef; simpl in H |- *; try now (eelim external_call_empty; eauto).
  - destruct H; constructor.
    destruct H.
    + simpl in H. transport H. subst.
      simpl in H0. transport H0. subst.
      eapply Events.volatile_load_vol; eauto.
      revert H1. rauto.
    + simpl in H. transport H. subst.
      eapply Events.volatile_load_nonvol; eauto.
  - destruct H; constructor.
    destruct H.
    + simpl in H. transport H. subst.
      simpl in H0. transport H0. subst.
      eapply Events.volatile_store_vol; eauto.
      revert H1. rauto.
    + simpl in H. transport H. subst.
      eapply Events.volatile_store_nonvol; eauto.
  - destruct H; econstructor; eauto.
  - destruct H; econstructor; eauto.
  - destruct H; econstructor; eauto.
  - destruct H; econstructor; eauto.
    revert H. rauto.
  - destruct H; econstructor; eauto.
    revert H. rauto.
  - eelim inline_assembly_sem_empty; eauto.
  - destruct H; econstructor; eauto.
Qed.

Definition state_is_internal ge s :=
  let '(State rs m) := s in
  match rs#PC with
    | Vptr b ofs => Senv.block_is_internal ge b
    | _ => false
  end.

Lemma genv_fundef_is_internal (p: Asm.program):
  Genv.genv_fundef_is_internal (Genv.globalenv p) = _.
Proof.
  unfold Genv.globalenv, Genv.add_globals.
  pattern (prog_defs p).
  eapply rev_ind.
  - simpl. reflexivity.
  - intros.
    rewrite fold_left_app. simpl. auto.
Qed.

Lemma asm_step_linkorder (ge1 ge2: Asm.genv) s t s' :
  linkorder ge1 ge2 ->
  Genv.genv_fundef_is_internal ge1 = _ ->
  Asm.step ge1 s t s' ->
  Asm.step ge2 s t s'.
Proof.
  intros Hge Hfi Hstep.
  destruct Hstep.
  - transport H0.
    inversion H4; clear H4; subst.
    econstructor; eauto.
  - transport H0.
    inversion H6; clear H6; subst.
    eapply Asm.exec_step_builtin; eauto.
    eapply external_call_linkorder; eauto.
  - generalize H0.
    transport H0.
    inversion H5; clear H5; subst.
    + intros _.
      eapply Asm.exec_step_external; eauto.
      eapply external_call_linkorder; eauto.
    + (* external -> internal *)
      simpl in H2.
      eelim external_call_empty; eauto.
Qed.

Section HCOMP.
  Context (p1 p2 p: Asm.program) (Hp: link p1 p2 = Some p).
  Let L1 := Asm.semantics p1.
  Let L2 := Asm.semantics p2.
  Let L := Asm.semantics p.
  Let L12 := SHComp.semantics (symbolenv L) L1 L2.

  Inductive match_states : rel SFComp.state (state L) :=
    | match_states_l s1 :
        match_states (SFComp.state_l s1 (initial_state L2)) s1
    | match_states_r s2 :
        match_states (SFComp.state_r s2 (initial_state L1)) s2.

  Inductive link_cases : bool -> bool -> bool -> Prop :=
    | lc_none : link_cases false false false
    | lc_left : link_cases true false true
    | lc_right : link_cases false true true.

  Lemma lc_l x:
    link_cases x false x.
  Proof.
    destruct x; constructor.
  Qed.

  Lemma lc_r x:
    link_cases false x x.
  Proof.
    destruct x; constructor.
  Qed.

  Lemma link_cases_fundef (f1 f2 f: fundef):
    link f1 f2 = Some f ->
    link_cases
      (ast_fundef_is_internal f1)
      (ast_fundef_is_internal f2)
      (ast_fundef_is_internal f).
  Proof.
    change (link f1 f2) with (link_fundef f1 f2).
    destruct f1 as [f1|e1], f2 as [f2|e2], f as [f|e]; simpl;
      try constructor;
      try (now inversion 1).
    - destruct e2; inversion 1.
    - destruct e1; inversion 1.
    - destruct e1, e2; destruct external_function_eq; inversion 1.
  Qed.

  Lemma query_is_internal_cases q:
    link_cases
      (query_is_internal li_asm (Genv.globalenv p1) q)
      (query_is_internal li_asm (Genv.globalenv p2) q)
      (query_is_internal li_asm (Genv.globalenv p) q).
  Proof.
    edestruct (link_linkorder p1 p2 p Hp) as [Hp1p Hp2p]; eauto.
    apply Genv.globalenv_linkorder in Hp1p.
    apply Genv.globalenv_linkorder in Hp2p.
    simpl.
    destruct q as [rs m].
    destruct (rs PC); try constructor.
    unfold Genv.block_is_internal.
    unfold Genv.find_funct_ptr, Genv.find_def.
    destruct (Block.ident_of b) as [id | ]; [ | constructor].
    rewrite !Genv.globalenv_defs.
    rewrite !genv_fundef_is_internal.
    destruct (link_prog_inv p1 p2 p Hp) as (_ & Hlp & Hp12).
    subst p. unfold prog_defmap at 3. simpl.
    rewrite PTree_Properties.of_list_elements.
    rewrite PTree.gcombine by reflexivity.
    specialize (Hlp id).
    destruct ((prog_defmap p1) ! id) as [d1 | ] eqn:Hd1; eauto using lc_r.
    destruct ((prog_defmap p2) ! id) as [d2 | ] eqn:Hd2; eauto using lc_l.
    specialize (Hlp _ _ eq_refl eq_refl) as (_ & _ & gd & Hlp).
    simpl. rewrite Hlp.
    change (link d1 d2) with (link_def d1 d2) in Hlp.
    destruct d1 as [|], d2 as [|], gd as [|];
    try now inversion Hlp; try constructor.
    - simpl in Hlp.
      apply link_cases_fundef.
      destruct (link f f0); congruence.
    - inversion Hlp.
      destruct (link f f0); congruence.
    - inversion Hlp.
      destruct (link v v0); congruence.
  Qed.

  Lemma internal_hcomp_l q :
    query_is_internal li_asm (Genv.globalenv p1) q = true ->
    query_is_internal li_asm (Genv.globalenv p) q = true.
  Proof.
    destruct (query_is_internal_cases q); congruence.
  Qed.

  Lemma internal_hcomp_r q :
    query_is_internal li_asm (Genv.globalenv p2) q = true ->
    query_is_internal li_asm (Genv.globalenv p) q = true.
  Proof.
    destruct (query_is_internal_cases q); congruence.
  Qed.

  Lemma internal_hcomp_inv q :
    query_is_internal li_asm (Genv.globalenv p) q = true ->
    query_is_internal li_asm (Genv.globalenv p1) q = true \/
    query_is_internal li_asm (Genv.globalenv p2) q = true.
  Proof.
    destruct (query_is_internal_cases q); intuition congruence.
  Qed.

  Lemma asm_hcomp_fsim_cont :
    fsim_match_cont cc_id (fun _ => match_states) tt
      (SFComp.liftk (initial_state L1) (initial_state L2))
      (simple_initial_state Asm.initial_state (Genv.globalenv p)).
  Proof.
    intros [] [[] | q] _ [].
    unfold SFComp.liftk.
    cbn -[query_is_internal]. unfold simple_dom.
    destruct (query_is_internal_cases q); constructor;
    intros _ [s Hs];
    exists s; split; auto; repeat constructor.
  Qed.

  Definition measure (s : state (SHComp.semantics (symbolenv L) L1 L2)) :=
    match s with
      | SFComp.state_l s1 _ =>
        if query_is_internal li_asm (Genv.globalenv p1) s1 then 0%nat else 1%nat
      | SFComp.state_r s2 _ =>
        if query_is_internal li_asm (Genv.globalenv p2) s2 then 0%nat else 1%nat
    end.

  Lemma measure_switch q S12' s12':
    SFComp.liftk
      (simple_initial_state Asm.initial_state (Genv.globalenv p1))
      (simple_initial_state Asm.initial_state (Genv.globalenv p2))
      q = Some S12' ->
    S12' s12' ->
    measure s12' = 0%nat.
  Proof.
    unfold SFComp.liftk.
    destruct q; try discriminate.
    cbn -[li_asm]; unfold simple_dom.
    assert (query_is_internal li_asm (Genv.globalenv p1) q = true ->
            forall k, measure (SFComp.state_l q k) = 0) as Hm1.
    {
      intros H k. unfold measure. rewrite H. auto.
    }
    assert (query_is_internal li_asm (Genv.globalenv p2) q = true ->
            forall k, measure (SFComp.state_r q k) = 0) as Hm2.
    {
      intros H k. unfold measure. rewrite H. auto.
    }
    destruct (query_is_internal_cases q); simpl; try congruence;
    intros H; inversion H; clear H; subst;
    intros [s Hs]; destruct Hs; eauto.
  Qed.

  Lemma asm_hcomp_fsim :
    forward_simulation cc_id (SHComp.semantics (symbolenv L) L1 L2) L.
  Proof.
    apply forward_simulation_star with (fun _ => match_states) measure; simpl.
    - reflexivity.
    - apply asm_hcomp_fsim_cont.
    - intros _ s12 s r12 k12 Hs H;
      destruct H as  [s12 r12 k12 Hk12 Hr];
      destruct Hk12 as [si r ki kj Hki | si r ki kj Hki];
      destruct Hki as [si Hsi];
      inversion Hs; clear Hs; subst;
      exists tt, (inl s), (simple_initial_state Asm.initial_state (Genv.globalenv p));
      intuition auto using asm_hcomp_fsim_cont;
      constructor;
      simpl in Hr; unfold SFComp.liftk in Hr;
      unfold simple_initial_state, simple_dom in Hr;
      destruct (query_is_internal_cases s); simpl in Hr; try congruence.
    - intros _ s12 t s12' Hs12' s Hs.
      destruct Hs12' as [s12 t s12' Hs12' | s12 r12 k12 s12' Hk12 Hs12'].
      + (* internal step *)
        apply link_linkorder in Hp as [Hp1p Hp2p].
        destruct Hs12' as  [si t si' kj Hsi' | si t si' kj Hsi']; simpl in *;
        inversion Hs; clear Hs; subst;
        left; exists si'; (split; [apply plus_one | constructor]);
        eapply asm_step_linkorder;
        eauto using genv_fundef_is_internal;
        eauto using Genv.globalenv_linkorder.
      + (* internal switching *)
        right.
        destruct Hk12 as [si r ki k' Hki | si r ki k' Hki];
          cbn -[query_is_internal] in *;
        destruct Hs12' as (S12' & Hq & Hs12');
        inversion Hs; clear Hs; subst;
        destruct Hki as [s Hs];
        erewrite measure_switch by eauto;
        unfold SFComp.liftk in Hq;
        cbn -[li_asm] in Hq; unfold simple_dom in Hq;
        destruct (query_is_internal_cases s); simpl in Hq; try congruence;
        inversion Hq; clear Hq; subst;
        intuition auto;
        destruct Hs12' as [q Hq];
        destruct Hq;
        constructor.
  Qed.

  Lemma asm_hcomp:
    modref (Behavior.of L) (HComp.of (Behavior.of L1) (Behavior.of L2)).
  Proof.
    transitivity (Behavior.of (SHComp.semantics (globalenv L) L1 L2)).
    - apply Behavior.bsim_sound.
      admit. (* flip forward simulation *)
    - apply HComp.of_emb.
  Admitted.
End HCOMP.
