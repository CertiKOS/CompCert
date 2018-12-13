Require Import Relations.
Require Import LogicalRelations.
Require Import OptionRel.
Require Import KLR.
Require Import List.
Require Import Classical.
Require Import Events.
Require Import Smallstep.
Require Import Behaviors.
Require Export ATS.
Require Import Obs.


(** * CompCert games *)

(** The moves of CompCert games are queries, replies, CompCert events.
  Queries are inputs; replies and CompCert events are outputs. *)

Canonical Structure lang (li : language_interface) : game :=
  {|
    question := query li;
    answer := reply li;
  |}.

Definition cc {li1 li2} (cc : callconv li1 li2) : grel (lang li2) (lang li1) :=
  {|
    question_rel w q2 q1 := match_query cc w q1 q2;
    answer_rel w r2 r1 := match_reply cc w r1 r2;
  |}.

Coercion lang : language_interface >-> game.
Coercion cc : callconv >-> grel.
Bind Scope li_scope with game.


(** * Behaviors from small step semantics *)

Module Behavior.
  Section LTS.
    Context {li} {L : Smallstep.semantics li}.

    (** ** Transition system *)

    (** A continuation is a stack of "at external" states. *)

    Definition cont :=
      list (Smallstep.state L).

    (** A state is an optional state of [L], together with a stack of
      pending "at external" states. [None] indicates the semantics
      went wrong. *)

    Inductive state :=
      st (s : Smallstep.state L) (stk : cont).

    Inductive state_in (S : _ -> Prop) k : option state -> Prop :=
      | safe_state_in s : S s -> state_in S k (Some (st s k))
      | unsafe_state_in : ~ ex S -> state_in S k None.

    Inductive resume : cont -> omove li li -> option state -> Prop :=
      | resume_initial_state k q s :
          state_in (initial_state L q) k s ->
          resume k (oq q) s
      | resume_after_external s k r s' :
          state_in (after_external L s r) k s' ->
          resume (s :: k) (oa r) s'.

    Inductive step : state -> option state -> Prop :=
      | step_running s s' k :
          Step L s E0 s' ->
          step (st s k) (Some (st s' k))
      | step_wrong s k :
          ~ ((exists r : reply li, final_state L s r) \/
             (exists q : query li, at_external L s q) \/
             (exists (t : trace) (s'' : Smallstep.state L), Step L s t s'')) ->
          step (st s k) None.

    Inductive suspend : state -> pmove li li * cont -> Prop :=
      | suspend_at_external s q k :
          at_external L s q ->
          suspend (st s k) (pq q, s :: k)
      | suspend_final_state s r k :
          final_state L s r ->
          suspend (st s k) (pa r, k).

    Inductive refuse : cont -> oqmove li li -> Prop :=
      | refuse_intro k q :
          query_is_internal li (symbolenv L) q = false ->
          refuse k q.

    Definition of :=
      ATS.Build_ats li li state cont step suspend resume refuse.

    Definition strat :=
      ATS.Build_strat li li (Obs.state li li cont) cont (Obs.of of) nil.

    (** The following properties of the transition system will be
      useful in the soundness proof below. *)

    (** ** [Obs.reachable] *)

    Lemma star_steps s s' ks os :
      Star L s E0 s' ->
      Obs.reachable of (Some (st s' ks)) os ->
      Obs.reachable of (Some (st s ks)) os.
    Proof.
      intros Hs'. pattern s, s'. revert s s' Hs'.
      apply star_E0_ind; auto.
      intros s1 s2 s3 Hs12 Hs23 Hs3.
      apply Obs.reachable_step with (Some (st s2 ks)); auto.
      econstructor; eauto.
    Qed.

    Definition safe (s : option state) :=
      match s with
        | Some (st s k) => Smallstep.safe L s
        | None => False
      end.

    Lemma unsafe_goes_wrong s:
      ~ safe s ->
      Obs.reachable of s None.
    Proof.
      destruct s as [[s k] | ]; eauto using Obs.reachable_none.
      intros Hs. unfold safe, Smallstep.safe in Hs.
      apply not_all_ex_not in Hs as [s' Hs].
      apply not_all_ex_not in Hs as [Hs' Hs].
      eapply star_steps; eauto.
      econstructor; eauto using Obs.reachable_none.
      constructor; auto.
    Qed.

    (** ** [Obs.diverges] *)

    Lemma rts_forever_silent s k:
      Obs.diverges of (st s k) ->
      Forever_silent L s.
    Proof.
      revert s. cofix IH.
      intros.
      destruct H. inversion H; clear H; subst.
      econstructor; eauto.
    Qed.

    Lemma forever_silent_rts s k:
      Forever_silent L s ->
      Obs.diverges of (st s k).
    Proof.
      revert s. cofix IH.
      intros.
      destruct H. econstructor; eauto.
      constructor. eauto.
    Qed.

    (** ** Determinism *)

    (*
    (** From deterministic small-step semantics, we can obtain a
      deterministic transition system. *)

    Lemma cont_deterministic k:
      cont_determinate L k ->
      RTS.nonbranching_cont (liftk k) (liftk k).
    Proof.
      intros Hk q r1 r2 Hr1 Hr2.
      unfold liftk in *. destruct k as [S | ] eqn:HS.
      - inversion Hr1 as [s1 Hs1]; clear Hr1; subst.
        inversion Hr2 as [s2 Hs2]; clear Hr2; subst.
        destruct Hs1 as [Hw1 | s1 Hs1], Hs2 as [Hw2 | s2 Hs2].
        + reflexivity.
        + elim Hw1; eauto.
        + elim Hw2; eauto.
        + repeat f_equal. eapply (Hk q s1 s2); eexists; eauto.
      - destruct Hr1, Hr2. reflexivity.
    Qed.

    Lemma deterministic:
      Smallstep.determinate L ->
      RTS.deterministic step.
    Proof.
      intros HL s r1 r2 H1 H2.
      destruct H1.
      - inversion H2; clear H2; subst.
        repeat constructor.
      - inversion H2; clear H2; subst.
        + edestruct (sd_determ HL s E0 s' E0 s'0); eauto.
          specialize (H2 eq_refl) as [ ].
          repeat constructor.
        + eelim sd_final_nostep; eauto.
        + eelim H1; eauto.
      - inversion H2; clear H2; subst.
        + eelim sd_final_nostep; eauto.
        + edestruct (sd_final_determ HL s r k r0 k0) as ([ ] & [ ] & Hk); eauto.
          constructor. simpl.
          eapply cont_deterministic; eauto.
        + eelim H3; eauto.
      - inversion H2; clear H2; subst.
        + eelim H; eauto.
        + eelim H0; eauto.
        + repeat constructor.
    Qed.
     *)
  End LTS.

  Arguments cont {li} L.
  Arguments state {li} L.
  Arguments of {li} L.
  Arguments strat {li} L.

  (** ** Monotonicity *)

  (** Backward simulations of small-step semantics are sound with
    respect to the embedding defined above: given a backward
    simulation between two small-step semantics, we can establish a
    corresponding simulation between their embeddings.
    We use the following simulation relation. *)

  Section SIM.
    Context {li1 li2} (cc : callconv li1 li2).
    Context (L1 : semantics li1).
    Context (L2 : semantics li2).
    Context {ind ord} R (HL : bsim_properties cc L1 L2 ind ord R).

    Definition after_external_rel wA wB s1 s2 :=
      forall r1 r2,
        match_reply cc wA r1 r2 ->
        bsim_match_cont (rexists i, R wB i)
          (after_external L1 s1 r1)
          (after_external L2 s2 r2).

    Inductive cont_rel : klr (gworld cc cc) (cont L2) (cont L1) :=
      | cont_nil_rel :
          cont_rel nil nil nil
      | cont_inl_rel wA wB s1 s2 ws k1 k2 :
          after_external_rel wA wB s1 s2 ->
          cont_rel ws k2 k1 ->
          cont_rel (inl wA :: inr wB :: ws) (s2 :: k2) (s1 :: k1).

    Inductive state_rel : klr (gworld cc cc) (state L2) (state L1) :=
      | state_rel_intro w i s1 s2 ws k1 k2 :
          R w i s1 s2 ->
          cont_rel ws k2 k1 ->
          state_rel (inr w :: ws) (st s2 k2) (st s1 k1).

    (** Showing the simulation for the resumption relation is
      straightforward if intricate. *)

    Global Instance state_in_sim w ws :
      Monotonic state_in
        (bsim_match_cont (rexists i, R w i) -->
         cont_rel ws ++>
         set_le (option_ge (state_rel (inr w :: ws)))).
    Proof.
      intros S2 S1 [Hex Hmatch] k2 k1 Hk s2 Hs2.
      destruct Hs2 as [s2 Hs2 | Hn2].
      - destruct (classic (ex S1)) as [[s1 Hs1] | Hn1].
        + edestruct Hmatch as (s1' & Hs1' & i & Hs); eauto.
          exists (Some (st s1' k1)). repeat (econstructor; eauto).
        + exists None. repeat (econstructor; eauto).
      - destruct (classic (ex S1)) as [[s1 Hs1] | Hn1].
        + eelim Hn2; eauto.
        + exists None. repeat (econstructor; eauto).
    Qed.

    Global Instance resume_sim :
      Monotonic resume (|= cont_rel ++> []-> k1 set_le (k1 option_ge state_rel)).
    Proof.
      intros ws k2 k1 Hk q2 q1 ws' Hq s2 Hs2.
      destruct Hs2 as [k2 q2 s2 Hs2 | s2 k2 r2 s2' Hs2'];
      inversion Hq; clear Hq; subst;
      inversion H3 as [wA m2 m1 | wB m2 m1]; clear H3; subst;
      simpl in *.
      - (* initial state *)
        edestruct state_in_sim as (s1 & ? & ?); eauto.
        + eapply bsim_initial_states; eauto.
        + exists s1. repeat (constructor; auto).
      - (* resume after external *)
        inversion Hk as [| xwA wB sk1 sk2 ws k1' k2' Hsk Hk']; clear Hk; subst.
        edestruct state_in_sim as (s1 & ? & ?); eauto.
        + eapply Hsk; eauto.
        + exists s1. repeat (constructor; auto).
    Qed.

    (** For [suspend], we can't show a direct simulation but we can
      show it modulo reachability, so that once we apply the
      observation operator the simulation will hold. *)

    Global Instance reachable_sim :
      Monotonic
        (Obs.reachable (of _))
        (|= k1 option_ge state_rel ++>
            k1 set_le (k1 option_ge (Obs.state_rel cc cc cont_rel))).
    Proof.
      intros ws os2 os1 Hos os2' Hs2'.
      destruct (classic (safe os1)) as [Hsafe | ];
        [ | exists None; split; eauto using unsafe_goes_wrong; rauto ].
      revert os1 Hos Hsafe.
      induction Hs2' as [s2 mk2 Hmk2 | | s2 s2' s2'' Hs2' Hs2'' IHs2'']; intros;
      inversion Hos as [xs2 s1 Hs | ]; clear Hos; subst; try contradiction.
      - (* target reached an exit state *)
        destruct Hs as [wB i s1 s2 ws k1 k2 Hs Hk].
        inversion Hmk2 as [? q2 ? Hq2 | ? r2 ? Hr2]; clear Hmk2; subst.
        + (* at external *)
          edestruct @bsim_match_external
            as (wA & s1' & q1 & Hs1' & Hq1 & Hq & Hs'); eauto.
          eexists (Some (Obs.st (pq q1, _))). split.
          * eapply star_steps; eauto. repeat constructor; auto.
          * repeat constructor. exists (inl wA :: inr wB :: ws).
            repeat (constructor; auto).
        + (* final state *)
          edestruct @bsim_match_final_states
            as (s1' & r1 & Hs1' & Hr & Hr1); eauto.
          eexists (Some (Obs.st (pa r1, _))). split.
          * eapply star_steps; eauto. repeat constructor; auto.
          * repeat (econstructor; eauto).
      - (* target takes an internal step *)
        destruct Hs2' as [s2 s2' k2 Hs2' | ].
        + inversion Hs; clear Hs; subst.
          edestruct @bsim_E0_star as (i' & s1' & Hs1' & Hs'); eauto using star_one.
          destruct (IHs2'' (Some (st s1' k1))) as (s1'' & Hs1'' & Hs'').
          * repeat (econstructor; eauto).
          * simpl in Hsafe |- *; eauto using star_safe.
          * eexists; split; eauto.
            eapply star_steps; eauto.
        + inversion Hs; clear Hs; subst.
          elim H. eapply bsim_progress; eauto.
    Qed.

    Lemma diverges_sim i w s1 s2 k1 k2:
      R w i s1 s2 ->
      Smallstep.safe L1 s1 ->
      Obs.diverges (of L2) (st s2 k2) ->
      Obs.diverges (of L1) (st s1 k1).
    Proof.
      intros.
      eapply forever_silent_rts.
      eapply backward_simulation_forever_silent; eauto.
      eapply rts_forever_silent; eauto.
    Qed.

    Lemma obs_resume_sim :
      Monotonic
        (Obs.resume (of _))
        (|= cont_rel ++> [] ->
            k1 set_le (k1 option_ge (Obs.state_rel cc cc cont_rel))).
    Proof.
      intros w k2 k1 Hk m2 m1 w' Hw' s2 Hs2.
      destruct Hs2 as [k2 m2 s2 s2' Hs2 Hs2' | k2 m2 s2 Hs2 Hs2d].
      - edestruct resume_sim as (s1 & Hs1 & Hs); eauto.
        edestruct reachable_sim as (s1' & Hs1' & Hs'); eauto.
        exists s1'. split; [ | rauto]. econstructor; eauto.
      - edestruct resume_sim as (os1 & Hos1 & Hos); eauto.
        destruct (classic (safe os1)) as [Hsafe | Hunsafe].
        + inversion Hos as [xs2 s1 Hs | ]; clear Hos; subst; [ | contradiction].
          destruct Hs as [w' i s1 s2 ws k1' k2' Hs Hk'].
          exists (Some Obs.div). repeat constructor; auto.
          eapply Obs.resume_diverges; eauto.
          eapply diverges_sim; eauto.
        + exists None. split; [ | rauto].
          eapply Obs.resume_reachable; eauto using unsafe_goes_wrong.
    Qed.

    Lemma refuse_sim :
      Monotonic refuse (|= cont_rel ++> ([] -> k impl)).
    Proof.
      intros w k2 k1 Hk q2 q1 w' Hq Hq2.
      destruct Hq2 as [k2 xq2 Hq2].
    Admitted.

    Lemma bsim_sound :
      ATS.sim cc cc (Obs.state_rel cc cc cont_rel) cont_rel
        (Obs.of (of L2))
        (Obs.of (of L1)).
    Proof.
      split; simpl.
      - eapply Obs.step_sim; eauto.
      - eapply Obs.suspend_sim; eauto.
      - eapply obs_resume_sim; eauto.
      - eapply refuse_sim; eauto.
    Qed.
  End SIM.

  Global Instance strat_sim :
    Monotonic
      (@strat)
      (forallr cc, backward_simulation cc --> ATS.ref cc cc).
  Proof.
    intros li1 li2 cc L1 L2 [index order match_states HL]. unfold strat.
    econstructor; simpl; eauto.
    exists (cont_rel cc L2 L1 match_states). split.
    - eapply bsim_sound; eauto.
    - constructor.
  Qed.

End Behavior.
