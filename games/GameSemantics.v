Require Import LogicalRelations.
Require Import List.
Require Import Classical.
Require Import Events.
Require Import Smallstep.
Require Import Behaviors.
Require Import RTS.
Require Import ModuleSemantics.


(** * CompCert games *)

(** The moves of CompCert games are queries, replies, CompCert events.
  Queries are inputs; replies and CompCert events are outputs. *)

Canonical Structure lang (li : language_interface) : game :=
  {|
    input := query li;
    output := reply li;
  |}.

Coercion lang : language_interface >-> game.
Bind Scope li_scope with game.


(** * Modules *)

(** ** Definition *)

Record modsem {li : language_interface} :=
  {
    modsem_state : Type;
    modsem_lts :> rts li modsem_state;
    modsem_entry : input li -> option (modsem_state -> Prop);
  }.

Arguments modsem : clear implicits.

(** ** Refinement preorder *)

Record modref {li} (α β : modsem li) : Prop :=
  {
    modref_state :
      rel (modsem_state α) (modsem_state β);
    modref_sim :
      RTS.sim modref_state (modsem_lts α) (modsem_lts β);
    modref_init q :
      option_rel (set_le modref_state) (modsem_entry α q) (modsem_entry β q);
  }.

Global Instance modref_preo li:
  PreOrder (@modref li).
Proof.
  split.
  - intros [A α a].
    exists eq; simpl.
    + apply RTS.sim_id.
    + intros q. reflexivity.
  - intros [A α a] [B β b] [C γ c] [RAB Hαβ Hab] [RBC Hβγ Hbc]; simpl in *.
    eexists; simpl.
    + eapply RTS.sim_compose; eauto.
    + intros q. specialize (Hab q). specialize (Hbc q).
      destruct Hab; inversion Hbc; clear Hbc; subst; constructor.
      revert H H2. clear.
      intros H12 H23 a1 Ha1.
      edestruct H12 as (? & ? & ?); eauto.
      edestruct H23 as (? & ? & ?); eauto.
      eexists; split; eauto.
      eexists; split; eauto.
Qed.

(** ** Observations *)

Definition mobs {li} (α : modsem li) : modsem li :=
  {|
    modsem_lts := RTS.obs α;
    modsem_entry := modsem_entry α;
  |}.

Global Instance mobs_ref :
  Monotonic (@mobs) (forallr -, modref ++> modref).
Proof.
  intros li [A α a] [B β b] [R Hαβ Hab]; unfold mobs; simpl in *.
  exists R; simpl; eauto. rauto.
Qed.


(** * Behaviors from small step semantics *)

Module Behavior.
  Section LTS.
    Context {li} (L : Smallstep.semantics li).

    (** ** Transition system *)

    Inductive state {A} :=
      | running (s : A)
      | wrong.

    Inductive lifts {A} (S : A -> Prop) : state -> Prop :=
      | lifts_goes_wrong : ~ ex S -> lifts S wrong
      | lifts_resumes s : S s -> lifts S (running s).

    Definition liftk {A} (k : cont li A): cont li state :=
      fun q => option_map lifts (k q).

    Inductive step : rts li state :=
      | step_goes_initially_wrong :
          step wrong (RTS.goes_wrong)
      | step_internal s s' :
          Step L s E0 s' ->
          step (running s) (RTS.internal (running s'))
      | step_interacts s r k :
          final_state L s r k ->
          step (running s) (RTS.interacts r (liftk k))
      | step_goes_wrong s :
          Nostep L s ->
          (forall r k, ~ final_state L s r k) ->
          step (running s) (RTS.internal wrong).

    Definition of : modsem li :=
      {|
        modsem_state := state;
        modsem_lts := RTS.obs step;
        modsem_entry := liftk (initial_state L);
      |}.

    (** The following properties of the transition system will be
      useful in the soundness proof below. *)

    Lemma star_reachable s s' :
      Star L s E0 s' ->
      RTS.reachable step (running s) (running s').
    Proof.
      revert s s'. eapply star_E0_ind; eauto.
      intros s1 s2 s3 Hs12 Hs23.
      eapply RTS.reachable_step; eauto.
      constructor; eauto.
    Qed.

    Lemma step_run_star s s':
      Star L s E0 s' ->
      RTS.obs step (running s') RTS.diverges ->
      RTS.obs step (running s) RTS.diverges.
    Proof.
      intros H. pattern s, s'.
      eapply star_E0_ind; eauto using step_internal, RTS.obs_internal.
    Qed.

    Definition safe S :=
      match S with
        | running s => Smallstep.safe L s
        | wrong => False
      end.

    Lemma unsafe_goes_wrong S:
      ~ safe S ->
      RTS.obs step S RTS.goes_wrong.
    Proof.
      intros HS.
      destruct S as [ | ]; simpl in *; eauto using step_goes_initially_wrong.
      apply not_all_ex_not in HS as [s' HS].
      apply not_all_ex_not in HS as [Hs' HS].
      revert HS. pattern s, s'. revert s s' Hs'.
      eapply star_E0_ind; eauto; intros.
      - apply RTS.obs_external with wrong; auto.
        + constructor.
        + econstructor; eauto.
          eapply step_goes_wrong; firstorder.
      - eapply RTS.obs_internal; eauto.
        constructor; eauto.
    Qed.

    (** ** Determinism *)

    (** From deterministic small-step semantics, we can obtain a
      deterministic transition system. *)

    Lemma cont_deterministic k:
      cont_determinate L k ->
      RTS.nonbranching_cont (liftk k) (liftk k).
    Proof.
      intros Hk q S1 S2 s1 s2 HS1 HS2 Hs1 Hs2.
      assert (S2 = S1) by congruence. subst. clear HS2.
      unfold liftk in HS1.
      destruct k as [S | ] eqn:HS; simpl in HS1; inversion HS1; clear HS1; subst.
      destruct Hs1 as [Hw1 | s1 Hs1], Hs2 as [Hw2 | s2 Hs2].
      - reflexivity.
      - elim Hw1; eauto.
      - elim Hw2; eauto.
      - f_equal.
        eapply (Hk q s1 s2); eexists; eauto.
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
          specialize (H2 eq_refl) as [].
          repeat constructor.
        + eelim sd_final_nostep; eauto.
        + eelim H1; eauto.
      - inversion H2; clear H2; subst.
        + eelim sd_final_nostep; eauto.
        + edestruct (sd_final_determ HL s r k r0 k0) as ([] & [] & Hk); eauto.
          constructor. simpl.
          eapply cont_deterministic; eauto.
        + eelim H3; eauto.
      - inversion H2; clear H2; subst.
        + eelim H; eauto.
        + eelim H0; eauto.
        + repeat constructor.
    Qed.
  End LTS.

  (** ** Monotonicity *)

  (** Backward simulation of small-step semantics are sound with
    respect to the embedding defined above: given a backward
    simulation between two small-step semantics, we can show
    alternating refinement between their embeddings.

    We use the following alternating simulation relation. *)

  Inductive state_rel {A B} R : rel (@state A) (@state B) :=
    | running_rel s1 s2 :
        R s1 s2 ->
        state_rel R (running s1) (running s2)
    | wrong_rel S1 :
        state_rel R S1 wrong.

  Hint Constructors state_rel.

  Lemma rts_forever_silent {li} (L : semantics li) s:
    RTS.forever_internal (step L) (running s) ->
    Forever_silent L s.
  Proof.
    revert s. cofix IH.
    intros.
    destruct H. inversion H; clear H; subst.
    - econstructor; eauto.
    - destruct H0. inversion H.
  Qed.

  Lemma forever_silent_rts {li} (L : semantics li) s:
    Forever_silent L s ->
    RTS.forever_internal (step L) (running s).
  Proof.
    revert s. cofix IH.
    intros.
    destruct H. econstructor; eauto.
    constructor. eauto.
  Qed.

  Lemma forever_internal_bsim {li1 li2} cc L1 L2 ind ord ms i w S1 S2:
    @bsim_properties li1 li2 cc L2 L1 ind ord ms ->
    ms w i S2 S1 ->
    Smallstep.safe L2 S2 ->
    RTS.forever_internal (step L1) (running S1) ->
    RTS.forever_internal (step L2) (running S2).
  Proof.
    intros.
    eapply forever_silent_rts.
    eapply backward_simulation_forever_silent; eauto.
    eapply rts_forever_silent; eauto.
  Qed.

  Hint Extern 10 => rstep : coqrel.

  Lemma bsim_lifts {A B} (R : rel A B) (k1 k2 : _ -> Prop) :
    (forall s, k2 s -> ex k1) ->
    (forall s, k2 s -> set_le R k1 k2) ->
    set_le (state_rel R) (lifts k1) (lifts k2).
  Proof.
    intros Hex Hk s1 Hs1.
    destruct Hs1 as [Hk1 | s1 Hs1].
    - exists wrong; split; constructor.
      intros [s2 Hs2]. eauto.
    - destruct (classic (ex k2)) as [[s2e Hs2e] | H2].
      + edestruct Hk as (s2 & Hs2 & Hs); eauto.
        exists (running s2); split; constructor; eauto.
      + exists wrong; split; constructor; eauto.
  Qed.

  Lemma bsim_sound_liftk {li1 li2} cc L1 L2 ind ord ms w k1 k2 w' q1 q2 :
    @bsim_properties li1 li2 cc L2 L1 ind ord ms ->
    bsim_match_cont cc (match_ex ms) w k2 k1 ->
    cc_query cc q2 q1 w w' ->
    option_rel (set_le (state_rel (flip (rel_ex (match_ex ms))))) (liftk k1 q1) (liftk k2 q2).
  Proof.
    intros HL Hk Hq. unfold liftk.
    specialize (Hk w' q2 q1 Hq). destruct Hk as [S2 S1 HS | ]; constructor.
    eapply bsim_lifts.
    - intros.
      edestruct @bsim_sets_exists as (? & ? & ?); eauto.
    - intros s1 Hs1 s2 Hs2. unfold flip, rel_ex.
      edestruct @bsim_sets_match as (? & ? & ?); eauto.
  Qed.

  Lemma reachable_inv {li} (L : semantics li) s S':
    Smallstep.safe L s ->
    RTS.reachable (step L) (running s) S' ->
    exists s', S' = running s' /\ Star L s E0 s'.
  Proof.
    intros Hs HS'.
    change (safe L (running s)) in Hs.
    remember (running s) as S eqn:HS. revert s HS.
    induction HS' as [S | S1 S2 S3 HS12 HS23].
    - eauto using star_refl.
    - inversion HS12; clear HS12; subst.
      + inversion 1; clear HS; subst.
        edestruct IHHS23 as (s'' & Hs'' & Hsteps); eauto using star_step.
        simpl in Hs |- *. eauto using star_safe, star_one.
      + edestruct Hs as [(r & k & Hk) | (t & s' & Hs')]; eauto using star_refl.
        * eelim H2; eauto.
        * eelim H0; eauto.
  Qed.

  Lemma bsim_sound_step {li} (L1 L2: semantics li) ind ord ms:
    bsim_properties cc_id L2 L1 ind ord ms ->
    RTS.sim (state_rel (flip (rel_ex (match_ex ms))))
      (RTS.obs (step L1))
      (RTS.obs (step L2)).
  Proof.
    set (R := flip (rel_ex (match_ex ms))). unfold flip, rel_ex in R.
    intros HL S1 S2 HS r1 Hr1.
    destruct (classic (safe L2 S2)) as [HS2 | ];
      [ | now eauto using unsafe_goes_wrong with coqrel ].
    destruct HS as [s1 s2 Hs | ]; simpl in HS2; try contradiction.
    inversion Hr1 as [Hs1 | S1 r Hrext Hr Hs1']; clear Hr1; subst.

    - (* Divergence *)
      exists RTS.diverges. split; [ | rauto].
      destruct Hs as (w & i & Hs).
      apply RTS.obs_diverges.
      eapply forever_internal_bsim; eauto.

    - (* Observation *)
      assert (HS1: Smallstep.safe L1 s1)
        by (destruct Hs as (? & ? & ?); eauto using bsim_safe).
      apply reachable_inv in Hs1' as (s1' & ? & Hs1'); auto; subst.
      revert s2 Hs HS2. clear HS1.
      revert Hr. pattern s1, s1'. revert s1 s1' Hs1'.
      apply star_E0_ind.

      + (* Final states *)
        intros s1 Hr s2 Hs Hs2.
        inversion Hr; clear Hr; subst; try now inversion Hrext.
        destruct Hs as (w & i & Hs).
        eapply bsim_match_final_states in H0; eauto.
        destruct H0 as (s2' & w' & r2 & k2 & Hs2' & Hr & Hsk2 & Hk); eauto.
        simpl in Hr; subst.
        exists (RTS.interacts r (liftk k2)). split.
        * eapply RTS.obs_external with (running s2'); eauto.
          -- constructor; eauto.
          -- eapply star_reachable; eauto.
        * constructor. intro q.
           eapply bsim_sound_liftk; eauto.
           instantiate (1 := w'). constructor.

      + (* Silent steps *)
        intros s1 s1' s1'' Hs1' Hs1'' Hr1 s2 Hs Hs2.
        specialize (Hs1'' Hr1). clear Hr1 s1''.
        destruct Hs as (w & i & Hs).
        edestruct (bsim_E0_star HL) as (j & s2' & Hs2' & Hs12');
          eauto using star_one.
        edestruct Hs1'' as (r2 & Hr2 & Hr12).
        -- eexists. eexists. eauto.
        -- eauto using star_safe.
        -- exists r2. split; eauto.
           eapply RTS.obs_reachable; eauto.
           eapply star_reachable; eauto.
  Qed.

  Global Instance bsim_sound:
    Monotonic (@of) (forallr -, backward_simulation cc_id --> modref).
  Proof.
    intros li L1 L2 [index order match_states HL]. unfold of.
    econstructor; simpl; eauto.
    - eapply bsim_sound_step; eauto.
    - intros q.
      eapply bsim_sound_liftk; eauto.
      eapply bsim_initial_states; eauto.
      instantiate (1 := tt). constructor.
  Qed.
End Behavior.
