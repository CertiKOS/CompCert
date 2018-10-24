Require Import LogicalRelations.
Require Import KLR.
Require Import List.
Require Import Classical.
Require Import Events.
Require Import Smallstep.
Require Import Behaviors.
Require Import RTS.
Require Import ModuleSemantics.
Require Import Sets.


(** * CompCert games *)

(** The moves of CompCert games are queries, replies, CompCert events.
  Queries are inputs; replies and CompCert events are outputs. *)

Canonical Structure lang (li : language_interface) : game :=
  {|
    input := query li;
    output := reply li;
  |}.

Definition cc {li1 li2} (cc : callconv li1 li2) : abrel (lang li2) (lang li1) :=
  {|
    abr_init := cc_init cc;
    abr_input w w' q2 q1 := cc_query cc w w' q1 q2;
    abr_output w w' q2 q1 := cc_reply cc w w' q1 q2;
  |}.

Coercion lang : language_interface >-> game.
Coercion cc : callconv >-> abrel.
Bind Scope li_scope with game.


(** * Modules *)

(** ** Definition *)

Record modsem {G : game} :=
  {
    modsem_state : Type;
    modsem_lts :> rts G modsem_state;
    modsem_entry : RTS.cont G modsem_state;
  }.

Arguments modsem : clear implicits.

(** ** Refinement preorder *)

Record modref {GA GB} (GR : abrel GA GB) (α β : modsem _) : Prop :=
  {
    modref_state :
      abr_state GR -> rel (modsem_state α) (modsem_state β);
    modref_sim :
      RTS.sim GR modref_state (modsem_lts α) (modsem_lts β);
    modref_init :
      RTS.cont_le GR modref_state (abr_init GR) (modsem_entry α) (modsem_entry β);
  }.

(*
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
    + ercompose; eauto.
    + ercompose; eauto.
Qed.
*)


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

    Definition liftk {A} (k : cont li A): RTS.cont li state :=
      fun q =>
        match k q with
          | Some s => set_map RTS.resume (lifts s)
          | None => singl RTS.reject
        end.

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
  End LTS.

  (** ** Monotonicity *)

  (** Backward simulation of small-step semantics are sound with
    respect to the embedding defined above: given a backward
    simulation between two small-step semantics, we can show
    alternating refinement between their embeddings.

    We use the following alternating simulation relation. *)

  Inductive state_rel {W A B} R (w : W) : rel (@state A) (@state B) :=
    | running_rel s1 s2 :
        R w s2 s1 ->
        state_rel R w (running s1) (running s2)
    | wrong_rel S1 :
        state_rel R w S1 wrong.

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

  Lemma bsim_lifts {W A B} (R : klr W A B) w S1 S2 :
    bsim_match_sets (R w) S1 S2 ->
    set_le (state_rel R w) (lifts S2) (lifts S1).
  Proof.
    intros HS s2 Hs2.
    destruct Hs2 as [Hns2 | s2 Hs2].
    - exists wrong; split; constructor.
      intros [s1 Hs1]. apply Hns2. firstorder.
    - destruct (classic (ex S1)) as [[s1e Hs1e] | H1].
      + edestruct @bsim_sets_match as (s1 & Hs1 & Hs); eauto.
        exists (running s1); split; constructor; eauto.
      + exists wrong; split; constructor; eauto.
  Qed.

  Lemma bsim_sound_liftk {li1 li2} (cc: callconv li1 li2) {A B} (R : _ -> rel A B):
    Monotonic
      liftk
      (rforall w, bsim_match_cont cc R w --> RTS.cont_le cc (state_rel R) w).
  Proof.
    intros w k2 k1 Hk w' q2 q1 Hq b2 Hb2. unfold liftk in *.
    specialize (Hk w' q1 q2 Hq). destruct Hk as [S2 S1 HS | ].
    - destruct Hb2 as [s2 Hs2].
      eapply bsim_lifts in Hs2 as (s1 & Hs1 & Hs); eauto.
      exists (RTS.resume s1). split; constructor; eauto.
    - destruct Hb2 as [ ].
      eexists; split; constructor.
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

  Lemma bsim_sound_step {li1 li2} (cc: callconv li1 li2) L1 L2 ind ord ms:
    bsim_properties cc L1 L2 ind ord ms ->
    RTS.sim cc (state_rel (match_ex ms))
      (RTS.obs (step L2))
      (RTS.obs (step L1)).
  Proof.
    intros HL w S2 S1 HS r2 Hr2.
    destruct (classic (safe L1 S1)) as [HS1 | ];
      [ | now eauto using unsafe_goes_wrong with coqrel ].
    destruct HS as [s2 s1 [i Hs] | ]; simpl in HS1; try contradiction.
    inversion Hr2 as [Hs2 | S2 r Hrext Hr Hs2']; clear Hr2; subst.

    - (* Divergence *)
      exists RTS.diverges. split; [ | rauto].
      apply RTS.obs_diverges.
      eapply forever_internal_bsim; eauto.

    - (* Observation *)
      assert (HS2 : Smallstep.safe L2 s2) by eauto using bsim_safe.
      apply reachable_inv in Hs2' as (s2' & ? & Hs2'); auto; subst.
      revert i s1 Hs HS1. clear HS2.
      revert Hr. pattern s2, s2'. revert s2 s2' Hs2'.
      apply star_E0_ind.

      + (* Final states *)
        intros s2 Hr i s1 Hs Hs1.
        inversion Hr; clear Hr; subst; try now inversion Hrext.
        eapply bsim_match_final_states in H0; eauto.
        destruct H0 as (s1' & w' & r1 & k1 & Hs1' & Hr & Hsk1 & Hk); eauto.
        simpl in Hr; subst.
        exists (RTS.interacts r1 (liftk k1)). split.
        * eapply RTS.obs_external with (running s1'); eauto.
          -- constructor; eauto.
          -- eapply star_reachable; eauto.
        * econstructor. { eapply Hr. }
          intros w'' q1 q2 H1.
          eapply bsim_sound_liftk; eauto.

      + (* Silent steps *)
        intros s2 s2' s2'' Hs2' Hs2'' Hr2 i s1 Hs Hs1.
        specialize (Hs2'' Hr2). clear Hr2 s2''.
        edestruct (bsim_E0_star HL) as (j & s1' & Hs1' & Hs12');
          eauto using star_one.
        edestruct Hs2'' as (r1 & Hr1 & Hr12); eauto.
        -- eauto using star_safe.
        -- exists r1. split; eauto.
           eapply RTS.obs_reachable; eauto.
           eapply star_reachable; eauto.
  Qed.

  Global Instance bsim_sound :
    Monotonic (@of) (forallr cc, backward_simulation cc --> modref cc).
  Proof.
    intros li1 li2 cc L1 L2 [index order match_states HL]. unfold of.
    econstructor; simpl; eauto.
    - eapply bsim_sound_step; eauto.
    - intros w q1 q2 Hq.
      eapply bsim_sound_liftk; eauto.
      eapply bsim_initial_states; eauto.
  Qed.
End Behavior.
