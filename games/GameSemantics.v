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

Coercion lang (li : language_interface) : game :=
  {|
    input := query li;
    output := reply li;
  |}.

Bind Scope li_scope with game.


(** * Modules *)

Record modsem {li : language_interface} :=
  {
    modsem_state : Type;
    modsem_lts :> rts li modsem_state;
    modsem_entry : input li -> option modsem_state;
  }.

Arguments modsem : clear implicits.

Record modref {li} (α β : modsem li) : Prop :=
  {
    modref_state :
      rel (modsem_state α) (modsem_state β);
    modref_sim :
      RTS.sim modref_state (modsem_lts α) (modsem_lts β);
    modref_init :
      forall q, option_rel modref_state (modsem_entry α q) (modsem_entry β q);
  }.


(** * Behaviors from small step semantics *)

Module Behavior.
  Section LTS.
    Context {li} (L : Smallstep.semantics li).

    (** ** Transition system *)

    Inductive state {A} :=
      | resumed (k : A -> Prop)
      | running (s : A).

    Definition liftk {A} (k : cont li A) (q : input li): option state :=
      option_map resumed (k q).

    Inductive step : rts li state :=
      | step_resumed (k : Smallstep.state L -> Prop) s :
          k s ->
          step (resumed k) (RTS.internal (running s))
      | step_goes_initially_wrong (k : Smallstep.state L -> Prop) :
          ~ ex k ->
          step (resumed k) (RTS.goes_wrong)
      | step_internal s s' :
          Step L s E0 s' ->
          step (running s) (RTS.internal (running s'))
      | step_interacts s r k :
          final_state L s r k ->
          step (running s) (RTS.interacts (G:=li) r (liftk k))
      | step_goes_wrong s :
          Nostep L s ->
          (forall r k, ~ final_state L s r k) ->
          step (running s) (RTS.goes_wrong).

    Definition of : modsem li :=
      {|
        modsem_state := state;
        modsem_lts := RTS.obs step;
        modsem_entry := liftk (initial_state L);
      |}.

    (** ** Properties *)

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
        | resumed k => ex k /\ forall s, k s -> Smallstep.safe L s
        | running s => Smallstep.safe L s
      end.

    Lemma unsafe_goes_wrong S:
      ~ safe S ->
      RTS.obs step S RTS.goes_wrong.
    Proof.
      assert (forall s, ~ Smallstep.safe L s ->
                        RTS.obs step (running s) RTS.goes_wrong).
      {
        intros s HS.
        apply not_all_ex_not in HS as [s' HS].
        apply not_all_ex_not in HS as [Hs' HS].
        revert HS. pattern s, s'. revert s s' Hs'.
        eapply star_E0_ind; eauto; intros.
        + econstructor; eauto.
          eapply step_goes_wrong; firstorder.
        + eapply RTS.obs_internal; eauto.
          constructor; eauto.
      }
      intros HS.
      destruct S as [ | ]; simpl in *; eauto.
      apply not_and_or in HS as [HS | HS].
      - econstructor; eauto.
        constructor; eauto.
      - eapply not_all_ex_not in HS as [s HS].
        eapply not_all_ex_not in HS as [Hs HS].
        eapply RTS.obs_internal; eauto.
        constructor; eauto.
    Qed.

    (** ** Determinism *)

    (** From deterministic small-step semantics, we can obtain a
      deterministic transition system.
      However we need to restrict the state space in order to avoid
      non-deterministic continuations. *)

    Definition state_determ (s : state (A := Smallstep.state L)) : Prop :=
      match s with
        | resumed k => forall s1 s2, k s1 -> k s2 -> s1 = s2
        | _ => True
      end.

    Definition step_determ : rts li (sig state_determ) :=
      fun s r =>
        step (proj1_sig s) (RTS.behavior_map (@proj1_sig _ _) r).

    Lemma program_lts_determ:
      Smallstep.determinate L ->
      RTS.deterministic step_determ.
    Proof.
      intros HL [s Hs] r1 r2 H1 H2.
      red in H1, H2. simpl in *.
      destruct r1 as [[s' Hs'] | m k1 | | ]; inversion H1; clear H1; subst.
    Abort. (* determinism -- tedious but straightforward *)

  End LTS.


  (** ** Monotonicity *)

  (** Backward simulation of small-step semantics are sound with
    respect to the embedding defined above: given a backward
    simulation between two small-step semantics, we can show
    alternating refinement between their embeddings.

    We use the following alternating simulation relation. *)

  Inductive state_rel {A B} (R : rel A B) : rel state state :=
    | resumed_rel (k1 k2 : _ -> Prop) :
        (forall s2, k2 s2 -> exists s1, k1 s1) ->
        (forall s1 s2, k1 s1 -> k2 s2 -> exists s2', k2 s2' /\ R s1 s2') ->
        state_rel R (resumed k1) (resumed k2)
    | running_rel s1 s2 :
        R s1 s2 ->
        state_rel R (running s1) (running s2).

  Hint Constructors state_rel.

  Lemma rts_forever_silent {li} (L : semantics li) s:
    RTS.forever_internal (step L) (running s) ->
    Forever_silent L s.
  Proof.
    revert s. cofix IH.
    intros.
    destruct H. inversion H; clear H; subst.
    econstructor; eauto.
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

  Lemma forever_internal_bsim {li} (L1 L2: semantics li) ind ord ms i S1 S2:
    bsim_properties L2 L1 ind ord ms ->
    ms i S2 S1 ->
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

  Lemma bsim_sound_liftk {li} L1 L2 ind ord ms (k1 k2: cont li _) q :
    @bsim_properties li L2 L1 ind ord ms ->
    bsim_match_cont (rel_ex ms) k2 k1 ->
    option_rel (state_rel (flip (rel_ex ms))) (liftk k1 q) (liftk k2 q).
  Proof.
    intros HL Hk. unfold liftk.
    specialize (Hk q). destruct Hk as [S1 S2 HS | ]; constructor.
    constructor.
    - intros.
      edestruct @bsim_sets_exists as (? & ? & ?); eauto.
    - intros. unfold flip, rel_ex.
      edestruct @bsim_sets_match as (? & ? & ?); eauto.
  Qed.

  Lemma bsim_sound_step {li} (L1 L2: semantics li) ind ord ms:
    bsim_properties L2 L1 ind ord ms ->
    RTS.sim (state_rel (flip (rel_ex ms)))
      (RTS.obs (step L1))
      (RTS.obs (step L2)).
  Proof.
    set (R := flip (rel_ex ms)). unfold flip, rel_ex in R.
    intros HL S1 S2 HS S1' HS1'.
    destruct (classic (safe L2 S2)) as [HS2 | ];
      [ | now eauto using unsafe_goes_wrong with coqrel ].
    destruct HS1' as [HS1 | S1' r Hrext Hr HS1'].

    - (* Divergence *)
      exists RTS.diverges. split; [ | rauto].
      destruct HS.
      + destruct HS1 as [S1' HS1' HS1].
        inversion HS1'; clear HS1'; subst.
        simpl in HS2. destruct HS2 as [[s2 Hks2] Hk].
        edestruct H0 as (s2' & Hs2' & i & Hs'); eauto.
        apply RTS.obs_diverges.
        econstructor.
        * econstructor; eauto.
        * eapply forever_internal_bsim; eauto.
      + destruct H as [i H].
        apply RTS.obs_diverges.
        eapply forever_internal_bsim; eauto.

    - (* Observation *)
      revert S2 HS HS2.
      induction HS1'; intros.

      + (* Noisy steps *)
        destruct Hr; inversion HS; clear HS; inversion Hrext; clear Hrext; subst.
        * (* Can't initially go wrong *)
          simpl in HS2. destruct HS2 as [[s2 Hs2] Hk2].
          edestruct H1 as [s1 Hs1]; eauto.
          elim H; eauto.
        * (* Final states *)
          destruct H1 as (i & Hs).
          eapply bsim_match_final_states in H; eauto.
          destruct H as (s2' & k2 & Hs2' & Hsk2 & Hk); eauto.
          exists (RTS.interacts (G:=li) r (liftk k2)). split.
          -- eapply RTS.obs_external with (running s2'); eauto.
             ++ constructor; eauto.
             ++ eapply star_reachable; eauto.
          -- constructor. intro q.
             eapply bsim_sound_liftk; eauto.
        * (* Can't go wrong *)
          simpl in HS2. subst R. destruct H2 as [i Hs].
          eapply bsim_safe in HS2; eauto. red in HS2. clear - HS2 H0 H. exfalso.
          edestruct HS2 as [(r & k & Hs)|(t & s' & Hs')]; eauto using star_refl.
          -- eapply H0; eauto.
          -- eapply H; eauto.

      + (* Silent steps *)
        specialize (IHHS1' Hr). clear Hr a'' HS1'.
        destruct HS; inversion H; clear H; subst.
        * (* Resumed execution *)
          simpl in HS2. destruct HS2 as [[s2 Hs2] Hk2].
          edestruct H1 as (s2' & Hs2' & Hs); eauto.
          edestruct IHHS1' as (r2 & Hr2 & Hr12); eauto.
          -- simpl. eauto.
          -- exists r2. split; eauto.
             eapply RTS.obs_internal; eauto.
             constructor; eauto.
        * (* E0 step *)
          destruct H0 as [i Hs12]. simpl in HS2.
          edestruct (bsim_E0_star HL) as (j & s2' & Hs2' & Hs12');
            eauto using star_one.
          edestruct IHHS1' as (r2 & Hr2 & Hr12).
          -- constructor. eexists. eauto.
          -- simpl. eauto using star_safe.
          -- exists r2. split; eauto.
             eapply RTS.obs_reachable; eauto.
             eapply star_reachable; eauto.
  Qed.

  Global Instance bsim_sound:
    Monotonic (@of) (forallr -, backward_simulation --> modref).
  Proof.
    intros li L1 L2 [index order match_states HL]. unfold of.
    econstructor; simpl; eauto.
    - eapply bsim_sound_step; eauto.
    - intros q.
      eapply bsim_sound_liftk; eauto.
      eapply bsim_initial_states; eauto.
  Qed.
End Behavior.
