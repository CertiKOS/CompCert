Require Import LogicalRelations.
Require Import List.
Require Import Classical.
Require Import Events.
Require Import Smallstep.
Require Import Behaviors.
Require Import LTS.
Require Import Trees.
Require Import ModuleSemantics.


(** * CompCert games *)

(** The moves of CompCert games are queries, replies, CompCert events,
  and two special moves that denote silent divergence and going wrong.
  Queries are inputs, and all other moves are outputs.

  Because divergence is counted as an output move, this corresponds to
  total correctness. It may useful in the future to consider
  refinement lattices where divergence counts as in input (for partial
  correctness). *)

Inductive move {li} :=
  | qm (q : query li) : move
  | rm (r : reply li) : move
  | ev (e : event)
  | crash
  | diverge.

Arguments move : clear implicits.

Definition tc {li} (m : move li) :=
  match m with
    | qm _ => false
    | rm _ => true
    | ev _ => true
    | crash => true
    | diverge => true
  end.

Definition behavior li :=
  Gametree.t (move li).


(** * Behaviors from small step semantics *)

Module Behavior.
  Section LTS.
    Context {li} (L : Smallstep.semantics li).

    (** ** Transition system *)

    Inductive state :=
      | waiting (k: query li -> Smallstep.state L -> Prop)
      | running (q: list event) (s: option (Smallstep.state L))
      | wrong.

    Inductive step: lts (option (move li)) state :=
      | step_query k q s:
          apply_cont L k q s ->
          step (Some (qm q)) (waiting k) (running nil s)
      | step_run s t s':
          Step L s t s' ->
          step None (running nil (Some s)) (running t (Some s'))
      | step_deq e t s:
          step (Some (ev e)) (running (e :: t) s) (running t s)
      | step_terminate s r k:
          final_state L s r k ->
          step (Some (rm r)) (running nil (Some s)) (waiting k)
      | step_stuck s:
          Nostep L s ->
          (forall r k, ~ final_state L s r k) ->
          step (Some crash) (running nil (Some s)) wrong
      | step_wrong :
          step (Some crash) (running nil None) wrong.

    Definition of: behavior li :=
      Gametree.c
        (LTS.sup tc (LTS.bigstep step diverge))
        (LTS.bigstep_initial step (waiting (initial_state L))).

    (** ** Properties *)

    (*

    (** The following properties of the transition system will be
      useful in the soundness proof below. *)

    Lemma step_run_star s s' m S:
      Star L s E0 s' ->
      LTS.bigstep step diverge m (Some (running E0 s')) S ->
      LTS.bigstep step diverge m (Some (running E0 s)) S.
    Proof.
      intros H. pattern s, s'.
      eapply star_E0_ind; eauto using step_run, LTS.bigstep_silent_step.
    Qed.

    Lemma running_no_input m t s S':
      LTS.bigstep step diverge m (Some (running t s)) S' ->
      tc m = true.
    Proof.
      intros HS'. remember (Some (running t s)) as S eqn:HS. revert t s HS.
      induction HS'; eauto.
      - inversion 1; subst. inversion H; eauto.
      - inversion 1; subst. inversion H; clear H; subst; eauto.
    Qed.

    Definition safe S :=
      match S with
        | Some (running nil s) => Smallstep.safe L s
        | _ => True
      end.

    Lemma unsafe_goes_wrong m S:
      tc m = true ->
      ~ safe S ->
      exists S', LTS.bigstep step diverge m S S' /\ ~ safe S'.
    Proof.
      intros Hm HS.
      destruct S as [ [ ] | ]; simpl in *; try tauto.
      destruct t; try contradiction.
      apply not_all_ex_not in HS as [s' HS].
      apply not_all_ex_not in HS as [Hs' HS].
      revert HS. pattern s, s'. revert s s' Hs'.
      eapply star_E0_ind; eauto; intros.
      - eexists; split.
        + eapply LTS.bigstep_step. apply step_wrong; firstorder.
        + simpl. intros Hs. apply HS. eapply Hs. apply star_refl.
      - edestruct H0 as (S' & HSS' & HS'); eauto. eexists; split; eauto.
        eapply LTS.bigstep_silent_step; eauto.
        eapply step_run; eauto.
    Qed.

    (** ** Determinism *)

    (** From deterministic small-step semantics, we can obtain a
      deterministic transition system without the use of [LTS.sup].
      However we need to restrict the state space in order to avoid
      non-deterministic continuations. *)

    Definition state_determ (s : state) : Prop :=
      match s with
        | waiting k => forall q s1 s2, k q s1 -> k q s2 -> s1 = s2
        | _ => True
      end.

    Definition step_determ m (s s' : sig state_determ) : Prop :=
      step m (proj1_sig s) (proj1_sig s').

    (*
    Lemma program_lts_determ:
      Smallstep.determinate L ->
      LTS.determ (LTS.bigstep step_determ diverge).
    Proof.
      intros HL m [s Hs] [s1 Hs1] [s2 Hs2] H1 H2.
      red in H1, H2. simpl in *.
      cut (s1 = s2). { intro; subst. f_equal. apply proof_irrelevance. }
      revert s2 Hs2 H2.
      induction H1; intros; inversion H2; clear H2; simpl in *; subst; eauto.
      - specialize (Hs _ _ _ H H3). congruence.
      - eapply IHstep; eauto.
        edestruct @sd_determ; [ | apply H | apply H3 | ]; eauto.
    Abort. (* determinism -- tedious but straightforward *)
     *)

    *)

  End LTS.

  (*
  (** ** Monotonicity *)

  (** Backward simulation of small-step semantics are sound with
    respect to the embedding defined above: given a backward
    simulation between two small-step semantics, we can show
    alternating refinement between their embeddings.

    We use the following alternating simulation relation. *)

  Inductive state_rel {li L1 L2} (R : rel _ _) : rel _ _ :=
    | waiting_rel (k1 k2: query li -> _ -> Prop):
        (forall q s2, k2 q s2 -> exists s1, k1 q s1) ->
        (forall q s1 s2, k1 q s1-> k2 q s2-> exists s2', k2 q s2' /\ R s1 s2') ->
        state_rel R (Some (waiting L1 k1)) (Some (waiting L2 k2))
    | running_rel t1 s1 s2 t2 s2':
        Star L2 s2 t2 s2' ->
        R s1 s2' ->
        state_rel R (Some (running L1 (t1 ** t2) s1)) (Some (running L2 t1 s2))
    | wrong_rel S1 S2:
        ~ safe L2 S2 ->
        state_rel R S1 S2
    | diverge_rel:
        state_rel R None None.

  Hint Constructors state_rel.

  Lemma forever_silent_trace {li} (L : semantics li) t s:
    LTS.forever_silent (step L) (running L t s) ->
    t = E0.
  Proof.
    destruct t.
    - reflexivity.
    - intros H. destruct H. inversion H.
  Qed.

  Lemma lts_forever_silent {li} (L : semantics li) t s:
    LTS.forever_silent (step L) (running L t s) ->
    Forever_silent L s.
  Proof.
    revert t s. cofix IH.
    intros.
    assert (t = E0) by eauto using forever_silent_trace; subst.
    destruct H. inversion H; clear H; subst.
    assert (t = E0) by eauto using forever_silent_trace; subst.
    econstructor; eauto.
  Qed.

  Lemma forever_silent_lts {li} (L : semantics li) s:
    Forever_silent L s ->
    LTS.forever_silent (step L) (running L E0 s).
  Proof.
    revert s. cofix IH.
    intros.
    destruct H. econstructor; eauto.
    constructor. eauto.
  Qed.

  Lemma bsim_sound_step {li} (L1 L2: semantics li) ind ord ms:
    bsim_properties L2 L1 ind ord ms ->
    LTS.ref tc (set_le (state_rel (flip (rel_ex ms))))
      (LTS.sup tc (LTS.bigstep (step L1) diverge))
      (LTS.sup tc (LTS.bigstep (step L2) diverge)).
  Proof.
    set (R := flip (rel_ex ms)). unfold flip, rel_ex in R.
    intros HL.
    eapply LTS.sup_nref. intros m S1 S2 HS.
    destruct (tc m) eqn:Hm.

    - (* Output moves *)
      intros S1' HS1'.
      destruct (classic (safe L2 S2)) as [HS2 | ];
        [ | edestruct @unsafe_goes_wrong as (? & ? & ?); eauto; fail ].
      revert S2 HS HS2. induction HS1'; intros.

      + (* Noisy steps *)
        inversion H; clear H; subst.
        * (* query *)
          discriminate.
        * (* deq *)
          inversion HS; clear HS; subst; eauto using LTS.bigstep_step, step_wrong.
          clear HS2 Hm. revert t1 H. induction H1; intros.
          -- rewrite E0_right in H. subst.
             exists (Some (running L2 t s0)). rewrite <- (E0_right t) at 3.
             split; econstructor; eauto using star_refl. constructor.
          -- subst.
             destruct t3 as [ | e0 t0].
             ++ rewrite E0_left in H2.
                edestruct IHstar as (S2 & HS2 & HS); eauto.
                exists S2. split; eauto.
                eapply LTS.bigstep_silent_step; eauto.
                eapply step_run; eauto.
             ++ setoid_rewrite <- app_comm_cons in H2. inversion H2; clear H2; subst.
                edestruct IHstar as (S2 & HS2 & HS); eauto.
                { instantiate (1 := e :: t0 ** t1).
                  setoid_rewrite <- app_comm_cons. f_equal.
                  setoid_rewrite app_assoc. reflexivity. }
                exists (Some (running L2 t0 s1)).
                split. constructor. constructor.
                econstructor; eauto.
                eapply star_step; eauto.
          -- contradiction.
        * (* terminate *)
          inversion HS; clear HS; subst; eauto using LTS.bigstep_step, step_wrong.
          apply Eapp_E0_inv in H as [? ?]; subst. simpl in *.
          destruct H4 as [i Hs].
          edestruct @bsim_match_final_states as (s2'' & k2 & Hs2'' & Hk2 & Hk);
            eauto using star_safe.
          exists (Some (waiting L2 k2)). split.
          -- revert Hs Hk2. pattern s2, s2''. clear - H2 Hs2''.
             eapply star_E0_ind; eauto; intros.
             ++ eauto using LTS.bigstep_step, step_terminate.
             ++ eauto using LTS.bigstep_silent_step, step_run.
             ++ eapply star_trans; eauto.
          -- revert Hk. clear. intros [Hke Hkm].
             constructor; eauto.
             intros q s1 s2 Hs1 Hs2.
             edestruct Hkm as (i & s2' & Hs2' & Hs'); eauto.
             unfold R. eauto.
          -- contradiction.
        * (* staying wrong *)
          inversion HS; clear HS; subst; try contradiction.
          apply Eapp_E0_inv in H as [? ?]; subst. simpl in *.
          destruct H6 as [i Hs].
          edestruct @bsim_progress as [(?&?&?) | (?&?&?)]; eauto using star_safe.
          -- eelim H2; eauto.
          -- eelim H1; eauto.

      + (* Silent steps *)
        inversion H; clear H; subst.
        * (* run *)
          inversion HS; clear HS; subst; eauto using LTS.bigstep_step,step_wrong.
          apply Eapp_E0_inv in H as [? ?]; subst. simpl in *.
          destruct H4 as [i Hs].
          edestruct @bsim_simulation as (i' & s1' & Hs1' & Hs');
            eauto using star_safe.
          eapply IHHS1'; eauto.
          rewrite <- (E0_left t). econstructor; subst R; simpl; eauto.
          eapply star_trans; eauto using E0_left.
          intuition auto using plus_star.

      + (* Silent divergence *)
        inversion HS; clear HS; subst.
        * destruct H. inversion H.
        * assert (Ht : t1 ** t2 = E0) by eauto using forever_silent_trace.
          apply Eapp_E0_inv in Ht as [Ht1 Ht2]; subst. simpl in *.
          destruct H2 as [i Hs].
          eapply lts_forever_silent in H.
          eapply (backward_simulation_forever_silent HL) in H; eauto using star_safe.
          eapply forever_silent_lts in H.
          exists None. split; [ | constructor; fail ].
          revert H. pattern s2, s2'. revert H1. clear.
          eapply star_E0_ind; eauto; intros.
          -- constructor; eauto.
          -- eapply LTS.bigstep_silent_step; eauto.
             eapply step_run; eauto.
        * contradiction.

    - (* Input moves *)
      intros S2x HS2x.
      revert S1 HS. induction HS2x; simpl in *; try congruence; intros.

      + (* Regular steps *)
        inversion H; clear H; subst; simpl in *; try congruence.
        inversion HS; clear HS; subst; simpl in *; try contradiction.
        split.
        * edestruct H0 as [s1' Hs1']; eauto.
          exists (Some (running L1 E0 s1')). constructor.
          constructor; eauto.
        * intros S1' HS1'.
          inversion HS1'; clear HS1'; subst.
          -- inversion H4; clear H4; subst.
             edestruct H3 as (s2' & Hs2' & Hs'); eauto.
             change E0 with (E0 ++ E0).
             exists (Some (running L2 E0 s2')); split; econstructor; eauto.
             ++ econstructor; eauto.
             ++ apply star_refl.
          -- inversion H2.

      + (* Silent steps *)
        inversion H; clear H; subst.
        apply running_no_input in HS2x. congruence.
  Qed.

  Global Instance bsim_sound:
    Monotonic (@of) (forallr -, backward_simulation --> Gametree.ref tc).
  Proof.
    intros li L1 L2 [index order match_states HL].
    eapply Gametree.c_ref.
    - eapply LTS.sup_determ.
    - eapply LTS.sup_determ.
    - eapply bsim_sound_step; eauto.
    - unfold set_le, flip, rel_ex. intros. subst.
      exists (Some (waiting L2 (initial_state L2))). split; eauto.
      constructor.
      + eapply bsim_initial_states_exist; eauto.
      + intros. edestruct @bsim_match_initial_states as (? & ? & ? & ?); eauto.
  Qed.
   *)
End Behavior.
