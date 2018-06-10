Require Import LogicalRelations.
Require Import List.
Require Import Classical.
Require Import Events.
Require Import Smallstep.
Require Import Behaviors.
Require Import LTS.
Require Import Trees.


(** * CompCert games *)

(** The moves of CompCert games are queries, replies, CompCert events,
  and two special moves that denote silent divergence and going wrong.
  Queries are inputs, and all other moves are outputs.

  Because divergence is counted as an output move, this corresponds to
  total correctness. It may useful in the future to consider
  refinement lattices where divergence counts as in input (for partial
  correctness). *)

Inductive move {li} :=
  | qm (q : query li) :> move
  | rm (r : reply li) :> move
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
      | running (t: trace) (s: Smallstep.state L)
      | silent
      | wrong.

    Inductive step: lts (move li) state :=
      | step_query (k: _ -> _ -> Prop) q s:
          k q s ->
          step (qm q) (waiting k) (running E0 s)
      | step_run s t s' m S:
          Step L s t s' ->
          step m (running t s') S ->
          step m (running E0 s) S
      | step_deq e t s:
          step (ev e) (running (e :: t) s) (running t s)
      | step_terminate s r k:
          final_state L s r k ->
          step (rm r) (running E0 s) (waiting k)
      | step_diverge s:
          Forever_silent L s ->
          step diverge (running E0 s) silent
      | step_goes_wrong s m S:
          Nostep L s ->
          (forall r k, ~ final_state L s r k) ->
          step m wrong S ->
          step m (running E0 s) S
      | step_wrong m:
          tc m = true ->
          step m wrong wrong.

    Definition of: behavior li :=
      Gametree.c (LTS.sup tc step) (eq (waiting (initial_state L))).

    (** ** Properties *)

    (** The following properties of the transition system will be
      useful in the soundness proof below. *)

    Lemma step_run_star s s' m S:
      Star L s E0 s' ->
      step m (running E0 s') S ->
      step m (running E0 s) S.
    Proof.
      intros H. pattern s, s'. eapply star_E0_ind; eauto using step_run.
    Qed.

    Lemma running_no_input m t s S':
      step m (running t s) S' ->
      tc m = true.
    Proof.
      intros HS'. remember (running t s) as S eqn:HS. revert t s HS.
      induction HS'; inversion 1; subst; simpl; eauto.
      inversion HS'; eauto.
    Qed.

    Definition safe S :=
      match S with
        | wrong => False
        | running nil s => Smallstep.safe L s
        | _ => True
      end.

    Lemma unsafe_goes_wrong m S:
      tc m = true ->
      ~ safe S ->
      step m S wrong.
    Proof.
      intros Hm HS.
      destruct S; simpl in *; try tauto.
      - destruct t; try contradiction.
        apply not_all_ex_not in HS as [s' HS].
        apply not_all_ex_not in HS as [Hs' HS].
        revert HS. pattern s, s'. revert s s' Hs'.
        eapply star_E0_ind; eauto; intros.
        + eapply step_goes_wrong.
          * firstorder.
          * firstorder.
          * constructor. assumption.
        + eapply step_run; eauto.
      - constructor; eauto.
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

    Definition step_determ (m : move li) (s s' : sig state_determ) : Prop :=
      step m (proj1_sig s) (proj1_sig s').

    Lemma program_lts_determ:
      Smallstep.determinate L ->
      LTS.determ step_determ.
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

  End LTS.

  (** ** Monotonicity *)

  (** Backward simulation of small-step semantics are sound with
    respect to the embedding defined above: given a backward
    simulation between two small-step semantics, we can show
    alternating refinement between their embeddings.

    We use the following alternating simulation relation. *)

  Inductive state_rel {li L1 L2} (R : rel _ _) : rel (state L1) (state L2) :=
    | waiting_rel (k1 k2: query li -> _ -> Prop):
        (forall q s2, k2 q s2 -> exists s1, k1 q s1) ->
        (forall q s1 s2, k1 q s1-> k2 q s2-> exists s2', k2 q s2' /\ R s1 s2') ->
        state_rel R (waiting L1 k1) (waiting L2 k2)
    | running_rel t1 s1 s2 t2 s2':
        Star L2 s2 t2 s2' ->
        R s1 s2' ->
        state_rel R (running L1 (t1 ** t2) s1) (running L2 t1 s2)
    | silent_rel:
        state_rel R (silent L1) (silent L2)
    | wrong_rel S1:
        state_rel R S1 (wrong L2).

  Hint Constructors state_rel.

  Lemma bsim_sound_step {li} (L1 L2: semantics li) ind ord ms:
    bsim_properties L2 L1 ind ord ms ->
    LTS.ref tc (set_le (state_rel (flip (rel_ex ms))))
      (LTS.sup tc (step L1))
      (LTS.sup tc (step L2)).
  Proof.
    set (R := flip (rel_ex ms)). unfold flip, rel_ex in R.
    intros HL.
    eapply LTS.sup_nref. intros m S1 S2 HS.
    destruct (tc m) eqn:Hm.
    - intros S1' HS1'.
      destruct (classic (safe L2 S2)) as [HS2 | ]; eauto using unsafe_goes_wrong.
      revert S2 HS HS2. induction HS1'; intros.
      + (* query *)
        discriminate.
      + (* run *)
        inversion HS; clear HS; subst; eauto using step_wrong.
        apply Eapp_E0_inv in H0 as [? ?]; subst. simpl in *.
        destruct H4 as [i Hs].
        edestruct @bsim_simulation as (i' & s1' & Hs1' & Hs'); eauto using star_safe.
        eapply IHHS1'; eauto.
        rewrite <- (E0_left t). econstructor; subst R; simpl; eauto.
        eapply star_trans; eauto using E0_left.
        intuition auto using plus_star.
      + (* deq *)
        inversion HS; clear HS; subst; eauto using step_wrong.
        clear HS2 Hm. revert t1 H. induction H1; intros.
        * rewrite E0_right in H. subst.
          exists (running L2 t s0). rewrite <- (E0_right t) at 3.
          split; econstructor; eauto using star_refl.
        * subst.
          destruct t3 as [ | e0 t0].
          -- rewrite E0_left in H2.
             edestruct IHstar as (S2 & HS2 & HS); eauto.
             exists S2. split; eauto.
             eapply step_run; eauto.
          -- setoid_rewrite <- app_comm_cons in H2. inversion H2; clear H2; subst.
             edestruct IHstar as (S2 & HS2 & HS); eauto.
             { instantiate (1 := e :: t0 ** t1).
               setoid_rewrite <- app_comm_cons. f_equal.
               setoid_rewrite app_assoc. reflexivity. }
             exists (running L2 t0 s1). split. constructor. econstructor; eauto.
             eapply star_step; eauto.
      + (* terminate *)
        inversion HS; clear HS; subst; eauto using step_wrong.
        apply Eapp_E0_inv in H0 as [? ?]; subst. simpl in *.
        destruct H4 as [i Hs].
        edestruct @bsim_match_final_states as (s2'' & k2 & Hs2'' & Hk2 & Hk);
          eauto using star_safe.
        exists (waiting L2 k2). split.
        * revert Hs Hk2. pattern s2, s2''. clear - H2 Hs2''.
          eapply star_E0_ind; eauto; intros.
          -- eapply step_terminate; eauto.
          -- eapply step_run; eauto.
          -- eapply star_trans; eauto.
        * revert Hk. clear. intros [Hke Hkm].
          constructor; eauto.
          intros q s1 s2 Hs1 Hs2.
          edestruct Hkm as (i & s2' & Hs2' & Hs'); eauto.
          unfold R. eauto.
      + (* diverge *)
        inversion HS; clear HS; subst; eauto using step_wrong.
        apply Eapp_E0_inv in H0 as [? ?]; subst. simpl in *.
        destruct H4 as [i Hs].
        eapply (backward_simulation_forever_silent HL) in H; eauto using star_safe.
        exists (silent L2). split; [ | constructor].
        revert H. pattern s2, s2'. revert H2. clear.
        eapply star_E0_ind; eauto; intros.
        * eapply step_diverge; eauto.
        * eapply step_run; eauto.
      + (* going wrong *)
        inversion HS; clear HS; subst; eauto using step_wrong.
        apply Eapp_E0_inv in H1 as [? ?]; subst. simpl in *.
        destruct H5 as [i Hs].
        edestruct @bsim_progress as [(?&?&?) | (?&?&?)]; eauto using star_safe.
        * eelim H0; eauto.
        * eelim H; eauto.
      + (* staying wrong *)
        inversion HS; clear HS; subst; eauto using step_wrong.
    - intros S2x HS2x.
      revert S1 HS. induction HS2x; simpl in *; try congruence; intros.
      + (* query *)
        inversion HS; clear HS; subst.
        split.
        * edestruct H1 as [s1' Hs1']; eauto.
          exists (running L1 E0 s1').
          constructor; eauto.
        * intros S1' HS1'.
          inversion HS1'; clear HS1'; subst.
          edestruct H3 as (s2' & Hs2' & Hs'); eauto.
          change E0 with (E0 ++ E0).
          exists (running L2 E0 s2'); split; econstructor; eauto.
          apply star_refl.
      + apply running_no_input in HS2x. congruence.
      + inversion HS2x. congruence.
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
      exists (waiting L2 (initial_state L2)). split; eauto.
      constructor.
      + eapply bsim_initial_states_exist; eauto.
      + intros. edestruct @bsim_match_initial_states as (? & ? & ? & ?); eauto.
  Qed.
End Behavior.
