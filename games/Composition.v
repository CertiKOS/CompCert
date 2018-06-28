Require Import LogicalRelations.
Require Import List.
Require Import Classical.
Require Import Events.
Require Import Smallstep.
Require Import Behaviors.
Require Import LTS.
Require Import Trees.
Require Import GameSemantics.
Require Import ModuleSemantics.
Require Import Classical.


(** * Resolution operator *)

Module Res.

  (** ** Core transition system *)

  Section RESOLVE.
    Context {li : language_interface}.
    Context (dom : query li -> bool).
    Context {A} (α : lts (option (move (li -o li))) A) (a0 : A).

    Definition state : Type := list A.

    Definition fcall q := Some (@qm (li -o li) (inr q)).
    Definition fret  r := Some (@rm (li -o li) (inr r)).
    Definition xcall q := Some (@rm (li -o li) (inl q)).
    Definition xret  r := Some (@qm (li -o li) (inl r)).

    Definition observable (at_outer_layer : Prop) (m : option (move (li -o li))) :=
      match m with
        | Some (rm (inr r)) => at_outer_layer
        | Some (rm (inl q)) => dom q = false
        | _ => True
      end.

    Inductive step : option (move (li -o li)) -> relation state :=
      | step_observable m a a' ks:
          observable (ks = nil) m ->
          α m a a' ->
          step m (a :: ks) (a' :: ks)
      | step_push q a k aq ks :
          dom q = true ->
          α (xcall q) a k ->
          α (fcall q) a0 aq ->
          step None (a :: ks) (aq :: k :: ks)
      | step_pop r a a' k ar ks :
          α (fret r) a a' ->
          α (xret r) k ar ->
          step None (a :: k :: ks) (ar :: ks).

  End RESOLVE.

  (** ** Core commutation theorem *)

  Section COMMUT.
    Context {li} (L : semantics (li -o li)) (dom : query li -> bool).

    Inductive res_commut_st ks : rel _ (option (ModuleSemantics.Res.state L)) :=
      | res_commut_st_none:
          res_commut_st ks None None
      | res_commut_st_some s:
          res_commut_st ks s (Some (s, ks)).

    Hint Constructors res_commut_st.

    Inductive res_commut_sim : rel _ _ :=
      | res_commut_sim_waiting k ks :
          res_commut_sim
            (Behavior.waiting L k :: map (Behavior.waiting L) ks)
            (Behavior.waiting (Res.semantics L dom) (Res.liftk L k ks))
      | res_commut_sim_running_some t s rs ks :
          res_commut_st ks s rs ->
          res_commut_sim
            (Behavior.running L t s :: map (Behavior.waiting L) ks)
            (Behavior.running (Res.semantics L dom) t rs)
      | res_commut_sim_wrong ks :
          res_commut_sim
            (Behavior.wrong L :: ks)
            (Behavior.wrong (Res.semantics L dom)).

    Lemma commut_observable r ks :
      ModuleSemantics.Res.observable L dom r ks <->
      Res.observable dom (map (Behavior.waiting L) ks = nil) (Some (rm r)).
    Proof.
      simpl. unfold ModuleSemantics.Res.observable.
      destruct r.
      - reflexivity.
      - split.
        + intro. subst. reflexivity.
        + destruct ks; simpl; congruence.
    Qed.

    Lemma apply_cont_exists k q:
      exists s, apply_cont L k q s.
    Proof.
      destruct (classic (exists s, k q s)) as [[s Hs] | Hns].
      - exists (Some s). constructor. eauto.
      - exists None. constructor. eauto.
    Qed.

    Lemma commut_goes_wrong s ks:
      (Nostep L s /\ forall r k, ~ final_state L s r k) <->
      (Nostep (Res.semantics L dom) (Some s, ks) /\
       forall r k, ~ final_state (Res.semantics L dom) (Some s, ks) r k).
    Proof.
      split.
      - intros [Hns Hnf]. split.
        + intros t s' Hs'.
          inversion Hs'; clear Hs'; subst.
          * eapply Hns; eauto.
          * eapply Hnf; eauto.
          * eapply Hnf; eauto.
        + intros r k Hs.
          inversion Hs; clear Hs; subst.
          eapply Hnf; eauto.
      - intros [Hns Hnf]. split.
        + intros t s' Hs'.
          eapply Hns. constructor. eauto.
        + intros r k Hs.
          destruct r as [q | r].
          * destruct (dom q) eqn:Hq.
            -- edestruct apply_cont_exists as [s' Hs'].
               eapply Hns. eapply Res.step_call; eauto.
            -- eapply Hnf. constructor; eauto.
               simpl. assumption.
          * destruct ks.
            -- eapply Hnf. constructor; eauto.
               simpl. reflexivity.
            -- edestruct apply_cont_exists as [s' Hs'].
               eapply Hns. eapply Res.step_return; eauto.
    Qed.

    Lemma apply_cont_commut k q s ks:
      let os := option_map (fun s => (Some s, ks)) s in
      apply_cont L k q s ->
      apply_cont (Res.semantics L dom) (Res.liftk L k ks) q os.
    Proof.
      intro; subst os.
      destruct 1.
      - constructor. constructor. assumption.
      - constructor. intros s Hs. destruct Hs. eapply H; eauto.
    Qed.

    Lemma res_commut :
      LTS.bisim res_commut_sim
        (step dom (Behavior.step L) (Behavior.waiting L (initial_state L)))
        (Behavior.step (Res.semantics L dom)).
    Proof.
      intros m s1 s2 Hs.
      split.
      - (* Forward *)
        intros s1' Hs1'.
        destruct Hs1'.
        + (* observable step *)
          destruct H0; inversion Hs; clear Hs; subst; simpl in H.
          * eexists; split; constructor.
            -- eapply apply_cont_commut; eauto.
            -- destruct s; simpl; eauto.
          * inversion H5; clear H5; subst.
            eexists; split; constructor; constructor; eauto.
          * eexists; split; constructor; eauto.
          * inversion H5; clear H5; subst.
            eexists; split; constructor; eauto.
            constructor; eauto. apply commut_observable. simpl. auto.
          * inversion H6; clear H6; subst.
            eexists; split; constructor; eauto;
            eapply commut_goes_wrong; eauto.
          * inversion H4; clear H4; subst;
            eexists; split; constructor; eauto.
            -- intros t s' Hs'. inversion Hs'.
            -- intros r k Hs. inversion Hs.
        + (* push *)
          inversion H0; clear H0; subst.
          inversion Hs; clear Hs; subst.
          inversion H6; clear H6; subst.
          inversion H1; clear H1; subst.
          change (?f ?hd :: map ?f ?tl) with (map f (hd :: tl)).
          eexists. split.
          * constructor. eapply Res.step_call; eauto.
          * econstructor. destruct H4; constructor.
        + (* pop *)
          inversion H; clear H; subst.
          inversion H0; clear H0; subst.
          inversion Hs; clear Hs; subst.
          inversion H5; clear H5; subst.
          destruct ks0 as [ | xk xks]; try discriminate.
          inversion H4; clear H4; subst.
          eexists. split.
          * constructor. eapply Res.step_return; eauto.
          * constructor. destruct H1; constructor.
      - (* Backward *)
        intros s2' Hs2'.
        destruct Hs2'; inversion Hs; clear Hs; subst.
        + (* waiting -> running *)
          destruct H.
          * destruct H.
            eexists; split; econstructor; simpl; eauto.
            constructor. constructor; eauto.
          * eexists; split; econstructor; simpl; eauto.
            constructor. constructor; eauto.
            intros s Hs. eapply H. constructor; eauto.
        + (* running *)
          inversion H2; clear H2; subst.
          inversion H; clear H; subst.
          * (* internal step *)
            eexists; split; constructor; simpl; eauto.
            constructor; eauto.
          * (* call *)
            eexists; split; [ | constructor; eauto]. simpl. econstructor.
            -- eassumption.
            -- constructor; eauto.
            -- constructor; eauto.
          * (* return *)
            eexists. split.
            -- eapply step_pop.
               ++ constructor; eauto.
               ++ constructor; eauto.
            -- constructor; eauto.
        + (* dequeue *)
          eexists; split; constructor; simpl; eauto.
          constructor.
        + (* terminate *)
          destruct H.
          inversion H2; clear H2; subst.
          apply commut_observable in H.
          eexists; split; constructor; simpl; eauto.
          constructor; eauto.
        + (* go wrong *)
          inversion H3; clear H3; subst.
          destruct s0.
          * edestruct (proj2 (commut_goes_wrong s ks)) as [Hns Hnf]; eauto.
            eexists. split; constructor.
            -- simpl. auto.
            -- constructor; eauto.
          * eexists. split; constructor.
            -- simpl. auto.
            -- constructor; eauto.
        + inversion H1; clear H1; subst.
          eexists; split; constructor; simpl; auto.
          constructor.
    Qed.

  End COMMUT.
End Res.
