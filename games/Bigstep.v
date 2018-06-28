Require Export LogicalRelations.
Require Export LTS.
Require Export Trees.


(** * Bigstepping operator *)

Module Bigstep.

  (** ** Transition system *)

  (** Note that silent steps are taken *after* one noisy steps. This
    is important so that ↓(τ₁ ⊔ ετ₂) = τ₁ ⊔ τ₂ once we compose the
    bigstep operator below with [sup]. If we were to take silent steps
    first then a noisy step, the joining would happen one step into τ₁
    and τ₂ instead, which is not what we want. *)

  Section LTS.
    Context {M A} (α : lts (option M) A) (d : M).

    CoInductive forever_silent (a : A) : Prop :=
      forever_silent_intro a' :
        α None a a' ->
        forever_silent a' ->
        forever_silent a.

    Inductive silent_successor (a : A) : A -> Prop :=
      | succ_refl :
          silent_successor a a
      | succ_step a' a'' :
          α None a a' ->
          silent_successor a' a'' ->
          silent_successor a a''.

    Inductive step : lts M (option A) :=
      | step_intro m a a' a'' :
          α (Some m) a a' ->
          silent_successor a' a'' ->
          step m (Some a) (Some a'')
      | step_diverge a :
          forever_silent a ->
          step d (Some a) None.

    Inductive initial (a : A) : option A -> Prop :=
      initial_intro a' :
        silent_successor a a' ->
        initial a (Some a').

  End LTS.

  Section BISIM.
    Context {M A B} (R : rel A B) (α : lts (option M) A) (β : lts (option M) B).

    Lemma silent_successor_bisim a b a' :
      LTS.bisim R α β ->
      R a b -> silent_successor α a a' ->
      exists b', silent_successor β b b' /\ R a' b'.
    Proof.
      intros Hαβ Hab Ha'. revert b Hab.
      induction Ha'; intros.
      - exists b. split; eauto. constructor.
      - edestruct Hαβ as [(b' & Hb' & Hab') _]; eauto.
        edestruct IHHa' as (b'' & Hb'' & Hab''); eauto.
        exists b''. split; eauto. econstructor; eauto.
    Qed.

    Lemma forever_silent_bisim a b :
      LTS.bisim R α β ->
      R a b ->
      forever_silent α a ->
      forever_silent β b.
    Proof.
      intros Hαβ. revert a b. cofix IH. intros a b Hab H.
      destruct H as [a' Ha' H].
      eapply Hαβ in Ha' as (b' & Hb' & Hab'); eauto.
      econstructor; eauto.
    Qed.

    Lemma step_bisim_sim d :
      LTS.bisim R α β ->
      LTS.sim (fun _ => True) (option_rel R) (step α d) (step β d).
    Proof.
      intros Hαβ m _ a b Hab a' Ha'.
      revert b Hab.
      induction Ha'; intros; inversion Hab; clear Hab; subst.
      - eapply Hαβ in H as (b' & Hb' & Hab'); eauto.
        edestruct silent_successor_bisim as (b'' & Hb'' & Hab''); eauto.
        eexists; split; econstructor; eauto.
      - eapply forever_silent_bisim in H; eauto.
        exists None. split; constructor; eauto.
    Qed.
  End BISIM.

  Lemma option_rel_flip {A B} (R : rel A B) a b :
    option_rel R a b <->
    option_rel (flip R) b a.
  Proof.
    split; destruct 1; constructor; eauto.
  Qed.

  Lemma step_bisim {M A B} R (α : lts (option M) A) (β : lts (option M) B) d :
    LTS.bisim R α β ->
    LTS.bisim (option_rel R) (step α d) (step β d).
  Proof.
    intros Hαβ m a b Hab. split.
    - eapply step_bisim_sim; eauto.
    - intros. edestruct (step_bisim_sim (flip R) β α) as (? & ? & ?); eauto.
      + apply LTS.bisim_flip; eauto.
      + constructor.
      + apply option_rel_flip; eauto.
      + apply option_rel_flip in H1; eauto.
  Qed.

  (** ** Operator on trees *)

  Definition tree {M} p (div : M) (τ : gametree (option M)) : gametree M :=
    Gametree.c
      (LTS.sup p (step Gametree.d div))
      (initial Gametree.d τ).
 
End Bigstep.

Notation bigstep := Bigstep.tree.