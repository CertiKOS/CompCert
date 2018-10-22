Require Import LogicalRelations.
Require Import List.
Require Import Classical.
Require Import Events.
Require Import Smallstep.
Require Import Behaviors.
Require Import RTS.
Require Import Trees.
Require Import GameSemantics.
Require Import ModuleSemantics.
Require Import Classical.
Require Import Axioms.
Require Import ModuleSemantics.
Require Import Sets.


(** * Flat composition *)

Module FComp.
  Import RTS.

  (** ** Definition *)

  (** Given a RTS, we can create a new RTS that maintains the states
    of two threads within this RTS. At any time, only one of the
    threads will be running and we will store a suspended continuation
    for the inactive thread. *)

  Inductive state {G A} :=
    | running (a : A) (k : cont G A)
    | conflict.

  Arguments state : clear implicits.

  Definition set_prod {A B} (sA : set A) (sB : set B) : set (A * B) :=
    fun '(a, b) => sA a /\ sB b.

  Global Instance set_prod_le :
    Monotonic (@set_prod) (forallr RA, forallr RB, set_le RA ++> set_le RB ++> set_le (RA * RB)).
  Proof.
    intros A1 A2 RA B1 B2 RB sA1 sA2 HsA sB1 sB2 HsB [a1 b1] [Ha1 Hb1].
    apply HsA in Ha1 as (a2 & Ha2 & Ha).
    apply HsB in Hb1 as (b2 & Hb2 & Hb).
    exists (a2, b2). split; [firstorder | rauto].
  Qed.

  (** Two continuations for the underlying can be combined into a
    continuation for the two-threaded RTS in the following way. *)

  Definition liftr {G A} k1 k2 r : resumption (state G A) :=
    match r with
      | (reject, reject) => reject
      | (resume a, reject) => resume (running a k2)
      | (reject, resume a) => resume (running a k1)
      | (resume _, resume _) => resume conflict
    end.

  Definition liftk {G A} (k1 k2 : cont G A) (q : input G) :=
    set_map (liftr k1 k2) (set_prod (k1 q) (k2 q)).

  (** When the running thread interacts with the environment, its
    continuation will be combined with the suspended continuation, so
    that the environment may resume either thread. *)

  Definition liftb {G A} (r : behavior G A) k :=
    match r with
      | internal a' => internal (running a' k)
      | interacts mo k' => interacts mo (liftk k' k)
      | diverges => diverges
      | goes_wrong => goes_wrong
    end.

  Inductive step {G A} (α : rts G A) : rts G (state G A) :=
    | step_intro a k r :
        α a r ->
        step α (running a k) (liftb r k)
    | step_conflict :
        step α conflict goes_wrong.

  (** ** Monotonicity *)

  Inductive state_rel {G A B} R : rel (state G A) (state G B) :=
    | running_rel :
        Monotonic running (R ++> cont_le R ++> state_rel R)
    | conflict_rel :
        Monotonic conflict (state_rel R).

  Global Existing Instance running_rel.
  Global Existing Instance conflict_rel.
  Global Instance running_rel_params : Params (@running) 2.

  Global Instance liftr_sim :
    Monotonic
      (@liftr)
      (forallr -, forallr R, cont_le R ++> cont_le R ++>
       resumption_rel R * resumption_rel R ++> resumption_rel (state_rel R)).
  Proof.
    unfold liftr. rauto.
  Qed.

  Global Instance liftk_sim :
    Monotonic
      (@liftk)
      (forallr -, forallr R, cont_le R ++> cont_le R ++> cont_le (state_rel R)).
  Proof.
    unfold liftk. rauto.
  Qed.

  Global Instance liftb_sim :
    Monotonic
      (@liftb)
      (forallr -, forallr R,
        behavior_le R ++>
        cont_le R ++>
        behavior_le (state_rel R)).
  Proof.
    unfold liftb. rauto.
  Qed.

  Global Instance step_sim {G A B} R :
    Monotonic step (sim R ++> sim (@state_rel G A B R)).
  Proof.
    intros α β Hαβ sa sb Hs ra Hra.
    destruct Hra as [a ka ra Hra | ].
    - inversion Hs as [xa b Hab xka kb Hk | ]; clear Hs; subst.
      edestruct Hαβ as (rb & Hrb & Hr); eauto.
      exists (liftb rb kb). split.
      + constructor; auto.
      + rauto.
    - inversion Hs; clear Hs; subst.
      exists goes_wrong. repeat constructor.
  Qed.

  Global Instance step_sim_params :
    Params (@step) 1.

  (** ** Modules *)

  (** When we wish to compute the flat composition of two modules, we
    can use the sum of the underlying RTS and combine the two initial
    continuations. *)

  Definition of {li} (α β : modsem li) : modsem li :=
    {|
      modsem_lts := step (modsem_lts α + modsem_lts β);
      modsem_entry :=
        liftk
          (cont_map inl (modsem_entry α))
          (cont_map inr (modsem_entry β));
    |}.

  Global Instance of_ref :
    Monotonic (@of) (forallr -, modref ++> modref ++> modref).
  Proof.
    intros li α1 β1 Hαβ1 α2 β2 Hαβ2.
    pose proof Hαβ1 as [R1 H1 He1].
    pose proof Hαβ2 as [R2 H2 He2].
    exists (state_rel (R1 + R2)); simpl.
    - apply step_sim.
      rauto.
    - intro q.
      apply liftk_sim; unfold cont_map; repeat rstep; auto.
  Qed.

  (** ** Commutation with embedding *)

  Definition state_l {G A B} a k : FComp.state G (A + B) :=
    FComp.running (inl a) (cont_map inr k).

  Definition state_r {G A B} b k : FComp.state G (A + B) :=
    FComp.running (inr b) (cont_map inl k).

  Inductive emb_match_states {li: language_interface} {A B} : rel _ _ :=
    | emb_match_l (s: A) (k: Smallstep.cont li B) :
        emb_match_states
          (Behavior.running (SFComp.state_l s k))
          (state_l (Behavior.running s) (Behavior.liftk k))
    | emb_match_r (s: B) (k: Smallstep.cont li A) :
        emb_match_states
          (Behavior.running (SFComp.state_r s k))
          (state_r (Behavior.running s) (Behavior.liftk k))
    | emb_match_wrong s :
        (exists k, s = state_l Behavior.wrong k) \/
        (exists k, s = state_r Behavior.wrong k) \/
        s = conflict ->
        emb_match_states Behavior.wrong s.

  Hint Constructors emb_match_states.
  Hint Constructors resumption_rel.

  Lemma lifts_ex {A} (S : set A) :
    exists s, Behavior.lifts S s.
  Proof.
    destruct (classic (ex S)) as [[s Hs] | Hns].
    - exists (Behavior.running s). constructor; auto.
    - exists (Behavior.wrong). constructor; auto.
  Qed.

  Lemma cont_emb_lr {li A B} (k1: Smallstep.cont li A) (k2: Smallstep.cont li B):
    (cont_le emb_match_states)
      (Behavior.liftk (SFComp.liftk k1 k2))
      (liftk
         (cont_map inl (Behavior.liftk k1))
         (cont_map inr (Behavior.liftk k2))).
  Proof.
    intros q.
    unfold liftk, Behavior.liftk at 1 4 5, SFComp.liftk, cont_map at 3 4.
    destruct k1 as [S1 | ], k2 as [S2 | ].
    - intros _ [_ [Hns | s Hs]]; try contradiction.
      destruct (lifts_ex S1) as [s1 Hs1].
      destruct (lifts_ex S2) as [s2 Hs2].
      eexists (liftr _ _ (resumption_map inl (resume s1),
                          resumption_map inr (resume s2))). split.
      + repeat constructor; auto.
      + simpl. auto.
    - intros _ [_ [Hns | _ [s Hs]]].
      + eexists (liftr _ _ (_, _)). split.
        * repeat constructor.
          intros [y Hy]. apply Hns. eexists. constructor. eauto.
        * constructor. constructor. left. eexists. reflexivity.
      + eexists (liftr _ _ (_, _)). split.
        * constructor; constructor; constructor; constructor.
          apply Behavior.lifts_resumes; eauto.
        * constructor. constructor.
    - intros _ [_ [Hns | _ [s Hs]]].
      + eexists (liftr _ _ (_, _)). split.
        * repeat constructor.
          intros [y Hy]. apply Hns. eexists. constructor. eauto.
        * constructor. constructor. right. left. eexists. reflexivity.
      + eexists (liftr _ _ (_, _)). split.
        * constructor; constructor; constructor; constructor.
          apply Behavior.lifts_resumes; eauto.
        * constructor. constructor.
    - intros _ [ ].
      eexists (liftr _ _ (_, _)). split.
      + repeat constructor.
      + constructor.
  Qed.

  Lemma cont_emb_rl {li A B} (k1: Smallstep.cont li A) (k2: Smallstep.cont li B):
    (cont_le emb_match_states)
      (Behavior.liftk (SFComp.liftk k1 k2))
      (liftk
         (cont_map inr (Behavior.liftk k2))
         (cont_map inl (Behavior.liftk k1))).
  Proof.
    intros q.
    unfold liftk, Behavior.liftk at 1 4 5, SFComp.liftk, cont_map at 3 4.
    destruct k1 as [S1 | ], k2 as [S2 | ].
    - intros _ [_ [Hns | s Hs]]; try contradiction.
      destruct (lifts_ex S1) as [s1 Hs1].
      destruct (lifts_ex S2) as [s2 Hs2].
      eexists (liftr _ _ (resumption_map inr (resume s2),
                          resumption_map inl (resume s1))). split.
      + repeat constructor; auto.
      + simpl. auto.
    - intros _ [_ [Hns | _ [s Hs]]].
      + eexists (liftr _ _ (_, _)). split.
        * repeat constructor.
          intros [y Hy]. apply Hns. eexists. constructor. eauto.
        * constructor. constructor. left. eexists. reflexivity.
      + eexists (liftr _ _ (_, _)). split.
        * constructor; constructor; constructor; constructor.
          apply Behavior.lifts_resumes; eauto.
        * constructor. constructor.
    - intros _ [_ [Hns | _ [s Hs]]].
      + eexists (liftr _ _ (_, _)). split.
        * repeat constructor.
          intros [y Hy]. apply Hns. eexists. constructor. eauto.
        * constructor. constructor. right. left. eexists. reflexivity.
      + eexists (liftr _ _ (_, _)). split.
        * constructor; constructor; constructor; constructor.
          apply Behavior.lifts_resumes; eauto.
        * constructor. constructor.
    - intros _ [ ].
      eexists (liftr _ _ (_, _)). split.
      + repeat constructor.
      + constructor.
  Qed.

  Lemma step_emb {li} ge (L1 L2: semantics li):
    RTS.sim emb_match_states
      (Behavior.step (SFComp.semantics ge L1 L2))
      (step (Behavior.step L1 + Behavior.step L2)).
  Proof.
    intros s1 s2 Hs s1' Hs1'.
    destruct Hs1'.
    - inversion Hs; clear Hs; subst.
      exists goes_wrong; split; [ | constructor].
      destruct H as [[k Hs2] | [[k Hs2] | Hs2]]; subst.
      + eapply (step_intro _ _ (cont_map inr k) goes_wrong).
        eapply (sum_inl _ _ _ goes_wrong).
        constructor.
      + eapply (step_intro _ _ (cont_map inl k) goes_wrong).
        eapply (sum_inr _ _ _ goes_wrong).
        constructor.
      + constructor.
    - inversion H; clear H; subst;
      inversion Hs; clear Hs; subst.
      + exists (liftb (behavior_map inl (internal (Behavior.running s'0)))
                      (cont_map inr (Behavior.liftk k))).
        repeat (constructor; eauto).
      + exists (liftb (behavior_map inr (internal (Behavior.running s'0)))
                      (cont_map inl (Behavior.liftk k))).
        repeat (constructor; eauto).
    - destruct H; inversion Hs; clear Hs; subst.
      + exists (liftb (behavior_map inl (interacts r (Behavior.liftk k)))
                      (cont_map inr (Behavior.liftk k'))).
        repeat (constructor; eauto).
        apply cont_emb_lr.
      + exists (liftb (behavior_map inr (interacts r (Behavior.liftk k)))
                      (cont_map inl (Behavior.liftk k'))).
        repeat (constructor; eauto).
        apply cont_emb_rl.
    - inversion Hs; clear Hs; subst.
      + eexists (liftb (behavior_map inl (internal Behavior.wrong)) _).
        split.
        * constructor. apply sum_inl. constructor.
          -- intros t s' Hs'. eapply H. econstructor. eassumption.
          -- intros r k' Hrk'. eapply H0. econstructor. eassumption.
        * repeat econstructor; fail.
      + eexists (liftb (behavior_map inr (internal Behavior.wrong)) _).
        split.
        * constructor. apply sum_inr. constructor.
          -- intros t s' Hs'. eapply H. econstructor. eassumption.
          -- intros r k' Hrk'. eapply H0. econstructor. eassumption.
        * repeat econstructor; fail.
  Qed.

  Lemma emb_cont_lr {li A B} (k1: Smallstep.cont li A) (k2: Smallstep.cont li B):
    (cont_le (flip emb_match_states))
      (liftk
         (cont_map inl (Behavior.liftk k1))
         (cont_map inr (Behavior.liftk k2)))
      (Behavior.liftk
         (SFComp.liftk k1 k2)).
  Proof.
    unfold liftk, cont_map at 3 4, Behavior.liftk at 3 4 5, SFComp.liftk.
    intros q _ [[_ _] [[r1 Hr1] [r2 Hr2]]].
    destruct k1 as [S1 | ], k2 as [S2 | ]; clear q.
    - destruct Hr1 as [s1 Hr1], Hr2 as [s2 Hs2].
      exists (resume Behavior.wrong). split.
      + repeat constructor. firstorder.
      + do 2 constructor. auto.
    - destruct Hr1 as [_ [Hns | s Hs]], Hr2.
      + exists (resume Behavior.wrong). split.
        * repeat constructor. intros [_ [s Hs]]. apply Hns; eauto.
        * repeat (econstructor; eauto); fail.
      + exists (resume (Behavior.running (SFComp.state_l s k2))).
        repeat (constructor; auto).
        apply (set_map_intro (fun s => SFComp.state_l s k2) S1 s); auto.
    - destruct Hr2 as [_ [Hns | s Hs]], Hr1.
      + exists (resume Behavior.wrong). split.
        * repeat constructor. intros [_ [s Hs]]. apply Hns; eauto.
        * repeat (econstructor; eauto); fail.
      + exists (resume (Behavior.running (SFComp.state_r s k1))).
        repeat (constructor; auto).
        apply (set_map_intro (fun s => SFComp.state_r s k1) S2 s); auto.
    - destruct Hr1, Hr2. simpl. repeat econstructor.
  Qed.

  Lemma emb_cont_rl {li A B} (k1: Smallstep.cont li A) (k2: Smallstep.cont li B):
    (cont_le (flip emb_match_states))
      (liftk
         (cont_map inr (Behavior.liftk k2))
         (cont_map inl (Behavior.liftk k1)))
      (Behavior.liftk
         (SFComp.liftk k1 k2)).
  Proof.
    unfold liftk, cont_map at 3 4, Behavior.liftk at 3 4 5, SFComp.liftk.
    intros q _ [[_ _] [[r1 Hr1] [r2 Hr2]]].
    destruct k1 as [S1 | ], k2 as [S2 | ]; clear q.
    - destruct Hr1 as [s1 Hr1], Hr2 as [s2 Hs2].
      exists (resume Behavior.wrong). split.
      + repeat constructor. firstorder.
      + do 2 constructor. auto.
    - destruct Hr1, Hr2 as [_ [Hns | s Hs]].
      + exists (resume Behavior.wrong). split.
        * repeat constructor. intros [_ [s Hs]]. apply Hns; eauto.
        * repeat (econstructor; eauto); fail.
      + exists (resume (Behavior.running (SFComp.state_l s k2))).
        repeat (constructor; auto).
        apply (set_map_intro (fun s => SFComp.state_l s k2) S1 s); auto.
    - destruct Hr1 as [_ [Hns | s Hs]], Hr2.
      + exists (resume Behavior.wrong). split.
        * repeat constructor. intros [_ [s Hs]]. apply Hns; eauto.
        * repeat (econstructor; eauto); fail.
      + exists (resume (Behavior.running (SFComp.state_r s k1))).
        repeat (constructor; auto).
        apply (set_map_intro (fun s => SFComp.state_r s k1) S2 s); auto.
    - destruct Hr1, Hr2. simpl. repeat econstructor.
  Qed.

  Lemma emb_step {li} ge (L1 L2: semantics li):
    RTS.sim (flip emb_match_states)
      (step (Behavior.step L1 + Behavior.step L2))
      (Behavior.step (SFComp.semantics ge L1 L2)).
  Proof.
    intros s1 s2 Hs s1' Hs1'.
    destruct Hs1' as [s1 k1 r Hr1 | ].
    {
    destruct Hr1 as [s1 r Hr1 | s1 r Hr1].
    - inversion Hs as [s k | | ]; clear Hs; subst.
      + inversion Hr1; clear Hr1; subst.
        * exists (internal (Behavior.running (SFComp.state_l s' k))).
          split; repeat (constructor; auto).
        * exists (interacts r0 (Behavior.liftk (SFComp.liftk k0 k))).
          split; repeat (constructor; auto).
          apply (emb_cont_lr k0 k).
        * exists (internal Behavior.wrong).
          split; [ constructor | repeat econstructor; fail ].
          -- intros ? ? H. inversion H. eapply H0; eauto.
          -- intros ? ? H. inversion H. eapply H1; eauto.
      + exists goes_wrong.
        split; repeat (constructor; auto).
    - inversion Hs as [s k | | ]; clear Hs; subst.
      + inversion Hr1; clear Hr1; subst.
        * exists (internal (Behavior.running (SFComp.state_r s' k))).
          split; repeat (constructor; auto).
        * exists (interacts r0 (Behavior.liftk (SFComp.liftk k k0))).
          split; repeat (constructor; auto).
          apply (emb_cont_rl k k0).
        * exists (internal Behavior.wrong).
          split; [ constructor | repeat (econstructor; eauto); fail ].
          -- intros ? ? H. inversion H. eapply H0; eauto.
          -- intros ? ? H. inversion H. eapply H1; eauto.
      + exists goes_wrong.
        split; repeat (constructor; auto).
    }
    {
      inversion Hs; clear Hs; subst.
      destruct H as [[? ?] | [[? ?] | ?]]; inversion H.
      repeat (econstructor; eauto); fail.
    }
  Qed.

  (** ** Commutation with [obs] *)

  Lemma step_forever_internal_inv {G A} (α : rts G A) a k :
    forever_internal (step α) (running a k) ->
    forever_internal α a.
  Proof.
    revert a. cofix IH. intros.
    destruct H as [a' Ha' H].
    inversion Ha'; clear Ha'; subst.
    destruct r; inversion H3; subst.
    exists a'0; auto.
  Qed.

  Lemma step_reachable_inv {G A} (α : rts G A) a k s' :
    reachable (step α) (running a k) s' ->
    exists a', s' = running a' k /\ reachable α a a'.
  Proof.
    remember (running a k) as s.
    intros H. revert a k Heqs.
    induction H as [s | s1 s2 s3 Hs12 Hs23].
    - eauto.
    - intros. subst.
      inversion Hs12; clear Hs12; subst.
      destruct r; inversion H2; clear H2; subst.
      edestruct IHHs23 as (ai & H23 & Hai); eauto.
  Qed.

  Lemma obs_step {G A} (α : rts G A) :
    sim eq (step (obs α)) (obs (step α)).
  Proof.
    intros s _ [] s' Hs'.
    destruct Hs'.
    exists (liftb r k). split; [ | rauto].
    destruct H.
    - simpl.
      constructor.
      revert a k H. cofix IH. intros.
      destruct H as [a' H].
      exists (running a' k); eauto.
      change (internal _) with (liftb (internal a') k).
      constructor; auto.
    - induction H1.
      + econstructor; eauto.
        * destruct r; try now inversion H; simpl; auto.
        * constructor; auto.
      + eapply obs_internal; eauto.
      change (internal _) with (liftb (internal a') k).
      constructor; auto.
    - exists goes_wrong. split.
      + eapply obs_external; eauto.
        constructor.
      + reflexivity.
  Qed.

  Lemma step_obs {G A} (α : rts G A) :
    sim eq (obs (step α)) (step (obs α)).
  Proof.
    intros s _ [] s' Hs'.
    destruct Hs'.
    - exists diverges. split; [ | rauto].
      destruct s as [a k | ].
      + change diverges with (liftb diverges k).
        constructor; eauto using step_forever_internal_inv.
      + destruct H. inversion H.
    - destruct s as [a k | ].
      + apply step_reachable_inv in H1 as (? & ? & ?). subst.
        exists r. split; [ | rauto].
        inversion H0; clear H0; subst.
        econstructor.
        destruct r0; try now inversion H; eauto.
      + exists goes_wrong. split; constructor.
  Qed.

  (** ** Full commutation theorem *)

  Lemma of_emb {li} ge (L1 L2: semantics li) :
    modref
      (Behavior.of (SFComp.semantics ge L1 L2))
      (FComp.of (Behavior.of L1) (Behavior.of L2)).
  Proof.
    eexists; simpl.
    - eapply RTS.sim_compose. { eapply RTS.obs_sim, step_emb. }
      eapply RTS.sim_compose. { eapply step_obs. }
                              { eapply step_sim, RTS.sum_obs. }
    - eapply cont_le_compose. { eapply cont_emb_lr. }
      eapply cont_le_compose. { rauto. }
                              { eapply (liftk_sim li); rauto. }
  Qed.

  Lemma emb_of {li} ge (L1 L2: semantics li) :
    modref
      (FComp.of (Behavior.of L1) (Behavior.of L2))
      (Behavior.of (SFComp.semantics ge L1 L2)).
  Proof.
    eexists; simpl.
    - eapply RTS.sim_compose. { eapply step_sim, RTS.obs_sum. }
      eapply RTS.sim_compose. { eapply obs_step. }
                              { eapply RTS.obs_sim, (emb_step ge L1 L2). }
    - eapply cont_le_compose. { rstep; rstep; reflexivity. }
      eapply cont_le_compose. { rauto. }
                              { eapply emb_cont_lr. }
  Qed.
End FComp.


(** * Resolution operator *)

Module Res.
  Import RTS.

  (** ** Definition *)

  Definition xcall {G A} mo k (r : resumption A) : behavior G A :=
    match r with
      | resume a => internal a
      | reject => interacts mo k
    end.

  Definition res_behavior {G A} sw (r : behavior G A) : behavior G A -> Prop :=
    match r with
      | interacts mo k => set_map (xcall mo k) (k (sw mo))
      | _ => singl r
    end.

  Definition res {G A} sw (α : rts G A) : rts G A :=
    fun a => set_bind (res_behavior sw) (α a).

  (** ** Monotonicity *)

  Lemma set_behavior_le_top {G A B} (R : rel A B) (x : behavior G A -> Prop) :
    set_le (behavior_le R) x (singl goes_wrong).
  Proof.
    intros ? _. eexists; split; constructor.
  Qed.

  Global Instance xcall_sim :
    Monotonic
      (@xcall)
      (forallr -, forallr R,
         - ==> cont_le R ++> resumption_rel R ++> behavior_le R).
  Proof.
    unfold xcall. rauto.
  Qed.

  Global Instance res_sim :
    Monotonic (@res) (forallr -, forallr R, - ==> sim R ++> sim R).
  Proof.
    unfold res, res_behavior, sim. repeat rstep.
    destruct H1; eauto using set_behavior_le_top; rauto.
  Qed.

  (** ** Modules *)

  Definition sw li (mo : output (li -o li)) : input (li -o li) :=
    match mo with
      | inr x => inl x
      | inl x => inr x
    end.

  Definition of {li} (α : modsem (li -o li)) : modsem (li -o li) :=
    {|
      modsem_lts := obs (res (sw li) α);
      modsem_entry := modsem_entry α;
    |}.

  Global Instance of_sim :
    Monotonic (@of) (forallr -, modref ++> modref).
  Proof.
    intros li α β [R Hαβ He].
    esplit; simpl; eauto. rauto.
  Qed.

  (** ** Commutation with embedding *)

  Lemma emb_res {li} (L: semantics (li -o li)):
    determinate L ->
    sim eq
      (res (Res.sw li) (Behavior.step L))
      (Behavior.step (SRes.semantics SHComp.sw L)).
  Proof.
    intros HL s _ [] _ [r r' Hr Hr'].
    exists r'. split; [ | reflexivity].
    destruct Hr; simpl in Hr'.
    - (* wrong *)
      destruct Hr'.
      change (state L) with (state (SRes.semantics (sw li) L)). constructor.
    - (* internal step *)
      destruct Hr'.
      change (state L) with (state (SRes.semantics (sw li) L)). constructor.
      constructor; eauto.
    - (* final state *)
      destruct Hr' as [r' Hr']. red in Hr'. unfold xcall.
      destruct k as [S | ] eqn:HS.
      + (* switching *)
        destruct Hr' as [r' Hr'].
        destruct Hr' as [Hnostep | s' Hs'].
        * change (state L) with (state (SRes.semantics (sw li) L)).
          constructor.
          -- intros t s' Hs'. simpl in *.
             destruct Hs'.
             ++ eapply sd_final_nostep; eauto.
             ++ edestruct (sd_final_determ HL s r k) as (?&?&_); eauto; subst.
                destruct H1 as (S' & HS' & Hs'). assert (S=S') by congruence.
                subst. elim Hnostep; eauto.
          -- intros r' k' H'. simpl in *. destruct H'.
             edestruct (sd_final_determ HL s r k) as (?&?&_); eauto; congruence.
        * change (state L) with (state (SRes.semantics (sw li) L)).
          constructor.
          eapply SRes.step_switch; eauto. red. eauto.
      + (* regular *)
        destruct Hr'.
        change (state L) with (state (SRes.semantics (sw li) L)).
        constructor. constructor; eauto.
    - (* going wrong *)
      destruct Hr'.
      change (state L) with (state (SRes.semantics (sw li) L)).
      constructor.
      + intros t s' Hs'.
        destruct Hs'.
        * eapply H; eauto.
        * eapply H0; eauto.
      + intros r k Hk.
        destruct Hk.
        eapply H0; eauto.
  Qed.

  Lemma res_emb {li} (L: semantics (li -o li)):
    sim eq
      (Behavior.step (SRes.semantics SHComp.sw L))
      (res (Res.sw li) (Behavior.step L)).
  Proof.
    intros s _ [] s' Hs'.
    destruct Hs'; (eexists; split; [ | reflexivity]).
    - exists goes_wrong; repeat constructor.
      eapply (Behavior.step_goes_initially_wrong L).
    - inversion H; clear H; subst.
      + (* internal step *)
        econstructor.
        * eapply (Behavior.step_internal L); eauto.
        * constructor.
      + (* switching *)
        econstructor.
        * eapply (Behavior.step_interacts L); eauto.
        * destruct H1 as (S & HS & Hs').
          apply set_map_intro with (a := resume (Behavior.running s')).
          unfold Behavior.liftk.
          replace (k _) with (Some S) by eauto.
          repeat (constructor; auto).
    - destruct H.
      econstructor.
      + eapply (Behavior.step_interacts L); eauto.
      + simpl.
        change (interacts _ _) with (xcall r (Behavior.liftk k) reject).
        constructor.
        unfold Behavior.liftk.
        replace (k _) with (@None (state L -> Prop)) by eauto. simpl.
        constructor.
    - destruct (classic (exists r k, final_state L s r k /\
                         exists S, k (sw li r) = Some S /\ ~ ex S)) as [Hsw|Hsw].
      + (* switches, then goes initially wrong *)
        destruct Hsw as (r & k & Hk & S & HS & HnS).
        exists (interacts r (Behavior.liftk k)).
        * eapply (Behavior.step_interacts L); eauto.
        * simpl.
          eapply (set_map_intro (xcall _ _)) with (a := resume Behavior.wrong).
          unfold Behavior.liftk. rewrite HS.
          repeat (econstructor; eauto); fail.
      + (* no step or final state in original semantics *)
        exists (internal Behavior.wrong); [ | constructor].
        eapply (Behavior.step_goes_wrong L).
        * intros t s' Hs'. eapply H.
          constructor; eauto.
        * intros r k Hrk.
          eapply not_ex_all_not in Hsw.
          eapply not_ex_all_not in Hsw.
          eapply not_and_or in Hsw as [Hnfs | Hsw]; eauto.
          destruct (k (sw li r)) as [S | ] eqn:HS.
          -- (* switches -> would be a step *)
            eapply not_ex_all_not in Hsw.
            eapply not_and_or in Hsw as [Hnfs | Hsw]; eauto.
            eapply NNPP in Hsw as (s' & Hs').
            eapply H.
            eapply SRes.step_switch; eauto.
            exists S; eauto.
          -- (* no switch -> would be a final state *)
            eapply H0; eauto. econstructor; eauto.
  Qed.

  (** ** Commutation with [obs] *)

  (** We prove that [res] semi-commutes with [obs], in the sense
    that applying [obs] after horizontal composition only should yield
    the same result as applying it both before and after horizontal
    composition: in particular, for any step of [obs (res sw α)],
    there is a corresponding step of [obs (res sw (obs α))]. This is
    used as a lemma in proofs of syntactic composition. The proof is
    non-trivial both in the diverging and terminating cases. *)

  (** *** Divergence *)

  (** First, if [res sw α] diverges, we need to distinguish two subcases.
    On one hand, the divergence may result from an infinite number of
    terminating segments which are stiched together by internal
    switching, resulting in an infinite sequence of internal
    actions. On the other hand, it may be that [α] itself diverges,
    with [res] simply passing along these internal actions; even in
    this case, this may be preceded by a finite number of internal
    switches.

    In order to simplify the case analysis we introduce the following
    positive formulation of divergence. *)

  Lemma forever_internal_nbr {G A} (α : rts G A) a :
    nonbranching α ->
    forever_internal α a <->
    (forall a', reachable α a a' -> exists a'', α a' (internal a'')).
  Proof.
    intros Hα. split.
    - intros Ha a' Ha'.
      induction Ha' as [a | a a' a'' Ha' Ha'' IHa''].
      + destruct Ha. eauto.
      + eapply fi_inv_internal in Ha; eauto.
    - revert a. cofix IH. intros a H.
      destruct (H a) as (a' & Ha'); [ eauto .. | ].
      econstructor; eauto.
  Qed.

  (** The formulation above is only valid when [α] is nonbranching,
    otherwise [Σ n . τ^n] may be mistaken for [τ^ω]. To apply it to
    [obs (res sw α)] we use the following lemmas. *)

  Lemma res_behavior_det {G A} sw (r r' : behavior G A) :
    res_behavior sw r r' ->
    deterministic_behavior r ->
    deterministic_behavior r'.
  Proof.
    intros Hr' Hr.
    unfold res_behavior, xcall in Hr'.
    destruct r; try (destruct Hr'; simpl in *; auto).
    destruct a; simpl; auto.
  Qed.

  Lemma res_det {G A} sw (α : rts G A) :
    deterministic α ->
    deterministic (res sw α).
  Proof.
    intros Hα s x y Hx Hy.
    destruct Hx as [x x' Hx Hx'], Hy as [y y' Hy Hy'].
    assert (H: psat deterministic_behavior x y) by eauto.
    destruct H as [H]. clear - Hx' Hy' H.
    unfold res_behavior, xcall in *.
    destruct x; try (destruct Hx', Hy'; simpl in *; auto).
    simpl in H. pose proof (H (sw m)).
    assert (a = a0) as [] by eauto. constructor. simpl. auto.
    destruct a; simpl; auto.
  Qed.

  (** In addition, we will use the following properties relating
    reachability in various flavors of the transition system. *)

  Lemma reachable_obs_res_inv {G A} sw (α : rts G A) a a' :
    reachable (res sw (obs α)) a a' ->
    reachable (res sw α) a a'.
  Proof.
    induction 1 as [a | a1 a2 a3 Ha12 Ha23].
    - constructor.
    - clear Ha23.
      inversion Ha12 as [r1 x Hr2]; clear Ha12; subst.
      destruct Hr2 as [ | a1' r2 Hr2ext Hr2 Ha1']; [inversion H | ].
      induction Ha1' as [a1 | a1 a1' a1'' Ha1' Ha1''].
      + eapply reachable_step with a2; eauto.
        econstructor; eauto.
      + eapply reachable_step with a1'; eauto.
        econstructor; eauto. constructor.
  Qed.

  Lemma reachable_res {G A} sw (α : rts G A) a a' :
    reachable α a a' ->
    reachable (res sw α) a a'.
  Proof.
    induction 1 as [a | a1 a2 a3 Ha2 Ha3]; eauto.
    eapply reachable_step; eauto.
    econstructor; eauto. constructor.
  Qed.

  (** Another important key property is is the following: the
    behaviors of [obs α] will all be external, so that an internal
    transition in [res sw (obs α)] can only come from internal
    switching. If there is no such internal switching, and [res sw α]
    takes an internal step, then it must have come from an internal
    step of [α]. *)

  Lemma res_noswitch_internal_inv {G A} sw (α : rts G A) a a' :
    ~ (exists x, res sw (obs α) a (internal x)) ->
    res sw α a (internal a') ->
    α a (internal a').
  Proof.
    intros Hnoswitch Ha'.
    inversion Ha' as [r x]; clear Ha'; subst.
    destruct r; try (inversion H0; congruence).
    eelim Hnoswitch.
    exists a'. econstructor; eauto.
  Qed.

  (** This is used to show the following key property, which spells
    out the case analysis for the divergence of [res sw α]. *)

  Lemma forever_internal_res_inv {G A} sw (α : rts G A) a :
    deterministic α ->
    forever_internal (res sw α) a ->
    (exists a', reachable (res sw α) a a' /\ forever_internal α a') \/
    forever_internal (res sw (obs α)) a.
  Proof.
    intros Hα Ha1.
    destruct (classic (forever_internal (res sw (obs α)) a)) as [? | Ha2]; auto.
    left.
    rewrite forever_internal_nbr in Ha1; eauto using res_det.
    rewrite forever_internal_nbr in Ha2; eauto using res_det, obs_deterministic.
    apply not_all_ex_not in Ha2 as [a' Ha2].
    apply not_all_ex_not in Ha2 as [Ha' Ha2].
    exists a'. split; auto using reachable_obs_res_inv.
    apply forever_internal_nbr; eauto.
    intros a'' Ha''.
    specialize (Ha1 a'') as (a''' & Ha''').
    - transitivity a'; eauto using reachable_res, reachable_obs_res_inv.
    - exists a'''.
      eapply res_noswitch_internal_inv; eauto.
      intros (a'''' & Ha'''').
      apply Ha2. exists a''''.
      inversion Ha''''; clear Ha''''; subst.
      econstructor; eauto.
      eapply obs_reachable; eauto.
  Qed.

  (** *** External behavior *)

  (** If [res sw α] eventually reaches an externally observable step,
    this will potentially happen after an interleaving of internal
    steps of [α], and external steps of [α] that have been turned into
    internal steps of [res sw α]. We need to decompose those, because
    on the [obs (res sw (obs α))] side, internal steps of [α] will
    have been absorbed by the innermost [obs], whereas internal steps
    introduced by [res] will be absorbed by the outermost [obs].

    This makes the induction on the internal segment in [res sw α]
    somewhat tricky, because proving that [obs (res sw (obs α))]
    is invariant under the addition of an additional initial internal
    step of [res sw α] is complicated. However, the following,
    equivalent formulation works very well in that context. *)

  Definition obs_res_obs {G A} sw (α : rts G A) r a :=
    forall x,
      reachable α x a ->
      obs (res sw (obs α)) x r.

  Lemma obs_res_obs_internal {G A} sw (α : rts G A) a a' r:
    res sw α a (internal a') ->
    obs_res_obs sw α r a' ->
    obs_res_obs sw α r a.
  Proof.
    intros Ha' H x Hx.
    inversion Ha' as [ra xa Hra Hra']; clear Ha'; subst.
    destruct ra; try (inversion Hra'; congruence).
    - (* internal step of α *)
      inversion Hra'; clear Hra'; subst.
      eapply H; eauto.
      transitivity a; eauto.
    - (* external step of α turned internal step of [res α] *)
      eapply obs_internal; eauto.
      econstructor; eauto.
  Qed.

  Lemma res_behavior_external {G A} sw (r r' : behavior G A) :
    res_behavior sw r r' ->
    behavior_external r' ->
    behavior_external r.
  Proof.
    destruct r; try inversion 1; eauto.
  Qed.

  Lemma obs_res_obs_external {G A} sw (α : rts G A) a a' r :
    reachable (res sw α) a a' ->
    res sw (obs α) a' r ->
    behavior_external r ->
    obs (res sw (obs α)) a r.
  Proof.
    intros Ha' Hr Hrext.
    cut (obs_res_obs sw α r a).
    - unfold obs_res_obs. eauto.
    - induction Ha'; eauto using obs_res_obs_internal.
      intros x Hx.
      eapply obs_external with x; eauto.
      inversion Hr; clear Hr; subst. econstructor; eauto.
      eauto using obs_reachable, res_behavior_external.
  Qed.

  (** *** Main proof *)

  (** Putting these pieces together, *)

  Lemma res_obs {G A} sw (α : rts G A) :
    deterministic α ->
    sim eq (obs (res sw α)) (obs (res sw (obs α))).
  Proof.
    intros Hα s _ [] r Hr.
    exists r. split; [ | rauto].
    destruct Hr.
    - edestruct @forever_internal_res_inv as [(s' & Hs' & Hd) | ]; eauto.
      eapply obs_res_obs_external; eauto.
      econstructor; eauto. constructor.
    - apply obs_res_obs_external with a'; auto.
      inversion H0; clear H0; subst. econstructor; eauto.
      eauto using res_behavior_external.
  Qed.

  (** *** Other direction *)

  Lemma forever_internal_res_obs_inv {G A} sw (α : rts G A) a :
    deterministic α ->
    forever_internal (res sw (obs α)) a ->
    forever_internal (res sw α) a.
  Proof.
    intros Hα.
    revert a. cofix IH. intros a Ha.
    destruct Ha as [a' Ha' H].
    inversion Ha' as [r ? Hr]; clear Ha'; subst.
    destruct Hr as [ | ai r Hrext Hr Hai].
    - inversion H0.
    - destruct Hai as [a | a1 a2 a3 Ha12 Ha23].
      + exists a'; auto. clear IH.
        econstructor; eauto.
      + admit.
  Admitted.

  Lemma obs_res {G A} sw (α : rts G A) :
    deterministic α ->
    sim eq (obs (res sw (obs α))) (obs (res sw α)).
  Proof.
    intros Hα s _ [] r Hr.
    exists r. split; [ | rauto].
    destruct Hr.
    - eapply obs_diverges.
      eapply forever_internal_res_obs_inv; eauto.
    - induction H1 as [a | a1 a2 a3 Ha12 Ha23].
      + destruct H0.
        destruct H0.
        * unfold res_behavior in H1. simpl in H1. inversion H1; clear H1; subst.
          eapply obs_diverges.
          revert a H0. cofix IH. intros.
          destruct H0 as [a' H0].
          econstructor; eauto.
          econstructor; eauto.
          unfold res_behavior. simpl. constructor.
        * unfold res_behavior in H1.
          eapply obs_external with a'; eauto.
          -- econstructor; eauto.
          -- induction H3; eauto.
             eapply reachable_step with a'; eauto.
             econstructor; eauto. constructor.
      + eapply obs_reachable; eauto.
        eapply reachable_obs_res_inv; eauto.
  Qed.

  (** ** Full commutation theorem *)

  Lemma of_emb {li} (L: semantics (li -o li)) :
    Smallstep.determinate L ->
    modref
      (Behavior.of (SRes.semantics (sw li) L))
      (Res.of (Behavior.of L)).
  Proof.
    econstructor; simpl.
    - eapply RTS.sim_compose.
      + rstep. apply res_emb.
      + apply res_obs. apply (Behavior.deterministic L); auto.
    - intro q.
      eapply cont_le_compose; reflexivity.
  Qed.
End Res.


(** * Horizontal composition *)

Module HComp.
  Definition of {li} (α β : modsem (li -o li)) :=
    Res.of (FComp.of α β).

  (** ** Commutation with embedding *)

  Lemma of_emb {li} ge (L1 L2 : Smallstep.semantics (li -o li)) :
    Smallstep.determinate L1 ->
    Smallstep.determinate L2 ->
    modref
      (Behavior.of (SHComp.semantics ge L1 L2))
      (HComp.of (Behavior.of L1) (Behavior.of L2)).
  Proof.
    intros HL1 HL2.
    unfold HComp.of, SHComp.semantics.
    etransitivity.
    - eapply Res.of_emb.
      admit. (* flat composition preserves determinism *)
    - rstep. eapply FComp.of_emb.
  Admitted.
End HComp.
