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


Instance arrow_pointwise_rel_refl {A B} (R : relation B) :
  Reflexive R -> @Reflexive (A -> B) (- ==> R).
Proof.
  firstorder.
Qed.

Definition cont_map {Q A B} (f : A -> B) k :=
  (fun q : Q => option_map (set_map f) (k q)).

(*Definition cont_le {Q A B} (R : rel A B) : rel (Q -> _) (Q -> _) :=*)
Notation cont_le R := (- ==> option_rel (set_le R))%rel.

Lemma cont_le_compose {Q A B C} (R : rel A B) (S : rel B C) (k1 k2 k3 : Q -> _) :
  cont_le R k1 k2 ->
  cont_le S k2 k3 ->
  cont_le (rel_compose R S) k1 k3.
Proof.
  intros H12 H23 q. specialize (H12 q). specialize (H23 q).
  destruct H12; inversion H23; clear H23; subst; constructor.
  intros a Ha.
  specialize (H a Ha) as (b & Hb & Hab).
  specialize (H2 b Hb) as (c & Hc & Hbc).
  unfold rel_compose; eauto.
Qed.

Global Instance cont_map_le :
  Monotonic
    (@cont_map)
    (forallr -, forallr R, forallr S, (R ++> S) ++> cont_le R ++> cont_le S).
Proof.
  unfold cont_map.
  rauto.
Qed.


(** * Flat composition *)

Module FComp.
  Import RTS.

  (** ** Definition *)

  (** Given a RTS, we can create a new RTS that maintains the states
    of two threads within this RTS. At any time, only one of the
    threads will be running and we will store a suspended continuation
    for the inactive thread. *)

  Inductive state {G A} :=
    | running (a : A) (k : input G -> option (A -> Prop)).

  Arguments state : clear implicits.

  (** Two continuations for the underlying can be combined into a
    continuation for the two-threaded RTS in the following way. *)

  Definition liftk {G A} (k1 k2 : input G -> option (A -> Prop)) (q : input G) :=
    match k1 q, k2 q with
      | None, None => None
      | Some a1, None => Some (set_map (fun s => running s k2) a1)
      | None, Some a2 => Some (set_map (fun s => running s k1) a2)
      | Some _, Some _ => Some (fun _ => False)
    end.

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
    step_intro a k r :
      α a r ->
      step α (running a k) (liftb r k).

  (** ** Monotonicity *)

  Inductive state_rel {G A B} R : rel (state G A) (state G B) :=
    | running_rel :
        Monotonic running (R ++> (- ==> option_rel (set_le R)) ++> state_rel R).

  Global Existing Instance running_rel.
  Global Instance running_rel_params : Params (@running) 2.

  Global Instance liftk_sim :
    Monotonic
      (@liftk)
      (forallr -, forallr R, cont_le R ++> cont_le R ++> cont_le (state_rel R)).
  Proof.
    unfold liftk. repeat rstep. inversion 1.
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
    destruct Hra as [a ka ra Hra].
    inversion Hs as [xa b Hab xka kb Hk]; clear Hs; subst.
    edestruct Hαβ as (rb & Hrb & Hr); eauto.
    exists (liftb rb kb). split.
    - constructor; auto.
    - rauto.
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
    | emb_match_l (s: A) (k: cont li B) :
        emb_match_states
          (state_l (G:=li) (Behavior.running s) (Behavior.liftk k))
          (Behavior.running (SFComp.state_l s k))
    | emb_match_r (s: B) (k: cont li A) :
        emb_match_states
          (state_r (G:=li) (Behavior.running s) (Behavior.liftk k))
          (Behavior.running (SFComp.state_r s k))
    | emb_match_wrong s :
        emb_match_states s Behavior.wrong.

  Lemma emb_cont_lr {li A B} (k1: cont li A) (k2: cont li B) :
    (cont_le emb_match_states)
      (liftk (G:=li)
         (cont_map inl (Behavior.liftk k1))
         (cont_map inr (Behavior.liftk k2)))
      (Behavior.liftk
         (SFComp.liftk k1 k2)).
  Proof.
    intros q. cbv.
    destruct k1, k2; constructor; try contradiction.
    - intros _ [_ [_ [Hns | s Hs]]].
      + exists Behavior.wrong.
        repeat (constructor; auto).
        intros [_ [s Hs]]. apply Hns; eauto.
      + exists (Behavior.running (SFComp.state_l s k2)).
        repeat (constructor; auto).
        apply (set_map_intro (fun s => SFComp.state_l s k2) P s); auto.
    - intros _ [_ [_ [Hns | s Hs]]].
      + exists Behavior.wrong.
        repeat (constructor; auto).
        intros [_ [s Hs]]. apply Hns; eauto.
      + exists (Behavior.running (SFComp.state_r s k1)).
        repeat (constructor; auto).
        apply (set_map_intro (fun s => SFComp.state_r s k1) P s); auto.
  Qed.

  Lemma emb_cont_rl {li A B} (k1: cont li A) (k2: cont li B) :
    (cont_le emb_match_states)
      (liftk (G:=li)
         (cont_map inr (Behavior.liftk k2))
         (cont_map inl (Behavior.liftk k1)))
      (Behavior.liftk
         (SFComp.liftk k1 k2)).
  Proof.
    intros q. cbv.
    destruct k1, k2; constructor; try contradiction.
    - intros _ [_ [_ [Hns | s Hs]]].
      + exists Behavior.wrong.
        repeat (constructor; auto).
        intros [_ [s Hs]]. apply Hns; eauto.
      + exists (Behavior.running (SFComp.state_l s k2)).
        repeat (constructor; auto).
        apply (set_map_intro (fun s => SFComp.state_l s k2) P s); auto.
    - intros _ [_ [_ [Hns | s Hs]]].
      + exists Behavior.wrong.
        repeat (constructor; auto).
        intros [_ [s Hs]]. apply Hns; eauto.
      + exists (Behavior.running (SFComp.state_r s k1)).
        repeat (constructor; auto).
        apply (set_map_intro (fun s => SFComp.state_r s k1) P s); auto.
  Qed.

  Lemma emb_step {li} ge (L1 L2: semantics li):
    RTS.sim emb_match_states
      (step (Behavior.step L1 + Behavior.step L2))
      (Behavior.step (SFComp.semantics ge L1 L2)).
  Proof.
    intros s1 s2 Hs s1' Hs1'.
    destruct Hs1' as [s1 k1 r Hr1].
    destruct Hr1 as [s1 r Hr1 | s1 r Hr1].
    - inversion Hs as [s k | | ]; clear Hs; subst.
      + inversion Hr1; clear Hr1; subst.
        * exists (internal (Behavior.running (SFComp.state_l s' k))).
          split; repeat (constructor; auto).
        * exists (interacts (G:=li) r0 (Behavior.liftk (SFComp.liftk k0 k))).
          split; repeat (constructor; auto).
          apply (emb_cont_lr k0 k).
        * exists (internal Behavior.wrong).
          split; repeat (constructor; auto).
          -- intros ? ? H. inversion H. eapply H0; eauto.
          -- intros ? ? H. inversion H. eapply H1; eauto.
      + exists goes_wrong.
        split; repeat (constructor; auto).
    - inversion Hs as [s k | | ]; clear Hs; subst.
      + inversion Hr1; clear Hr1; subst.
        * exists (internal (Behavior.running (SFComp.state_r s' k))).
          split; repeat (constructor; auto).
        * exists (interacts (G:=li) r0 (Behavior.liftk (SFComp.liftk k k0))).
          split; repeat (constructor; auto).
          apply (emb_cont_rl k k0).
        * exists (internal Behavior.wrong).
          split; repeat (constructor; auto).
          -- intros ? ? H. inversion H. eapply H0; eauto.
          -- intros ? ? H. inversion H. eapply H1; eauto.
      + exists goes_wrong.
        split; repeat (constructor; auto).
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
  Qed.

  Lemma step_obs {G A} (α : rts G A) :
    sim eq (obs (step α)) (step (obs α)).
  Proof.
    intros s _ [] s' Hs'.
    destruct Hs'.
    - exists diverges. split; [ | rauto].
      destruct s as [a k].
      change diverges with (liftb diverges k).
      constructor; eauto using step_forever_internal_inv.
    - destruct s as [a k].
      apply step_reachable_inv in H1 as (? & ? & ?). subst.
      exists r. split; [ | rauto].
      inversion H0; clear H0; subst.
      econstructor.
      destruct r0; try now inversion H; eauto.
  Qed.

  (** ** Full commutation theorem *)

  Lemma emb_of {li} ge (L1 L2: semantics li) :
    modref
      (FComp.of (Behavior.of L1) (Behavior.of L2))
      (Behavior.of (SFComp.semantics ge L1 L2)).
  Proof.
    eexists; simpl.
    - eapply RTS.sim_compose. { eapply step_sim, RTS.obs_sum. }
      eapply RTS.sim_compose. { eapply obs_step. }
                              { eapply RTS.obs_sim, (emb_step ge L1 L2). }
    - eapply cont_le_compose. { rauto. }
      eapply cont_le_compose. { rauto. }
                              { rstep. eapply emb_cont_lr. }
  Qed.
End FComp.


(** * Resolution operator *)

Module Res.
  Import RTS.

  (** ** Definition *)

  Definition xcall {G A} sw (r : behavior G A): option (A -> Prop) :=
    match r with
      | interacts mo k => k (sw mo)
      | _ => None
    end.

  Definition res_behavior {G A} sw (r : behavior G A) : behavior G A -> Prop :=
    match xcall sw r with
      | Some s => set_map internal s
      | None => singl r
    end.

  Definition res {G A} sw (α : rts G A) : rts G A :=
    fun a => set_bind (res_behavior sw) (α a).

  (** ** Monotonicity *)

  Lemma set_behavior_le_top {G A B} (R : rel A B) x :
    set_le (behavior_le (G:=G) R) x (singl goes_wrong).
  Proof.
    intros ? _. eexists; split; constructor.
  Qed.

  Global Instance res_sim :
    Monotonic (@res) (forallr -, forallr R, - ==> sim R ++> sim R).
  Proof.
    unfold res, res_behavior, xcall, sim. repeat rstep.
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
      unfold res_behavior in Hr'.
      destruct xcall eqn:Hxc.
      + (* switching *)
        destruct Hr' as [r' Hr'].
        simpl in Hxc. unfold Behavior.liftk in Hxc.
        destruct k eqn:Hkr; simpl in Hxc; inversion Hxc; clear Hxc; subst.
        destruct Hr' as [Hnostep | s' Hs'].
        * change (state L) with (state (SRes.semantics (sw li) L)).
          constructor.
          -- intros t s' Hs'. simpl in *.
             destruct Hs'.
             ++ eapply sd_final_nostep; eauto.
             ++ edestruct (sd_final_determ HL s r k) as [Hr Hk]; eauto; subst.
                admit. (* cont_determinate too weak *)
          -- intros r' k' H'. simpl in *.
             destruct H'. admit. (* cont_determinate too weak *)
        * change (state L) with (state (SRes.semantics (sw li) L)).
          constructor.
          eapply SRes.step_switch; eauto. red. eauto.
      + (* regular *)
        destruct Hr'.
        simpl in Hxc. unfold Behavior.liftk in Hxc.
        destruct k eqn:Hk; simpl in Hxc; try discriminate.
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
  Admitted.

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
    destruct k; try (destruct Hr'; simpl in *; auto).
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
    destruct k; try (destruct Hx', Hy'; simpl in *; auto).
    assert (a = a0) as [] by eauto. constructor. simpl. auto.
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
    modref
      (Behavior.of (SRes.semantics (sw li) L))
      (Res.of (Behavior.of L)).
  Proof.
    econstructor; simpl.
    - eapply RTS.sim_compose. { rstep. 
  Admitted.
End Res.


(** * Horizontal composition *)

Module HComp.
  Definition of {li} (α β : modsem (li -o li)) :=
    Res.of (FComp.of α β).

  (** ** Commutation with embedding *)

  Lemma of_emb {li} ge (L1 L2 : Smallstep.semantics (li -o li)) :
    modref
      (Behavior.of (SHComp.semantics ge L1 L2))
      (HComp.of (Behavior.of L1) (Behavior.of L2)).
  Proof.
  Admitted.
End HComp.
