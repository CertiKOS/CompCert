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


(** * Flat composition *)

Module FComp.
  Import RTS.

  (** ** Definition *)

  (** Given a RTS, we can create a new RTS that maintains the states
    of two threads within this RTS. At any time, only one of the
    threads will be running and we will store a suspended continuation
    for the inactive thread. *)

  Inductive state {G A} :=
    | running (a : A) (k : input G -> option A)
    | conflict.

  Arguments state : clear implicits.

  (** Two continuations for the underlying can be combined into a
    continuation for the two-threaded RTS in the following way. *)

  Definition liftk {G A} (k1 k2 : input G -> option A) (q : input G) :=
    match k1 q, k2 q with
      | None, None => None
      | Some a1, None => Some (running a1 k2)
      | None, Some a2 => Some (running a2 k1)
      | Some _, Some _ => Some conflict
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
        Monotonic running (R ++> (- ==> option_rel R) ++> state_rel R)
    | conflict_rel :
        Monotonic conflict (state_rel R).

  Global Existing Instance running_rel.
  Global Existing Instance conflict_rel.
  Global Instance running_rel_params : Params (@running) 2.

  Global Instance liftk_sim :
    Monotonic
      (@liftk)
      (forallr -, forallr R,
        (- ==> option_rel R) ++>
        (- ==> option_rel R) ++>
        (- ==> option_rel (state_rel R))).
  Proof.
    unfold liftk. rauto.
  Qed.

  Global Instance liftb_sim :
    Monotonic
      (@liftb)
      (forallr -, forallr R,
        behavior_le R ++>
        (- ==> option_rel R) ++>
        behavior_le (state_rel R)).
  Proof.
    unfold liftb. rauto.
  Qed.

  Global Instance step_sim {G A B} R :
    Monotonic step (sim R ++> sim (@state_rel G A B R)).
  Proof.
    intros α β Hαβ sa sb Hs ra Hra.
    destruct Hra as [a ka ra Hra].
    inversion Hs as [xa b Hab xka kb Hk | ]; clear Hs; subst.
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
          (fun q => option_map inl (modsem_entry α q))
          (fun q => option_map inr (modsem_entry β q));
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
      apply liftk_sim; repeat rstep; auto.
  Qed.
End FComp.


(** * Resolution operator *)

Module Res.
  Import RTS.

  (** ** Definition *)

  Definition res_behavior {G A} sw (r : behavior G A) : behavior G A :=
    match r with
      | interacts mo k =>
        match sw mo with
          | Some mi =>
            match k mi with
              | Some a' => internal a'
              | None => r
            end
          | None => r
        end
      | _ => r
    end.

  Inductive res {G A} sw (α : rts G A) : rts G A :=
    res_intro a r :
      α a r ->
      res sw α a (res_behavior sw r).

  (** ** Monotonicity *)

  Global Instance res_sim :
    Monotonic (@res) (forallr -, forallr R, - ==> sim R ++> sim R).
  Proof.
    intros G A B R sw α β Hαβ a b Hab ra Hra.
    destruct Hra as [a' ra Hra].
    edestruct Hαβ as (rb & Hrb & Hr); eauto.
    exists (res_behavior sw rb). split.
    - constructor; auto.
    - unfold res_behavior. rauto.
  Qed.

  (** ** Modules *)

  Definition sw li (mo : output (li -o li)) : option (input (li -o li)) :=
    match mo with
      | inr x => Some (inl x)
      | inl x => Some (inr x)
    end.

  Definition of {li} (α : modsem (li -o li)) : modsem (li -o li) :=
    {|
      modsem_lts := res (sw li) α;
      modsem_entry := modsem_entry α;
    |}.

  Global Instance of_sim :
    Monotonic (@of) (forallr -, modref ++> modref).
  Proof.
    intros li α β [R Hαβ He].
    esplit; simpl; eauto. rauto.
  Qed.

  (** ** Commutation with embedding *)

  Inductive plus {G A} (α : rts G A) : rts G A :=
    | plus_one a r : α a r -> plus α a r
    | plus_step a a' r : α a (internal a') -> plus α a' r -> plus α a r.

  Inductive res_emb_comm_match {li} (L: semantics (li -o li)) :
    rel (Behavior.state (A := Smallstep.state L))
        (Behavior.state (A := Res.state L)) :=
    | res_emb_comm_resumed k :
        res_emb_comm_match L
          (Behavior.resumed (A := Smallstep.state L) k)
          (Behavior.resumed (Res.liftr L k))
    | res_emb_comm_running s :
        res_emb_comm_match L
          (Behavior.running s)
          (Behavior.running (Res.running L s))
    | res_emb_comm_switching k :
        res_emb_comm_match L
          (Behavior.resumed k)
          (Behavior.running (Res.resumed L k)).

  Lemma res_emb_comm_step {li} (L: semantics (li -o li)):
    sim (res_emb_comm_match L)
      (res (Res.sw li) (Behavior.step L))
      (Behavior.step (Res.semantics L)).
  Proof.
    intros s1 s2 Hs r1 Hr1.
    destruct Hr1; inversion Hs; clear Hs; subst.
    - inversion H; clear H; subst.
      + exists (internal (Behavior.running (Res.running L s))).
        repeat (constructor; auto).
      + exists goes_wrong.
        split; constructor.
        intros [_ [s Hs]]. eauto.
    - inversion H; clear H; subst.
      + exists (internal (Behavior.running (Res.running L s'))).
        repeat (constructor; auto).
      + rename r0 into r. simpl.
        destruct sw eqn:Hsw.
        * unfold Behavior.liftk at 1.
          destruct dom eqn:Hdom.
          -- exists (internal (Behavior.running (Res.resumed L (k i)))).
             split.
             ++ constructor. econstructor; eauto.
                unfold sw, ModuleSemantics.Res.sw in *.
                destruct r; inversion Hsw; clear Hsw; subst.
                ** rewrite Hdom. reflexivity.
                ** admit. (* sw should not handle returns this way *)
             ++ repeat constructor.
          -- eexists. split.
             ++ eapply (Behavior.step_interacts (Res.semantics L)).
                econstructor; eauto.
                unfold ModuleSemantics.Res.sw.
                destruct r; inversion Hsw; clear Hsw; subst; eauto.
                rewrite Hdom; eauto.
             ++ repeat rstep.
                unfold Behavior.liftk.
                unfold dom. simpl. repeat rstep.
                constructor.
                constructor.
        * eexists. split.
             ++ eapply (Behavior.step_interacts (Res.semantics L)).
                econstructor; eauto.
                unfold ModuleSemantics.Res.sw.
                destruct r; inversion Hsw; clear Hsw; subst; eauto.
             ++ repeat rstep.
                unfold Behavior.liftk.
                unfold dom. simpl. repeat rstep.
                constructor.
                constructor.
      + exists goes_wrong.
        split; constructor.
        * intros t s' Hs'.
          inversion Hs'; clear Hs'; subst; simpl in *.
          -- eapply H1; eauto.
          -- eapply H2; eauto.
        * intros r k H.
          inversion H; clear H; subst.
          eapply H2; eauto.
    - inversion H; clear H; subst.
      + exists (internal (Behavior.running (Res.running L s))).
        split; repeat (constructor; auto).
      + exists goes_wrong.
        split; repeat (constructor; auto).
        * intros t s' Hs'.
          inversion Hs'; clear Hs'; subst.
          eauto.
        * inversion 1.
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

  Lemma res_det {G A} sw (α : rts G A) :
    deterministic α ->
    deterministic (res sw α).
  Proof.
    intros Hα s x y Hx Hy.
    destruct Hx. inversion Hy.
    f_equal; eauto.
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
      inversion Ha12 as [xa1 r2 Hr2]; clear Ha12; subst.
      destruct Hr2 as [ | a1' r2 Hr2ext Hr2 Ha1']; [inversion H0 | ].
      induction Ha1' as [a1 | a1 a1' a1'' Ha1' Ha1''].
      + eapply reachable_step with a2; eauto.
        rewrite <- H0. constructor; auto.
      + eapply reachable_step with a1'; eauto.
        change (internal a1') with (res_behavior sw (internal a1')).
        constructor; auto.
  Qed.

  Lemma reachable_res {G A} sw (α : rts G A) a a' :
    reachable α a a' ->
    reachable (res sw α) a a'.
  Proof.
    induction 1 as [a | a1 a2 a3 Ha2 Ha3]; eauto.
    eapply reachable_step; eauto.
    change (internal a2) with (res_behavior sw (internal a2)).
    constructor; eauto.
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
    inversion Ha'; clear Ha'; subst.
    destruct r; try now inversion H.
    - simpl. auto.
    - eelim Hnoswitch.
      exists a'. rewrite <- H. constructor. eauto.
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
      constructor.
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
    inversion Ha' as [xa ra Hra]; clear Ha'; subst.
    destruct ra; try now inversion H1.
    - (* internal step of α *)
      inversion H1; clear H1; subst.
      eapply H; eauto.
      transitivity a; eauto.
    - (* external step of α turned internal step of [res α] *)
      eapply obs_internal; eauto.
      rewrite <- H1. constructor. eauto.
  Qed.

  Lemma res_behavior_external {G A} sw (r : behavior G A) :
    behavior_external (res_behavior sw r) ->
    behavior_external r.
  Proof.
    destruct r; inversion 1; constructor.
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
      inversion Hr; clear Hr; subst. constructor.
      eauto using obs_reachable, res_behavior_external.
  Qed.

  (** *** Main proof *)

  (** Putting these pieces together, *)

  Lemma obs_res_comm {G A} sw (α : rts G A) :
    deterministic α ->
    sim eq (obs (res sw α)) (obs (res sw (obs α))).
  Proof.
    intros Hα s _ [] r Hr.
    exists r. split; [ | rauto].
    destruct Hr.
    - edestruct @forever_internal_res_inv as [(s' & Hs' & Hd) | ]; eauto.
      eapply obs_res_obs_external; eauto.
      change diverges with (@res_behavior G A sw diverges). constructor.
      eauto.
    - apply obs_res_obs_external with a'; auto.
      inversion H0; clear H0; subst. constructor.
      eauto using res_behavior_external.
  Qed.
End Res.


(** * Horizontal composition *)

Module HComp.
  Definition of {li} (α β : modsem (li -o li)) :=
    Res.of (FComp.of α β).
End HComp.
