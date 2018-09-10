Require Import LogicalRelations.
Require Import Axioms.
Require Import Classical.

Axiom prop_ext : ClassicalFacts.prop_extensionality.


(** * Receptive transition systems *)

(** We do metatheory in a setting ...
  The whole thing in this file is parametrized by a set of events [E]
  and a set of moves [M]. Events can only ever serve as outputs,
  whereas moves can be used both as outputs and inputs. *)

Section RTS.
  Context (E M : Type).

  Inductive output :=
    | event (e : E)
    | move (m : M).

  (** ** Definition *)

  (** The possible behaviors of each state in a RTS are as follows. *)

  Inductive behavior {A} :=
    | internal (a' : A)
    | interacts (m : output) (k : M -> A)
    | diverges
    | goes_wrong.

  Arguments behavior : clear implicits.

  Inductive behavior_le {A B} (R : rel A B) : rel (behavior A) (behavior B) :=
    | internal_le :
        Monotonic internal (R ++> behavior_le R)
    | interacts_le :
        Monotonic interacts (- ==> (- ==> R) ++> behavior_le R)
    | diverges_le :
        Monotonic diverges (behavior_le R)
    | goes_wrong_le ra :
        Related ra goes_wrong (behavior_le R).

  Global Existing Instance internal_le.
  Global Existing Instance interacts_le.
  Global Existing Instance diverges_le.
  Global Existing Instance goes_wrong_le.
  Global Instance internal_le_params : Params (@internal) 1.
  Global Instance interacts_le_params : Params (@interacts) 2.

  Global Instance behavior_le_refl {A} (R: relation A) :
    Reflexive R ->
    Reflexive (behavior_le R).
  Proof.
    intros H [a' | m k | | ]; rauto.
  Qed.

  Definition behavior_map {A B} (f : A -> B) (r : behavior A) : behavior B :=
    match r with
      | internal a' => internal (f a')
      | interacts m k => interacts m (fun mi => f (k mi))
      | diverges => diverges
      | goes_wrong => goes_wrong
    end.

  Global Instance behavior_map_le :
    Monotonic
      (@behavior_map)
      (forallr RA, forallr RB, (RA++>RB) ++> behavior_le RA ++> behavior_le RB).
  Proof.
    unfold behavior_map. rauto.
  Qed.

  (** A receptive transition system simply assigns a set of possible
    behaviors to each state. *)

  Definition rts A :=
    rel A (behavior A).

  Arguments rts : clear implicits.
  Bind Scope rts_scope with rts.

  (** ** Simulations *)

  (** A simulation between two RTS assets that each possible behavior
    in the first has a correponding behavior in the second. In
    particular, internal transitions must correspond one-to-one. *)

  Definition sim {A B} (R : rel A B) : rel (rts A) (rts B) :=
    (R ++> set_le (behavior_le R)).

  Hint Extern 1 (RElim (sim _) _ _ _ _) =>
    eapply arrow_relim : typeclass_instances.

  Hint Extern 1 (Transport _ _ _ (?α _ _) _) =>
    match type of α with rts _ => set_le_transport α end
    : typeclass_instances.

  (** ** Externally observable behaviors *)

  (** Given a RTS, we can define a reduced version that only contains
    observable behaviors: internal transitions are hidden, except in
    the case of silent divergence. *)

  CoInductive forever_internal {A} (α : rts A) (a : A) : Prop :=
    | forever_internal_intro a' :
        α a (internal a') ->
        forever_internal α a' ->
        forever_internal α a.

  Inductive reachable {A} (α : rts A) : relation A :=
    | reachable_refl a :
        reachable α a a
    | reachable_step a a' a'' :
        α a (internal a') ->
        reachable α a' a'' ->
        reachable α a a''.

  Inductive behavior_external {A} : behavior A -> Prop :=
    | interacts_external m k :
        behavior_external (interacts m k)
    | diverges_external :
        behavior_external diverges
    | goes_wrong_external :
        behavior_external goes_wrong.

  Inductive obs {A} (α : rts A) a : behavior A -> Prop :=
    | obs_diverges :
        forever_internal α a ->
        obs α a diverges
    | obs_external a' r :
        behavior_external r ->
        α a' r ->
        reachable α a a' ->
        obs α a r.

  Hint Resolve reachable_refl.
  Hint Immediate reachable_step.
  Hint Constructors behavior_external.
  Hint Constructors obs.

  Global Instance reachable_trans {A} (α : rts A) :
    Transitive (reachable α).
  Proof.
    intros a a' a'' Ha' Ha''.
    induction Ha'; auto.
    econstructor; eauto.
  Qed.

  (** Observations are compatible with simulations. *)

  Lemma forever_internal_sim {A B} (R : rel A B) α β a b :
    sim R α β ->
    R a b ->
    forever_internal α a ->
    forever_internal β b \/ obs β b goes_wrong.
  Proof.
    intros Hαβ Hab Ha.
    destruct (classic (obs β b goes_wrong)); eauto. left.
    revert a b Hab H Ha. cofix IH. intros.
    destruct Ha as [a' Ha' Hda'].
    edestruct Hαβ as (rb & Hb' & Hrab); eauto.
    inversion Hrab; clear Hrab; subst.
    - econstructor; eauto.
      eapply IH; eauto.
      inversion 1; eauto.
    - destruct H.
      econstructor; eauto.
  Qed.

  Lemma reachable_sim {A B} (R : rel A B) α β a b a' :
    sim R α β ->
    R a b ->
    reachable α a a' ->
    exists b',
      reachable β b b' /\
      (R a' b' \/ β b' goes_wrong).
  Proof.
    intros Hαβ Hab Ha'. revert b Hab.
    induction Ha' as [a | a a' a'' Ha' Ha'' IHa'']; eauto.
    intros b Hab.
    edestruct Hαβ as (rb' & Hb' & Hab'); eauto.
    inversion Hab'; clear Hab'; subst; eauto.
    edestruct IHa'' as (b'' & Hb'' & Hab''); eauto.
  Qed.

  Global Instance behavior_external_sim :
    Monotonic (@behavior_external) (forallr R, behavior_le R ++> impl).
  Proof.
    intros A B R a b Hab Ha.
    destruct Ha; inversion Hab; eauto.
  Qed.

  Hint Extern 10 (Transport _ _ _ (behavior_external _) _) =>
    eapply impl_transport : typeclass_instances.

  Global Instance obs_sim :
    Monotonic (@obs) (forallr R, sim R ++> sim R).
  Proof.
    intros A B R α β Hαβ a b Hab ra Hra.
    destruct Hra as [Ha | a' ra Hext Hra Ha' ].
    - edestruct @forever_internal_sim as [Hb | Hb]; eauto.
      + exists diverges. split; eauto. rauto.
      + exists goes_wrong. split; eauto. rauto.
    - edestruct @reachable_sim as (b' & Hb' & [Hab' | Hgw]); eauto.
      + edestruct Hαβ as (rb & Hrb & Hr); eauto.
        transport Hext. eauto.
      + exists goes_wrong. split; eauto. rauto.
  Qed.

  (** Additional properties. *)

  Lemma obs_behavior_external {A} (α : rts A) a r :
    obs α a r ->
    behavior_external r.
  Proof.
    destruct 1; eauto.
  Qed.

  Lemma obs_internal_inv {A} (α : rts A) a a' :
    ~ obs α a (internal a').
  Proof.
    inversion 1.
    inversion H0.
  Qed.

  Lemma reachable_obs {A} (α : rts A) a a' :
    reachable (obs α) a a' ->
    reachable α a a'.
  Proof.
    intros Ha'.
    destruct Ha'; eauto.
    eelim obs_internal_inv; eauto.
  Qed.

  Lemma forever_internal_reachable {A} (α : rts A) a a' :
    reachable α a a' ->
    forever_internal α a' ->
    forever_internal α a.
  Proof.
    induction 1; auto.
    econstructor; eauto.
  Qed.

  Lemma obs_reachable {A} (α : rts A) a a' r :
    reachable α a a' ->
    obs α a' r ->
    obs α a r.
  Proof.
    intros Ha' H.
    destruct H.
    - eauto using forever_internal_reachable.
    - eapply obs_external; eauto.
      etransitivity; eauto.
  Qed.

  (** ** [obs] is idempotent *)

  Lemma obs_idempotent {A} (α : rts A) :
    obs (obs α) = obs α.
  Proof.
    apply functional_extensionality; intros a.
    apply functional_extensionality; intros r.
    apply prop_ext.
    split.
    - intros [Ha | a' ra' Hext Hra' Ha' ].
      + destruct Ha. eelim obs_internal_inv; eauto.
      + eapply reachable_obs in Ha'.
        destruct Hra'.
        * eauto using forever_internal_reachable, reachable_obs.
        * econstructor; eauto.
          etransitivity; eauto.
    - intros [Ha | a' ra' Hra' Hext Ha' ]; eauto.
  Qed.

  (** ** Operators *)

  (** *** Sum *)

  Section SUM.
    Context {A B} (α : rts A) (β : rts B).

    Inductive sum : rts (A + B) :=
      | sum_inl a ra : α a ra -> sum (inl a) (behavior_map inl ra)
      | sum_inr b rb : β b rb -> sum (inr b) (behavior_map inr rb).
  End SUM.

  Hint Constructors sum.
  Infix "+" := sum : rts_scope.

  Global Instance sum_sim :
    Monotonic
      (@sum)
      (forallr RA, forallr RB, sim RA ++> sim RB ++> sim (RA + RB)).
  Proof.
    intros A1 A2 RA B1 B2 RB α1 α2 Hα β1 β2 Hβ s1 s2 Hs s1' Hs1'.
    destruct Hs1'; inversion Hs; transport H; (eexists; split; [eauto | rauto]).
  Qed.


  (** * Modules *)

  Record modsem :=
    {
      modsem_dom : M -> bool;
      modsem_state : Type;
      modsem_lts :> rts modsem_state;
      modsem_entry : M -> modsem_state;
    }.

  Record modref (α β : modsem) : Prop :=
    {
      modref_dom :
        forall q, modsem_dom α q = modsem_dom β q;
      modref_state :
        rel (modsem_state α) (modsem_state β);
      modref_sim :
        sim modref_state (modsem_lts α) (modsem_lts β);
      modref_init :
        forall q, modref_state (modsem_entry α q) (modsem_entry β q);
    }.

  Global Instance modsem_dom_ref :
    Monotonic (@modsem_dom) (modref ++> - ==> eq).
  Proof.
    intros ? ? []. firstorder.
  Qed.


  (** * Horizontal composition *)

  (** ** Transition system *)

  Section HCOMP_RTS.
    Context {A} (dom : M -> bool) (α : rts A).

    Inductive hc_state : Type :=
      | hc_r (a : A) (k : M -> A)
      | hc_z.

    Definition hc_xcall (mo : output) : option M :=
      match mo with
        | move m => if dom m then Some m else None
        | _ => None
      end.

    Definition hc_behavior (r : behavior A) (k : M -> A) :=
      match r with
        | internal a =>
          internal (hc_r a k)
        | interacts mo k' =>
          match hc_xcall mo with
            | Some m => internal (hc_r (k m) k')
            | None => interacts mo (fun mi => hc_r (k' mi) k)
          end
        | diverges =>
          diverges
        | goes_wrong =>
          goes_wrong
      end.

    Inductive hc : rts hc_state :=
      | hc_intro a k r :
          α a r ->
          hc (hc_r a k) (hc_behavior r k).
  End HCOMP_RTS.

  Arguments hc_state : clear implicits.

  (** ** Monotonicity *)

  Section HCOMP_REL.
    Context {A B} (R : rel A B).

    Inductive hc_rel : rel (hc_state A) (hc_state B) :=
      | hc_r_rel :
          Monotonic hc_r (R ++> (- ==> R) ++> hc_rel)
      | hc_z_rel :
          Monotonic hc_z hc_rel.

    Global Existing Instance hc_r_rel.
    Global Existing Instance hc_z_rel.
    Global Instance hc_r_rel_params : Params (@hc_r) 2.

    Global Instance hc_behavior_rel dom :
      Monotonic
        (hc_behavior dom)
        (behavior_le R ++> (- ==> R) ++> behavior_le hc_rel).
    Proof.
      unfold hc_behavior. rauto.
    Qed.

    Global Instance hc_behavior_rel_params :
      Params (@hc_behavior) 2.

    Global Instance hc_sim :
      Monotonic hc (- ==> sim R ++> sim hc_rel).
    Proof.
      intros dom α β Hαβ sa sb Hs ka Hka.
      destruct Hka as [a ka ra].
      inversion Hs as [xa b Hab xka kb Hk | ]; clear Hs; subst.
      edestruct Hαβ as (rb & Hrb & Hr); eauto.
      exists (hc_behavior dom rb kb). split; [ | rauto].
      constructor; auto.
    Qed.

    Global Instance hc_sim_params :
      Params (@hc) 2.
  End HCOMP_REL.

  (** ** Properties *)

  Lemma hc_behavior_external {A} dom (r : behavior A) (k : M -> A) :
    behavior_external (hc_behavior dom r k) ->
    behavior_external r.
  Proof.
    destruct r; inversion 1; constructor.
  Qed.

  Lemma hc_reachable {A} dom (α : rts A) a a' k :
    reachable α a a' ->
    reachable (hc dom α) (hc_r a k) (hc_r a' k).
  Proof.
    induction 1; eauto.
    econstructor; eauto.
    change (internal _) with (hc_behavior dom (internal a') k).
    constructor; eauto.
  Qed.

  (** ** Modules *)

  Definition hcomp_dom (α1 α2 : modsem) (q : M) : bool :=
    (modsem_dom α1 q || modsem_dom α2 q)%bool.

  Definition hcomp (α1 α2 : modsem) : modsem :=
    let α : bool -> modsem := fun i => if i then α1 else α2 in
    {|
      modsem_dom := hcomp_dom α1 α2;
      modsem_lts := hc (hcomp_dom α1 α2) (α1 + α2);
      modsem_entry q :=
        match modsem_dom α1 q, modsem_dom α2 q with
          | true, true => hc_z
          | true, false =>
              hc_r (inl (modsem_entry α1 q)) (fun m => inr (modsem_entry α2 m))
          | false, true =>
              hc_r (inr (modsem_entry α2 q)) (fun m => inl (modsem_entry α1 m))
          | false, false => hc_z
        end;
    |}.

  Global Instance hcomp_dom_ref :
    Monotonic (@hcomp_dom) (modref ++> modref ++> - ==> eq).
  Proof.
    unfold hcomp_dom. repeat rstep. f_equal; rauto.
  Qed.

  Global Instance hcomp_ref :
    Monotonic (@hcomp) (modref ++> modref ++> modref).
  Proof.
    intros α1 β1 Hαβ1 α2 β2 Hαβ2.
    pose proof Hαβ1 as [Hd1 R1 H1 He1].
    pose proof Hαβ2 as [Hd2 R2 H2 He2].
    exists (hc_rel (R1 + R2)); simpl.
    - intros q. rauto.
    - change (sim (hc_rel (R1 + R2)) (hc (hcomp_dom α1 α2) (α1 + α2))
                                     (hc (hcomp_dom β1 β2) (β1 + β2))).
      replace (hcomp_dom β1 β2) with (hcomp_dom α1 α2).
      + eapply hc_sim. rauto.
      + apply functional_extensionality. intros i. rauto.
    - intros q.
      repeat rstep; simpl; eauto.
  Qed.

  (** ** [hcomp] and [obs] *)

  (** We prove that [hcomp] semi-commutes with [obs], in the sense
    that applying [obs] after horizontal composition only should yield
    the same result as applying it both before and after horizontal
    composition. *)

  CoInductive forever_switching {A} dom (α : rts A) : hc_state A -> Prop :=
    | forever_switching_intro a a' ra k s' :
        reachable α a a' ->
        α a' ra ->
        behavior_external ra ->
        hc_behavior dom ra k = internal s' ->
        forever_switching dom α s' ->
        forever_switching dom α (hc_r a k).

  Lemma forever_switching_internal {A} dom (α : rts A) s s' :
    hc dom α s (internal s') ->
    forever_switching dom α s' ->
    forever_switching dom α s.
  Proof.
    intros Hs' Hd.
    inversion Hs' as [a0 k0 ra0 Hra0]; clear Hs'.
    destruct ra0; inversion H0; clear H0.
    - destruct Hd.
      inversion H2; clear H2; subst.
      eapply (forever_switching_intro dom α a0 a'0); eauto.
    - destruct hc_xcall as [mx|] eqn:Hmx; inversion H2; clear H2; subst.
      eapply (forever_switching_intro dom α a0 a0); eauto.
      simpl. rewrite Hmx. reflexivity.
  Qed.

  Inductive hc_settles {A} dom (α : rts A) : rts (hc_state A) :=
    | hc_settles_external a a' ra k r :
        α a' ra ->
        reachable α a a' ->
        hc_behavior dom ra k = r ->
        behavior_external r ->
        hc_settles dom α (hc_r a k) r
    | hc_settles_diverges a k :
        forever_internal α a ->
        hc_settles dom α (hc_r a k) diverges
    | hc_settles_switch a a' ra k s' r :
        α a' ra ->
        reachable α a a' ->
        behavior_external ra ->
        hc_behavior dom ra k = internal s' ->
        hc_settles dom α s' r ->
        hc_settles dom α (hc_r a k) r.

  Hint Constructors hc_settles.

  Lemma hc_settles_internal {A} dom (α : rts A) s s' r :
    hc dom α s (internal s') ->
    hc_settles dom α s' r ->
    hc_settles dom α s r.
  Proof.
    intros Hs' Hr.
    inversion Hs' as [a k ra Hra]; clear Hs'; subst.
    destruct ra; inversion H0; clear H0.
    - destruct Hr; inversion H1; clear H1; subst.
      + eapply (hc_settles_external dom α a a'0); eauto.
      + eapply (hc_settles_diverges dom α a); eauto.
        econstructor; eauto.
      + eapply (hc_settles_switch dom α a a'0); eauto.
    - destruct hc_xcall as [mx|] eqn:Hmx; inversion H1; clear H1; subst.
      eapply (hc_settles_switch dom α a a (interacts m k0)); eauto.
      simpl. rewrite Hmx. reflexivity.
  Qed.

  Inductive obs_hc {A} dom (α : rts A) : rts (hc_state A) :=
    | obs_hc_settles s r :
        hc_settles dom α s r ->
        obs_hc dom α s r
    | obs_hc_forever_switching s :
        forever_switching dom α s ->
        obs_hc dom α s diverges.

  Lemma forever_hc {A} dom (α : rts A) s :
    forever_internal (hc dom α) s ->
    (exists a k, reachable (hc dom α) s (hc_r a k) /\ forever_internal α a) \/
    forever_switching dom α s.
  Proof.
  Admitted.

  Lemma obs_hc_obs_hc {A} dom (α : rts A) s r :
    obs (hc dom α) s r ->
    obs_hc dom α s r.
  Proof.
    intros Hr.
    destruct Hr as [Hs | s' r Hrext Hr Hs'].
    - apply forever_hc in Hs as [(a & k & Hs' & Ha) | Hs].
      + eapply obs_hc_settles.
        remember (hc_r a k) as s' in Hs'.
        induction Hs'; eauto using hc_settles_internal.
        subst. constructor; auto.
      + eapply obs_hc_forever_switching; eauto.
    - eapply obs_hc_settles; eauto.
      induction Hs'; eauto using hc_settles_internal.
      inversion Hr; clear Hr; subst.
      destruct r0; simpl in *; (try now inversion Hrext); eauto.
  Qed.

  Lemma obs_hc_obs_hc_obs {A} dom (α : rts A) s r :
    obs_hc dom α s r ->
    obs (hc dom (obs α)) s r.
  Proof.
    intro.
    destruct H.
    - induction H.
      + apply obs_external with (hc_r a k); eauto.
        subst. constructor.
        eapply obs_external with a'; eauto.
        eapply hc_behavior_external; eauto.
      + apply obs_external with (hc_r a k); eauto.
        change diverges with (hc_behavior dom diverges k).
        constructor. auto.
      + apply obs_reachable with s'; auto.
        econstructor; eauto.
        rewrite <- H2. constructor. eauto.
    - eapply obs_diverges.
      revert s H. cofix IH. intros.
      destruct H. econstructor; eauto. Guarded.
      rewrite <- H2. constructor. eauto.
  Qed.

  Lemma obs_hc_obs_hc_obs_sim {A} dom (α : rts A) :
    sim eq (obs (hc dom α)) (obs (hc dom (obs α))).
  Proof.
    intros s _ [] r Hr.
    exists r. split; [ | rauto].
    apply obs_hc_obs_hc_obs.
    apply obs_hc_obs_hc. auto.
  Qed.
End RTS.
