Require Import LogicalRelations.
Require Import Axioms.
Require Import Classical.

Axiom prop_ext : ClassicalFacts.prop_extensionality.


(** * Games *)

Record game :=
  {
    input : Type;
    output : Type;
  }.

Inductive move {G} :=
  | input_move (m : input G) :> move
  | output_move (m : output G) :> move.

Arguments move : clear implicits.


(** * Receptive transition systems *)

(** We do metatheory in a setting ...
  The whole thing in this file is parametrized by a set of events [E]
  and a set of moves [M]. Events can only ever serve as outputs,
  whereas moves can be used both as outputs and inputs. *)

Module RTS.

  (** ** Definition *)

  (** The possible behaviors of each state in a RTS are as follows. *)

  Inductive behavior {G A} :=
    | internal (a' : A)
    | interacts (m : output G) (k : input G -> A)
    | diverges
    | goes_wrong.

  Arguments behavior : clear implicits.

  Inductive behavior_le {G A B} R : rel (behavior G A) (behavior G B) :=
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

  Global Instance behavior_le_refl {G A} (R: relation A) :
    Reflexive R ->
    Reflexive (behavior_le (G:=G) R).
  Proof.
    intros H [a' | m k | | ]; constructor; eauto. intro. reflexivity.
  Qed.

  Definition behavior_map {G A B} (f : A -> B) (r : behavior G A) :=
    match r with
      | internal a' => internal (f a')
      | interacts m k => interacts m (fun mi => f (k mi))
      | diverges => diverges
      | goes_wrong => goes_wrong
    end.

  Global Instance behavior_map_le :
    Monotonic
      (@behavior_map)
      (forallr -, forallr RA, forallr RB,
        (RA ++> RB) ++> behavior_le RA ++> behavior_le RB).
  Proof.
    unfold behavior_map. rauto.
  Qed.

  (** A receptive transition system simply assigns a set of possible
    behaviors to each state. *)

  Definition rts G A :=
    rel A (behavior G A).

  Bind Scope rts_scope with rts.
  Delimit Scope rts_scope with rts.

  (** ** Simulations *)

  (** A simulation between two RTS assets that each possible behavior
    in the first has a correponding behavior in the second. In
    particular, internal transitions must correspond one-to-one. *)

  Definition sim {G A B} (R : rel A B) : rel (rts G A) (rts G B) :=
    (R ++> set_le (behavior_le R)).

  Hint Extern 1 (RElim (sim _) _ _ _ _) =>
    eapply arrow_relim : typeclass_instances.

  Hint Extern 1 (Transport _ _ _ (?α _ _) _) =>
    match type of α with rts _ _ => set_le_transport α end
    : typeclass_instances.

  (** ** Externally observable behaviors *)

  (** Given a RTS, we can define a reduced version that only contains
    observable behaviors: internal transitions are hidden, except in
    the case of silent divergence. *)

  CoInductive forever_internal {G A} (α : rts G A) (a : A) : Prop :=
    | forever_internal_intro a' :
        α a (internal a') ->
        forever_internal α a' ->
        forever_internal α a.

  Inductive reachable {G A} (α : rts G A) : relation A :=
    | reachable_refl a :
        reachable α a a
    | reachable_step a a' a'' :
        α a (internal a') ->
        reachable α a' a'' ->
        reachable α a a''.

  Inductive behavior_external {G A} : behavior G A -> Prop :=
    | interacts_external m k :
        behavior_external (interacts m k)
    | diverges_external :
        behavior_external diverges
    | goes_wrong_external :
        behavior_external goes_wrong.

  Inductive obs {G A} (α : rts G A) a : behavior G A -> Prop :=
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

  Global Instance reachable_trans {G A} (α : rts G A) :
    Transitive (reachable α).
  Proof.
    intros a a' a'' Ha' Ha''.
    induction Ha'; auto.
    econstructor; eauto.
  Qed.

  (** Observations are compatible with simulations. *)

  Lemma forever_internal_sim {G A B} (R : rel A B) α β a b :
    sim (G:=G) R α β ->
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

  Lemma reachable_sim {G A B} (R : rel A B) α β a b a' :
    sim (G:=G) R α β ->
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
    Monotonic (@behavior_external) (forallr -, forallr R, behavior_le R ++> impl).
  Proof.
    intros G A B R a b Hab Ha.
    destruct Ha; inversion Hab; eauto.
  Qed.

  Hint Extern 10 (Transport _ _ _ (behavior_external _) _) =>
    eapply impl_transport : typeclass_instances.

  Global Instance obs_sim :
    Monotonic (@obs) (forallr -, forallr R, sim R ++> sim R).
  Proof.
    intros G A B R α β Hαβ a b Hab ra Hra.
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

  Lemma obs_behavior_external {G A} (α : rts G A) a r :
    obs α a r ->
    behavior_external r.
  Proof.
    destruct 1; eauto.
  Qed.

  Lemma obs_internal_inv {G A} (α : rts G A) a a' :
    ~ obs α a (internal a').
  Proof.
    inversion 1.
    inversion H0.
  Qed.

  Lemma reachable_obs {G A} (α : rts G A) a a' :
    reachable (obs α) a a' ->
    reachable α a a'.
  Proof.
    intros Ha'.
    destruct Ha'; eauto.
    eelim obs_internal_inv; eauto.
  Qed.

  Lemma forever_internal_reachable {G A} (α : rts G A) a a' :
    reachable α a a' ->
    forever_internal α a' ->
    forever_internal α a.
  Proof.
    induction 1; auto.
    econstructor; eauto.
  Qed.

  Lemma obs_internal {G A} (α : rts G A) a a' r :
    RTS.obs α a' r ->
    α a (RTS.internal a') ->
    RTS.obs α a r.
  Proof.
    intros Hr Ha'.
    destruct Hr.
    - constructor. econstructor; eauto.
    - econstructor; eauto.
  Qed.

  Lemma obs_reachable {G A} (α : rts G A) a a' r :
    obs α a' r ->
    reachable α a a' ->
    obs α a r.
  Proof.
    intros Ha' H.
    induction H; eauto using obs_internal.
  Qed.

  (** ** [obs] is idempotent *)

  Lemma obs_idempotent {G A} (α : rts G A) :
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

  (** ** Structural properties *)

  Definition nonbranching_behaviors {G A} (r1 r2 : behavior G A) :=
    match r1, r2 with
      | internal a1, internal a2 => a1 = a2
      | interacts m1 k1, interacts m2 k2 => m1 = m2 -> k1 = k2
      | internal _, _ | _, internal _ => False
      | _, _ => True
    end.

  Definition nonbranching {G A} (α : rts G A) :=
    forall a r1 r2, α a r1 -> α a r2 -> nonbranching_behaviors r1 r2.

  Definition deterministic {G A} (α : rts G A) :=
    forall a r1 r2, α a r1 -> α a r2 -> r1 = r2.

  Lemma deterministic_nonbranching {G A} (α : rts G A) :
    deterministic α ->
    nonbranching α.
  Proof.
    intros Hα a r1 r2 Hr1 Hr2.
    assert (r1 = r2) as [] by eauto.
    destruct r1; simpl; auto.
  Qed.

  Hint Resolve deterministic_nonbranching.

  Lemma nonbranching_internal {G A} (α : rts G A) a a1 a2 :
    nonbranching α ->
    α a (internal a1) ->
    α a (internal a2) ->
    a1 = a2.
  Proof.
    firstorder.
  Qed.

  Lemma nonbranching_internal_external {G A} (α : rts G A) a r a' :
    nonbranching α ->
    behavior_external r ->
    α a r ->
    α a (internal a') ->
    False.
  Proof.
    intros Hα Hrext Hr Ha'.
    destruct Hrext; apply (Hα _ _ _ Hr Ha').
  Qed.

  (** A particular property of nonbranching transition systems is
    that any observable behavior remains unchanged after taking any
    number of silent steps. *)

  Lemma fi_inv_internal {G A} (α : rts G A) a a' :
    nonbranching α ->
    forever_internal α a ->
    α a (internal a') ->
    forever_internal α a'.
  Proof.
    intros Hα Ha Ha'.
    destruct Ha as [a1 Ha1 Ha1div].
    assert (H: a1 = a') by eauto using nonbranching_internal; subst.
    eauto.
  Qed.

  Lemma fi_inv_reachable {G A} (α : rts G A) a a' :
    nonbranching α ->
    forever_internal α a ->
    reachable α a a' ->
    forever_internal α a'.
  Proof.
    intros Hα Ha Ha'.
    induction Ha' as [ | a a' a'' Ha' Ha'' IHa''];
      eauto using fi_inv_internal.
  Qed.

  Lemma reachable_inv_reachable {G A} (α : rts G A) a a' a'' r :
    nonbranching α ->
    behavior_external r ->
    α a'' r ->
    reachable α a a'' ->
    reachable α a a' ->
    reachable α a' a''.
  Proof.
    intros Hα Hrext Hr Ha'' Ha'.
    revert a'' Hr Ha''.
    induction Ha' as [ | a1 a2 a3 Ha12 Ha23]; eauto; intros.
    destruct Ha'' as [ | a1 a' a'' Ha' Ha''].
    - eelim nonbranching_internal_external; eauto.
    - assert (a2 = a') by eauto using nonbranching_internal; subst. eauto.
  Qed.

  (** ** Sum *)

  Inductive sum {G A B} (α : rts G A) (β : rts G B) : rts G (A + B) :=
    | sum_inl a ra : α a ra -> sum α β (inl a) (behavior_map inl ra)
    | sum_inr b rb : β b rb -> sum α β (inr b) (behavior_map inr rb).

  Hint Constructors sum.
  Infix "+" := sum : rts_scope.

  Global Instance sum_sim :
    Monotonic
      (@sum)
      (forallr -, forallr RA, forallr RB, sim RA ++> sim RB ++> sim (RA + RB)).
  Proof.
    intros G A1 A2 RA B1 B2 RB α1 α2 Hα β1 β2 Hβ s1 s2 Hs s1' Hs1'.
    destruct Hs1'; inversion Hs; transport H; (eexists; split; [eauto | try rauto]).
  Qed.

  Global Instance obs_params : Params (@obs) 4.
  Global Instance sum_params : Params (@sum) 6.
End RTS.

Notation rts := RTS.rts.

Delimit Scope rts_scope with rts.
Infix "+" := RTS.sum : rts_scope.
