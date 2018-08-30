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
    | goes_wrong.

  Arguments behavior : clear implicits.

  Definition behavior_map {A B} (f : A -> B) (r : behavior A) : behavior B :=
    match r with
      | internal a' => internal (f a')
      | interacts m k => interacts m (fun mi => f (k mi))
      | goes_wrong => goes_wrong
    end.

  Inductive behavior_le {A B} (R : rel A B) : rel (behavior A) (behavior B) :=
    | internal_le :
        Monotonic internal (R ++> behavior_le R)
    | interacts_le :
        Monotonic interacts (- ==> (- ==> R) ++> behavior_le R)
    | goes_wrong_le ra :
        Related ra goes_wrong (behavior_le R).

  Global Existing Instance internal_le.
  Global Existing Instance interacts_le.
  Global Existing Instance goes_wrong_le.
  Global Instance internal_le_params : Params (@internal) 1.
  Global Instance interacts_le_params : Params (@interacts) 2.

  Global Instance behavior_le_refl {A} (R: relation A) :
    Reflexive R ->
    Reflexive (behavior_le R).
  Proof.
    intros H [a' | m k | ]; rauto.
  Qed.

  (** A receptive transition system simply assigns a set of possible
    behaviors to each state. *)

  Definition rts A :=
    rel A (behavior A).

  Arguments rts : clear implicits.

  (** ** Simulations *)

  (** A simulation between two RTS assets that each possible behavior
    in the first has a correponding behavior in the second. In
    particular, internal transitions must correspond one-to-one. *)

  Definition sim {A B} (R : rel A B) : rel (rts A) (rts B) :=
    (R ++> set_le (behavior_le R)).

  (** ** Externally observable behaviors *)

  (** Given a RTS, we can define a reduced version that only contains
    observable behaviors: internal transitions are hidden, except in
    the case of silent divergence. *)

  CoInductive diverges {A} (α : rts A) (a : A) : Prop :=
    | diverges_intro a' :
        α a (internal a') ->
        diverges α a' ->
        diverges α a.

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
    | goes_wrong_external :
        behavior_external goes_wrong.

  Inductive obs {A} (α : rts A) a : behavior A -> Prop :=
    | obs_diverges :
        diverges α a ->
        obs α a (internal a)
    | obs_external a' r :
        behavior_external r ->
        α a' r ->
        reachable α a a' ->
        obs α a r.

  Hint Resolve reachable_refl.
  Hint Immediate reachable_step.
  Hint Constructors behavior_external.
  Hint Constructors obs.

  (** Observations are compatible with simulations. *)

  Lemma diverges_sim {A B} (R : rel A B) α β a b :
    sim R α β ->
    R a b ->
    diverges α a ->
    diverges β b \/ obs β b goes_wrong.
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
    - edestruct @diverges_sim as [Hb | Hb]; eauto.
      + exists (internal b). split; eauto. rauto.
      + exists goes_wrong. split; eauto. rauto.
    - edestruct @reachable_sim as (b' & Hb' & [Hab' | Hgw]); eauto.
      + edestruct Hαβ as (rb & Hrb & Hr); eauto.
        transport Hext. eauto.
      + exists goes_wrong. split; eauto. rauto.
  Qed.

  (** The reduction process preserves observations, so that [obs] is
    idempotent. *)

  Lemma obs_internal_inv {A} (α : rts A) a a' :
    obs α a (internal a') ->
    diverges α a /\ a' = a /\ exists a'', α a (internal a'').
  Proof.
    inversion 1; subst.
    - intuition; eauto. destruct H1; eauto.
    - inversion H0.
  Qed.

  Lemma reachable_obs {A} (α : rts A) a a' :
    reachable (obs α) a a' ->
    a = a'.
  Proof.
    intros Ha'.
    induction Ha' as [a | a a' a'' Ha' Ha'' IHa'']; eauto.
    apply obs_internal_inv in Ha' as (_ & Ha' & _). congruence.
  Qed.

  Lemma diverges_obs {A} (α : rts A) a :
    diverges (obs α) a <-> diverges α a.
  Proof.
    split.
    - intros [a' Ha' Hda'].
      apply obs_internal_inv in Ha' as (Hda & _); auto.
    - revert a. cofix IH.
      intros a Ha.
      econstructor; eauto.
  Qed.

  Lemma obs_idempotent {A} (α : rts A) :
    obs (obs α) = obs α.
  Proof.
    apply functional_extensionality; intros a.
    apply functional_extensionality; intros r.
    apply prop_ext.
    split.
    - intros [Ha | a' ra' Hra' Hext Ha' ].
      + constructor. apply diverges_obs; auto.
      + apply reachable_obs in Ha'. subst. auto.
    - intros [Ha | a' ra' Hra' Hext Ha' ].
      + constructor. apply diverges_obs; auto.
      + econstructor; eauto.
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


  (** * Horizontal composition *)

  (** ** Transition system *)

  Section HCOMP_RTS.
    Context {A} (α : forall i : bool, rts (A i)) (dom : bool -> M -> bool).

    Inductive hc_state : Type :=
      | hc_r (i : bool) (a : A i) (k : M -> A (negb i))
      | hc_z.

    Definition hc_x i : A (negb i) -> (M -> A i) -> hc_state :=
      match i with
        | true => hc_r false
        | false => hc_r true
      end.

    Definition hc_xcall (i : bool) (mo : output) : option M :=
      match mo with
        | move m => if dom (negb i) m then Some m else None
        | _ => None
      end.

    Definition hc_behavior i (r : behavior (A i)) (k : M -> A (negb i)) :=
      match r with
        | internal a =>
          internal (hc_r i a k)
        | interacts mo k' =>
          match hc_xcall i mo with
            | Some m => internal (hc_x i (k m) k')
            | None => interacts mo (fun mi => hc_r i (k' mi) k)
          end
        | goes_wrong =>
          goes_wrong
      end.

    Inductive hc : rts hc_state :=
      | hc_intro i a k r :
          α i a r ->
          hc (hc_r i a k) (hc_behavior i r k).
  End HCOMP_RTS.

  Arguments hc_state : clear implicits.

  (** ** Monotonicity *)

  Section HCOMP_REL.
    Context {A B} (R : forall i : bool, rel (A i) (B i)).

    Inductive hc_rel : rel (hc_state A) (hc_state B) :=
      | hc_r_rel i :
          Monotonic (hc_r i) (R i ++> (- ==> R (negb i)) ++> hc_rel)
      | hc_z_rel :
          Monotonic hc_z hc_rel.

    Global Existing Instance hc_r_rel.
    Global Existing Instance hc_z_rel.
    Global Instance hc_r_rel_params : Params (@hc_r) 2.

    Global Instance hc_x_rel i :
      Monotonic (hc_x i) (R (negb i) ++> (- ==> R i) ++> hc_rel).
    Proof.
      destruct i; simpl; rauto.
    Qed.

    Global Instance hc_x_rel_params :
      Params (@hc_x) 2.

    Global Instance hc_behavior_rel dom i :
      Monotonic
        (hc_behavior dom i)
        (behavior_le (R i) ++> (- ==> R (negb i)) ++> behavior_le hc_rel).
    Proof.
      unfold hc_behavior. rauto.
    Qed.

    Global Instance hc_behavior_rel_params :
      Params (@hc_behavior) 2.

    Global Instance hc_sim :
      Monotonic hc ((forallr - @ i, sim (R i)) ++> - ==> sim hc_rel).
    Proof.
      intros α β Hαβ dom sa sb Hs ka Hka.
      destruct Hka as [i a ka ra].
      inversion Hs as [xi xa b Hab xka kb Hk | ]; clear Hs; subst.
      apply inj_pair2 in H1.
      apply inj_pair2 in H2.
      subst.
      edestruct Hαβ as (rb & Hrb & Hr); eauto.
      exists (hc_behavior dom i rb kb). split; [ | rauto].
      constructor; auto.
    Qed.

    Global Instance hc_sim_params :
      Params (@hc) 2.
  End HCOMP_REL.

  (** ** Modules *)

  Definition hcomp (α1 α2 : modsem) : modsem :=
    let α : bool -> modsem := fun i => if i then α1 else α2 in
    {|
      modsem_dom q :=
        (modsem_dom α1 q || modsem_dom α2 q)%bool;
      modsem_lts :=
        hc (fun i => modsem_lts (α i)) (fun i => modsem_dom (α i));
      modsem_entry q :=
        match modsem_dom α1 q, modsem_dom α2 q with
          | true, true => hc_z
          | true, false => hc_r true (modsem_entry α1 q) (modsem_entry α2)
          | false, true => hc_r false (modsem_entry α2 q) (modsem_entry α1)
          | false, false => hc_z
        end;
    |}.

  Global Instance hcomp_ref :
    Monotonic (@hcomp) (modref ++> modref ++> modref).
  Proof.
    intros α1 β1 [Hd1 R1 Hαβ1 He1].
    intros α2 β2 [Hd2 R2 Hαβ2 He2].
    pose (α := fun i : bool => if i then α1 else α2).
    pose (β := fun i : bool => if i then β1 else β2).
    pose (R := fun i : bool =>
            match i return rel (modsem_state (α i)) (modsem_state (β i)) with
              | true => R1
              | false => R2
            end).
    exists (hc_rel R); simpl.
    - intros q. f_equal; auto.
    - change (sim (hc_rel R) (hc α (fun i => modsem_dom (α i)))
                             (hc β (fun i => modsem_dom (β i)))).
      replace (fun i => modsem_dom (α i)) with (fun i => modsem_dom (β i)).
      + eapply hc_sim.
        intros [ | ]; simpl; eauto.
      + apply functional_extensionality. intros i.
        apply functional_extensionality. intros q.
        destruct i; simpl; eauto.
    - intros q.
      rewrite !Hd1, !Hd2.
      repeat rstep; simpl; eauto.
  Qed.
End RTS.
