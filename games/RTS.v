Require Import LogicalRelations.
Require Import Axioms.


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

  Definition behavior_in {A} (dom : M -> bool) (r : behavior A) :=
    match r with
      | interacts (move m) k => dom m
      | _ => false
    end.

  Inductive behavior_le {A B} (R : rel A B) : rel (behavior A) (behavior B) :=
    | internal_le a' b' :
        R a' b' ->
        behavior_le R (internal a') (internal b')
    | interacts_le m ka kb :
        (forall mi, R (ka mi) (kb mi)) ->
        behavior_le R (interacts m ka) (interacts m kb)
    | goes_wrong_le ra :
        behavior_le R ra goes_wrong.

  Global Instance behavior_le_refl {A} (R: relation A) :
    Reflexive R ->
    Reflexive (behavior_le R).
  Proof.
    intros H [a' | m k | ]; constructor; eauto.
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
    fun α β =>
      forall a b ra,
        R a b ->
        α a ra ->
        exists rb,
          β b rb /\
          behavior_le R ra rb.

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

  Inductive obs {A} (α : rts A) a : behavior A -> Prop :=
    | obs_diverges :
        diverges α a ->
        obs α a (internal a)
    | obs_interacts a' m k :
        reachable α a a' ->
        α a' (interacts m k) ->
        obs α a (interacts m k)
    | obs_goes_wrong a' :
        reachable α a a' ->
        α a' goes_wrong ->
        obs α a goes_wrong.

  (** Observations are compatible with simulations. *)

  Require Import Classical.

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
      intros Hgw. inversion Hgw; clear Hgw; subst.
      apply H. econstructor; eauto.
      econstructor; eauto.
    - destruct H.
      econstructor; eauto.
      constructor.
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
    induction Ha' as [a | a a' a'' Ha' Ha'' IHa'']; intros.
    - exists b. split; auto. constructor.
    - edestruct Hαβ as (rb' & Hb' & Hab'); eauto.
      inversion Hab'; clear Hab'; subst.
      + edestruct IHa'' as (b'' & Hb'' & Hab''); eauto.
        exists b''. split; eauto. econstructor; eauto.
      + exists b. split; eauto. constructor.
  Qed.

  Global Instance obs_sim :
    Monotonic (@obs) (forallr R, sim R ++> sim R).
  Proof.
    intros A B R α β Hαβ a b ra Hab Hra.
    destruct Hra as [Ha | a' m ka H Hka | a' H Ha'].
    - edestruct @diverges_sim as [Hb | Hb]; eauto.
      + exists (internal b). split; constructor; eauto.
      + exists goes_wrong. split; eauto. constructor.
    - edestruct @reachable_sim as (b' & Hb' & [Hab' | Hgw]); eauto.
      + edestruct Hαβ as (rb & Hrb & Hr); eauto.
        exists rb. split; auto.
        inversion Hr; clear Hr; subst; econstructor; eauto.
      + exists goes_wrong. split; econstructor; eauto.
    - edestruct @reachable_sim as (b' & Hb' & [Hab' | Hgw]); eauto.
      + edestruct Hαβ as (rb & Hrb & Hr); eauto.
        exists rb. split; auto.
        inversion Hr; clear Hr; subst; econstructor; eauto.
      + exists goes_wrong. split; econstructor; eauto.
  Qed.

  (** The reduction process preserves observations, so that [obs] is
    idempotent. *)

  Lemma reachable_obs {A} (α : rts A) a a' :
    reachable (obs α) a a' ->
    a = a'.
  Proof.
    intros Ha'.
    induction Ha' as [a | a a' a'' Ha' Ha'' IHa'']; eauto.
    inversion Ha'. congruence.
  Qed.

  Lemma diverges_obs {A} (α : rts A) a :
    diverges (obs α) a <-> diverges α a.
  Proof.
    split.
    - intros [a' Ha' Hda'].
      inversion Ha' as [Ha | | ]; clear Ha'; subst.
      assumption.
    - revert a. cofix IH.
      intros a Ha.
      econstructor; eauto.
      constructor; eauto.
  Qed.

  Lemma reduce_observed_step {A} (α : rts A) a ra :
    obs (obs α) a ra <-> obs α a ra.
  Proof.
    split.
    - intros [Ha | a' m k Ha' Hk | a' Ha' Hk].
      + constructor. apply diverges_obs; auto.
      + apply reachable_obs in Ha'. subst. auto.
      + apply reachable_obs in Ha'. subst. auto.
    - intros [Ha | a' m k Ha' Hk | a' Ha' Hk].
      + constructor. apply diverges_obs; auto.
      + econstructor; eauto using reachable_refl.
        econstructor; eauto.
      + econstructor; eauto using reachable_refl.
        econstructor; eauto.
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

    Definition hc_extcall (i : bool) (mo : output) :=
      match mo with
        | move m => if dom i m then None else Some m
        | _ => None
      end.

    Definition hc_behavior i (r : behavior (A i)) (k : M -> A (negb i)) :=
      match r with
        | internal a =>
          internal (hc_r i a k)
        | interacts mo k' =>
          match hc_extcall i mo with
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
      unfold hc_behavior.
      repeat rstep.
      - constructor. constructor; eauto.
      - constructor. repeat rstep. auto.
      - constructor. intro. repeat rstep. auto.
      - constructor.
    Qed.

    Global Instance hc_behavior_rel_params :
      Params (@hc_behavior) 2.

    Global Instance hc_sim :
      Monotonic hc ((forallr - @ i, sim (R i)) ++> - ==> sim hc_rel).
    Proof.
      intros α β Hαβ dom sa sb ka Hs Hka.
      destruct Hka as [i a ka ra].
      inversion Hs as [xi xa b Hab xka kb Hk | ]; clear Hs; subst.
      apply inj_pair2 in H1.
      apply inj_pair2 in H2.
      subst.
      edestruct Hαβ as (rb & Hrb & Hr); eauto.
      exists (hc_behavior dom i rb kb). split; [ | rauto].
      constructor; auto.
    Qed.
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
