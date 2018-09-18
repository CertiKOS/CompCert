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


(** * Horizontal composition *)

Module HComp.
  Import RTS.

  Section RTS.
    Context {G A} (sw : output G -> option (input G)) (α : rts G A).

    Inductive hc_state : Type :=
      | hc_r (a : A) (k : input G -> A)
      | hc_z.

    Definition hc_behavior (r : RTS.behavior G A) (k : input G -> A) :=
      match r with
        | internal a =>
          internal (hc_r a k)
        | interacts mo k' =>
          match sw mo with
            | Some m => internal (hc_r (k m) k')
            | None => interacts mo (fun mi => hc_r (k' mi) k)
          end
        | diverges =>
          diverges
        | goes_wrong =>
          goes_wrong
      end.

    Inductive hc : rts G hc_state :=
      | hc_intro a k r :
          α a r ->
          hc (hc_r a k) (hc_behavior r k).

  End RTS.

  Arguments hc_state : clear implicits.

  (** ** Monotonicity *)

  Inductive hc_rel {G A B} R : rel (hc_state G A) (hc_state G B) :=
    | hc_r_rel :
        Monotonic hc_r (R ++> (- ==> R) ++> hc_rel R)
    | hc_z_rel :
        Monotonic hc_z (hc_rel R).

  Global Existing Instance hc_r_rel.
  Global Existing Instance hc_z_rel.
  Global Instance hc_r_rel_params : Params (@hc_r) 2.

  Global Instance hc_behavior_rel {G A B} R sw :
    Monotonic
      (hc_behavior sw)
      (behavior_le R ++> (- ==> R) ++> behavior_le (@hc_rel G A B R)).
  Proof.
    unfold hc_behavior. rauto.
  Qed.

  Global Instance hc_behavior_rel_params :
    Params (@hc_behavior) 2.

  Global Instance hc_sim {G A B} R :
    Monotonic hc (- ==> sim R ++> sim (@hc_rel G A B R)).
  Proof.
    intros sw α β Hαβ sa sb Hs ka Hka.
    destruct Hka as [a ka ra].
    inversion Hs as [xa b Hab xka kb Hk | ]; clear Hs; subst.
    edestruct Hαβ as (rb & Hrb & Hr); eauto.
    exists (hc_behavior sw rb kb). split; [ | rauto].
    constructor; auto.
  Qed.

  Global Instance hc_sim_params :
    Params (@hc) 2.

  (** ** Properties *)

  Lemma hc_behavior_external {G A} sw (r : behavior G A) (k : input G -> A) :
    behavior_external (hc_behavior sw r k) ->
    behavior_external r.
  Proof.
    destruct r; inversion 1; constructor.
  Qed.

  Lemma hc_reachable {G A} sw (α : rts G A) a a' k :
    reachable α a a' ->
    reachable (hc sw α) (hc_r a k) (hc_r a' k).
  Proof.
    induction 1; eauto.
    econstructor; eauto.
    change (internal _) with (hc_behavior sw (internal a') k).
    constructor; eauto.
  Qed.

  (** ** Modules *)

  Section HCOMP.
    Context {li} (α1 α2 : modsem (li -o li)).

    Definition hcomp_dom (q : query (li -o li)) : bool :=
      modsem_dom α1 q || modsem_dom α2 q.

    Definition hcomp_sw (q : reply (li -o li)) : option (query (li -o li)) :=
      match q with
        | inl q => if hcomp_dom (inr q) then Some (inr q) else None
        | inr r => Some (inl r) (* XXX need to know whether outermost reply *)
      end.

    Definition hcomp_entry (q : query (li -o li)) :=
      match modsem_dom α1 q, modsem_dom α2 q with
        | true, false =>
            hc_r (G := li -o li)
              (inl (modsem_entry α1 q))
              (fun m => inr (modsem_entry α2 m))
        | false, true =>
            hc_r (G := li -o li)
              (inr (modsem_entry α2 q))
              (fun m => inl (modsem_entry α1 m))
        | _, _ =>
            hc_z
      end.

    Definition hcomp : modsem (li -o li) :=
      {|
        modsem_lts := hc (G := li -o li) hcomp_sw (α1 + α2)%rts;
        modsem_dom := hcomp_dom;
        modsem_entry := hcomp_entry;
      |}.
  End HCOMP.

  Global Instance hcomp_dom_ref :
    Monotonic (@hcomp_dom) (forallr -, modref ++> modref ++> - ==> eq).
  Proof.
    unfold hcomp_dom. repeat rstep. f_equal; rauto.
  Qed.

  Global Instance hcomp_sw_ref :
    Monotonic (@hcomp_sw) (forallr -, modref ++> modref ++> - ==> eq).
  Proof.
    unfold hcomp_sw. rauto.
  Qed.

  Global Instance hcomp_ref :
    Monotonic (@hcomp) (forallr -, modref ++> modref ++> modref).
  Proof.
    intros li α1 β1 Hαβ1 α2 β2 Hαβ2.
    pose proof Hαβ1 as [Hd1 R1 H1 He1].
    pose proof Hαβ2 as [Hd2 R2 H2 He2].
    exists (hc_rel (R1 + R2)); simpl.
    - intros q. rauto.
    - replace (hcomp_sw β1 β2) with (hcomp_sw α1 α2).
      + eapply hc_sim. rauto.
      + apply functional_extensionality. intros i. rauto.
    - intros q. unfold hcomp_entry.
      rewrite <- Hd1, <- Hd2.
      repeat rstep; simpl; eauto.
  Qed.

  (** ** [hcomp] and [obs] *)

  (** We prove that [hcomp] semi-commutes with [obs], in the sense
    that applying [obs] after horizontal composition only should yield
    the same result as applying it both before and after horizontal
    composition. *)

  CoInductive forever_switching {G A} sw (α : rts G A) : hc_state G A -> Prop :=
    | forever_switching_intro a a' ra k s' :
        reachable α a a' ->
        α a' ra ->
        behavior_external ra ->
        hc_behavior sw ra k = internal s' ->
        forever_switching sw α s' ->
        forever_switching sw α (hc_r a k).

  Lemma forever_switching_internal {G A} sw (α : rts G A) s s' :
    hc sw α s (internal s') ->
    forever_switching sw α s' ->
    forever_switching sw α s.
  Proof.
    intros Hs' Hd.
    inversion Hs' as [a0 k0 ra0 Hra0]; clear Hs'.
    destruct ra0; inversion H0; clear H0.
    - destruct Hd.
      inversion H2; clear H2; subst.
      eapply (forever_switching_intro sw α a0 a'0); eauto.
    - destruct sw as [mx|] eqn:Hmx; inversion H2; clear H2; subst.
      eapply (forever_switching_intro sw α a0 a0); eauto.
      simpl. rewrite Hmx. reflexivity.
  Qed.

  Inductive hc_settles {G A} sw (α : rts G A) : rts G (hc_state G A) :=
    | hc_settles_external a a' ra k r :
        α a' ra ->
        reachable α a a' ->
        hc_behavior sw ra k = r ->
        behavior_external r ->
        hc_settles sw α (hc_r a k) r
    | hc_settles_diverges a k :
        forever_internal α a ->
        hc_settles sw α (hc_r a k) diverges
    | hc_settles_switch a a' ra k s' r :
        α a' ra ->
        reachable α a a' ->
        behavior_external ra ->
        hc_behavior sw ra k = internal s' ->
        hc_settles sw α s' r ->
        hc_settles sw α (hc_r a k) r.

  Hint Constructors hc_settles.

  Lemma hc_settles_internal {G A} sw (α : rts G A) s s' r :
    hc sw α s (internal s') ->
    hc_settles sw α s' r ->
    hc_settles sw α s r.
  Proof.
    intros Hs' Hr.
    inversion Hs' as [a k ra Hra]; clear Hs'; subst.
    destruct ra; inversion H0; clear H0.
    - destruct Hr; inversion H1; clear H1; subst.
      + eapply (hc_settles_external sw α a a'0); eauto.
      + eapply (hc_settles_diverges sw α a); eauto.
        econstructor; eauto.
      + eapply (hc_settles_switch sw α a a'0); eauto.
    - destruct sw as [mx|] eqn:Hmx; inversion H1; clear H1; subst.
      eapply (hc_settles_switch sw α a a (interacts m k0)); eauto.
      simpl. rewrite Hmx. reflexivity.
  Qed.

  Inductive obs_hc {G A} sw (α : rts G A) : rts G (hc_state G A) :=
    | obs_hc_settles s r :
        hc_settles sw α s r ->
        obs_hc sw α s r
    | obs_hc_forever_switching s :
        forever_switching sw α s ->
        obs_hc sw α s diverges.

  (** *** Alternative formulations for coinductive properties *)

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

  Lemma forever_switching_inv_internal {G A} sw (α : rts G A) s s' :
    deterministic α ->
    forever_switching sw α s ->
    hc sw α s (internal s') ->
    forever_switching sw α s'.
  Proof.
    intros Hα Hs Hs'.
    inversion Hs'; clear Hs'; subst.
    destruct r; simpl in H; try now inversion H.
    - inversion Hs as [a1 a2 ra l s2 Ha2 Hra Hs2 Hs2d]; clear Hs; subst.
      inversion H; clear H; subst.
      eapply (reachable_inv_reachable α a a' a2) in Ha2; eauto.
      econstructor; eauto.
    - destruct sw eqn:Hm; inversion H; clear H; subst.
      inversion Hs; clear Hs; subst.
      assert (a' = a).
      {
        destruct H2; eauto.
        eelim (nonbranching_internal_external α a (interacts m k0)); eauto.
      }
      subst.
      assert (ra = interacts m k0).
      {
        eapply Hα; eauto.
      }
      subst.
      simpl in H5.
      rewrite Hm in H5.
      inversion H5.
      congruence.
  Qed.

  Lemma forever_switching_nbr {G A} sw (α : rts G A) s :
    deterministic α ->
    forever_switching sw α s <->
    (s <> hc_z /\
     forall a k, reachable (hc sw α) s (hc_r a k) ->
                 exists a' r s', reachable α a a' /\
                                 α a' r /\
                                 behavior_external r /\
                                 hc_behavior sw r k = internal s').
  Proof.
    intros Hα. split.
    - intros Hs.
      split. { destruct Hs. congruence. }
      intros a k Hak.
      remember (hc_r a k) as s' eqn:Hs' in Hak.
      revert a k Hs'.
      induction Hak; intros.
      + destruct Hs.
        inversion Hs'; clear Hs'; subst.
        exists a', ra, s'. eauto.
      + eapply IHHak; eauto.
        eapply forever_switching_inv_internal; eauto.
    - revert s. cofix IH. intros s [Hnz Hs].
      destruct s as [a k | ]; try congruence.
      edestruct (Hs a k) as (a' & r & s' & Ha' & Hr & Hrext & Hs'); [ eauto .. | ].
      eapply (forever_switching_intro sw α a a' r k); eauto.
      eapply IH.
      split. { destruct r; simpl in Hs'; try congruence.
               destruct sw; congruence. }
      intros.
      eapply Hs.
      transitivity s'; auto.
      transitivity (hc_r a' k); auto using hc_reachable.
      econstructor; eauto.
      rewrite <- Hs'. constructor. auto.
  Qed.

  Lemma hc_det {G A} sw (α : rts G A) :
    deterministic α ->
    deterministic (hc sw α).
  Proof.
    intros Hα s x y Hx Hy.
    destruct Hx. inversion Hy.
    f_equal; eauto.
  Qed.

  Lemma forever_hc {G A} sw (α : rts G A) s :
    deterministic α ->
    forever_internal (hc sw α) s ->
    (exists a k, reachable (hc sw α) s (hc_r a k) /\ forever_internal α a) \/
    forever_switching sw α s.
  Proof.
    intros Hα Hs1.
    destruct (classic (forever_switching sw α s)) as [? | Hs2]; auto. left.
    rewrite forever_internal_nbr in Hs1; eauto using hc_det.
    rewrite forever_switching_nbr in Hs2; eauto.
    apply not_and_or in Hs2 as [? | Hs2].
    {
      specialize (Hs1 s (reachable_refl _ s)) as (s' & Hs').
      destruct Hs'. elim H. congruence.
    }
    apply not_all_ex_not in Hs2 as [a Hs2].
    apply not_all_ex_not in Hs2 as [k Hs2].
    apply not_all_ex_not in Hs2 as [Hak Hs2].
    exists a, k. split; auto.
    revert a Hak Hs2. cofix IH. intros.
    edestruct (Hs1 _ Hak) as (a'' & Ha'').
    inversion Ha''; clear Ha''; subst.
    destruct r; try now inversion H2.
    - simpl in H2. inversion H2; clear H2; subst.
      econstructor; eauto.
      eapply IH.
      + transitivity (hc_r a k); eauto.
        econstructor; eauto.
        change (internal _) with (hc_behavior sw (internal a') k).
        constructor; eauto.
      + intros (a'' & r & s' & Ha'' & Hr & Hrext & Hs'); eauto 10.
    - elim Hs2; eauto 10.
  Qed.

  Lemma obs_hc_obs_hc {G A} sw (α : rts G A) s r :
    deterministic α ->
    obs (hc sw α) s r ->
    obs_hc sw α s r.
  Proof.
    intros Hα Hr.
    destruct Hr as [Hs | s' r Hrext Hr Hs'].
    - apply forever_hc in Hs as [(a & k & Hs' & Ha) | Hs]; auto.
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

  Lemma obs_hc_obs_hc_obs {G A} sw (α : rts G A) s r :
    obs_hc sw α s r ->
    obs (hc sw (obs α)) s r.
  Proof.
    intro.
    destruct H.
    - induction H.
      + apply obs_external with (hc_r a k); eauto.
        subst. constructor.
        eapply obs_external with a'; eauto.
        eapply hc_behavior_external; eauto.
      + apply obs_external with (hc_r a k); eauto.
        change diverges with (hc_behavior sw diverges k).
        constructor. auto.
      + apply obs_reachable with s'; auto.
        econstructor; eauto.
        rewrite <- H2. constructor. eauto.
    - eapply obs_diverges.
      revert s H. cofix IH. intros.
      destruct H. econstructor; eauto.
      rewrite <- H2. constructor. eauto.
  Qed.

  Lemma obs_hc_obs_hc_obs_sim {G A} sw (α : rts G A) :
    deterministic α ->
    sim eq (obs (hc sw α)) (obs (hc sw (obs α))).
  Proof.
    intros Hα s _ [] r Hr.
    exists r. split; [ | rauto].
    apply obs_hc_obs_hc_obs.
    apply obs_hc_obs_hc; auto.
  Qed.

End HComp.
