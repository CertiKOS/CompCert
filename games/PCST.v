Require Import List.
Require Import Axioms.

(** This library defined prefix-closed sets of traces, and a number of
  useful operations on them. Prefix-closed sets of traces are used as
  the internal representation of game trees, which gives us
  extensionality and helps us avoid having to deal with the quirks of
  Coq's coinductive types. However the implementation of game trees
  will be made opaque, so that the user normally doesn't have to
  concern themselves with the constructions below. *)

Axiom prop_ext : forall (P Q : Prop), (P <-> Q) -> P = Q.


(** * Prefix closure *)

Definition prefix_closed {A} (P : list A -> Prop) :=
  P nil /\ forall u m, P (u++m::nil) -> P u.

Definition prefix_closure {A} (P : list A -> Prop) : list A -> Prop :=
  fun u => u = nil \/ exists v, P (u ++ v).

Lemma prefix_closed_app {A} (P : list A -> Prop) u v :
  prefix_closed P -> P (u ++ v) -> P u.
Proof.
  intros HP.
  pattern v. revert v. apply rev_ind.
  - rewrite app_nil_r. auto.
  - intros x v IHv H.
    eapply IHv, HP.
    rewrite <- app_assoc. eauto.
Qed.

Lemma prefix_closure_closed {A} (P : list A -> Prop) :
  prefix_closed (prefix_closure P).
Proof.
  unfold prefix_closed, prefix_closure.
  intuition eauto.
  - pose proof (app_cons_not_nil u nil m).
    congruence.
  - destruct H0 as (v & Hv).
    rewrite <- app_assoc in Hv. simpl in Hv.
    eauto.
Qed.

Lemma prefix_closure_infl {A} (P : list A -> Prop) u :
  P u -> prefix_closure P u.
Proof.
  unfold prefix_closure.
  intros Hu. right.
  exists nil. rewrite app_nil_r. assumption.
Qed.

Lemma prefix_closure_minimal {A} (P Q : list A -> Prop) :
  prefix_closed Q ->
  (forall u, P u -> Q u) ->
  (forall u, prefix_closure P u -> Q u).
Proof.
  intros [HQnil HQ] HPQ u [ | [v Hv]].
  - congruence.
  - apply HPQ in Hv.
    revert Hv. pattern v. revert v. apply rev_ind.
    + rewrite app_nil_r. auto.
    + intros m v IHv Hm.
      eapply IHv, HQ.
      rewrite <- app_assoc. eauto.
Qed.

Lemma prefix_closed_closure {A} (P : list A -> Prop) :
  prefix_closed P ->
  prefix_closure P = P.
Proof.
  intros HP.
  apply functional_extensionality. intros u.
  apply prop_ext. split.
  - apply prefix_closure_minimal; eauto.
  - apply prefix_closure_infl.
Qed.

Lemma prefix_closure_idemp {A} (P : list A -> Prop) :
  prefix_closure (prefix_closure P) = prefix_closure P.
Proof.
  apply prefix_closed_closure.
  apply prefix_closure_closed.
Qed.


(** * Prefix-closed sets of traces *)

Definition pcst M :=
  sig (@prefix_closed M).

Section PCST.
  Context {M : Type}.

  (** ** Basic accessors *)

  Definition has_trace (x : pcst M) : list M -> Prop :=
    proj1_sig x.

  Lemma has_trace_prefix_closed (x : pcst M) :
    prefix_closed (has_trace x).
  Proof.
    unfold has_trace.
    apply proj2_sig.
  Qed.

  (** ** Equality *)

  Lemma pcst_eq (x y : pcst M) :
    (forall u, has_trace x u <-> has_trace y u) -> x = y.
  Proof.
    destruct x as [x Hx], y as [y Hy]. simpl.
    intros H.
    cut (x = y).
    - intro. subst. f_equal. apply proof_irr.
    - auto using functional_extensionality, prop_ext.
  Qed.

  (** ** As a tree *)

  Definition has_child (x : pcst M) (m : M) : Prop :=
    has_trace x (m :: nil).

  Program Definition subtree (x : pcst M) (m : M) : pcst M :=
    fun u => u = nil \/ has_trace x (m :: u).
  Next Obligation.
    destruct x as [x Hx].
    split; eauto; simpl.
    intros u n H. right.
    pose proof (app_cons_not_nil u nil n).
    destruct H; try congruence.
    rewrite app_comm_cons in H.
    eapply Hx. eauto.
  Qed.

  Lemma has_trace_cons (x : pcst M) (m : M) (u : list M) :
    has_trace x (m :: u) <-> (has_child x m /\ has_trace (subtree x m) u).
  Proof.
    simpl. split.
    - intros Hxmu.
      split; eauto. red.
      eapply prefix_closed_app with (v := u); auto.
      apply has_trace_prefix_closed.
    - intros [Hxm [Hu | Hxmu]]; subst; eauto.
  Qed.

End PCST.
