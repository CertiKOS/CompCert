Require Import LogicalRelations.
Require Import OptionRel.
Require Import List.
Require Import Axioms.
Require Import PCST.
Require Import LTS.


(** * Definition *)

(** We use a refinement-based approach with game trees as our main
  semantic objects. Game trees generalize the usual definitions of
  strategies, but they can serve as more general specfications:
  a game tree as defined below can specify, for every position,
  what inputs must be accepted, and what outputs are allowed. *)

Module Type GametreeSpec.

  Parameter t : Type -> Type.
  Parameter d : forall {M}, lts M (t M).
  Parameter c : forall {M A}, lts M A -> A -> t M.

  Axiom d_determ : forall {M}, @LTS.determ M _ d.
  Axiom c_mor : forall {M A} δ, @LTS.determ M A δ -> LTS.morphism (c δ) δ d.
  Axiom c_uniq : forall {M A} (f : A -> t M) δ, LTS.morphism f δ d -> f = c δ.

  Parameter ref : forall {M} (p : M -> bool), relation (t M).

  Axiom d_ref :
    forall M p, Monotonic (@d M) (LTS.ref p (ref p)).
  Axiom c_ref :
    forall M p, Monotonic (@c M) (forallr R, LTS.ref p R ++> R ++> ref p).

End GametreeSpec.

(** We implement gametrees based on prefix-closed sets of traces.
  However we only rely on the coinduction interface above, so that any
  implementation could be substituted. *)

Module GametreeImpl : GametreeSpec.

  Definition t := pcst.

  Definition d {M} : lts M (t M) :=
    fun m x y => has_child x m /\ y = subtree x m.

  Definition c {M A} (α : lts M A) (a : A) :=
    LTS.traces α a.

  Lemma d_determ {M} :
    LTS.determ (@d M).
  Proof.
    intros a m a1 a2 H1 H2. red in H1, H2.
    intuition congruence.
  Qed.

  Lemma c_mor {M A} (δ : lts M A) :
    LTS.determ δ ->
    LTS.morphism (c δ) δ d.
  Proof.
    intros Hδ. red. unfold c, d.
    split.
    - intros m a a' Ha'. split.
      + apply LTS.traces_has_child. eauto.
      + erewrite LTS.traces_subtree; eauto.
    - intros m a b' [Hm Hb']; subst.
      rewrite LTS.traces_has_child in Hm. destruct Hm as [a' Ha'].
      exists a'. erewrite LTS.traces_subtree; eauto.
  Qed.

  Lemma c_uniq {M A} (f : A -> t M) (δ : lts M A) :
    LTS.morphism f δ d ->
    f = c δ.
  Proof.
    intros [Hδf Hfδ].
    apply functional_extensionality. intros a.
    apply pcst_eq. intros u. simpl.
    revert a. induction u as [ | m u IHu]; simpl.
    - intros a. intuition.
      + eexists; constructor.
      + apply has_trace_prefix_closed.
    - intros a.
      rewrite has_trace_cons.
      split.
      + intros [Hm Hu].
        assert (d m (f a) (subtree (f a) m)) as H by (red; auto).
        apply Hfδ in H as (a' & Ha' & Hfa').
        rewrite <- Ha' in Hu. apply IHu in Hu as [a'' Ha''].
        exists a''; econstructor; eauto.
      + intros [a'' Ha'']. inversion Ha''; clear Ha''; subst.
        assert (has_trace (f a') u) as Hu by (apply IHu; eauto).
        edestruct Hδf as [? ?]; eauto.
        split; auto. congruence.
  Qed.

  Parameter ref : forall {M} (p : M -> bool), relation (t M).

  Axiom d_ref :
    forall M p, Monotonic (@d M) (LTS.ref p (ref p)).
  Axiom c_ref :
    forall M p, Monotonic (@c M) (forallr R, LTS.ref p R ++> R ++> ref p).

End GametreeImpl.


(** * Theory *)

(** From these basic primitives we can build up more operations and
  properties of gametrees, and define the refinement lattice. *)

Module Gametree.
  Include GametreeImpl.

  Global Existing Instances d_ref c_ref.
  Global Instance c_ref_params : Params (@c) 3.
  Global Instance d_ref_params : Params (@d) 3.

  (** ** Derived categorical properties *)

  Lemma c_d :
    forall {M} (x : t M), c d x = x.
  Proof.
    intros M x.
    cut (c d = (fun x : t M => x)). { intros H. rewrite H. reflexivity. }
    erewrite c_uniq; eauto.
    apply LTS.morphism_id.
  Qed.

  Lemma final_morphism_uniq {M A} (α : lts M A) f g :
    LTS.morphism f α d ->
    LTS.morphism g α d ->
    f = g.
  Proof.
    intros.
    erewrite (c_uniq f); eauto.
    erewrite (c_uniq g); eauto.
  Qed.

  (** ** Extensionality *)

  Lemma c_bisim_eq {M A B} (R : rel A B) (α β : lts M _) a b :
    LTS.determ α ->
    LTS.determ β ->
    LTS.bisim R α β ->
    R a b ->
    c α a = c β b.
  Proof.
    intros Hα Hβ Hαβ Hab.
    pose (r := rpair a b Hab).
    pose (f := fun r : relement R => c α (rfst r)).
    pose (g := fun r : relement R => c β (rsnd r)).
    change (f r = g r). cut (f = g); try congruence. subst f g.
    eapply final_morphism_uniq.
    - eapply LTS.morphism_compose; eauto using c_mor.
      eapply LTS.rfst_morphism. rauto.
    - eapply LTS.morphism_compose; eauto using c_mor.
      eapply LTS.rsnd_morphism. apply LTS.bisim_sim, LTS.bisim_flip. auto.
  Qed.

  (** ** Refinement *)

  (** Each assignment of polarity to moves defines a refinement
    partial order on trees and an associated complete bounded lattice
    structure. *)

  Section REF.
    Context {M} (p : M -> bool).

    (** *** Partial order *)

    (** First, we show that the refinement is a partial order. Proving
      reflexivity and transitivity is straightforward: we expand the
      relevant trees as transition systems and build a simulation to
      prove their refinement. *)

    Global Instance ref_preo :
      PreOrder (ref p).
    Proof.
      split.
      - intros x.
        rewrite <- (c_d x).
        monotonicity; reflexivity.
      - intros x y z Hxy Hyz.
        rewrite <- (c_d x), <- (c_d z).
        apply c_ref with (rel_compose (ref p) (ref p)); eauto.
        rewrite LTS.ref_compose.
        eexists; split; rauto.
    Qed.

    (** We prove antisymmetry by establishing that mutual refinement
      is a bisimulation on trees. *)

    Global Instance ref_po :
      PartialOrder eq (ref p).
    Proof.
      intros x y. red.
      split.
      - intro. subst. split; reflexivity.
      - intros [Hxy Hyx].
        rewrite <- (c_d x), <- (c_d y).
        eapply c_bisim_eq with (ref p /\ flip (ref p))%rel; eauto using d_determ.
        + eapply LTS.ref_bisim_inter; eauto using d_determ.
          * rauto.
          * eapply LTS.ref_flip.
            rewrite opp_invol.
            rauto.
        + rauto.
    Qed.

    (** *** Lattice structure *)

    Definition bot : t M :=
      c (LTS.bot p) tt.

    Lemma bot_ref y :
      ref p bot y.
    Proof.
      unfold bot. rewrite <- (c_d y). rstep.
      - apply LTS.bot_ref.
      - constructor.
    Qed.

    Definition sup (X : t M -> Prop) : t M :=
      c (LTS.sup p d) X.

    Lemma sup_ub (x : t M) (X : t M -> Prop) :
      X x -> ref p x (sup X).
    Proof.
      intros Hx. unfold sup. rewrite <- (c_d x). rstep.
      - apply LTS.sup_ub.
      - simpl. assumption.
    Qed.

    Lemma sup_lub (X : t M -> Prop) (y : t M) :
      (forall x, X x -> ref p x y) -> ref p (sup X) y.
    Proof.
      intros Hy. unfold sup. rewrite <- (c_d y). rstep.
      - apply LTS.sup_lub; eauto using d_determ. rauto.
      - simpl. assumption.
    Qed.

    (* By taking the opposite polarity we obtain the inverse
      lattice. *)

    Lemma ref_opp :
      flip (ref p) = ref (opp p).
    Proof.
      apply functional_extensionality; intro x.
      apply functional_extensionality; intro y.
      apply prop_ext. split.
      - intros Hyx.
        rewrite <- (c_d x), <- (c_d y).
        apply c_ref with (flip (ref p)); eauto.
        apply LTS.ref_flip. setoid_rewrite opp_invol. rauto.
      - intros Hxy. red.
        rewrite <- (c_d x), <- (c_d y).
        apply c_ref with (flip (ref (fun m => negb (p m)))); [ | rauto].
        apply LTS.ref_flip. rauto.
    Qed.

  End REF.

End Gametree.
