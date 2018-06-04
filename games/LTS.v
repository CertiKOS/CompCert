Require Import LogicalRelations.
Require Import OptionRel.
Require Import List.
Require Import Axioms.
Require Import PCST.

(** In the following we define the labelled transition systems used as
  a core component in the interface of game trees. Theoretically, they
  are the F-coalgebras associated with the functor [F X := M -> P^1(X)]
  corresponding to the coinductive shape of game trees. Practically,
  our fundamental constructor generates a tree from an LTS, and our
  fundamental destructor defines an LTS on game trees, where the
  possible "next state" associated to a move is the subtree
  corresponding to that move.

  We also define alternating simulations on LTS, which will correspond
  through the relational properties for the constructor and destructor
  to alternating refinement of game trees. *)


Hint Constructors psat.
Hint Unfold rel_compose.

Global Instance set_le_refl {A} (R : relation A) :
  Reflexive R ->
  Reflexive (set_le R).
Proof.
  firstorder.
Qed.


(** ** Complement of a boolean predicate *)

(** This will be needed to obtain the opposite polarity assignment
  when we define alternating simulations. Reversing polarity will
  yield the converse relation. *)

Definition opp {M} (p : M -> bool) :=
  fun m => negb (p m).

Lemma opp_invol {M} (p : M -> bool) :
  opp (opp p) = p.
Proof.
  apply functional_extensionality.
  intros m. unfold opp. destruct p; reflexivity.
Qed.

(** ** Elements of a relation *)

(** We will use the following type to construct transition systems
  over the elements of a bisimulation. *)

Record relement {A B} {R : rel A B} :=
  rpair {
    rfst : A;
    rsnd : B;
    rprf : R rfst rsnd;
  }.

Arguments relement {A B} R.
Arguments rpair {A B R} _ _ _.


(** * Transition systems *)

(** ** Definition *)

Definition lts (M A : Type) :=
  M -> relation A.

Module LTS.
  Section LTS.
  Context {M : Type}.

  (** ** Determinism *)

  (** A LTS is deterministic is there is at most one transition for
    each initial state and event. Game trees are defined using
    deterministic transistion systems. However, for convenience, we
    keep the property separate instead of baking it into the [lts]
    type, and only require it where necessary. *)

  Definition determ {A} (α : lts M A) : Prop :=
    forall m a a1 a2, α m a a1 -> α m a a2 -> a1 = a2.

  (** ** Morphisms *)

  (** A homomorphism of LTS is a mapping between their states that
    acts as a bisimulation in the following sense. That notion is used
    to characterize our fundamental constructor as the unique LTS
    homomorphism from the generating LTS into the LTS of game trees. *)

  Definition morphism {A B} (f : A -> B) (α : lts M A) (β : lts M B) :=
    (forall m a a', α m a a' -> β m (f a) (f a')) /\
    (forall m a b', β m (f a) b' -> exists a', f a' = b' /\ α m a a').

  Lemma morphism_id {A} (α : lts M A) :
    morphism id α α.
  Proof.
    firstorder.
  Qed.

  Lemma morphism_compose {A B C} α β γ (f : A -> B) (g : B -> C) :
    morphism f α β ->
    morphism g β γ ->
    morphism (compose g f) α γ.
  Proof.
    intros [Hab Hba] [Hbc Hcb]. split.
    - eauto.
    - intros.
      edestruct Hcb as (? & ? & ?); eauto; subst.
      edestruct Hba as (? & ? & ?); eauto; subst.
      unfold compose. eauto.
  Qed.

  (** ** Partial simulations *)

  (** More generally we can define a (forward) simulation diagram for
    LTS in as follows. We restrict the simulation to a given set of
    events, so that we can use [sim] for defining more complex
    alternating simulations below. *)

  Definition sim P {A B} (R : rel A B) : rel (lts M A) (lts M B) :=
    (psat P ++> R ++> set_le R).

  Global Instance sim_refl {A} P :
    @Reflexive (lts M A) (sim P eq).
  Proof.
    intros α m _ [Hm] a _ [].
    reflexivity.
  Qed.

  Lemma sim_compose {A B C} P (R : rel A B) (S : rel B C) α β γ :
    sim P R α β ->
    sim P S β γ ->
    sim P (rel_compose R S) α γ.
  Proof.
    intros Hαβ Hβγ m _ [Hm] a c (b & Hab & Hbc) a' Ha'.
    edestruct Hαβ as (b' & Hb' & Hab'); eauto.
    edestruct Hβγ as (c' & Hc' & Hbc'); eauto 10.
  Qed.

  Lemma sim_inter {A B} P (R1 R2 : rel A B) α β :
    sim P R1 α β ->
    sim P R2 α β ->
    determ β ->
    sim P (R1 /\ R2) α β.
  Proof.
    intros H1 H2 Hβ m _ [Hm] a b [Hab1 Hab2] a' Ha'.
    edestruct H1 as (b' & Hb1' & Hab1'); eauto.
    edestruct H2 as (xb' & Hb2' & Hab2'); eauto.
    assert (xb' = b') by eauto; subst.
    exists b'. split; eauto. rauto.
  Qed.

  (** ** Alternating simulations *)

  Definition ref {A B} (p : M -> bool) R : rel (lts M A) (lts M B) :=
    sim (fun m => p m = true) R /\
    flip (sim (fun m => p m = false) (flip R)).

  Global Instance ref_id {A} p :
    @Reflexive (lts M A) (ref p eq).
  Proof.
    split.
    - reflexivity.
    - replace (flip eq) with (@eq A).
      + reflexivity.
      + clear.
        apply functional_extensionality; intro x.
        apply functional_extensionality; intro y.
        apply prop_ext; split; congruence.
  Qed.

  Lemma ref_compose {A B C} p (R : rel A B) (S : rel B C) :
    ref p (rel_compose R S) =
    rel_compose (ref p R) (ref p S).
  Admitted.

  Lemma ref_inter {A B} p (R1 R2 : rel A B) α β :
    ref p R1 α β ->
    ref p R2 α β ->
    determ α ->
    determ β ->
    ref p (R1 /\ R2) α β.
  Proof.
    intros [Hαβ1 Hβα1] [Hαβ2 Hβα2] Hα Hβ.
    split; apply sim_inter; eauto.
  Qed.

  Lemma ref_flip {A B} p (R : rel A B) α β :
    ref (opp p) R β α ->
    ref p (flip R) α β.
  Proof.
    intros [Hβα Hαβ]. split; unfold flip in *.
    - intros m _ [Hm].
      apply Hαβ. constructor. unfold opp.
      destruct (p m); simpl; congruence.
    - intros m _ [Hm].
      apply Hβα. constructor. unfold opp.
      destruct (p m); simpl; congruence.
  Qed.

  (** ** Relational invariants *)

  Definition invr {A B} (R : rel A B) (α β : lts M _) :=
    forall m a b a' b', α m a a' -> β m b b' -> R a b -> R a' b'.

  (** For deterministic transition systems, any simulation relation is
    also a relational inveriant. *)

  Lemma ref_invr {A B} p (R : rel A B) (α β : lts M _) :
    ref p R α β ->
    determ α ->
    determ β ->
    invr R α β.
  Proof.
    intros [Hαβ Hβα] Hα Hβ m a b a' b' Ha' Hb' Hab.
    destruct (p m) eqn:Hm.
    - edestruct Hαβ as (xb' & Hxb' & Hab'); eauto.
      assert (xb' = b') by eauto. congruence.
    - edestruct Hβα as (xa' & Hxa' & Hab'); eauto. red in Hab'.
      assert (xa' = a') by eauto. congruence.
  Qed.

  Lemma invr_flip {A B} (R : rel A B) α β :
    invr R α β ->
    invr (flip R) β α.
  Proof.
    intros H m b a b' a' Hb' Ha' Hab.
    red in Hab |- *. eauto.
  Qed.

  (** Relational invariants are interesting because they can be used
    to strengthen simulations. *)

  Lemma invr_sim {A B} P (R R' : rel A B) (α β : lts M _) :
    sim P R α β ->
    invr R' α β ->
    sim P (R /\ R') α β.
  Proof.
    intros Hαβ HR' m _ [Hm] a b [Hab H'ab] a' Ha'.
    edestruct Hαβ as (b' & Hb' & Hab'); eauto.
    exists b'; split; eauto. split; eauto.
  Qed.

  Lemma invr_ref {A B} p (R R' : rel A B) (α β : lts M _) :
    ref p R α β ->
    invr R' α β ->
    ref p (R /\ R') α β.
  Proof.
    intros [Hαβ Hβα] HR'.
    split; apply invr_sim; eauto using invr_flip.
  Qed.

  (** ** Bisimulations *)

  Definition bisim {A B} (R : rel A B) : rel (lts M A) (lts M B) :=
    sim (fun _ => True) R /\
    flip (sim (fun _ => True) (flip R)).

  Lemma ref_bisim p {A B} (R : rel A B) α β :
    ref p R α β ->
    ref p (flip R) β α ->
    bisim R α β.
  Proof.
    intros [Hαβ Hβα] [Hβα' Hαβ']. unfold flip in *.
    split.
    - intros m _ [_].
      destruct (p m) eqn:Hpm; eauto.
    - intros m _ [_].
      destruct (p m) eqn:Hpm; eauto.
  Qed.

  Lemma ref_bisim_inter p {A B} (R1 R2 : rel A B) (α β : lts M _) :
    LTS.ref p R1 α β ->
    LTS.ref (opp p) R2 α β ->
    LTS.determ α ->
    LTS.determ β ->
    LTS.bisim (R1 /\ R2) α β.
  Proof.
    intros.
    eapply ref_bisim.
    - apply invr_ref; eauto.
      eapply ref_invr; eauto.
    - apply ref_flip.
      (* prove /\ commut. *)
  Admitted.

  (** ** Pairing transition systems *)

  (** Given a relation [R] and transition systems over its domain and
    codomain, we can construct a joint transition system over the
    elements of [R]. *)

  Definition pair {A B} R (α : lts M A) (β : lts M B) : lts M (relement R) :=
    fun m => (α m @@ rfst /\ β m @@ rsnd)%rel.

  (** If [R] is a bisimulation for [α] and [β], then the projections
    are LTS homomorphisms. This will be useful for proving
    extensionality from the categorical definition of trees. *)

  Lemma rfst_morphism {A B} (R : rel A B) (α β : lts M _) :
    LTS.sim (fun _ => True) R α β ->
    LTS.morphism rfst (pair R α β) α.
  Proof.
    intros Hαβ.
    split.
    - clear. firstorder.
    - intros m [a b Hab] a' Ha'.
      edestruct Hαβ as (b' & Hb' & Hab'); eauto.
      exists (rpair a' b' Hab'). simpl.
      unfold pair. split; rauto.
  Qed.

  Lemma rsnd_morphism {A B} (R : rel A B) (α β : lts M _) :
    LTS.sim (fun _ => True) (flip R) β α ->
    LTS.morphism rsnd (pair R α β) β.
  Proof.
    intros Hβα.
    split.
    - clear. firstorder.
    - intros m [a b Hab] b' Hb'.
      edestruct Hβα as (a' & Ha' & Hab'); eauto.
      exists (rpair a' b' Hab'). simpl.
      unfold pair. split; rauto.
  Qed.

  (** ** Lattice *)

  Definition bot (p : M -> bool) : lts M unit :=
    fun m _ _ => p m = false.

  Lemma bot_determ (α : lts M unit) :
    determ α.
  Proof.
    intros _ _ [] [] _ _.
    reflexivity.
  Qed.

  Lemma bot_ref {A} p (α : lts M A) :
    ref p ⊤ (bot p) α.
  Proof.
    unfold ref, sim, bot. split.
    - intros m _ [Hm] [] a _ [] H. congruence.
    - intros m _ [Hm] a [] _ a' H. exists tt; split; eauto. rauto.
  Qed.

  Definition sup {A} (p : M -> bool) (δ : lts M A) : lts M (A -> Prop) :=
    fun m sA sA' =>
      (forall a', sA' a' <-> exists a, sA a /\ δ m a a') /\
      if p m then
        (exists a, sA a /\ exists a', δ m a a')
      else
        (forall a, sA a -> exists a', δ m a a').

  Lemma sup_determ {A} (p : M -> bool) (δ : lts M A) :
    determ (sup p δ).
  Proof.
    intros m s s1 s2 [Hs1 _] [Hs2 _].
    apply functional_extensionality. intros a'.
    apply prop_ext. etransitivity.
    - eauto.
    - symmetry. eauto.
  Qed.

  Lemma sup_ub {A} (p : M -> bool) (δ : lts M A) :
    ref p (fun a sA => sA a) δ (sup p δ).
  Proof.
    split.
    - intros m _ [Hm] a sA H a' Ha'.
      exists (fun a' => exists a, sA a /\ δ m a a'). split; eauto.
      split.
      + reflexivity.
      + rewrite Hm. eauto.
    - intros m _ [Hm] sA a Ha sA' [HsA' ?]. unfold flip in *. rewrite Hm in H.
      edestruct H as [a' Ha']; eauto.
      exists a'. split; eauto.
      apply HsA'. eauto.
  Qed.

  Lemma sup_lub {A B} (p : M -> bool) R (α : lts M A) (β : lts M B) :
    ref p R α β ->
    determ α ->
    determ β ->
    ref p (fun sA b => forall a, impl (sA a) (R a b)) (sup p α) β.
  Proof.
    intros [Hαβ Hβα] Hα Hβ.
    split.
    - intros m _ [Hm] sA b Hab sA' [HsA' H].
      rewrite Hm in H. destruct H as (a & Ha & a' & Ha').
      unfold impl in Hab.
      edestruct Hαβ as (b' & Hb' & Hab'); eauto.
      exists b'. split; eauto.
      intros a2' Ha2'. apply HsA' in Ha2'.
      destruct Ha2' as (a2 & Ha2 & Ha2').
      edestruct Hαβ with (x0 := a2) as (b2' & Hb2' & Hab2'); eauto.
      assert (b2' = b') by eauto. congruence.
    - unfold flip, impl in *.
      intros m _ [Hm] b sA Hab b' Hb'.
      exists (fun a' => exists a, sA a /\ α m a a'). split; [split | ].
      + reflexivity.
      + rewrite Hm. intros a Ha.
        edestruct Hβα as (a' & Ha' & Hab'); simpl; eauto.
      + intros a' (a & Ha & Ha').
        edestruct Hβα as (a2' & Ha2' & Hab2'); simpl; eauto.
        assert (a2' = a') by eauto. congruence.
  Qed.

  End LTS.

  (** ** Traces *)

  Inductive star {M A} (δ : lts M A) : lts (list M) A :=
    | star_nil a :
        star δ nil a a
    | star_cons m ms a a' a'' :
        δ m a a' ->
        star δ ms a' a'' ->
        star δ (m :: ms) a a''.

  Program Definition traces {M A} (δ : lts M A) (a : A) : pcst M :=
    fun u => ex (star δ u a).
  Next Obligation.
    split.
    - exists a. constructor.
    - intros u m [a' Ha']. revert a a' Ha'.
      induction u.
      + intros. exists a. constructor.
      + intros. inversion Ha'; clear Ha'; subst.
        edestruct IHu as [x Hx]; eauto.
        eexists. econstructor; eauto.
  Qed.

  Lemma traces_has_child {M A} (δ : lts M A) a m :
    has_child (traces δ a) m <-> exists a', δ m a a'.
  Proof.
    simpl. split.
    - intros (a' & Ha'). inversion Ha'. eauto.
    - intros (a' & Ha'). eexists. econstructor; eauto. constructor.
  Qed.

  Lemma traces_subtree {M A} (δ : lts M A) a m a' :
    determ δ ->
    δ m a a' ->
    subtree (traces δ a) m = traces δ a'.
  Proof.
    intros Hδ Ha'.
    apply pcst_eq. intros u. simpl. split.
    - intros [Hu | [a'' Ha'']].
      + subst. eexists. constructor.
      + inversion Ha''; clear Ha''; subst.
        exists a''. assert (a' = a'0) by eauto. congruence.
    - intros [a'' Ha''].
      right. exists a''. econstructor; eauto.
  Qed.

End LTS.
