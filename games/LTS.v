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

  Definition sim (P : M -> Prop) {A B} (R : rel A B) : rel (lts M A) (lts M B) :=
    fun α β =>
      forall m, P m ->
      forall a b, R a b ->
      forall a', α m a a' ->
      exists b', β m b b' /\ R a' b'.

  Global Instance sim_refl {A} P :
    @Reflexive (lts M A) (sim P eq).
  Proof.
    intros α m Hm a _ []. eauto.
  Qed.

  Lemma sim_compose {A B C} P (R : rel A B) (S : rel B C) α β γ :
    sim P R α β ->
    sim P S β γ ->
    sim P (rel_compose R S) α γ.
  Proof.
    intros Hαβ Hβγ m Hm a c (b & Hab & Hbc) a' Ha'.
    edestruct Hαβ as (b' & Hb' & Hab'); eauto.
    edestruct Hβγ as (c' & Hc' & Hbc'); eauto 10.
  Qed.

  Lemma sim_inter {A B} P (R1 R2 : rel A B) α β :
    sim P R1 α β ->
    sim P R2 α β ->
    determ β ->
    sim P (R1 /\ R2) α β.
  Proof.
    intros H1 H2 Hβ m Hm a b [Hab1 Hab2] a' Ha'.
    edestruct H1 as (b' & Hb1' & Hab1'); eauto.
    edestruct H2 as (xb' & Hb2' & Hab2'); eauto.
    assert (xb' = b') by eauto; subst.
    exists b'. split; eauto. rauto.
  Qed.

  (** ** Alternating simulations *)

  Definition ref {A B} (p : M -> bool) (R : rel A B) : rel (lts M A) (lts M B) :=
    fun α β =>
      forall m a b, R a b ->
      if p m then
        (forall a', α m a a' -> exists b', β m b b' /\ R a' b')
      else
        (forall b', β m b b' -> exists a', α m a a' /\ R a' b').

  Lemma sim_ref {A B} p (R : rel A B) α β :
    sim (fun m => p m = true) R α β ->
    sim (fun m => p m = false) (flip R) β α ->
    ref p R α β.
  Proof.
    intros Ht Hf m. unfold flip in *.
    destruct p eqn:Hm; eauto.
  Qed.

  Lemma ref_sim {A B} p (R : rel A B) α β :
    ref p R α β ->
    sim (fun m => p m = true) R α β /\
    sim (fun m => p m = false) (flip R) β α.
  Proof.
    intros H. unfold ref, flip in *.
    split; intros m Hm; specialize (H m); rewrite Hm in H; eauto.
  Qed.

  Global Instance ref_id {A} p :
    @Reflexive (lts M A) (ref p eq).
  Proof.
    intros α.
    apply sim_ref.
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
    intros H1 H2 Hα Hβ m.
    apply ref_sim in H1 as [Hαβ1 Hβα1].
    apply ref_sim in H2 as [Hαβ2 Hβα2].
    apply sim_ref; apply sim_inter; eauto.
  Qed.

  Lemma ref_flip {A B} p (R : rel A B) α β :
    ref (opp p) R β α ->
    ref p (flip R) α β.
  Proof.
    intros H. apply ref_sim in H as [Hβα Hαβ].
    apply sim_ref; unfold flip in *.
    - intros m Hm.
      apply Hαβ. unfold opp.
      destruct (p m); simpl; congruence.
    - intros m Hm.
      apply Hβα. unfold opp.
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
    intros H Hα Hβ m a b a' b' Ha' Hb' Hab. specialize (H m).
    destruct (p m).
    - edestruct H as (xb' & Hxb' & Hab'); simpl; eauto.
      assert (xb' = b') by eauto. congruence.
    - edestruct H as (xa' & Hxa' & Hab'); simpl; eauto.
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
    intros Hαβ HR' m Hm a b [Hab H'ab] a' Ha'.
    edestruct Hαβ as (b' & Hb' & Hab'); eauto.
    exists b'; split; eauto. split; eauto.
  Qed.

  Lemma invr_ref {A B} p (R R' : rel A B) (α β : lts M _) :
    ref p R α β ->
    invr R' α β ->
    ref p (R /\ R') α β.
  Proof.
    intros H HR'. apply ref_sim in H as [Hαβ Hβα].
    apply sim_ref; apply invr_sim; eauto using invr_flip.
  Qed.

  (** ** Bisimulations *)

  Definition bisim {A B} (R : rel A B) : rel (lts M A) (lts M B) :=
    fun α β =>
      forall m a b, R a b ->
        (forall a', α m a a' -> exists b', β m b b' /\ R a' b') /\
        (forall b', β m b b' -> exists a', α m a a' /\ R a' b').

  Global Instance bisim_sim P {A B} (R : rel A B) :
    Related (bisim R) (sim P R) subrel.
  Proof.
    firstorder.
  Qed.

  Global Instance bisim_sim_subrel_params:
    Params (@sim) 2.

  Lemma bisim_flip {A B} (R : rel A B) α β :
    bisim R α β ->
    bisim (flip R) β α.
  Proof.
    unfold flip. firstorder.
  Qed.

  Lemma ref_bisim p {A B} (R : rel A B) α β :
    ref p R α β ->
    ref p (flip R) β α ->
    bisim R α β.
  Proof.
    intros H1 H2 m. specialize (H1 m). specialize (H2 m). unfold flip in *.
    destruct p; eauto.
  Qed.

  Lemma ref_bisim_inter p {A B} (R1 R2 : rel A B) (α β : lts M _) :
    ref p R1 α β ->
    ref (opp p) R2 α β ->
    determ α ->
    determ β ->
    bisim (R1 /\ R2) α β.
  Proof.
    intros H1 H2 Hα Hβ.
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
      edestruct Hαβ as (b' & Hb' & Hab'); simpl; eauto.
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
      edestruct Hβα as (a' & Ha' & Hab'); simpl; eauto.
      exists (rpair a' b' Hab'). simpl.
      unfold pair. split; rauto.
  Qed.

  (** ** Lattice *)

  (** *** Bottom *)

  (** The bottom element for a polarity assignment [p] simply produces
    all possible outputs forever, using a trivial transition system. *)

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
    unfold ref, sim, bot.
    intros m [] a _. destruct p.
    - congruence.
    - intros a' H. exists tt; split; eauto. rauto.
  Qed.

  (** *** Supremum *)

  (** For a transition system [δ], the transition system [sup δ] can
    generate the supremum of a set of states. There will be an output
    whenever at least on state in the set produces that output, and an
    input when all states in the set produce that input. *)

  Inductive sup {A} (p : M -> bool) (δ : lts M A) (m : M) sA : _ -> Prop :=
    sup_intro :
      match p m with
        | true  => exists a, sA a /\ exists a', δ m a a'
        | false => forall a, sA a -> exists a', δ m a a'
      end ->
      sup p δ m sA (fun a' => exists a, sA a /\ δ m a a').

  Lemma sup_determ {A} (p : M -> bool) (δ : lts M A) :
    determ (sup p δ).
  Proof.
    intros m s _ _ [_] [_].
    reflexivity.
  Qed.

  Lemma sup_ub {A} (p : M -> bool) (δ : lts M A) :
    ref p (fun a sA => sA a) δ (sup p δ).
  Proof.
    apply sim_ref.
    - intros m Hm a sA H a' Ha'.
      eexists. split.
      + constructor. rewrite Hm. eauto.
      + simpl. eauto.
    - intros m Hm sA a Ha _ [H]. unfold flip in *. rewrite Hm in H.
      edestruct H as [a' Ha']; eauto.
  Qed.

  Lemma sup_lub {A B} (p : M -> bool) R (α : lts M A) (β : lts M B) :
    ref p R α β ->
    determ α ->
    determ β ->
    ref p (fun sA b => forall a, impl (sA a) (R a b)) (sup p α) β.
  Proof.
    intros H Hα Hβ. apply ref_sim in H as [Hαβ Hβα].
    apply sim_ref.
    - intros m Hm sA b Hab _ [H].
      rewrite Hm in H. destruct H as (a & Ha & a' & Ha').
      unfold impl in Hab.
      edestruct Hαβ as (b' & Hb' & Hab'); simpl; eauto.
      exists b'. split; eauto.
      intros a2' (a2 & Ha2 & Ha2').
      edestruct Hαβ with (a := a2) as (b2' & Hb2' & Hab2'); simpl; eauto.
      assert (b2' = b') by eauto. congruence.
    - unfold flip, impl in *.
      intros m Hm b sA Hab b' Hb'.
      eexists; split.
      + constructor. rewrite Hm. intros a Ha.
        edestruct Hβα as (a' & Ha' & Hab'); simpl; eauto.
      + intros a' (a & Ha & Ha').
        edestruct Hβα as (a2' & Ha2' & Hab2'); simpl; eauto.
        assert (a2' = a') by eauto. congruence.
  Qed.

  (** [sup] can also be used to determinize a transition system. In
    that case, the following refinement relation can be used between
    the non-deterministic transition systems, to establish [set_le R]
    as a refinement relation between the determinized systems. *)

  Definition nref {A B} (p: M -> bool) (R: rel A B) : rel (lts M A) (lts M B) :=
    fun α β =>
      forall m a b,
        R a b ->
        if p m then
          forall a', α m a a' -> exists b', β m b b' /\ R a' b'
        else
          forall x, β m b x ->
            (exists a', α m a a') /\
            (forall a', α m a a' -> exists b', β m b b' /\ R a' b').

  Lemma sup_nref {A B} p R (α : lts M A) (β : lts M B):
    nref p R α β ->
    ref p (set_le R) (LTS.sup p α) (LTS.sup p β).
  Proof.
    intros Hαβ m sA sB Hs.
    specialize (Hαβ m).
    destruct p eqn:Hm.
    - intros _ [H]. rewrite Hm in H. destruct H as (a & Ha & a' & Ha').
      eexists; split.
      + constructor. rewrite Hm.
        edestruct Hs as (b & Hb & Hab); eauto.
        edestruct Hαβ as (b' & Hb' & Hab'); eauto.
      + clear a Ha a' Ha'.
        intros a' (a & Ha & Ha').
        edestruct Hs as (b & Hb & Hab); eauto.
        edestruct Hαβ as (b' & Hb' & Hab'); eauto.
    - intros _ [HsB]. rewrite Hm in HsB.
      eexists; split.
      + constructor. rewrite Hm.
        intros a Ha.
        edestruct Hs as (b & Hb & Hab); eauto.
        eapply HsB in Hb as [x Hx].
        eapply Hαβ; eauto.
      + intros a' (a & Ha & Ha').
        edestruct Hs as (b & Hb & Hab); eauto.
        edestruct HsB as (x & Hx); eauto.
        edestruct Hαβ as [_ H]; eauto. clear x Hx.
        edestruct H as (b' & Hb' & Hab'); eauto.
  Qed.

  (** For deterministic transition systems, [sup] of a singleton is
    the original thing. *)

  Lemma sup_singleton {A} p (α : lts M A) :
    determ α ->
    bisim (fun sA a => sA = eq a) (sup p α) α.
  Proof.
    intros Hα m sA a H. subst.
    split.
    - intros _ [Hstep].
      assert (exists a', α m a a') as [a' Ha'].
      {
        destruct p.
        + destruct Hstep as (xa & Hxa & a' & Ha'). subst xa. eauto.
        + apply Hstep. eauto.
      }
      eexists; split; eauto.
      apply functional_extensionality; intro x.
      apply prop_ext. split; intro.
      + destruct H as (xa & Hxa & Hx). subst. eauto.
      + subst. eauto.
    - intros a' Ha'. eexists; split.
      + constructor. destruct p; intros; subst; eauto.
      + eapply functional_extensionality; intros x.
        eapply prop_ext; split; intros; subst; eauto.
        destruct H as (xa & Hxa & Ha); subst xa. eauto.
  Qed.

  (** Hence [sup] is idempotent in the following sense. *)

  Lemma sup_idemp {A} p (α : lts M A) :
    bisim (fun ssA sA => ssA = eq sA) (sup p (sup p α)) (sup p α).
  Proof.
    eapply sup_singleton.
    eapply sup_determ.
  Qed.

  (** We can also show that [sup] preserves bisimulations. *)

  Notation set_rel R := (set_le R /\ set_ge R)%rel.

  Lemma bisim_sup_sim {A B} p R (α : lts M A) (β : lts M B) :
    bisim R α β ->
    sim (fun _ => True) (set_rel R) (LTS.sup p α) (LTS.sup p β).
  Proof.
    intros H m Hm sA sB [HsAB HsBA].
    intros _ [H'].
    eexists; split.
    + constructor. destruct p.
      * destruct H' as (a & Ha & a' & Ha').
        edestruct HsAB as (b & Hb & Hab); eauto.
        specialize (H m a b) as [Hαβ Hβα]; eauto.
        edestruct Hαβ as (b' & Hb' & Hab'); eauto.
      * intros b Hb.
        edestruct HsBA as (a & Ha & Hab); eauto.
        specialize (H m a b) as [Hαβ Hβα]; eauto.
        edestruct H' as (a' & Ha'); eauto.
        edestruct Hαβ as (b' & Hb' & Hab'); eauto.
    + split.
      * intros a' (a & Ha & Ha').
        edestruct HsAB as (b & Hb & Hab); eauto.
        specialize (H m a b) as [Hαβ Hβα]; eauto.
        edestruct Hαβ as (b' & Hb' & Hab'); eauto.
      * intros b' (b & Hb & Hb').
        edestruct HsBA as (a & Ha & Hab); eauto.
        specialize (H m a b) as [Hαβ Hβα]; eauto.
        edestruct Hβα as (a' & Ha' & Hab'); eauto.
  Qed.

  Lemma sup_bisim {A B} p R (α : lts M A) (β : lts M B) :
    LTS.bisim R α β ->
    LTS.bisim (set_rel R) (LTS.sup p α) (LTS.sup p β).
  Proof.
    intros H m sA sB Hs.
    split.
    - eapply bisim_sup_sim; eauto.
    - intros.
      assert (HH: forall x y, set_rel (flip R) x y = set_rel R y x) by admit.
      rewrite <- HH in Hs.
      setoid_rewrite <- HH.
      eapply bisim_sup_sim; eauto.
      eapply LTS.bisim_flip; eauto.
  Admitted.

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
