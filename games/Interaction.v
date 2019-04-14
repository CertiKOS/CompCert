Require Import LogicalRelations.
Require Import Axioms.
Require Import ClassicalFacts.
Require Import List.
Require Import KLR.
Axiom prop_ext : prop_extensionality.

Local Obligation Tactic := cbn; eauto.

(** Following the usual approach, we formalize strategies as
  prefix-closed sets of odd-length traces. To make it possible to
  define strategies in compositional and operational ways,
  we encapsulate this construction in the *interaction* monad
  [I_{M,N}] defined in this library. *)

(** * The interaction monad *)

Module Behavior.

  (* The interaction monad models a computation which may interact with
    its environment. The computation can perform an output [m : M],
    at which point it will be suspended until an input [n : N] is
    received from the environment. This is modeled by the operation:

        interact : M -> I_{M,N}(N).

    Additionally, to model specifications which permit a range of
    possible behaviors, we allow non-deterministic strategies.
    Consequently, the interaction monad is equipped with a complete
    refinement lattice, which we extend with a distinguished greatest
    element:

        undef : I_{M,N}(A),

    modelling a computation whose behavior is undefined.

    Finally, we model non-deterministic iteration with the operator:

        iter : (A -> I_{M,N}(A)) -> (A -> I_{M,N}(A)).

    Notably, [iter] is different from the Kleene star associated with
    the refinement lattice because we account for silent divergence as
    a specific behavior, incomparable with terminating computations,
    rather than identifying it with the unsatisfiable specification ⊥.

    Using the interaction monad, alternating strategies for the game
    [G = (M_O, M_P)], where [O] is expected to make the first move,
    can be modelled as computations of type:

        M_O -> I_{M_P, M_O}(∅).

   *)

  (** ** Traces *)

  (** The traces we will consider are essentially odd-length sequences
    of moves. In order to support the monadic structure and to account
    for undefined behaviors and silent divergence, we extend them with
    the distinguished, terminal moves [v : A], [div] and [undef].
    Any trace is considered a prefix of [undef]. *)

  Inductive trace {M N A} :=
    | val (a : A)
    | div
    | undef
    | move (m : M)
    | tcons (m : M) (n : N) (t : trace).

  Arguments trace : clear implicits.

  Inductive prefix {M N A} : relation (trace M N A) :=
    | val_prefix v : prefix (val v) (val v)
    | div_prefix : prefix div div
    | undef_prefix t : prefix t undef
    | move_prefix m : prefix (move m) (move m)
    | tcons_prefix m n s t : prefix s t -> prefix (tcons m n s) (tcons m n t)
    | move_tcons_prefix m n t : prefix (move m) (tcons m n t).

  Hint Constructors prefix.

  Global Instance prefix_po M N A :
    PreOrder (@prefix M N A).
  Proof.
    split.
    - intro t. induction t; constructor; eauto.
    - intros t1 t2 t3 H12 H23. revert t1 H12.
      induction H23; eauto; inversion 1; subst; eauto.
  Qed.

  (** ** Computations *)

  (** An interactive computation is a prefix-closed set of traces.
    Note that since any trace is a prefix of [undef], a computation
    which admits a trace ending with [undef] will also admit all
    possible defined interactions sharing the same initial segment. *)

  Record t {M N A} :=
    {
      has : trace M N A -> Prop;
      closed s t : has t -> prefix s t -> has s;
    }.

  Arguments t : clear implicits.
  Hint Extern 1 (has _) => eapply closed; [assumption | ].

  (** Refinement is defined as trace containement. *)

  Definition ref {M N A} : relation (t M N A) :=
    fun x y => forall t, has x t -> has y t.

  Global Instance has_ref :
    Monotonic (@has) (forallr -, forallr -, forallr -, ref ++> prefix --> impl).
  Proof.
    repeat rstep. intro. eauto using closed.
  Qed.

  (** With some axioms, we get extensional equality for interactive
    computations. *)

  Global Instance ref_antisym M N A :
    Antisymmetric _ eq (@ref M N A).
  Proof.
    intros [x Hx] [y Hy] Hxy Hyx.
    cut (x = y). { intro. subst. f_equal. apply proof_irr. }
    red in Hxy, Hyx; cbn in *.
    apply functional_extensionality; intro t.
    apply prop_ext; firstorder.
  Qed.

  (** ** Monad operations *)

  (** *** Definition *)

  (** The monad's unit associate to each value [v] the computation
    with a single trace [val v]. *)

  Program Definition ret {M N A} (v : A) : t M N A :=
    {| has := eq (val v) |}.
  Next Obligation.
    intros. subst. inversion H0; auto.
  Qed.

  (** The Kleisli extension [bind] corresponds to the sequential
    composition of a computation [x : I_{M,N}(A)] and a continuation
    [f : A -> I_{M,N}(B)]. The result is in [I_{M,N}(B)] and contains
    the traces of [x], where traces ending in [val v] have been
    concatenated with traces in [f(v)]. *)

  Section BIND.
    (* Context {M N A B} (f : A -> trace M N B -> Prop) (x : trace M N A -> Prop).
    Context (Hf : forall a s t, f a t -> prefix s t -> f a s).
    Context (Hx : forall s t, x t -> prefix s t -> x s). *)
    Context {M N A B} (f : A -> t M N B) (x : t M N A).

    (* We first define the result of concatenating a single trace with
      the continuation [f]. *)

    Inductive bind_trace : trace M N A -> trace M N B -> Prop :=
      | bind_val a t :
          has (f a) t ->
          bind_trace (val a) t
      | bind_div :
          bind_trace div div
      | bind_undef t :
          bind_trace undef t
      | bind_move m :
          bind_trace (move m) (move m)
      | bind_tcons m n s t :
          bind_trace s t ->
          bind_trace (tcons m n s) (tcons m n t).

    Hint Constructors bind_trace.

    Lemma bind_trace_closed s t t' :
      bind_trace s t ->
      prefix t' t ->
      exists s', bind_trace s' t' /\ prefix s' s.
    Proof.
      intros Ht Ht'.
      revert t' Ht'; induction Ht; intros;
      inversion Ht'; clear Ht'; subst; eauto 6 using closed.
      edestruct IHHt as (s' & Ht' & Hs'); eauto.
    Qed.

    (** Now [bind] is straightforward to define. *)

    Program Definition bind :=
      {| has t := exists s, has x s /\ bind_trace s t |}.
    Next Obligation.
      intros s t (u & Hu & Hut) Hst.
      edestruct @bind_trace_closed as (s' & Ht' & Hs'); eauto using closed.
    Qed.

    (*
    Definition bind_has (t : trace M N B) : Prop :=
      exists s, x s /\ bind_trace s t.

    Lemma bind_has_closed (t' t : trace M N B) :
      bind_has t ->
      prefix t' t ->
      bind_has t'.
    Proof.
      intros (s & Hs & Hst) Ht. red.
      edestruct @bind_trace_closed as (s' & Ht' & Hs'); eauto using closed.
    Qed.
     *)

  End BIND.

  Hint Constructors bind_trace.
  Notation "x >>= f" := (bind f x) (at level 40, left associativity).

  (** *** Properties *)

  Lemma ret_bind {M N A B} (f : A -> t M N B) (a : A) :
    bind f (ret a) = f a.
  Proof.
    apply antisymmetry.
    - intros t (s & [ ] & Hst). cbn in *. subst.
      inversion Hst. congruence.
    - intros t Ht. cbn.
      exists (val a). intuition auto.
  Qed.

  Lemma bind_ret {M N A} (x : t M N A) :
    bind ret x = x.
  Proof.
    apply antisymmetry.
    - intros t (s & Hs & Hst). revert x Hs.
      cut (prefix t s); eauto using closed.
      induction Hst; intros; eauto using closed.
      + destruct H. auto.
    - intros t Ht. cbn.
      exists t. intuition auto. clear.
      induction t; constructor; cbn; eauto.
  Qed.

  Lemma bind_bind {M N A B C} (f : B -> t M N C) (g : A -> t M N B) x :
    bind (fun a => bind f (g a)) x = bind f (bind g x).
  Proof.
    apply antisymmetry.
    - intros t (s & Hs & Hst). cbn.
      revert Hs. generalize (has x). clear x.
      induction Hst; intros.
      + destruct H as (u & Hu & Hut).
        exists u. cbn. intuition auto.
        exists (val a). intuition auto.
      + repeat (exists div; split; [auto | constructor]).
      + repeat (exists undef; split; [auto | constructor]).
      + repeat (exists (move m); split; [auto | constructor]).
      + edestruct (IHHst (fun t => P (tcons m n t))) as (v & Hv & Hvt); auto.
        clear s Hs Hst IHHst.
        destruct Hv as (u & Hu & Huv).
        exists (tcons m n v). intuition auto.
        exists (tcons m n u). intuition auto.
    - intros t (v & (u & Hu & Huv) & Hvt).
      exists u. intuition auto. clear x Hu.
      revert t Hvt; induction Huv; intros.
      + constructor. cbn. eauto.
      + inversion Hvt; clear Hvt; subst; eauto.
      + constructor.
      + inversion Hvt; clear Hvt; subst; eauto.
      + inversion Hvt; clear Hvt; subst; eauto.
  Qed.

  (** ** Relator *)

  (** *** Definition *)

  (** The relator associated with [I_{M,N}] generalizes [ref] by
    extending a relation on values [R] to a relation on computations
    [I_{M,N}(R)]. This yields a notion of simulation asserting that if
    the first computation terminates with a value [a], then after an
    identical interaction the second computation will also terminate
    with a value [b] such that [R a b]. *)

  Inductive trace_rel M N {A B} (R: rel A B) : rel (trace M N A) (trace M N B) :=
    | val_rel a b :
        R a b ->
        trace_rel M N R (val a) (val b)
    | div_rel :
        trace_rel M N R div div
    | undef_rel s :
        trace_rel M N R s undef
    | move_rel m :
        trace_rel M N R (move m) (move m)
    | tcons_rel m n ta tb :
        trace_rel M N R ta tb ->
        trace_rel M N R (tcons m n ta) (tcons m n tb).

  Hint Constructors trace_rel.

  Definition r M N {A B} (R : rel A B) : rel (t M N A) (t M N B) :=
    set_le (trace_rel M N R) @@ has.

  (** *** Properties of [trace_rel] *)

  Global Instance trace_subrel M N A B :
    Monotonic (@trace_rel M N A B) (subrel ++> subrel).
  Proof.
    intros R1 R2 HR u v Huv.
    induction Huv; constructor; eauto.
  Qed.

  Global Instance trace_subrel_params :
    Params (@trace_rel) 3.

  Global Instance trace_rel_refl {M N A} (R : relation A) :
    Reflexive R ->
    Reflexive (trace_rel M N R).
  Proof.
    intros HR t.
    induction t; constructor; eauto.
  Qed.

  Global Instance trace_rel_compose {M N A B C} RAB RBC RAC :
    @RCompose A B C RAB RBC RAC ->
    RCompose (trace_rel M N RAB) (trace_rel M N RBC) (trace_rel M N RAC).
  Proof.
    intros HR ta tb tc Htab Htbc. revert tc Htbc.
    induction Htab; intros; inversion Htbc; clear Htbc; subst; constructor.
    - ercompose; eauto.
    - eauto.
  Qed.

  (** In addition to the standard properties above, we can show that
    [trace_rel] is compatible with [bind_trace]. *)

  Global Instance bind_trace_rel :
    Monotonic
      (@bind_trace)
      (forallr - @ M, forallr - @ N, forallr RA, forallr RB,
        (RA ++> r M N RB) ++> trace_rel M N RA ++> set_le (trace_rel M N RB)).
  Proof.
    intros M N A1 A2 RA B1 B2 RB f1 f2 Hf u1 u2 Hu v1 Hv1.
    revert u2 Hu; induction Hv1; intros;
    inversion Hu; clear Hu; subst; eauto.
    - edestruct Hf as (? & ? & ?); eauto.
    - edestruct IHHv1 as (? & ? & ?); eauto.
  Qed.

  (** *** Properties of [r] *)

  (** We can use the properties of [trace_rel] to establish that [r]
    is a monad relator in the following sense. *)

  Global Instance r_subrel {M N A B} :
    Monotonic (@r M N A B) (subrel ++> subrel).
  Proof.
    unfold r. rauto.
  Qed.

  Global Instance r_subrel_params :
    Params (@r_subrel) 3.

  Global Instance r_refl {M N A} (R : relation A) :
    Reflexive R ->
    Reflexive (r M N R).
  Proof.
    unfold r. typeclasses eauto.
  Qed.

  Global Instance r_compose {M N A B C} RAB RBC RAC :
    @RCompose A B C RAB RBC RAC ->
    RCompose (r M N RAB) (r M N RBC) (r M N RAC).
  Proof.
    unfold r. typeclasses eauto.
  Qed.

  Global Instance has_r :
    Monotonic
      (@has)
      (forallr - @ M, forallr - @ N, forallr R,
       r M N R ++> set_le (trace_rel M N R)).
  Proof.
    firstorder.
  Qed.

  Global Instance ret_r :
    Monotonic
      (@ret)
      (forallr - @ M, forallr - @ N, forallr R, R ++> r M N R).
  Proof.
    unfold r. repeat rstep.
    intros _ [ ]. cbn. eauto.
  Qed.

  Global Instance bind_r :
    Monotonic
      (@bind)
      (forallr - @ M, forallr - @ N, forallr RA, forallr RB,
        (RA ++> r M N RB) ++> r M N RA ++> r M N RB).
  Proof.
    intros M N A1 A2 RA B1 B2 RB f1 f2 Hf x1 x2 Hx t1 (s1 & Hs1 & Hst1). cbn.
    edestruct has_r as (s2 & Hs2 & Hs); eauto.
    edestruct bind_trace_rel as (t2 & Ht2 & Ht); eauto.
  Qed.

  (** *** Properties of [ref] *)

  (** Note that [ref] corresponds to the special case [I_{M,N}(=)].
    This allows us use the relator properties to show that [ref] is a
    preorder. *)

  Lemma ref_r M N A :
    @ref M N A = r M N eq.
  Proof.
    apply functional_extensionality; intro a.
    apply functional_extensionality; intro b.
    apply prop_ext. split.
    - intros Hab t Ht.
      exists t. split; eauto. reflexivity.
    - intros Hab t Ht.
      edestruct Hab as (t' & Ht' & H); eauto.
      eapply closed; eauto.
      clear - H. induction H; subst; eauto.
  Qed.

  Global Instance ref_r_eqrel M N A :
    Related (@ref M N A) (r M N eq) eqrel.
  Proof.
    red. rewrite ref_r. reflexivity.
  Qed.

  Global Instance r_ref_subrel M N A :
    Related (r M N eq) (@ref M N A) subrel.
  Proof.
    red. rewrite ref_r. reflexivity.
  Qed.

  Global Instance ref_refl M N A :
    Reflexive (@ref M N A).
  Proof.
    rewrite ref_r. typeclasses eauto.
  Qed.

  Global Instance ref_trans M N A :
    Transitive (@ref M N A).
  Proof.
    rewrite ref_r. typeclasses eauto.
  Qed.

  (** ** Lattice structure *)

  Program Definition bot {M N A} : t M N A :=
    {| has t := False |}.

  Program Definition top {M N A} : t M N A :=
    {| has t := True |}.

  Program Definition join {M N A} (x1 x2 : t M N A) : t M N A :=
    {| has t := has x1 t \/ has x2 t |}.
  Next Obligation.
    intuition eauto using closed.
  Qed.

  Program Definition meet {M N A} (x1 x2 : t M N A) : t M N A :=
    {| has t := has x1 t /\ has x2 t |}.
  Next Obligation.
    intuition eauto using closed.
  Qed.

  Program Definition sup {M N A I} (x : I -> t M N A) : t M N A :=
    {| has t := exists i, has (x i) t |}.
  Next Obligation.
    intros M N A I x s t (i & Ht) Hst.
    exists i. eauto using closed.
  Qed.

  Program Definition inf {M N A I} (x : I -> t M N A) : t M N A :=
    {| has t := forall i, has (x i) t |}.
  Next Obligation.
    intros M N A I x s t Ht Hst.
    intros i. eauto using closed.
  Qed.

  Lemma bot_ref {M N A} (x : t M N A) :
    ref bot x.
  Proof.
    firstorder.
  Qed.

  Lemma top_ref {M N A} (x : t M N A) :
    ref x top.
  Proof.
    firstorder.
  Qed.

  Lemma join_ub_l {M N A} (x y : t M N A) :
    ref x (join x y).
  Proof.
    firstorder.
  Qed.

  Lemma join_ub_r {M N A} (x y : t M N A) :
    ref y (join x y).
  Proof.
    firstorder.
  Qed.

  Lemma join_lub {M N A} (x y z : t M N A) :
    ref x z ->
    ref y z ->
    ref (join x y) z.
  Proof.
    firstorder.
  Qed.

  Global Instance join_ref :
    Monotonic (@join) (forallr -, forallr -, forallr -, ref ++> ref ++> ref).
  Proof.
    firstorder.
  Qed.

  Lemma meet_lb_l {M N A} (x y : t M N A) :
    ref (meet x y) x.
  Proof.
    firstorder.
  Qed.

  Lemma meet_lb_r {M N A} (x y : t M N A) :
    ref (meet x y) y.
  Proof.
    firstorder.
  Qed.

  Lemma meet_glb {M N A} (x y z : t M N A) :
    ref x y ->
    ref x z ->
    ref x (meet y z).
  Proof.
    firstorder.
  Qed.

  Global Instance meet_ref :
    Monotonic (@meet) (forallr -, forallr -, forallr -, ref ++> ref ++> ref).
  Proof.
    firstorder.
  Qed.

  Lemma sup_ub {M N A I} (x : I -> t M N A) :
    forall i, ref (x i) (sup x).
  Proof.
    firstorder.
  Qed.

  Lemma sup_lub {M N A I} (x : I -> t M N A) y :
    (forall i, ref (x i) y) -> ref (sup x) y.
  Proof.
    firstorder.
  Qed.

  Global Instance sup_ref :
    Monotonic
      (@sup)
      (forallr -, forallr -, forallr -, forallr -, (- ==> ref) ++> ref).
  Proof.
    firstorder.
  Qed.

  Lemma inf_lb {M N A I} (x : I -> t M N A) :
    forall i, ref (inf x) (x i).
  Proof.
    firstorder.
  Qed.

  Lemma inf_glb {M N A I} x (y : I -> t M N A) :
    (forall i, ref x (y i)) -> ref x (inf y).
  Proof.
    firstorder.
  Qed.

  Global Instance inf_ref :
    Monotonic
      (@inf)
      (forallr -, forallr -, forallr -, forallr -, (- ==> ref) ++> ref).
  Proof.
    firstorder.
  Qed.

  (** *** Extension to Kleisli morphisms *)

  Definition zero {M N A B} : A -> t M N B :=
    fun a => bot.

  Definition plus {M N A B} (f g : A -> t M N B) :=
    fun a => join (f a) (g a).

  Definition sum {M N A B I} (f : I -> A -> t M N B) :=
    fun a => sup (fun i => f i a).

  Definition comp {M N A B C} (f : A -> t M N B) (g : B -> t M N C) :=
    fun a => bind g (f a).

  Lemma comp_ret {M N A B} (f : A -> t M N B) :
    comp f ret = f.
  Proof.
    apply functional_extensionality; intro a.
    apply bind_ret.
  Qed.

  Lemma ret_comp {M N A B} (f : A -> t M N B) :
    comp ret f = f.
  Proof.
    apply functional_extensionality; intro a.
    apply ret_bind.
  Qed.

  Lemma comp_comp {M N A B C D} (f : A -> t M N B) (g : B -> _ C) (h : C -> _ D):
    comp (comp f g) h = comp f (comp g h).
  Proof.
    apply functional_extensionality; intro a.
    symmetry. apply bind_bind.
  Qed.

  (** ** Joins distribute over bind *)

  Lemma bind_join {M N A B} (x y : t M N A) (f : A -> t M N B) :
    bind f (join x y) = join (bind f x) (bind f y).
  Proof.
    apply antisymmetry; firstorder.
  Qed.

  Lemma bind_sup {M N A B I} (x : I -> t M N A) (f : A -> t M N B) :
    bind f (sup x) = sup (fun i => bind f (x i)).
  Proof.
    apply antisymmetry; firstorder.
  Qed.

  Lemma bind_trace_plus {M N A B} (f g : A -> t M N B) s t :
    bind_trace (plus f g) s t ->
    bind_trace f s t \/ bind_trace g s t.
  Proof.
    induction 1; firstorder.
  Qed.

  Lemma bind_trace_sum {M N A B I} (f : I -> A -> t M N B) s t :
    inhabited I ->
    bind_trace (sum f) s t ->
    exists i, bind_trace (f i) s t.
  Proof.
    intros [i].
    induction 1; try solve [exists i; firstorder].
    - destruct H. eauto.
    - destruct IHbind_trace. eauto.
  Qed.

  Lemma bind_plus {M N A B} (x : t M N A) (f g : A -> t M N B) :
    bind (plus f g) x = join (bind f x) (bind g x).
  Proof.
    apply antisymmetry.
    - intros t (s & Hs & Hst).
      apply bind_trace_plus in Hst as [Hst | Hst]; firstorder.
    - eapply join_lub; repeat rstep; rewrite <- ref_r; subst; firstorder.
  Qed.

  Lemma bind_sum {M N A B I} (f : I -> A -> t M N B) (x : t M N A) :
    inhabited I ->
    bind (sum f) x = sup (fun i => bind (f i) x).
  Proof.
    intros HI.
    apply antisymmetry.
    - intros t (s & Hs & Hst).
      apply bind_trace_sum in Hst as [i Hst]; firstorder.
    - eapply sup_lub; intro. repeat rstep. rewrite <- ref_r. subst. firstorder.
  Qed.

  (** ** Iteration *)

  Section REPEAT.
    Context {M N A} (f : A -> t M N A).

    CoInductive diverges (a : A) : Prop :=
      | diverges_val a' :
          has (f a) (val a') ->
          diverges a' ->
          diverges a
      | diverges_undef :
          has (f a) undef ->
          diverges a.

    Inductive repeat_has (a : A) : trace M N A -> Prop :=
      | repeat_refl :
          repeat_has a (val a)
      | repeat_step s t :
          repeat_has a s ->
          bind_trace f s t ->
          repeat_has a t
      | repeat_div :
          diverges a ->
          repeat_has a div.

    Hint Constructors repeat_has.

    Program Definition repeat (a : A) : t M N A :=
      {| has := repeat_has a |}.
    Next Obligation.
      intros a s t Ht Hs. revert s Hs.
      induction Ht; intros.
      - inversion Hs; clear Hs; subst; eauto.
      - edestruct @bind_trace_closed as (? & ? & ?); eauto.
      - inversion Hs; clear Hs; subst; eauto.
    Qed.
  End REPEAT.

  Global Instance diverges_r :
    Monotonic
      (@diverges)
      (forallr - @ M, forallr - @ N, forallr R, (R ++> r M N R) ++> R ++> impl).
  Proof.
    intros M N A B R f g Hfg. cofix IH. intros a b Hab H.
    destruct H as [a' Ha' H | ].
    - edestruct Hfg as (s & Hs & Has); eauto.
      inversion Has; clear Has; subst.
      + eapply diverges_val; eauto. eapply IH; eauto.
      + eapply diverges_undef; eauto.
    - edestruct Hfg as (s & Hs & Has); eauto.
      inversion Has; clear Has; subst.
      eapply diverges_undef; eauto.
  Qed.

  Global Instance repeat_r :
    Monotonic
      (@repeat)
      (forallr -@M, forallr -@N, forallr R, (R ++> r M N R) ++> R ++> r M N R).
  Proof.
    intros M N A B R f g Hfg x y Hxy u Hu.
    induction Hu; intros.
    - exists (val y); intuition eauto. constructor.
    - edestruct IHHu as (s' & Hs' & Hss'); eauto.
      edestruct bind_trace_rel as (t' & Ht' & Htt'); eauto.
      exists t'; intuition eauto. econstructor; eauto.
    - exists div; intuition eauto. constructor.
      revert H. rauto.
  Qed.

  (** ** Misc. *)

  Program Definition guard {M N} (P : Prop) : t M N unit :=
    {| has t := P /\ t = val tt |}.
  Next Obligation.
    intros M N P s t [H Ht] Hst. subst. intuition auto.
    inversion Hst; auto.
  Qed.

  Program Definition filter {M N A} (P : A -> Prop) (a : A) : t M N A :=
    {| has t := P a /\ t = val a |}.
  Next Obligation.
    intros M N A P a s t [H Ht] Hst. subst. intuition auto.
    inversion Hst; auto.
  Qed.

  Lemma filter_ret {M N A} P a :
    @ref M N A (filter P a) (ret a).
  Proof.
    intros t [Ha Ht]; subst.
    constructor.
  Qed.

  Program Definition diverge {M N A} : t M N A :=
    {| has := eq div |}.
  Next Obligation.
    intros; subst. inversion H0; auto.
  Qed.

  (** ** Interaction *)

  Program Definition interact {M N} (m : M) : t M N N :=
    {| has t := t = move m \/ exists n, t = tcons m n (val n) |}.
  Next Obligation.
    intros M N m u v Hv Huv.
    destruct Hv as [Hv | [n Hv]]; subst.
    - inversion Huv; subst; eauto.
    - inversion Huv; subst; eauto. inversion H1; subst; eauto.
  Qed.

  (** XXX bad no divergence *)

  (*
  Section SUBST.
    Context {A B C D X : Type} (f : A -> t C D B).

    Fixpoint subst_trace (s : trace A B X) : t C D X :=
      match s with
        | val x => ret x
        | move m => f m >>= fun _ => bot
        | div => diverge
        | undef => top
        | tcons m n t' =>
          f m >>= filter (eq n) >>= fun _ => subst_trace t'
      end.

    Program Definition subst (x : t A B X) :=
      {| has t := exists s, has x s /\ has (subst_trace s) t |}.
    Next Obligation.
      intros x s t (u & Hu & Ht) Hst.
      eauto using closed.
    Qed.

  End SUBST.

  Lemma bind_bot {M N A} (x : t M N A) :
    ref (x >>= fun _ => bot) x.
  Proof.
    (* rewrite <- (bind_ret x) at 2. rstep. *)
    intros t (s & Hs & Hst). revert Hs.
    cut (prefix t s); eauto using closed.
    induction Hst; eauto.
    inversion H.
  Qed.

  Lemma subst_interact {M N P Q} (m : M) (f : M -> t P Q N) :
    subst f (interact m) = (f m).
  Proof.
    apply antisymmetry.
    - intros t (s & Hs & Hst).
      destruct Hs as [Hs | (n & Hs)]; subst.
      + unfold subst_trace in Hst.
        eapply bind_bot; eauto.
      + unfold subst_trace in Hst.
        admit.
    - intros s Hs.
      simpl.
      admit.
  Admitted.
   *)


  (** ** Interaction (§3.6) *)

  Program Definition delta {M N A} (x : t M N A) (m : M) (n : N) : t M N A :=
    {| has t := has x (tcons m n t) |}.
  Next Obligation.
    eauto using closed.
  Qed.

  Global Instance delta_ref :
    Monotonic (@delta) (forallr -,forallr -,forallr -, ref ++> - ==> - ==> ref).
  Proof.
    firstorder.
  Qed.

  Lemma delta_bind {M N A B} (x : t M N A) (m : M) (n : N) (f : A -> t M N B) :
    ref (delta x m n >>= f) (delta (x >>= f) m n).
  Proof.
    intros t (s & Hs & Hst). cbn in *.
    exists (tcons m n s). intuition eauto.
  Qed.

  Lemma delta_join {M N A} (x y : t M N A) (m : M) (n : N) :
    delta (join x y) m n = join (delta x m n) (delta y m n).
  Proof.
    apply antisymmetry; firstorder.
  Qed.

  Lemma delta_meet {M N A} (x y : t M N A) (m : M) (n : N) :
    delta (meet x y) m n = meet (delta x m n) (delta y m n).
  Proof.
    apply antisymmetry; firstorder.
  Qed.

  Program Definition choose {M N A} (P : A -> Prop) : t M N A :=
    {| has t := exists a, P a /\ t = val a |}.
  Next Obligation.
    intros M N A P s t (a & Ha & Ht) Hst. subst.
    inversion Hst; eauto.
  Qed.

  Definition next_move {M N P Q A} (x : t M N A) : t P Q M :=
    choose (fun m => has x (move m)).

  Inductive rho_has {M N P Q A} (x : t M N A) : trace P Q A -> Prop :=
    | rho_val v : has x (val v) -> rho_has x (val v)
    | rho_div : has x div -> rho_has x div
    | rho_undef t : has x undef -> rho_has x t.

  Hint Constructors rho_has.

  Program Definition rho {M N P Q A} (x : t M N A) : t P Q A :=
    {| has := rho_has x |}.
  Next Obligation.
    destruct 1; inversion 1; subst; constructor; eauto using closed.
  Qed.

  Lemma rho_decr {M N A} (x : t M N A) :
    ref (rho x) x.
  Proof.
    destruct 1; eauto using closed.
  Qed.

  Lemma decompose {M N A} (x : t M N A) :
    x = join (rho x) (next_move x >>= fun m => interact m >>= delta x m).
  Proof.
    apply antisymmetry.
    - intros t Ht. simpl.
      destruct t; eauto 10.
      + right. exists (val m). intuition eauto.
        constructor. simpl. eauto.
      + right. exists (val m). intuition eauto using closed.
        constructor. simpl. eauto.
        exists (tcons m n (val n)). intuition eauto.
    - apply join_lub.
      + apply rho_decr.
      + intros t (s & (m & Hm & Hs) & Hst); subst.
        inversion Hst; clear Hst; subst. simpl in H0.
        destruct H0 as (? & [? | (? & ?)] & Hst); subst.
        * inversion Hst; auto.
        * inversion Hst; clear Hst; subst.
          inversion H3; clear H3; subst.
          simpl in H0. auto.
  Qed.

  Definition subst_step {M N P Q A} (f : M -> t P Q N) (x : t M N A) :=
    next_move x >>= fun m => f m >>= fun n => ret (delta x m n).

  Definition subst {M N P Q A} (f : M -> t P Q N) (x : t M N A) :=
    repeat (subst_step f) x >>= rho.


  (** ** Abstraction (trace relation) *)

  Section ABS.
    Context {Ma Mc Na Nc Xa Xc} (gamma : rel (trace Ma Na Xa) (trace Mc Nc Xc)).

    Program Definition abs (x : t Mc Nc Xc) : t Ma Na Xa :=
      {|
        has t := forall ta tc, gamma ta tc -> prefix ta t -> has x tc
      |}.
    Next Obligation.
      intros y s t Ht Hst ta tc Htac Hsta.
      eapply Ht; eauto. etransitivity; eauto.
    Qed.

    Program Definition concr (y : t Ma Na Xa) : t Mc Nc Xc :=
      {|
        has t := exists ta tc, gamma ta tc /\ prefix t tc /\ has y ta;
      |}.
    Next Obligation.
      intros x s t (ta & tc & Htac & Ht & Hta) Hst.
      exists ta, tc. intuition auto. etransitivity; eauto.
    Qed.

    Lemma abs_concr_galois x y :
      ref (concr x) y <-> ref x (abs y).
    Proof.
      split.
      - intros Hxy t Ht ta tc Htac Htat.
        eapply Hxy.
        exists ta, tc. intuition eauto using closed. reflexivity.
      - intros Hxy t (ta & tc & Htac & Ht & Hta).
        rewrite Ht.
        eapply Hxy; eauto. reflexivity.
    Qed.

    Instance concr_ref :
      Monotonic concr (ref ++> ref).
    Proof.
      intros x y Hxy.
      apply abs_concr_galois.
      transitivity y; auto.
      apply abs_concr_galois.
      reflexivity.
    Qed.

    Lemma concr_join x y :
      concr (join x y) = join (concr x) (concr y).
    Proof.
      apply antisymmetry.
      - apply abs_concr_galois; apply join_lub; apply abs_concr_galois.
        + apply join_ub_l.
        + apply join_ub_r.
      - apply join_lub; rstep.
        + apply join_ub_l.
        + apply join_ub_r.
    Qed.
  End ABS.

  (** ** Abstraction (KLR) *)

  Lemma has_ret {M N A} (x : t M N A) (a : A) :
    has x (val a) -> ref (ret a) x.
  Proof.
    intros Ha t [ ]. auto.
  Qed.

  Section SIM.
    Context {W : Type}.
    Context {M1 M2} (RM : klr W M1 M2).
    Context {N1 N2} (RN : klr W N1 N2).
    Context {A B} (R : rel A B).

    Inductive pull_has (x2 : t M2 N2 B) : trace M1 N1 A -> Prop :=
      | pull_val a b :
          has x2 (val b) ->
          R a b ->
          pull_has x2 (val a)
      | pull_div :
          has x2 div ->
          pull_has x2 div
      | pull_undef t :
          has x2 undef ->
          pull_has x2 t
      | pull_move w m1 m2 :
          has x2 (move m2) ->
          RM w m1 m2 ->
          pull_has x2 (move m1)
      | pull_tcons w m1 m2 n1 t1 :
          has x2 (move m2) ->
          RM w m1 m2 ->
          (forall n2, RN w n1 n2 -> pull_has (delta x2 m2 n2) t1) ->
          pull_has x2 (tcons m1 n1 t1).

    Lemma pull_has_undef_inv y t :
      pull_has y undef -> has y t.
    Proof.
      inversion 1; eauto using closed.
    Qed.

    Hint Constructors pull_has.
    Hint Resolve pull_has_undef_inv.

    Program Definition pull (x2 : t M2 N2 B) :=
      {| has := pull_has x2 |}.
    Next Obligation.
      intros x2 s t Ht Hst. revert s Hst.
      induction Ht; intros; eauto;
      inversion Hst; clear Hst; subst; eauto.
    Qed.

    Global Instance pull_ref :
      Monotonic (@pull) (ref ++> ref).
    Proof.
      intros x y Hxy t Ht.
      revert y Hxy. cbn in *.
      induction Ht; intros; eauto.
      eapply pull_tcons; eauto.
      intros n2 Hn.
      edestruct H2; eauto.
      eapply delta_ref; eauto.
    Qed.

    Lemma join_pull x y:
      ref (join (pull x) (pull y)) (pull (join x y)).
    Proof.
      eapply join_lub; rstep; auto using join_ub_l, join_ub_r.
    Qed.

    Lemma pull_top :
      pull top = top.
    Proof.
      apply antisymmetry; auto using top_ref.
      intros t _. simpl.
      apply pull_undef. firstorder.
    Qed.

    (*
      It would be satisfying to have a Galois adjoint for pull,
      but it's not clear to me how to define it at the moment.
      It's also possible that the asymmetry in non-determinism
      (we have P non-det but not O) prevents this. One step
      to ascertain this would be to try to show that pull
      preserves joins (which seems plausible), in which case
      an adjoint exists and can be defined implicitely.
      It would also be interesting thing to consider the behavior
      of pull(R^-1).

    Inductive push_has w (x1 : t M1 N1 A) : trace M2 N2 B -> Prop :=
      | push_val b :
          (forall a, R w a b -> has x1 (val a)) ->
          push_has w x1 (val b)
      | push_div :
          has x1 div ->
          push_has w x1 div
      | push_undef t :
          has x1 undef ->
          push_has w x1 t
      | push_move m2 :
          (forall w' m1, w ~> w' -> RM w' m1 m2 -> has x1 (move m1)) ->
          push_has w x1 (move m2)
      | push_tcons m2 n2 t2 :
          (forall w' m1, w  ~> w' -> RM w' m1 m2 ->
           has x1 (move m1) /\
           exists w'' n1, w' ~> w'' /\ RN w'' n1 n2 /\
           push_has w'' (delta x1 m1 n1) t2) ->
          push_has w x1 (tcons m2 n2 t2).

    Fixpoint push_has w (x1 : t M1 N1 A) (t2 : trace M2 N2 B) : Prop :=
      has x1 undef \/
      match t2 with
        | val b => forall a, R w a b -> has x1 (val a)
        | div => has x1 div
        | undef => False
        | move m2 =>
          forall w' m1, w ~> w' -> RM w' m1 m2 -> has x1 (move m1)
        | tcons m2 n2 t2 =>
          forall w' m1, w ~> w' -> RM w' m1 m2 -> has x1 (move m1) /\
          exists w'' n1, w ~> w'' /\ RN w'' n1 n2 /\ push_has w (delta x1 m1 n1) t2
      end.

    Lemma push_undef_has w x1 t2 :
      has x1 undef -> push_has w x1 t2.
    Proof.
      destruct t2; left; eauto.
    Qed.

    Hint Resolve push_undef_has.

    Program Definition push w (x1 : t M1 N1 A) :=
      {| has := push_has w x1 |}.
    Next Obligation.
      intros w x1 s t Ht Hst. revert x1 Ht.
      induction Hst; intros; eauto;
      destruct Ht as [? | Ht]; eauto.
      - destruct Ht.
      - right. intros.
        edestruct Ht as (Hm1 & w'' & n1 & Hw'' & Hn & Ht'); eauto 10.
      - right. intros.
        edestruct Ht as (Hm1 & _); eauto.
    Qed.

    Lemma pull_meet w x2 y2 :
      pull w (meet x2 y2) = meet (pull w x2) (pull w y2).
    Proof.
      apply antisymmetry.
      - apply meet_glb; rstep; auto using meet_lb_l, meet_lb_r.
      - intros t [Hxt Hyt]. cbn in Hxt, Hyt |- *.
        induction Hxt; inversion Hyt; clear Hyt; subst;
          try solve [eauto].
        eapply pull_val; simpl; eauto.


    Lemma pull_join w x2 y2 :
      pull w (join x2 y2) = join (pull w x2) (pull w y2).
    Proof.
      apply antisymmetry.
      - remember (join x2 y2) as z2.
        intros t Ht. cbn in Ht |- *. revert x2 y2 Heqz2.
        induction Ht; intros; subst; try solve [destruct H; eauto].
        destruct H as [H|H].
        + left. eapply pull_tcons; eauto.
          setoid_rewrite delta_join in H2. cbn in H2.
          intros. change (has (pull w'' (delta x0 m2 n2)) t1).
          erewrite join_ub_l.
        + subst x2. destruct H; eauto.
          *)

    Definition sim : rel (t M1 N1 A) (t M2 N2 B) :=
      fun x y => ref x (pull y).

    Lemma pull_ret b :
      pull (ret b) = choose (fun a => R a b).
    Proof.
    Admitted.

  End SIM.

  Global Instance pull_ref_params :
    Params (@pull) 1.

  Instance kf_unit : KripkeFrame unit unit :=
    { acc l w w' := True }.

  Lemma pull_eq {M N A} (x : t M N A) :
    pull (W:=unit) (k eq) (k eq) eq x = x.
  Proof.
    apply antisymmetry.
    - intros t Ht. cbn in Ht.
      induction Ht; unfold k in *; subst; cbn in *; eauto using closed.
    - intros t. revert x.
      induction t; intros; unfold k in *; try solve [ econstructor; eauto ].
      + apply pull_move with tt m; cbn; auto.
      + apply pull_tcons with tt m; cbn; eauto using closed.
        intros; subst.
        apply IHt. cbn. auto.
  Qed.

    Hint Constructors pull_has.
    Hint Resolve pull_has_undef_inv.

  Lemma sim_r M N {A B} (R : rel A B) :
    eqrel (sim (W:=unit) (k eq) (k eq) R) (r M N R).
  Proof.
    split.
    - intros x y Hxy t Ht.
      apply Hxy in Ht; clear x Hxy.
      induction Ht; unfold k in *; subst; eauto.
      cbn in H2. edestruct H2 as (s & Hs & Hst); eauto.
    - intros x y Hxy t Ht.
      apply Hxy in Ht as (s & Hs & Hst); clear x Hxy. unfold k; cbn.
      revert y Hs. assert (tt ~> tt) by constructor.
      induction Hst; intros; eauto.
      + eapply pull_move; eauto. constructor.
      + eapply pull_tcons; eauto using closed. constructor.
        intros; subst. eauto.
  Qed.

  Section SIM_PROP.
    Context `{Wkf : KripkeFrame unit}.

    Global Instance ret_sim :
      Monotonic
        (@ret)
        (forallr RM, forallr RN, forallr R, R ++> sim (W:=W) RM RN R).
    Proof.
      intros M1 M2 RM N1 N2 RN A B R a b Hab _ [ ].
      eapply pull_val; cbn; eauto.
    Qed.

    Global Instance bind_sim :
      Monotonic
        (@bind)
        (forallr RM, forallr RN, forallr RA, forallr RB,
           (RA ++> sim (W:=W) RM RN RB) ++> sim RM RN RA ++> sim RM RN RB).
    Proof.
      intros M1 M2 RM N1 N2 RN A1 A2 RA B1 B2 RB f1 f2 Hf x1 x2 Hx.
      intros t1 (s1 & Hs1 & Hst1). revert x1 x2 Hx Hs1.
      induction Hst1; intros; eauto.
      - apply Hx in Hs1. inversion Hs1; clear Hs1; subst.
        + assert (ref (pull RM RN RB (f2 b)) (pull RM RN RB (x2 >>= f2))).
          transitivity (pull RM RN RB (ret b >>= f2)).
          * rewrite ret_bind. reflexivity.
          * apply has_ret in H1. repeat rstep.
            subst. reflexivity.
          * rewrite <- H0.  eauto.
            eapply Hf; eauto.
        + repeat (econstructor; eauto).
      - apply Hx in Hs1. inversion Hs1; clear Hs1; subst.
        + repeat (econstructor; eauto).
        + eapply pull_div; eauto. econstructor; eauto.
      - apply Hx in Hs1. inversion Hs1; clear Hs1; subst.
        repeat (econstructor; eauto).
      - apply Hx in Hs1. inversion Hs1; clear Hs1; subst.
        + repeat (econstructor; eauto).
        + eapply pull_move; eauto. econstructor; eauto.
      - apply Hx in Hs1. inversion Hs1; clear Hs1; subst.
        + repeat (econstructor; eauto).
        + eapply pull_tcons; eauto. econstructor; eauto.
          intros.
          change (has (pull RM RN RB (delta (x2 >>= f2) m2 n2)) t0).
          cut (has (pull RM RN RB (delta x2 m2 n2 >>= f2)) t0); eauto.
          repeat rstep. apply delta_bind.
          eapply IHHst1; eauto.
          2: instantiate (1 := pull RM RN RA (delta x2 m2 n2)); cbn; eauto.
          red. reflexivity.
    Qed.

    Global Instance interact_sim :
      Monotonic
        (@interact)
        (forallr RM, forallr RN, |= RM ++> k1 (sim (W:=W) RM RN) RN).
    Proof.
      intros M1 M2 RM N1 N2 RN w m1 m2 Hm.
      intros t [Ht | [n1 Ht]]; subst; cbn.
      - eapply pull_move; cbn; eauto.
      - eapply pull_tcons; cbn; eauto.
        intros n2 Hn.
        eapply pull_val; cbn; eauto.
    Qed.

    Global Instance join_sim :
      Monotonic
        (@join)
        (forallr RM : klr W, forallr RN : klr W, forallr RX : rel,
         sim RM RN RX ++> sim RM RN RX ++> sim RM RN RX).
    Proof.
      intros M1 M2 RM N1 N2 RN X1 X2 RX.
      intros x1 x2 Hx y1 y2 Hy. unfold sim in *.
      rewrite Hx, Hy. apply join_pull.
    Qed.

    Global Instance guard_sim :
      Monotonic
        (@guard)
        (forallr RM : klr W, forallr RN : klr W, impl ++> sim RM RN ⊤).
    Proof.
      intros M1 M2 RM N1 N2 RN P Q HPQ. unfold sim in *.
      intros t (H & Ht); subst.
      eapply pull_val. simpl. eauto. constructor.
    Qed.

    Global Instance choose_sim :
      Monotonic
        (@choose)
        (forallr RM : klr W, forallr RN : klr W, forallr RA,
         set_le RA ++> sim RM RN RA).
    Proof.
      intros M1 M2 RM N1 N2 RN A1 A2 RA P Q HPQ. unfold sim in *.
      intros t (a & Ha & Ht); subst.
      edestruct HPQ as (b & Hb & Hab); eauto.
      apply pull_val with b; eauto.
      firstorder.
    Qed.

    Context {M1 M2} (RM : klr W M1 M2).
    Context {N1 N2} (RN : klr W N1 N2).
    Context {X1 X2} (RX : rel X1 X2).

    Global Instance sim_ref :
      Monotonic
        (@sim _ M1 M2 RM N1 N2 RN X1 X2 RX)
        (ref --> ref ++> impl).
    Proof.
      unfold sim. repeat rstep. intro.
      etransitivity; eauto.
      etransitivity; eauto.
      rauto.
    Qed.

    Global Instance sim_ref_params :
      Params (@sim) 2.

    Lemma join_lub_sim x y z :
      sim RM RN RX x z ->
      sim RM RN RX y z ->
      sim RM RN RX (join x y) z.
    Proof.
      apply join_lub.
    Qed.

  End SIM_PROP.

End Behavior.

(** Notations for behavior specifications. *)

Notation beh M N A := (Behavior.t M N A).
Bind Scope behavior_scope with Behavior.t.
Delimit Scope behavior_scope with beh.

Notation "x >>= f" := (Behavior.bind f x) (at level 40, left associativity).
Infix "\/" := Behavior.join : behavior_scope.
Notation "0" := Behavior.zero : behavior_scope.
Notation "1" := Behavior.ret : behavior_scope.
Infix "+" := Behavior.plus : behavior_scope.
Infix "@" := Behavior.comp (at level 30, right associativity) : behavior_scope.
Notation "x ^ *" := (Behavior.repeat x) (at level 30) : behavior_scope.
