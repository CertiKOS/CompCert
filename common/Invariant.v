Require Import Coqlib.
Require Import Values.
Require Import AST.
Require Import Globalenvs.
Require Import Events.
Require Import LanguageInterface.
Require Import Smallstep.

(** Simulation proofs sometimes rely on invariants of the source
  and/or target languages, such as type preservation. The
  constructions defined below can be used to decouple these
  preservation and simulation proofs, and to introduce calling
  conventions characterizing the invariant at module boundaries. *)


(** * Invariants *)

(** ** Interface *)

(** First, we need to define a sort of "invariant interface", which
  will describe how a given invariant impacts the queries and replies
  of the language under consideration. *)

Record invariant {li: language_interface} :=
  {
    inv_state : Type;
    inv_init : inv_state;
    query_inv : inv_state -> inv_state -> query li -> Prop;
    reply_inv : inv_state -> inv_state -> reply li -> Prop;
  }.

Arguments invariant : clear implicits.

Section MKINV.
  Context {li} (QI: query li -> Prop) (RI: query li -> reply li -> Prop).

  Inductive query_mkinv : option (query li) -> option (query li) -> _ -> Prop :=
    query_mkinv_intro q : QI q -> query_mkinv None (Some q) q.

  Inductive reply_mkinv : option (query li) -> option (query li) -> _ -> Prop :=
    reply_mkinv_intro q r : RI q r -> reply_mkinv (Some q) None r.

  Definition mkinv :=
    {|
      inv_init := None;
      query_inv := query_mkinv;
      reply_inv := reply_mkinv;
    |}.
End MKINV.

(** As a core example, here is an invariant for the C language
  interface asserting that the queries and replies are well-typed. *)

Definition wt_c : invariant li_c :=
  mkinv
    (fun q => Val.has_type_list (cq_args q) (sig_args (cq_sg q)))
    (fun q r => Val.has_type (fst r) (proj_sig_res (cq_sg q))).

(** ** Preservation *)

(** A small step semantics preserves an externally observable
  invariant if the following properties hold. In addition to the
  invariant interfaces for the incoming function call ([IB]) and any
  outgoing external calls ([IA]), we specify a "state invariant" [SI]
  which will be estblished by the initial query and external call
  returns, preserved by internal steps, and ensure the invariant
  interface is respected at external calls and final states. *)

Definition cont_preserves {li A} I (SI: _ -> _ -> Prop) w (k: cont li A) :=
  forall w' q, query_inv I w w' q ->
  forall S s, k q = Some S -> S s -> SI w' s.

Record preserves {li} (L: semantics li) I (SI: _->_-> Prop) :=
  {
    preserves_step q s t s':
      SI q s ->
      Step L s t s' ->
      SI q s';
    preserves_initial_state:
      cont_preserves I SI (inv_init I) (initial_state L);
    preserves_final_state w s r k:
      SI w s ->
      final_state L s r k ->
      exists w',
        reply_inv I w w' r /\
        cont_preserves I SI w' k;
 }.

(** ** As calling conventions *)

(** Invariant interfaces are essentially a unary version of calling
  conventions, and can in fact be lifted into actual, binary calling
  conventions asserting that the source and target queries are
  identical, and furthermore satisfy the given invariant. *)

Coercion cc_inv {li} (I: invariant li): callconv li li :=
  {|
    cc_init := inv_init I;
    cc_query q1 q2 w w' := psat (query_inv I w w') q1 q2;
    cc_reply r1 r2 w w' := psat (reply_inv I w w') r1 r2;
|}.

(** With this, an invariant preservation proof can itself be lifted
  into a self-simulation by the invariant calling conventions. *)

Lemma preserves_fsim_cont {li A} (I: invariant li) (IS: _ -> A -> Prop) w k:
  cont_preserves I IS w k ->
  fsim_match_cont I (fun w => psat (IS w)) w k k.
Proof.
  intros Hk w' q _ [Hq].
  specialize (Hk w' q Hq).
  destruct (k q) as [S | ]; constructor.
  intros s Hs. exists s; split; auto.
  constructor; eauto.
Qed.

Lemma preserves_fsim {li} (L: semantics li) I IS:
  preserves L I IS ->
  forward_simulation (cc_inv I) L L.
Proof.
  intros HL.
  apply forward_simulation_step with (match_states := fun w => psat (IS w)).
  - auto.
  - apply preserves_fsim_cont.
    apply preserves_initial_state; auto.
  - intros w s _ r k [Hs] Hsk.
    edestruct @preserves_final_state as (w' & Hr & Hk); eauto.
    exists w', r, k. intuition auto.
    + constructor; auto.
    + apply preserves_fsim_cont; auto.
  - intros w s t s' Hstep _ [Hs].
    exists s'. split; eauto.
    constructor.
    eapply preserves_step; eauto.
Qed.


(** * Invariant-based simulation proof methods *)

(** Once we have established that the source or target language
  preserves an invariant of interest, we wish to use that fact to
  help prove the forward simulation for the pass being considered.

  The most basic way to do that is to add an assertion to the
  simulation relation that the states satisfy the invariant. Then,
  we rely on these assertions to prove a simulation step, and use the
  relevant preservation lemmas to establish them again for the
  successor states. This approach is workable and has been used in
  CompCert for typing invariants, but it is somewhat ad-hoc and
  becomes more involved when the interaction with the environment is
  involved in the invariant's preservation.

  Instead, we would like to formulate a weaker simulation diagram,
  where the invariant can be assumed on the current states but does
  not need to be established for the successor states, then show that
  if the language involved [preserves] the invariant (in the sense
  defined above), then this weakened diagram is sufficient to
  establish a forward simulation for the pass.

  The most straightforward way to do this would be to define a
  weakened version of [forward_simulation] along these lines, however
  this comes with its own pitfall: there already exists many lemmas
  one can use to establish a [forward_simulation] using simplified
  diagrams rather than the more complex, general form, and we would
  like to be able to use simplified diagrams for our weakened version
  as well. Under this approach, we would have to duplicate such lemmas
  for the weakened diagram. Instead, the method implemented below
  reuses [forward_simulation] and expresses the weakened diagram as a
  special case, making it possible to reuse all existing techniques to
  prove it.

  Since by definition, [forward_simulation] uses the same simulation
  relation for the current and successor states, we accomplish this by
  acting on the transition systems themselves:

    - for the source language, we can build a strengthened version of
      the transition system which restricts the transitions to states
      which statisfy the invariant;
    - for the target language, we can build a relaxed version of the
      transition system which adds arbitrary transitions from states
      which do not satisfy the invariant.

  Proving a simulation from the strengthened source semantics, and/or
  to the weakened target semantics, is easier because we have
  hypotheses that the states involved satify the invariant. At the
  same time, for an invariant-preserving language, we can easily show
  a simulation from the original to the strengthened version, and from
  the weakened to the original version, and these simulations can be
  composed with that proved by the user to obtain the desired one. *)

(** ** Strengthening the source semantics *)

Section RESTRICT.
  Context {li} (L: semantics li).
  Context (I: invariant li).
  Context (IS: inv_state I -> state L -> Prop).

  Inductive restrict_step ge: _ -> trace -> _ -> Prop :=
    restrict_step_intro w s t s':
      step L ge s t s' ->
      IS w s ->
      IS w s' ->
      restrict_step ge (w, s) t (w, s').

  Inductive restrict_states w q (S: state L -> Prop): _ * state L -> Prop :=
    restrict_states_intro w' s :
      S s ->
      query_inv I w w' q ->
      IS w' s ->
      restrict_states w q S (w', s).

  Definition restrict_cont w (k: cont li (state L)): cont li (_ * state L) :=
    fun q => option_map (restrict_states w q) (k q).

  Inductive restrict_final_state: _ * state L -> reply li -> cont _ _ -> Prop :=
    restrict_final_state_intro w w' s r k:
      final_state L s r k ->
      IS w s ->
      reply_inv I w w' r ->
      restrict_final_state (w, s) r (restrict_cont w' k).

  Definition restrict :=
    {|
      state := inv_state I * state L;
      genvtype := genvtype L;
      step := restrict_step;
      initial_state := restrict_cont (inv_init I) (initial_state L);
      final_state := restrict_final_state;
      globalenv := globalenv L;
      symbolenv := symbolenv L;
    |}.

  Let ms w s s' := (w, s) = s' /\ IS w s.

  Lemma restrict_fsim_cont w k:
    cont_preserves I IS w k ->
    fsim_match_cont I ms w k (restrict_cont w k).
  Proof.
    intros Hk w' q _ [Hq].
    specialize (Hk w' q Hq). unfold restrict_cont.
    destruct (k q) as [S | ]; constructor. intros s Hs.
    exists (w', s). unfold ms. intuition eauto.
    constructor; eauto.
  Qed.

  Lemma restrict_fsim:
    preserves L I IS ->
    forward_simulation I L restrict.
  Proof.
    intros HL.
    apply forward_simulation_step with (match_states := ms).
    - reflexivity.
    - apply restrict_fsim_cont.
      apply preserves_initial_state; auto.
    - intros xw xs [w s] r k [Hx Hws] Hsk. inversion Hx; clear Hx; subst.
      edestruct @preserves_final_state as (w' & Hr & Hk); eauto.
      exists w', r, (restrict_cont w' k). intuition idtac.
      + constructor; auto.
      + constructor; auto.
      + apply restrict_fsim_cont; auto.
    - intros q s t s' Hstep _ [[] Hqs].
      assert (IS q s') by (eapply preserves_step; eauto).
      exists (q, s'). split; constructor; eauto.
  Qed.
End RESTRICT.

(** ** Weakening the target semantics *)

Section EXPAND.
  Context {li} (L: semantics li).
  Context (I: invariant li).
  Context (IS: inv_state I -> state L -> Prop).

  Inductive expand_step ge: _ -> trace -> _ -> Prop :=
    expand_step_intro (W: _ -> Prop) s t s':
      (forall w, W w -> IS w s -> step L ge s t s') ->
      expand_step ge (W, s) t (W, s').

  Inductive expand_states (W: _ -> Prop) q (S: state L -> Prop): _ -> Prop :=
    expand_states_intro s:
      let W' w' := exists w, W w /\ query_inv I w w' q in
      (forall w w', W w -> query_inv I w w' q -> S s) ->
      expand_states W q S (W', s).

  Definition expand_cont W (k: cont li (state L)): cont li _ :=
    fun q => option_map (expand_states W q) (k q).

  Inductive expand_final_state: _ -> reply li -> _ -> Prop :=
    expand_final_state_intro (W: _ -> Prop) s r k:
      let W' w' := exists w, W w /\ reply_inv I w w' r in
      (forall w, W w -> IS w s -> final_state L s r k) ->
      expand_final_state (W, s) r (expand_cont W' k).

  Definition expand :=
    {|
      state := (inv_state I -> Prop) * state L;
      genvtype := genvtype L;
      step := expand_step;
      initial_state := expand_cont (eq (inv_init I)) (initial_state L);
      final_state := expand_final_state;
      globalenv := globalenv L;
      symbolenv := symbolenv L;
    |}.

  Let ms := fun w s s' => fst s w /\ snd s = s' /\ IS w s'.

  Lemma expand_fsim_cont (W: _ -> Prop) w k:
    W w ->
    cont_preserves I IS w k ->
    fsim_match_cont I ms w (expand_cont W k) k.
  Proof.
    intros Hw Hk w' q _ [Hq].
    specialize (Hk w' q Hq). unfold expand_cont.
    destruct (k q) as [S | ]; constructor. intros _ [s W' Hs].
    exists s. unfold ms, W'. simpl. eauto 10.
  Qed.

  Lemma expand_fsim:
    preserves L I IS ->
    forward_simulation I expand L.
  Proof.
    intros HL.
    apply forward_simulation_step with (match_states := ms).
    - reflexivity.
    - eapply expand_fsim_cont; eauto.
      eapply preserves_initial_state; auto.
    - intros w ws s r k (Hw & Hws & Hs) Hsk.
      destruct Hsk as [W xs r k W' Hsk]. simpl in *. subst xs W'.
      edestruct @preserves_final_state as (w' & Hr & Hk); eauto.
      exists w', r, k. intuition eauto.
      + constructor; eauto.
      + apply expand_fsim_cont; eauto.
    - intros w ws t ws' Hstep s (Hw & Hws & Hs).
      destruct Hstep as [W xs t s' Hstep]. simpl in *. subst.
      exists s'. unfold ms. intuition eauto.
      eapply preserves_step; eauto.
  Qed.
End EXPAND.
