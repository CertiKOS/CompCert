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
    query_inv : query li -> Prop;
    reply_inv : query li -> reply li -> Prop;
  }.

Arguments invariant : clear implicits.

(** As a core example, here is an invariant for the C language
  interface asserting that the queries and replies are well-typed. *)

Definition wt_c : invariant li_c :=
  {|
    query_inv q := Val.has_type_list (cq_args q) (sig_args (cq_sg q));
    reply_inv q r := Val.has_type (fst r) (proj_sig_res (cq_sg q));
  |}.

(** ** Preservation *)

(** A small step semantics preserves an externally observable
  invariant if the following properties hold. In addition to the
  invariant interfaces for the incoming function call ([IB]) and any
  outgoing external calls ([IA]), we specify a "state invariant" [SI]
  which will be estblished by the initial query and external call
  returns, preserved by internal steps, and ensure the invariant
  interface is respected at external calls and final states. *)

Record preserves {li} (L: semantics li) IA IB (SI: _->_-> Prop) :=
  {
    preserves_step q s t s':
      SI q s ->
      Step L s t s' ->
      SI q s';
    preserves_initial_state q s:
      query_inv IB q ->
      initial_state L q s ->
      SI q s;
    preserves_external q s qA:
      SI q s ->
      at_external L s qA ->
      query_inv IA qA /\
      forall rA s',
        reply_inv IA qA rA ->
        after_external L s rA s' ->
        SI q s';
    preserves_final_state q s r:
      SI q s ->
      final_state L s r ->
      reply_inv IB q r;
  }.

(** ** As calling conventions *)

(** Invariant interfaces are essentially a unary version of calling
  conventions, and can in fact be lifted into actual, binary calling
  conventions asserting that the source and target queries are
  identical, and furthermore satisfy the given invariant. *)

Inductive rel_inv {A} (I: A -> Prop) (x: A): A -> Prop :=
  rel_inv_intro: I x -> rel_inv I x x.

Coercion cc_inv {li} (I: invariant li): callconv li li :=
  {|
    ccworld := query li;
    match_senv q := eq;
    match_query q q1 q2 := query_inv I q /\ q1 = q /\ q2 = q;
    match_reply q := rel_inv (reply_inv I q);
  |}.

(** With this, an invariant preservation proof can itself be lifted
  into a self-simulation by the invariant calling conventions. *)

Lemma preserves_fsim {li} (L: semantics li) IA IB IS:
  preserves L IA IB IS ->
  forward_simulation (cc_inv IA) (cc_inv IB) L L.
Proof.
  intros HL.
  apply forward_simulation_step with (match_states := fun w => rel_inv (IS w)).
  - auto.
  - intros q q1 q2 (Hq & Hq1 & Hq2) H. congruence.
  - intros q q1 q2 (Hq & Hq1 & Hq2) s Hs. subst.
    exists s. split; eauto.
    constructor.
    eapply preserves_initial_state; eauto.
  - intros w s _ qA [Hs] HAE.
    edestruct @preserves_external as (HqA & Hr); eauto.
    exists qA, qA. repeat apply conj; eauto.
    + intros r' _ s' [Hr'] Hs'.
      exists s'. split; eauto.
      constructor.
      eapply Hr; eauto.
  - intros w s _ r [Hs] Hr.
    exists r. split; eauto.
    constructor.
    eapply preserves_final_state; eauto.
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
  composed with that proved by the used to obtain the desired one. *)

(** ** Strengthening the source semantics *)

Section RESTRICT.
  Context {li} (L: semantics li).
  Context (IA: invariant li).
  Context (IB: invariant li).
  Context (IS: query li -> state L -> Prop).

  Inductive restrict_step ge: _ -> trace -> _ -> Prop :=
    restrict_step_intro q s t s':
      step L ge s t s' ->
      IS q s ->
      IS q s' ->
      restrict_step ge (q, s) t (q, s').

  Inductive restrict_initial_state (q: query li): _ -> Prop :=
    restrict_initial_state_intro s:
      initial_state L q s ->
      query_inv IB q ->
      IS q s ->
      restrict_initial_state q (q, s).

  Inductive restrict_at_external: _ -> query li -> Prop :=
    restrict_at_external_intro q s qA:
      at_external L s qA ->
      IS q s ->
      query_inv IA qA ->
      restrict_at_external (q, s) qA.

  Inductive restrict_after_external: _ -> reply li -> _ -> Prop :=
    restrict_after_external_intro q s qA rA s':
      at_external L s qA ->
      IS q s ->
      query_inv IA qA ->
      after_external L s rA s' ->
      reply_inv IA qA rA ->
      IS q s' ->
      restrict_after_external (q, s) rA (q, s').

  Inductive restrict_final_state: _ -> reply li -> Prop :=
    restrict_final_state_intro q s r:
      final_state L s r ->
      IS q s ->
      reply_inv IB q r ->
      restrict_final_state (q, s) r.

  Definition restrict :=
    {|
      state := query li * state L;
      genvtype := genvtype L;
      step := restrict_step;
      valid_query := valid_query L;
      initial_state := restrict_initial_state;
      at_external := restrict_at_external;
      after_external := restrict_after_external;
      final_state := restrict_final_state;
      globalenv := globalenv L;
      symbolenv := symbolenv L;
    |}.

  Lemma restrict_fsim:
    preserves L IA IB IS ->
    forward_simulation (cc_inv IA) (cc_inv IB) L restrict.
  Proof.
    intros HL.
    set (ms w s s' := (w, s) = s' /\ IS w s).
    apply forward_simulation_step with (match_states := ms).
    - reflexivity.
    - intros q q1 q2 (Hq & Hq1 & Hq2) H. cbn in *. congruence.
    - intros q q1 q2 (Hq & Hq1 & Hq2) s Hs. subst.
      assert (IS q s) by (eapply preserves_initial_state; eauto).
      exists (q, s). split; constructor; eauto.
    - intros q s _ qA [[] Hws] HAE.
      edestruct @preserves_external as (HqA & H); eauto.
      exists qA, qA.
      repeat apply conj; eauto.
      + constructor; eauto.
      + intros r _ s' [Hr] Hs1'.
        exists (q, s'). split; econstructor; eauto.
    - intros q s _ r [[] Hqs] Hr.
      assert (reply_inv IB q r) by eauto using preserves_final_state.
      exists r. split; constructor; eauto.
    - intros q s t s' Hstep _ [[] Hqs].
      assert (IS q s') by (eapply preserves_step; eauto).
      exists (q, s'). split; constructor; eauto.
  Qed.
End RESTRICT.

(** ** Weakening the target semantics *)

Section EXPAND.
  Context {li} (L: semantics li).
  Context (IA: invariant li).
  Context (IB: invariant li).
  Context (IS: query li -> state L -> Prop).

  Inductive expand_step ge: _ -> trace -> _ -> Prop :=
    expand_step_intro q s t s':
      (IS q s -> step L ge s t s') ->
      expand_step ge (q, s) t (q, s').

  Inductive expand_initial_state (q: query li): _ -> Prop :=
    expand_initial_state_intro s:
      (query_inv IB q -> initial_state L q s) ->
      expand_initial_state q (q, s).

  Inductive expand_at_external: _ -> query li -> Prop :=
    expand_external_intro q s qA:
      (IS q s -> at_external L s qA) ->
      expand_at_external (q, s) qA.

  Inductive expand_after_external: _ -> reply li -> _ -> Prop :=
    expand_after_external_intro q s rA (s': state L):
      (forall qA,
          IS q s ->
          at_external L s qA ->
          query_inv IA qA ->
          reply_inv IA qA rA ->
          after_external L s rA s') ->
      expand_after_external (q, s) rA (q, s').

  Inductive expand_final_state: _ -> reply li -> Prop :=
    expand_final_state_intro q s r:
      (IS q s -> final_state L s r) ->
      expand_final_state (q, s) r.

  Definition expand :=
    {|
      state := query li * state L;
      genvtype := genvtype L;
      step := expand_step;
      valid_query := valid_query L;
      initial_state := expand_initial_state;
      at_external := expand_at_external;
      after_external := expand_after_external;
      final_state := expand_final_state;
      globalenv := globalenv L;
      symbolenv := symbolenv L;
    |}.

  Lemma expand_fsim:
    preserves L IA IB IS ->
    forward_simulation (cc_inv IA) (cc_inv IB) expand L.
  Proof.
    intros HL.
    set (ms w s s' := s = (w, s') /\ IS w s').
    apply forward_simulation_step with (match_states := ms).
    - reflexivity.
    - intros q q1 q2 (Hq & Hq1 & Hq2) H. cbn in *. congruence.
    - intros q q1 q2 (Hq & Hq1 & Hq2) _ [s Hqs]. subst q1 q2 ms.
      exists s; intuition eauto.
      eapply preserves_initial_state; eauto.
    - intros q qs s qA [Hqs Hs] H. subst qs ms.
      inversion H; clear H; subst.
      edestruct @preserves_external as (HqA & HrA); eauto.
      exists qA, qA. simpl. intuition eauto.
      destruct H0 as [Hr].
      inversion H1; clear H1; subst.
      eauto 10.
    - intros q qs s r [Hqs Hs] Hr. subst qs ms.
      inversion Hr; clear Hr; subst.
      exists r. intuition eauto.
      constructor. eapply preserves_final_state; eauto.
    - intros q qs t qs' Hstep s [Hqs Hs]. subst ms qs.
      inversion Hstep; clear Hstep; subst.
      exists s'. intuition eauto.
      eapply preserves_step; eauto.
  Qed.
End EXPAND.
