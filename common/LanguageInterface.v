Require Import String.
Require Import RelationClasses.
Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Events.
Require Import KLR.
Require Import CKLR.
Require Import Inject.
Require Import InjectNeutral.
Require Import InjectFootprint.
Require Import Extends.


(** * Semantic interface of languages *)

Structure language_interface :=
  mk_language_interface {
    query: Type;
    reply: Type;
  }.

(** ** Interface for C-like languages *)

Record c_query :=
  cq {
    cq_fb: block;
    cq_sg: signature;
    cq_args: list val;
    cq_mem: mem;
  }.

Canonical Structure li_c :=
  {|
    query := c_query;
    reply := val * mem;
  |}.

(** ** Miscellaneous interfaces *)

Definition li_wp :=
  {|
    query := unit;
    reply := int;
  |}.

Definition li_empty :=
  {|
    query := Empty_set;
    reply := Empty_set;
  |}.

(** * Calling conventions *)

(** ** Definition *)

Record callconv T1 T2 :=
  mk_callconv {
    ccworld : Type;
    match_senv: klr ccworld Senv.t Senv.t;
    match_query: klr ccworld (query T1) (query T2);
    match_reply: klr ccworld (reply T1) (reply T2);
  }.

Arguments ccworld {_ _}.
Arguments match_senv {_ _} _ _ _.
Arguments match_query {_ _} _ _ _.
Arguments match_reply {_ _} _ _ _.

Delimit Scope cc_scope with cc.
Bind Scope cc_scope with callconv.

(** ** Identity *)

Program Definition cc_id {T}: callconv T T :=
  {|
    ccworld := unit;
    match_senv w := eq;
    match_query w := eq;
    match_reply w := eq;
  |}.

Lemma match_cc_id {T} q:
  exists w,
    match_query (@cc_id T) w q q /\
    forall r1 r2,
      match_reply (@cc_id T) w r1 r2 ->
      r1 = r2.
Proof.
  exists tt.
  firstorder.
Qed.

Lemma match_query_cc_id {T} w q1 q2:
  match_query (@cc_id T) w q1 q2 ->
  q1 = q2.
Proof.
  firstorder.
Qed.

Lemma match_reply_cc_id {T} w r:
  match_reply (@cc_id T) w r r.
Proof.
  firstorder.
Qed.

Notation "1" := cc_id : cc_scope.

(** ** Composition *)

Section COMPOSE.
  Context {li1 li2 li3} (cc12: callconv li1 li2) (cc23: callconv li2 li3).

  Definition cc_compose :=
    {|
      ccworld := ccworld cc12 * ccworld cc23;
      match_senv w :=
        rel_compose (match_senv cc12 (fst w)) (match_senv cc23 (snd w));
      match_query w :=
        rel_compose (match_query cc12 (fst w)) (match_query cc23 (snd w));
      match_reply w :=
        rel_compose (match_reply cc12 (fst w)) (match_reply cc23 (snd w));
    |}.

  Lemma match_cc_compose w12 w23 q1 q2 q3:
    match_query cc12 w12 q1 q2 ->
    match_query cc23 w23 q2 q3 ->
    exists w,
      match_query cc_compose w q1 q3 /\
      forall r1 r3,
        match_reply cc_compose w r1 r3 ->
        exists r2,
          match_reply cc12 w12 r1 r2 /\
          match_reply cc23 w23 r2 r3.
  Proof.
    intros Hq12 Hq23.
    exists (w12, w23). simpl. intuition eauto.
    eexists; eauto.
  Qed.

  Lemma match_query_cc_compose (P: _ -> _ -> _ -> _ -> Prop):
    (forall w12 q1 q2, match_query cc12 w12 q1 q2 ->
     forall w23 q2' q3, match_query cc23 w23 q2' q3 ->
     q2' = q2 ->
     P w12 w23 q1 q3) ->
    (forall w q1 q3, match_query cc_compose w q1 q3 ->
     P (fst w) (snd w) q1 q3).
  Proof.
    intros H [w12 w23] q1 q3 (q2 & Hq12 & Hq23).
    eauto.
  Qed.

  Lemma match_reply_cc_compose w r1 r2 r3:
    match_reply cc12 (fst w) r1 r2 ->
    match_reply cc23 (snd w) r2 r3 ->
    match_reply cc_compose w r1 r3.
  Proof.
    intros H12 H23.
    destruct w as [w12 w23].
    simpl in *.
    eexists; eauto.
  Qed.
End COMPOSE.

Infix "@" := cc_compose (at level 30, right associativity) : cc_scope.

Ltac inv_compose_query :=
  let w := fresh "w" in
  let q1 := fresh "q1" in
  let q2 := fresh "q2" in
  let Hq := fresh "Hq" in
  intros w q1 q2 Hq;
  pattern (fst w), (snd w), q1, q2;
  revert w q1 q2 Hq;
  apply match_query_cc_compose.

(** * Common calling conventions *)

(** ** Generic convention for [li_c] *)

Record match_c_query (R: cklr) (w: world R) (q1 q2: c_query) :=
  {
    match_cq_fb: block_inject (mi R w) (cq_fb q1) (cq_fb q2);
    match_cq_sg: cq_sg q1 = cq_sg q2;
    match_cq_args: list_rel (Val.inject (mi R w)) (cq_args q1) (cq_args q2);
    match_cq_mem: match_mem R w (cq_mem q1) (cq_mem q2);
  }.

Definition cc_c (R: cklr): callconv li_c li_c :=
  {|
    ccworld := world R;
    match_senv := symbols_inject @@ [mi R];
    match_query := match_c_query R;
    match_reply := <> Val.inject @@ [mi R] * match_mem R;
  |}.

Inductive match_c_query_tr R w: rel c_query c_query :=
  match_c_query_tr_intro q:
    inject_incr (Mem.flat_inj (Mem.nextblock (cq_mem q))) (mi R w) ->
    match_c_query R w q q ->
    match_c_query_tr R w q q.

Definition cc_c_tr R: callconv li_c li_c :=
  {|
    ccworld := world R;
    match_senv := symbols_inject @@ [mi R];
    match_query :=  match_c_query_tr R;
    match_reply := <> Val.inject @@ [mi R] * match_mem R;
  |}.

(** ** Well-typedness property *)

Inductive cc_wt_mq: klr signature c_query c_query :=
  | cc_wt_mq_intro id sg vargs m:
      cc_wt_mq sg (cq id sg vargs m) (cq id sg vargs m).

Inductive cc_wt_mr: klr signature (reply li_c) (reply li_c) :=
  | cc_wt_mr_intro sg vres m':
      Val.has_type vres (proj_sig_res sg) ->
      cc_wt_mr sg (vres, m') (vres, m').

Definition cc_wt: callconv li_c li_c :=
  {|
    ccworld := signature;
    match_senv := k eq;
    match_query := cc_wt_mq;
    match_reply := cc_wt_mr;
  |}.

Lemma match_cc_wt id sg vargs m:
  exists w,
    match_query cc_wt w (cq id sg vargs m) (cq id sg vargs m) /\
    forall vres1 m1' vres2 (m2': mem),
      match_reply cc_wt w (vres1, m1') (vres2, m2') ->
      vres1 = vres2 /\
      m1' = m2' /\
      Val.has_type vres2 (proj_sig_res sg).
Proof.
  exists sg.
  split.
  - constructor.
  - intros.
    inv H.
    eauto.
Qed.

(** ** Triangular diagrams *)

(** When proving simulation for initial and final states, we do not
  use the rectangular diagrams of [cc_extends] and [cc_inject]
  directly. Instead, we use triangular diagrams where initial states
  are identical. The execution can still introduce an extension or
  injection, so that final states may be different.

  Because initial states are identical, there is no possibility for
  the target program to modify regions that are present in the target
  initial memory, but not in the source initial memory (for instance,
  the caller's spilling locations. Consequently, the [Mem.unchanged]
  constraints specified in [cc_extends] and [cc_inject] hold
  automatically. This means the simulation relation does not need to
  keep track of these invariants, which simplifies the proof
  significantly.

  The reason this is sufficient is that the triangular diagram is a
  absorbed on the left by the rectangular diagram: for instance, if we
  compose the triangular diagram for injection passes with a proof
  that the target language is compatible with injections, and the
  rectangular diagram can be recovered. *)

(** *** Extensions *)

(** The following lemma and tactic are used in simulation proofs for
  initial states, as a way to inverse the [match_query] hypothesis.
  See also the [inv_triangle_query] tactic below. *)

Lemma match_query_cc_extends_triangle (P: _ -> _ -> _ -> _ -> _ -> _ -> Prop):
  (forall id sg vargs m,
    P id sg vargs m (cq id sg vargs m) (cq id sg vargs m)) ->
  (forall w q1 q2,
    match_query (cc_c_tr ext) w q1 q2 ->
    P (cq_fb q1) (cq_sg q1) (cq_args q1) (cq_mem q1) q1 q2).
Proof.
  intros H w q1 q2 Hq.
  destruct Hq.
  destruct q.
  apply H; auto.
Qed.

(** The following lemma is used in simulation proofs for final states,
  to show that corresponding replies are related. *)

Lemma match_reply_cc_extends_triangle w vres1 m1' vres2 m2':
  Val.lessdef vres1 vres2 ->
  Mem.extends m1' m2' ->
  match_reply (cc_c_tr ext) w (vres1, m1') (vres2, m2').
Proof.
  destruct w.
  intros.
  apply val_inject_lessdef in H.
  exists tt; split; rauto.
Qed.

(** *** Injections *)

Lemma val_inject_list_rel f:
  eqrel
    (Val.inject_list f)
    (list_rel (Val.inject f)).
Proof.
  split; induction 1; constructor; eauto.
Qed.

(** The triangular diagram for injections requires the initial
  memories and arguments to be "inject_neutral". *)

(** The following lemma is used to prove initial state simulations,
  as a way to inverse the [match_query] hypothesis. See also the
  [inv_triangle_query] tactic below. *)

Lemma match_query_cc_inject_triangle (P: _ -> _ -> _ -> _ -> _ -> _ -> Prop):
  (forall id sg vargs m,
    Val.inject_list (Mem.flat_inj (Mem.nextblock m)) vargs vargs ->
    Mem.inject (Mem.flat_inj (Mem.nextblock m)) m m ->
    P id sg vargs m (cq id sg vargs m) (cq id sg vargs m)) ->
  (forall w q1 q2,
    match_query (cc_c_tr inj) w q1 q2 ->
    P (cq_fb q1) (cq_sg q1) (cq_args q1) (cq_mem q1) q1 q2).
Proof.
  intros H w q1 q2 Hq.
  destruct Hq as [q Hw [Hfb _ Hvargs Hm]].
  destruct q as [fb sg vargs m]; simpl in *.
  assert (w = Mem.flat_inj (Mem.nextblock m)).
  {
    apply Axioms.functional_extensionality; intros b1.
    specialize (Hw b1).
    unfold Mem.flat_inj in *.
    destruct Block.lt_dec as [Hb|Hb]; eauto.
    destruct (w b1) as [[b2 delta] | ] eqn:Hb'; eauto.
    elim Hb. eapply Mem.valid_block_inject_1; eauto.
  }
  subst.
  apply H; auto.
  apply val_inject_list_rel; auto.
Qed.

(** The following lemma is used in simulation proofs for final states,
  to show that corresponding replies are related. *)

Lemma match_reply_cc_inject_triangle f f' vres1 m1' vres2 m2':
  Val.inject f' vres1 vres2 ->
  Mem.inject f' m1' m2' ->
  inject_incr f f' ->
  match_reply (cc_c_tr inj) f (vres1, m1') (vres2, m2').
Proof.
  intros Hvres Hm' Hf'.
  exists f'; split; rauto.
Qed.

(** *** Tactics *)

(** This tactic is used to apply the relevant lemma at the beginning
  of initial state simulation proofs. *)

Ltac inv_triangle_query :=
  let w := fresh "w" in
  let q1 := fresh "q1" in
  let q2 := fresh "q2" in
  let Hq := fresh "Hq" in
  intros w q1 q2 Hq;
  pattern (cq_fb q1), (cq_sg q1), (cq_args q1), (cq_mem q1), q1, q2;
  revert w q1 q2 Hq;
  first
    [ apply match_query_cc_extends_triangle
    | apply match_query_cc_inject_triangle ].
