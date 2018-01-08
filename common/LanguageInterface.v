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
    world_def: Type;
    match_senv:
      world_def -> Senv.t -> Senv.t -> Prop;
    match_query_def:
      world_def -> query T1 -> query T2 -> Prop;
    match_reply_def:
      world_def -> query T1 -> query T2 -> reply T1 -> reply T2 -> Prop;
  }.

Arguments world_def {_ _}.
Arguments match_senv {_ _} _ _ _.
Arguments match_query_def {_ _} _ _ _.
Arguments match_reply_def {_ _} _ _ _ _ _.

Record world {T1 T2} (cc: callconv T1 T2) :=
  mk_world {
    world_proj :> world_def cc;
    world_q1: query T1;
    world_q2: query T2;
    world_match_query:
      match_query_def cc world_proj world_q1 world_q2;
  }.

Arguments mk_world {T1 T2} cc _ _ _ _.
Arguments world_proj {T1 T2 cc} _.
Arguments world_q1 {T1 T2 cc} _.
Arguments world_q2 {T1 T2 cc} _.

Inductive match_query {T1 T2} cc: world cc -> query T1 -> query T2 -> Prop :=
  match_query_intro w q1 q2 Hq:
    match_query cc (mk_world cc w q1 q2 Hq) q1 q2.

Inductive match_reply {T1 T2} cc: world cc -> reply T1 -> reply T2 -> Prop :=
  match_reply_intro w q1 q2 r1 r2 Hq:
    match_reply_def cc w q1 q2 r1 r2 ->
    match_reply cc (mk_world cc w q1 q2 Hq) r1 r2.

Lemma match_query_determ {T1 T2} (cc: callconv T1 T2) w q q1 q2:
  match_query cc w q q1 ->
  match_query cc w q q2 ->
  q2 = q1.
Proof.
  intros H1 H2.
  destruct H1; inv H2.
  reflexivity.
Qed.

Delimit Scope cc_scope with cc.
Bind Scope cc_scope with callconv.

(** ** Identity *)

Program Definition cc_id {T}: callconv T T :=
  {|
    world_def := unit;
    match_senv w := eq;
    match_query_def w := eq;
    match_reply_def w q1 q2 := eq;
  |}.

Lemma cc_id_q {li} (w: world (@cc_id li)):
  world_q1 w = world_q2 w.
Proof.
  destruct w; assumption.
Qed.

Lemma match_cc_id {T} q:
  exists w,
    match_query (@cc_id T) w q q /\
    forall r1 r2,
      match_reply (@cc_id T) w r1 r2 ->
      r1 = r2.
Proof.
  exists (mk_world cc_id tt q q eq_refl).
  split.
  - constructor.
  - inversion 1.
    congruence.
Qed.

Lemma match_query_cc_id {T} w q1 q2:
  match_query (@cc_id T) w q1 q2 ->
  q1 = q2.
Proof.
  destruct 1.
  assumption.
Qed.

Lemma match_reply_cc_id {T} w r:
  match_reply (@cc_id T) w r r.
Proof.
  destruct w.
  repeat constructor.
Qed.

Notation "1" := cc_id : cc_scope.

(** ** Composition *)

Section COMPOSE.
  Context {li1 li2 li3} (cc12: callconv li1 li2) (cc23: callconv li2 li3).

  Definition cc_compose_mq :=
    fun '(w12, w23, q2) q1 q3 =>
      match_query_def cc12 w12 q1 q2 /\
      match_query_def cc23 w23 q2 q3.

  Definition cc_compose_mr :=
    fun '(w12, w23, q2) q1 q3 r1 r3 =>
      exists r2,
        match_reply_def cc12 w12 q1 q2 r1 r2 /\
        match_reply_def cc23 w23 q2 q3 r2 r3.

  Definition cc_compose :=
    {|
      world_def := world_def cc12 * world_def cc23 * query li2;
      match_senv w ge1 ge3 :=
        exists ge2,
          match_senv cc12 (fst (fst w)) ge1 ge2 /\
          match_senv cc23 (snd (fst w)) ge2 ge3;
      match_query_def := cc_compose_mq;
      match_reply_def := cc_compose_mr;
    |}.

  Definition comp_fst (w: world cc_compose) :=
    let '(mk_world (w12, w23, q2) q1 q3 (conj Hq12 Hq23)) := w in
    mk_world cc12 w12 q1 q2 Hq12.

  Definition comp_snd (w: world cc_compose) :=
    let '(mk_world (w12, w23, q2) q1 q3 (conj Hq12 Hq23)) := w in
    mk_world cc23 w23 q2 q3 Hq23.

  Lemma comp_fst_q1 (w: world cc_compose):
    world_q1 (comp_fst w) = world_q1 w.
  Proof.
    destruct w as [[[w12 w23] q2] q1 q3 [Hq12 Hq23]].
    reflexivity.
  Qed.

  Lemma comp_snd_q2 (w: world cc_compose):
    world_q2 (comp_snd w) = world_q2 w.
  Proof.
    destruct w as [[[w12 w23] q2] q1 q3 [Hq12 Hq23]].
    reflexivity.
  Qed.

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
    destruct Hq12 as [w12 q1 q2 Hq12], Hq23 as [w23 q2 q3 Hq23].
    assert (Hq: cc_compose_mq (w12, w23, q2) q1 q3).
    {
      constructor; eauto.
    }
    exists (mk_world cc_compose _ _ _ Hq); split.
    - constructor.
    - intros.
      inv H. destruct H5 as (r2 & Hr12 & Hr23).
      exists r2; split; econstructor; eauto.
  Qed.

  Lemma match_query_cc_compose (P: _ -> _ -> _ -> _ -> Prop):
    (forall w12 q1 q2, match_query cc12 w12 q1 q2 ->
     forall w23 q2' q3, match_query cc23 w23 q2' q3 ->
     q2' = q2 ->
     P w12 w23 q1 q3) ->
    (forall w q1 q3, match_query cc_compose w q1 q3 ->
     P (comp_fst w) (comp_snd w) q1 q3).
  Proof.
    intros H w q1 q3 Hq.
    destruct Hq as [w q1 q3 Hq].
    destruct w as [[w12 w23] q2].
    destruct Hq as [Hq12 Hq23].
    assert (match_query cc12 (mk_world _ w12 q1 q2 Hq12) q1 q2) by constructor.
    assert (match_query cc23 (mk_world _ w23 q2 q3 Hq23) q2 q3) by constructor.
    simpl in *.
    eauto.
  Qed.

  Lemma match_reply_cc_compose w r1 r2 r3:
    match_reply cc12 (comp_fst w) r1 r2 ->
    match_reply cc23 (comp_snd w) r2 r3 ->
    match_reply cc_compose w r1 r3.
  Proof.
    intros H12 H23.
    destruct w as [[[w12 w23] q2] q1 q3 [Hq12 Hq23]].
    simpl in *.
    inv H12.
    inv H23.
    constructor.
    exists r2.
    eauto.
  Qed.
End COMPOSE.

Arguments comp_fst {li1 li2 li3 cc12 cc23} w.
Arguments comp_snd {li1 li2 li3 cc12 cc23} w.

Infix "@" := cc_compose (at level 30, right associativity) : cc_scope.

Ltac inv_compose_query :=
  let w := fresh "w" in
  let q1 := fresh "q1" in
  let q2 := fresh "q2" in
  let Hq := fresh "Hq" in
  intros w q1 q2 Hq;
  pattern (comp_fst w), (comp_snd w), q1, q2;
  revert w q1 q2 Hq;
  apply match_query_cc_compose.

(** * Common calling conventions *)

(** ** Well-typedness property *)

Inductive cc_wt_mr: c_query -> c_query -> reply li_c -> reply li_c -> Prop :=
  | cc_wt_mr_intro id sg vargs m vres m':
      Val.has_type vres (proj_sig_res sg) ->
      cc_wt_mr (cq id sg vargs m) (cq id sg vargs m) (vres, m') (vres, m').

Definition cc_wt: callconv li_c li_c :=
  {|
    world_def := unit;
    match_senv q := eq;
    match_query_def q := eq;
    match_reply_def q := cc_wt_mr;
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
  eexists (mk_world cc_wt tt _ _ eq_refl).
  split.
  - constructor.
  - intros.
    inv H. inv H5.
    eauto.
Qed.

(** ** Extension passes *)

Definition cc_extends_mq :=
  fun '(cq id1 sg1 vargs1 m1) '(cq id2 sg2 vargs2 m2) =>
    id1 = id2 /\
    sg1 = sg2 /\
    Val.lessdef_list vargs1 vargs2 /\
    Mem.extends m1 m2.

Definition cc_extends_mr :=
  fun '(cq _ _ _ m1) '(cq _ _ _ m2) '(vres1, m1') '(vres2, m2') =>
    Val.lessdef vres1 vres2 /\
    Mem.extends m1' m2' /\
    Mem.unchanged_on (loc_out_of_bounds m1) m2 m2'.

Definition cc_extends: callconv li_c li_c :=
  {|
    world_def := unit;
    match_senv w := eq;
    match_query_def w := cc_extends_mq;
    match_reply_def w := cc_extends_mr;
  |}.

Lemma match_cc_extends id sg vargs1 m1 vargs2 m2:
  Mem.extends m1 m2 ->
  Val.lessdef_list vargs1 vargs2 ->
  exists w,
    match_query cc_extends w (cq id sg vargs1 m1) (cq id sg vargs2 m2) /\
    forall vres1 m1' vres2 m2',
      match_reply cc_extends w (vres1, m1') (vres2, m2') ->
      Val.lessdef vres1 vres2 /\
      Mem.extends m1' m2' /\
      Mem.unchanged_on (loc_out_of_bounds m1) m2 m2'.
Proof.
  intros Hm Hvargs.
  assert (Hq: match_query_def cc_extends tt (cq id sg vargs1 m1) (cq id sg vargs2 m2)).
  {
    simpl.
    eauto.
  }
  exists (mk_world cc_extends tt _ _ Hq).
  split.
  - constructor.
  - intros.
    inv H.
    assumption.
Qed.

(** ** Injection passes *)

Definition cc_inject_mq f :=
  fun '(cq id1 sg1 vargs1 m1) '(cq id2 sg2 vargs2 m2) =>
    id1 = id2 /\
    sg1 = sg2 /\
    Val.inject_list f vargs1 vargs2 /\
    Mem.inject f m1 m2.

Definition cc_inject_mr f :=
  fun '(cq _ _ _ m1) '(cq _ _ _ m2) '(vres1, m1') '(vres2, m2') =>
    exists f',
      Val.inject f' vres1 vres2 /\
      Mem.inject f' m1' m2' /\
      Mem.unchanged_on (loc_unmapped f) m1 m1' /\
      Mem.unchanged_on (loc_out_of_reach f m1) m2 m2' /\
      inject_incr f f' /\
      inject_separated f f' m1 m2 /\
      forall b ofs p,
        Mem.valid_block m1 b ->
        Mem.perm m1' b ofs Max p ->
        Mem.perm m1 b ofs Max p.

Definition cc_inject: callconv li_c li_c :=
  {|
    world_def := meminj;
    match_senv := symbols_inject;
    match_query_def := cc_inject_mq;
    match_reply_def := cc_inject_mr;
  |}.

Lemma match_cc_inject id sg f vargs1 m1 vargs2 m2:
  Val.inject_list f vargs1 vargs2 ->
  Mem.inject f m1 m2 ->
  exists w,
    match_query cc_inject w (cq id sg vargs1 m1) (cq id sg vargs2 m2) /\
    forall vres1 m1' vres2 m2',
      match_reply cc_inject w (vres1, m1') (vres2, m2') ->
      exists f',
        Val.inject f' vres1 vres2 /\
        Mem.inject f' m1' m2' /\
        Mem.unchanged_on (loc_unmapped f) m1 m1' /\
        Mem.unchanged_on (loc_out_of_reach f m1) m2 m2' /\
        inject_incr f f' /\
        inject_separated f f' m1 m2 /\
        forall b ofs p,
          Mem.valid_block m1 b ->
          Mem.perm m1' b ofs Max p ->
          Mem.perm m1 b ofs Max p.
Proof.
  intros Hvargs Hm.
  assert (match_query_def cc_inject f (cq id sg vargs1 m1) (cq id sg vargs2 m2)).
  {
    simpl.
    eauto.
  }
  exists (mk_world cc_inject _ _ _ H).
  split.
  - econstructor.
  - intros vres1 m1' vres2 m2' Hr.
    inv Hr.
    assumption.
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

(** *** Initial state accessors *)

(** Following CompCertX, our simulation proofs are parametrized over
  the components of the initial state (memory, arguments, etc.).
  These components can be obtained from the outer world used in the
  simulation as follows. *)

Notation tr_fb w := (cq_fb (world_q1 w)).
Notation tr_sg w := (cq_sg (world_q1 w)).
Notation tr_args w := (cq_args (world_q1 w)).
Notation tr_mem w := (cq_mem (world_q1 w)).

(** *** Extensions *)

Definition cc_extends_triangle_mr :=
  fun '(vres1, m1') '(vres2, m2') =>
    Val.lessdef vres1 vres2 /\
    Mem.extends m1' m2'.

Definition cc_extends_triangle: callconv li_c li_c :=
  {|
    world_def := unit;
    match_senv w := eq;
    match_query_def w := eq;
    match_reply_def w q1 q2 := cc_extends_triangle_mr;
  |}.

(** The following lemma and tactic are used in simulation proofs for
  initial states, as a way to inverse the [match_query] hypothesis.
  See also the [inv_triangle_query] tactic below. *)

Lemma match_query_cc_extends_triangle (P: _ -> _ -> _ -> _ -> _ -> _ -> Prop):
  (forall id sg vargs m,
    P id sg vargs m (cq id sg vargs m) (cq id sg vargs m)) ->
  (forall w q1 q2,
    match_query cc_extends_triangle w q1 q2 ->
    P (tr_fb w) (tr_sg w) (tr_args w) (tr_mem w) q1 q2).
Proof.
  intros H w q1 q2 Hq.
  destruct Hq.
  destruct Hq.
  destruct q1.
  apply H; auto.
Qed.

(** The following lemma is used in simulation proofs for final states,
  to show that corresponding replies are related. *)

Lemma match_reply_cc_extends_triangle w vres1 m1' vres2 m2':
  Val.lessdef vres1 vres2 ->
  Mem.extends m1' m2' ->
  match_reply cc_extends_triangle w (vres1, m1') (vres2, m2').
Proof.
  intros.
  destruct w as [f q1 q2 Hq].
  constructor.
  simpl.
  auto.
Qed.

(** *** Injections *)

(** The triangular diagram for injections requires the initial
  memories and arguments to be "inject_neutral". *)

Inductive cc_inject_triangle_mq: meminj -> query li_c -> query li_c -> Prop :=
  cc_inject_triangle_mq_intro id sg vargs m:
    Val.inject_list (Mem.flat_inj (Mem.nextblock m)) vargs vargs ->
    Mem.inject_neutral (Mem.nextblock m) m ->
    cc_inject_triangle_mq
      (Mem.flat_inj (Mem.nextblock m))
      (cq id sg vargs m)
      (cq id sg vargs m).

Definition cc_inject_triangle_mr f :=
  fun '(cq _ _ _ m1) '(cq _ _ _ m2) '(vres1, m1') '(vres2, m2') =>
    exists f',
      Val.inject f' vres1 vres2 /\
      Mem.inject f' m1' m2' /\
      inject_incr f f' /\
      inject_separated f f' m1 m2.

Definition cc_inject_triangle: callconv li_c li_c :=
  {|
    world_def := meminj;
    match_senv := symbols_inject;
    match_query_def := cc_inject_triangle_mq;
    match_reply_def := cc_inject_triangle_mr;
  |}.

(** The following lemma is used to prove initial state simulations,
  as a way to inverse the [match_query] hypothesis. See also the
  [inv_triangle_query] tactic below. *)

Lemma match_query_cc_inject_triangle (P: _ -> _ -> _ -> _ -> _ -> _ -> Prop):
  (forall id sg vargs m,
    Val.inject_list (Mem.flat_inj (Mem.nextblock m)) vargs vargs ->
    Mem.inject_neutral (Mem.nextblock m) m ->
    P id sg vargs m (cq id sg vargs m) (cq id sg vargs m)) ->
  (forall w q1 q2,
    match_query cc_inject_triangle w q1 q2 ->
    P (tr_fb w) (tr_sg w) (tr_args w) (tr_mem w) q1 q2).
Proof.
  intros H w q1 q2 Hq.
  destruct Hq.
  destruct Hq.
  apply H; auto.
Qed.

(** The following lemma is used in simulation proofs for final states,
  to show that corresponding replies are related. *)

Lemma match_reply_cc_inject_triangle w f' vres1 m1' vres2 m2':
  let m := cq_mem (world_q1 w) in
  let f := Mem.flat_inj (Mem.nextblock m) in
  Val.inject f' vres1 vres2 ->
  Mem.inject f' m1' m2' ->
  inject_incr f f' ->
  inject_separated f f' m m ->
  match_reply cc_inject_triangle w (vres1, m1') (vres2, m2').
Proof.
  intros.
  subst m f.
  destruct w as [f q1 q2 Hq].
  destruct Hq as [id sg vargs m Hvargs Hm].
  simpl in *.
  constructor.
  simpl.
  eauto 10.
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
  pattern (tr_fb w), (tr_sg w), (tr_args w), (tr_mem w), q1, q2;
  revert w q1 q2 Hq;
  first
    [ apply match_query_cc_extends_triangle
    | apply match_query_cc_inject_triangle ].
