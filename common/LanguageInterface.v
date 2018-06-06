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
Require Export Inject.
Require Export InjectFootprint.
Require Export Extends.
Require Export ExtendsFootprint.


(** * Semantic interface of languages *)

Structure language_interface :=
  mk_language_interface {
    query: Type;
    reply: Type;
  }.

Delimit Scope li_scope with li.
Bind Scope li_scope with language_interface.

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

(** ** Arrow *)

Definition li_arrow liA liB :=
  {|
    query := reply liA + query liB;
    reply := query liA + reply liB;
  |}.

Infix "-o" := li_arrow (at level 55, right associativity) : li_scope.

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
    cc_state : Type;
    cc_init : cc_state;
    cc_query : query T1 -> query T2 -> relation cc_state;
    cc_reply : reply T1 -> reply T2 -> relation cc_state;
  }.

Arguments cc_state {_ _}.
Arguments cc_init {_ _}.
Arguments cc_query {_ _}.
Arguments cc_reply {_ _}.

Delimit Scope cc_scope with cc.
Bind Scope cc_scope with callconv.

Definition match_query {li1 li2} (cc: callconv li1 li2) w q1 q2 :=
  cc_query cc q1 q2 (cc_init cc) w.

Definition match_reply {li1 li2} (cc: callconv li1 li2) w r1 r2 :=
  exists w', cc_reply cc r1 r2 w w'.

(** ** Identity *)

Program Definition cc_id {T}: callconv T T :=
  {|
    cc_state := unit;
    cc_init := tt;
    cc_query q1 q2 w w' := q1 = q2;
    cc_reply r1 r2 w w' := r1 = r2;
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
      cc_state := cc_state cc12 * cc_state cc23;
      cc_init := (cc_init cc12, cc_init cc23);
      cc_query q1 q3 w w' :=
        exists q2,
          cc_query cc12 q1 q2 (fst w) (fst w') /\
          cc_query cc23 q2 q3 (snd w) (snd w');
      cc_reply r1 r3 w w' :=
        exists r2,
          cc_reply cc12 r1 r2 (fst w) (fst w') /\
          cc_reply cc23 r2 r3 (snd w) (snd w');
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
    firstorder.
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
    intros [w12' H12] [w23' H23].
    destruct w as [w12 w23].
    simpl in *.
    exists (w12', w23'), r2; auto.
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

(** ** Arrow *)

Section ARROW.
  Context {liA1 liA2} (ccA : callconv liA1 liA2).
  Context {liB1 liB2} (ccB : callconv liB1 liB2).

  Inductive cc_arrow_query : query (liA1 -o liB1) -> query (liA2 -o liB2) ->
                             relation (cc_state ccA * cc_state ccB) :=
    | cc_arrow_query_l wA wA' wB rA1 rA2 :
        cc_reply ccA rA1 rA2 wA wA' ->
        cc_arrow_query (inl rA1) (inl rA2) (wA, wB) (wA', wB)
    | cc_arrow_query_r wA wB wB' qB1 qB2 :
        cc_query ccB qB1 qB2 wB wB' ->
        cc_arrow_query (inr qB1) (inr qB2) (wA, wB) (wA, wB').

  Inductive cc_arrow_reply : reply (liA1 -o liB1) -> reply (liA2 -o liB2) ->
                             relation (cc_state ccA * cc_state ccB) :=
    | cc_arrow_reply_l wA wA' wB qA1 qA2 :
        cc_query ccA qA1 qA2 wA wA' ->
        cc_arrow_reply (inl qA1) (inl qA2) (wA, wB) (wA', wB)
    | cc_arrow_reply_r wA wB wB' rB1 rB2 :
        cc_reply ccB rB1 rB2 wB wB' ->
        cc_arrow_reply (inr rB1) (inr rB2) (wA, wB) (wA, wB').

  Definition cc_arrow : callconv (liA1 -o liB1) (liA2 -o liB2) :=
    {|
      cc_state := cc_state ccA * cc_state ccB;
      cc_init := (cc_init ccA, cc_init ccB);
      cc_query := cc_arrow_query;
      cc_reply := cc_arrow_reply;
    |}.
End ARROW.

Infix "-o" := cc_arrow : cc_scope.

(** * Common calling conventions *)

(** ** KLR-based calling conventions *)

Section KLR_CALLCONV.
  Context {W: Type} {li1 li2: language_interface}.
  Context (Q: klr W (query li1) (query li2)).
  Context (R: klr W (reply li1) (reply li2)).

  Definition cc_klr_query (q1: query li1) (q2: query li2) (s s': option W) :=
    match s, s' with
      | None, Some w => Q w q1 q2
      | _, _ => False
    end.

  Definition cc_klr_reply (r1: reply li1) (r2: reply li2) (s s': option W) :=
    match s with
      | Some w => R w r1 r2
      | _ => False
    end.

  (*
  Inductive cc_klr_query (q1: query li1) (q2: query li2): relation (option W) :=
    cc_klr_query_intro w :
      Q w q1 q2 ->
      cc_klr_query q1 q2 None (Some w).

  Inductive cc_klr_reply (r1: reply li1) (r2: reply li2): relation (option W) :=
    cc_klr_reply_intro w :
      R w r1 r2 ->
      cc_klr_reply r1 r2 (Some w) None.
   *)

  Definition cc_klr : callconv li1 li2 :=
    {|
      cc_state := option W;
      cc_init := None;
      cc_query := cc_klr_query;
      cc_reply := cc_klr_reply;
    |}.
End KLR_CALLCONV.

(** ** Generic convention for [li_c] *)

Record match_c_query (R: cklr) (w: world R) (q1 q2: c_query) :=
  {
    match_cq_fb: block_inject (mi R w) (cq_fb q1) (cq_fb q2);
    match_cq_sg: cq_sg q1 = cq_sg q2;
    match_cq_args: list_rel (Val.inject (mi R w)) (cq_args q1) (cq_args q2);
    match_cq_mem: match_mem R w (cq_mem q1) (cq_mem q2);
  }.

Definition cc_c (R: cklr): callconv li_c li_c :=
  cc_klr
    (match_c_query R)
    (<> Val.inject @@ [mi R] * match_mem R).

Inductive match_c_query_tr R w: rel c_query c_query :=
  match_c_query_tr_intro q:
    inject_incr (Mem.flat_inj (Mem.nextblock (cq_mem q))) (mi R w) ->
    match_c_query R w q q ->
    match_c_query_tr R w q q.

Definition cc_c_tr R: callconv li_c li_c :=
  cc_klr
    (match_c_query_tr R)
    (<> Val.inject @@ [mi R] * match_mem R).

(** ** Rectangular diagrams *)

(** *** Extension passes *)

Lemma match_cc_ext id sg vargs1 m1 vargs2 m2:
  Mem.extends m1 m2 ->
  Val.lessdef_list vargs1 vargs2 ->
  exists w,
    match_query (cc_c ext) w (cq id sg vargs1 m1) (cq id sg vargs2 m2) /\
    forall vres1 m1' vres2 m2',
      match_reply (cc_c ext) w (vres1, m1') (vres2, m2') ->
      Val.lessdef vres1 vres2 /\
      Mem.extends m1' m2'.
Proof.
  intros Hm Hvargs.
  exists (Some tt). split.
  - constructor; simpl; eauto.
    + exists 0. reflexivity.
    + apply val_inject_list_lessdef in Hvargs.
      induction Hvargs; constructor; eauto.
  - intros vres1 m1' vres2 m2' (_ & w' & Hw' & Hvres & Hm'). simpl in *.
    split; auto.
    apply val_inject_lessdef; eauto.
Qed.

Lemma match_cc_extends id sg vargs1 m1 vargs2 m2:
  Mem.extends m1 m2 ->
  Val.lessdef_list vargs1 vargs2 ->
  exists w,
    match_query (cc_c extp) w (cq id sg vargs1 m1) (cq id sg vargs2 m2) /\
    forall vres1 m1' vres2 m2',
      match_reply (cc_c extp) w (vres1, m1') (vres2, m2') ->
      Val.lessdef vres1 vres2 /\
      Mem.extends m1' m2' /\
      Mem.unchanged_on (loc_out_of_bounds m1) m2 m2'.
Proof.
  intros Hm Hvargs.
  exists (Some (extpw m1 m2)). split.
  - constructor; simpl; eauto.
    + exists 0. reflexivity.
    + apply val_inject_list_lessdef in Hvargs.
      induction Hvargs; constructor; eauto.
    + constructor; eauto.
  - intros vres1 m1' vres2 m2' (_ & w' & Hw' & Hvres & Hm'). cbn [fst snd] in *.
    inversion Hw' as [xm1 xm2 xm1' xm2' Hperm Hunch]; subst.
    inv Hm'. simpl in Hvres. red in Hvres.
    intuition eauto.
    apply val_inject_lessdef; eauto.
Qed.

(** *** Injections *)

Lemma match_cc_inject fb1 sg f vargs1 m1 fb2 vargs2 m2:
  block_inject f fb1 fb2 ->
  Val.inject_list f vargs1 vargs2 ->
  Mem.inject f m1 m2 ->
  meminj_wf f ->
  exists w,
    match_query (cc_c injp) w (cq fb1 sg vargs1 m1) (cq fb2 sg vargs2 m2) /\
    forall vres1 m1' vres2 m2',
      match_reply (cc_c injp) w (vres1, m1') (vres2, m2') ->
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
  intros Hfb Hvargs Hm.
  exists (Some (injpw f m1 m2)). simpl. split.
  - constructor; simpl; eauto.
    induction Hvargs; constructor; eauto.
  - intros vres1 m1' vres2 m2' (_ & w' & Hw' & Hvres & Hm'). simpl in *.
    inv Hw'. inv Hm'.
    exists f'. intuition eauto.
    destruct (f b) as [[b' delta] | ] eqn:Hb.
    + eauto.
    + eapply Mem.unchanged_on_perm; eauto.
Qed.

(** For passes which use a triangular injection diagram for their
  incoming calls, the following lemma may be useful for proving the
  [block_inject] premise of [match_cc_inject]. *)

Lemma funct_ptr_flat_inject {F V} (ge: Genv.t F V) f fd b thr:
  Genv.find_funct_ptr ge b = Some fd ->
  Block.le Block.init thr ->
  inject_incr (Mem.flat_inj thr) f ->
  block_inject f b b.
Proof.
  clear.
  intros Hfd Hthr Hf.
  apply Genv.find_funct_ptr_iff in Hfd.
  apply Genv.genv_defs_range in Hfd.
  exists 0. apply Hf.
  unfold Mem.flat_inj.
  destruct Block.lt_dec; eauto.
  elim n. blomega.
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

Definition cc_extends_triangle :=
  cc_c_tr ext.

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
  intros H [w|] q1 q2 Hq; try contradiction.
  destruct Hq.
  destruct q.
  apply H; auto.
Qed.

(** The following lemma is used in simulation proofs for final states,
  to show that corresponding replies are related. *)

Lemma match_reply_cc_extends_triangle w vres1 m1' vres2 m2':
  Val.lessdef vres1 vres2 ->
  Mem.extends m1' m2' ->
  match_reply (cc_c_tr ext) (Some w) (vres1, m1') (vres2, m2').
Proof.
  destruct w.
  intros.
  apply val_inject_lessdef in H.
  exists None, tt; split; rauto.
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

Inductive cc_inject_triangle_mq: block -> query li_c -> query li_c -> Prop :=
  cc_inject_triangle_mq_intro fb sg vargs m:
    let f := Mem.flat_inj (Mem.nextblock m) in
    block_inject f fb fb ->
    Val.inject_list f vargs vargs ->
    Mem.inject f m m ->
    cc_inject_triangle_mq
      (Mem.nextblock m)
      (cq fb sg vargs m)
      (cq fb sg vargs m).

Definition cc_inject_triangle_mr nb: reply li_c -> reply li_c -> Prop :=
  fun '(vres1, m1') '(vres2, m2') =>
    exists f',
      inject_incr (Mem.flat_inj nb) f' /\
      Val.inject f' vres1 vres2 /\
      Mem.inject f' m1' m2' /\
      meminj_wf f'.

Definition cc_inject_triangle: callconv li_c li_c :=
  cc_klr
    cc_inject_triangle_mq
    cc_inject_triangle_mr.

(** The following lemma is used to prove initial state simulations,
  as a way to inverse the [match_query] hypothesis. See also the
  [inv_triangle_query] tactic below. *)

Lemma match_query_cc_inject_triangle (P: _ -> _ -> _ -> _ -> _ -> _ -> Prop):
  (forall fb sg vargs m,
    block_inject (Mem.flat_inj (Mem.nextblock m)) fb fb ->
    Val.inject_list (Mem.flat_inj (Mem.nextblock m)) vargs vargs ->
    Mem.inject (Mem.flat_inj (Mem.nextblock m)) m m ->
    P fb sg vargs m (cq fb sg vargs m) (cq fb sg vargs m)) ->
  (forall w q1 q2,
    match_query cc_inject_triangle w q1 q2 ->
    P (cq_fb q1) (cq_sg q1) (cq_args q1) (cq_mem q1) q1 q2).
Proof.
  intros H [m|] q1 q2 Hq; try contradiction.
  destruct Hq as [fb sg vargs f Hfb Hvargs Hm]; simpl in *.
  apply H; auto.
Qed.

(** The following lemma is used in simulation proofs for final states,
  to show that corresponding replies are related. *)

Lemma match_reply_cc_inject_triangle nb f' vres1 m1' vres2 m2':
  Val.inject f' vres1 vres2 ->
  Mem.inject f' m1' m2' ->
  inject_incr (Mem.flat_inj nb) f' ->
  meminj_wf f' ->
  match_reply cc_inject_triangle (Some nb) (vres1, m1') (vres2, m2').
Proof.
  intros Hvres Hm' Hf'.
  exists None, f'; eauto.
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
  try replace w with (Mem.nextblock (cq_mem q1)) by (inv Hq; eauto);
  pattern (cq_fb q1), (cq_sg q1), (cq_args q1), (cq_mem q1), q1, q2;
  revert w q1 q2 Hq;
  first
    [ apply match_query_cc_extends_triangle
    | apply match_query_cc_inject_triangle ].
