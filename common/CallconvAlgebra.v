Require Export List.
Require Export RelationClasses.
Require Export Morphisms.
Require Export Globalenvs.
Require Export Events.
Require Export LanguageInterface.
Require Export Smallstep.

(** Algebraic structures on calling conventions. *)

(** * Refinement and equivalence *)

(** ** Definition *)

(** The following relation asserts that the calling convention [cc] is
  refined by the calling convention [cc'], meaning that any
  [cc']-simulation is also a [cc]-simulation. *)

Definition ccref {li1 li2} (cc cc': callconv li1 li2) :=
  exists (f: world_def cc -> query li1 -> query li2 -> world_def cc'),
    forall w q1 q2,
      match_query_def cc w q1 q2 ->
      match_query_def cc' (f w q1 q2) q1 q2 /\
      forall r1 r2,
        match_reply_def cc' (f w q1 q2) q1 q2 r1 r2 ->
        match_reply_def cc w q1 q2 r1 r2.

Definition cceqv {li1 li2} (cc cc': callconv li1 li2) :=
  ccref cc cc' /\ ccref cc' cc.

Global Instance ccref_preo li1 li2:
  PreOrder (@ccref li1 li2).
Proof.
  split.
  - intros cc. red.
    exists (fun x _ _ => x).
    tauto.
  - intros cc cc' cc'' [f H'] [g H''].
    exists (fun x q1 q2 => g (f x q1 q2) q1 q2).
    intros w q1 q2 Hq.
    edestruct H' as (Hq' & Hr); eauto.
    edestruct H'' as (Hq'' & Hr'); eauto.
Qed.

Global Instance cceqv_equiv li1 li2:
  Equivalence (@cceqv li1 li2).
Proof.
  split.
  - intros cc.
    split; reflexivity.
  - intros cc1 cc2. unfold cceqv.
    tauto.
  - intros cc1 cc2 cc3 [H12 H21] [H23 H32].
    split; etransitivity; eauto.
Qed.

Global Instance ccref_po li1 li2:
  PartialOrder (@cceqv li1 li2) (@ccref li1 li2).
Proof.
  firstorder.
Qed.

(** ** Relation to forward simulations *)

Section FWSIM_CCREF.
  Context {liA1 liB1 liA2 liB2: language_interface}.
  Context (L1: semantics liA1 liB1).
  Context (L2: semantics liA2 liB2).
  Context {ccA ccA': callconv liA1 liA2} (HA: ccref ccA' ccA).
  Context {ccB ccB': callconv liB1 liB2} (HB: ccref ccB ccB').

  Lemma forward_simulation_ccref:
    forward_simulation ccA' ccB' L1 L2 ->
    forward_simulation ccA  ccB  L1 L2.
  Proof.
    revert HA HB.
    intros [fA HA] [fB HB] [I lt R H].
    set (R' := fun '(mk_world w q1 q2 Hq) i s1 s2 =>
           let (HBq, HBr) := HB w q1 q2 Hq in
           R (mk_world _ (fB w q1 q2) q1 q2 HBq) i s1 s2 /\
           forall r1 r2,
             match_reply_def ccB' (fB w q1 q2) q1 q2 r1 r2 ->
             match_reply_def ccB w q1 q2 r1 r2).
    eexists I lt R'.
    destruct H.
    split; eauto.
    - intros _ _ _ [w q1 q2 Hq] s1 Hs1. simpl.
      destruct (HB w q1 q2 Hq) as (Hq' & Hr').
      edestruct fsim_match_initial_states as (i & s2 & Hs2 & Hs); eauto.
      constructor.
    - intros [w qB1 qB2 HqB] i s1 s2 Hs q1 AE1 Hs1.
      subst R'. simpl in *. destruct HB as [HBq HBr]. destruct Hs as [Hs HrB].
      edestruct fsim_match_external as (wA' & q2 & AE2 & Hq & Hs2 & Hr); eauto.
      destruct Hq as [wA' q1 q2 Hq].
      edestruct HA as [HAq HAr]; eauto.
      exists (mk_world _ (fA wA' q1 q2) q1 q2 HAq), q2, AE2.
      intuition.
      + constructor.
      + edestruct Hr as (j & s2' & Hs2' & Hs'); eauto.
        inversion H.
        constructor; eauto.
    - intros [w q1 q2 Hq] i s1 s2 r1 Hs Hr1.
      subst R'. simpl in *. destruct HB as [HBq HBr]. destruct Hs as [Hs HrB].
      edestruct fsim_match_final_states as (r2 & Hr & Hr2); eauto.
      exists r2. intuition.
      inversion Hr.
      constructor; eauto.
    - intros [w q1 q2 Hq] s1 t s1' Hstep i s2 Hs.
      subst R'. simpl in *. destruct HB as [HBq HBr]. destruct Hs as [Hs HrB].
      edestruct fsim_simulation as (i' & s2' & Hstep' & Hs'); eauto.
  Qed.
End FWSIM_CCREF.


(** * Properties of [cc_compose] *)

(** Language interfaces and calling conventions form a category, with
  [cc_id] as the identity arrow and [cc_compose] as the composition. *)

Lemma cc_compose_id_left {li1 li2} (cc: callconv li1 li2):
  cceqv (cc_compose cc_id cc) cc.
Proof.
  split.
  - exists (fun '(tt, w, q1) _ _ => w).
    intros [[[] w] q1] ? q2 [? Hq]; simpl in *; subst.
    eauto 10.
  - red. exists (fun w q1 _ => (tt, w, q1)).
    intros w q1 q2 Hq.
    firstorder.
    congruence.
Qed.

Lemma cc_compose_id_right {li1 li2} (cc: callconv li1 li2):
  cceqv (cc_compose cc cc_id) cc.
Proof.
  split.
  - exists (fun '(w, tt, q2) _ _ => w).
    intros [[w []] q2] q1 ? [Hq ?]; simpl in *; subst.
    eauto 10.
  - exists (fun w q1 q2 => (w, tt, q2)).
    intros w q1 q2 Hq.
    firstorder.
    congruence.
Qed.

Lemma cc_compose_assoc {A B C D} cc1 cc2 cc3:
  cceqv
    (@cc_compose A C D (cc_compose cc1 cc2) cc3)
    (@cc_compose A B D cc1 (cc_compose cc2 cc3)).
Proof.
  split.
  - exists (fun '((w1, w2, qb), w3, qc) _ _ => (w1, (w2, w3, qc), qb)).
    intros [[[[w1 w2] qb] w3] qc] qa qd [[Hq1 Hq2] Hq3]. simpl.
    split; eauto.
    intros ra rd (rb & Hr1 & rc & Hr2 & Hr3); eauto.
  - exists (fun '(w1, (w2, w3, qc), qb) _ _ => ((w1, w2, qb), w3, qc)).
    intros [[w1 [[w2 w3] qc]] qb] qa qd [Hq1 [Hq2 Hq3]]. simpl.
    split; eauto.
    intros ra rd (rc & (rb & Hr1 & Hr2) & Hr3); eauto.
Qed.

(** In addition, composition is monotonic under [cc_ref]. *)

Global Instance cc_compose_ref li1 li2 li3:
  Proper (ccref ++> ccref ++> ccref) (@cc_compose li1 li2 li3).
Proof.
  intros cc12 cc12' [f12 H12] cc23 cc23' [f23 H23].
  exists (fun '(w12, w23, q2) q1 q3 => (f12 w12 q1 q2, f23 w23 q2 q3, q2)).
  intros [[w12 w23] q2] q1 q3 [Hq12 Hq23]. simpl.
  destruct (H12 w12 q1 q2 Hq12) as (Hq12' & Hr12').
  destruct (H23 w23 q2 q3 Hq23) as (Hq23' & Hr23').
  split; eauto.
  intros r1 r3 (r2 & Hr12 & Hr23); eauto.
Qed.

Global Instance cc_compose_eqv li1 li2 li3:
  Proper (cceqv ==> cceqv ==> cceqv) (@cc_compose li1 li2 li3).
Proof.
  intros cc12 cc12' [H12 H21] cc23 cc23' [H23 H32].
  split; eapply cc_compose_ref; eauto.
Qed.


(** * Kleene algebra *)

(** At each language interface [li], we can equip the type of calling
  conventions [callconv li li] with (most of) the structure of a
  Kleene algebra. At the moment, the [match_dummy_query_def]
  requiement on calling conventions prevents us from defining a zero
  element. Otherwise, we largely follow Kozen'94. *)

(** ** Union *)

(** The union of two calling conventions [cc1] and [cc2] is defined
  in such a way that a [ccplus cc1 cc2]-simulation is both a
  [cc1]-simulation and a [cc2]-simulation. *)

Section JOIN.
  Context {li: language_interface}.

  Definition copair {A B C} (f: A -> C) (g: B -> C) (x: A + B): C :=
    match x with
      | inl a => f a
      | inr b => g b
    end.

  Definition cc_join (cc1 cc2: callconv li li): callconv li li :=
    {|
      world_def := world_def cc1 + world_def cc2;
      match_senv := copair (match_senv cc1) (match_senv cc2);
      match_query_def := copair (match_query_def cc1) (match_query_def cc2);
      match_reply_def := copair (match_reply_def cc1) (match_reply_def cc2);
    |}.

  (** [cc_join] is the least upper bound with respect to [ccref]. *)

  Lemma cc_join_ub_l cc1 cc2:
    ccref cc1 (cc_join cc1 cc2).
  Proof.
    exists (fun w _ _ => inl w).
    intros w q1 q2 Hq.
    simpl; eauto.
  Qed.

  Lemma cc_join_ub_r cc1 cc2:
    ccref cc2 (cc_join cc1 cc2).
  Proof.
    exists (fun w _ _ => inr w).
    intros w q1 q2 Hq.
    simpl; eauto.
  Qed.

  Lemma cc_join_lub cc1 cc2 cc:
    ccref cc1 cc ->
    ccref cc2 cc ->
    ccref (cc_join cc1 cc2) cc.
  Proof.
    intros [f1 H1] [f2 H2].
    exists (copair f1 f2).
    intros [w | w] q1 q2 Hq; simpl in *; eauto.
  Qed.

  (** The following lemmas are useful as [auto] hints. *)

  Lemma cc_join_l cc cc1 cc2:
    ccref cc cc1 -> ccref cc (cc_join cc1 cc2).
  Proof.
    etransitivity; eauto using cc_join_ub_l.
  Qed.

  Lemma cc_join_r cc cc1 cc2:
    ccref cc cc2 -> ccref cc (cc_join cc1 cc2).
  Proof.
    etransitivity; eauto using cc_join_ub_r.
  Qed.

  (** Trivial consequences of the least upper bound property. *)

  Hint Resolve cc_join_lub cc_join_l cc_join_r (reflexivity (R:=ccref)).
  Hint Unfold cceqv.

  Global Instance cc_join_ref:
    Proper (ccref ++> ccref ++> ccref) cc_join.
  Proof.
    intros cc1 cc1' H1 cc2 cc2' H2; eauto 10.
  Qed.

  Global Instance cc_join_eqv:
    Proper (cceqv ==> cceqv ==> cceqv) cc_join.
  Proof.
    intros cc12 cc12' [H12 H21] cc23 cc23' [H23 H32]; eauto 10.
  Qed.

  Lemma cc_join_assoc cc1 cc2 cc3:
    cceqv (cc_join (cc_join cc1 cc2) cc3) (cc_join cc1 (cc_join cc2 cc3)).
  Proof.
    split; eauto 10.
  Qed.

  Lemma cc_join_comm cc1 cc2:
    cceqv (cc_join cc1 cc2) (cc_join cc2 cc1).
  Proof.
    split; eauto 10.
  Qed.

  Lemma cc_join_idemp cc:
    cceqv (cc_join cc cc) cc.
  Proof.
    split; eauto 10.
  Qed.

  Lemma ccref_join cc1 cc2:
    ccref cc1 cc2 <->
    cceqv (cc_join cc1 cc2) cc2.
  Proof.
    unfold cceqv; intuition.
    transitivity (cc_join cc1 cc2); eauto.
  Qed.
End JOIN.

Infix "+" := cc_join : cc_scope.

(** ** Iteration *)

Section STAR.
  Context {li: language_interface} (cc: callconv li li).

  (** *** Definition *)

  Definition cc_star_world :=
    list (world_def cc * query li).

  Fixpoint cc_star_me (ws: cc_star_world) (ge1 ge2: Senv.t) :=
    match ws with
      | nil => ge1 = ge2
      | (w, q) :: ws =>
        exists ge,
          match_senv cc w ge1 ge /\
          cc_star_me ws ge ge2
    end.

  Fixpoint cc_star_mq (ws: cc_star_world) (q1 q2: query li) :=
    match ws with
      | nil => q1 = q2
      | (w, q) :: ws =>
        match_query_def cc w q1 q /\
        cc_star_mq ws q q2
    end.

  Fixpoint cc_star_mr (ws: cc_star_world) (q1 q2: query li) (r1 r2: reply li) :=
    match ws with
      | nil => r1 = r2
      | (w, q) :: ws =>
        exists r,
          match_reply_def cc w q1 q r1 r /\
          cc_star_mr ws q q2 r r2
    end.

  Definition cc_star: callconv li li :=
    {|
      world_def := cc_star_world;
      match_senv := cc_star_me;
      match_query_def := cc_star_mq;
      match_reply_def := cc_star_mr;
    |}.

  (** *** Useful lemmas *)

  Lemma cc_star_mq_app_intro w12 w23 q1 q2 q3:
    cc_star_mq w12 q1 q2 ->
    cc_star_mq w23 q2 q3 ->
    cc_star_mq (w12 ++ w23) q1 q3.
  Proof.
    revert q1.
    induction w12 as [ | [w q] ws IHws]; simpl.
    - congruence.
    - intros q1 [Hq1 Hq2] Hq23; eauto.
  Qed.

  Lemma cc_star_mq_app_elim w12 w23 q1 q3:
    cc_star_mq (w12 ++ w23) q1 q3 ->
    exists q2, cc_star_mq w12 q1 q2 /\ cc_star_mq w23 q2 q3.
  Proof.
    revert q1.
    induction w12 as [ | [w q] ws IHws]; simpl.
    - firstorder.
    - intros q1 [Hq1 Hq3].
      edestruct IHws as (q2 & Hq12 & Hq23); eauto.
  Qed.

  Lemma cc_star_mr_app_elim w12 w23 q1 q2 q3 r1 r3:
    cc_star_mq w12 q1 q2 ->
    cc_star_mq w23 q2 q3 ->
    cc_star_mr (w12 ++ w23) q1 q3 r1 r3 ->
    exists r2, cc_star_mr w12 q1 q2 r1 r2 /\ cc_star_mr w23 q2 q3 r2 r3.
  Proof.
    revert q1 r1.
    induction w12 as [ | [w q] ws IHws]; simpl.
    - intros; subst; eauto.
    - intros q1 r1 [Hq1 Hq2] Hq23 (r & Hr1 & Hr2).
      edestruct IHws as (r2 & Hr12 & Hr23); eauto 10.
  Qed.

  (** *** Properties *)

  Lemma cc_star_fold_l:
    ccref (1 + cc @ cc_star) cc_star.
  Proof.
    exists
      (fun w _ _ =>
         match w with
         | inl tt => nil
         | inr (w, ws, q) => (w, q) :: ws
         end).
    intros [[] | [[w ws] q]] q1 q2; simpl.
    - intros [].
      simpl; eauto.
    - intros [Hqs Hq].
      simpl; eauto.
  Qed.

  Lemma cc_star_fold_r:
    ccref (1 + cc_star @ cc) cc_star.
  Proof.
    exists
      (fun w q1 q2 =>
         match w with
         | inl tt => nil
         | inr (ws, w, q) => ws ++ (w, q2) :: nil
         end).
    intros [[] | [[ws w] q]] q1 q2; simpl.
    - intros [].
      tauto.
    - intros [Hqs Hq].
      split.
      {
        eapply cc_star_mq_app_intro; simpl; eauto.
      }
      intros r1 r2 Hr.
      edestruct cc_star_mr_app_elim as (r & Hr1 & Hr2); eauto; simpl; eauto.
      simpl in Hr2. destruct Hr2 as (? & Hr2 & ?); subst; eauto.
  Qed.

  Lemma cc_id_star:
    ccref 1 cc_star.
  Proof.
    rewrite <- cc_star_fold_r.
    apply cc_join_ub_l.
  Qed.

  Lemma cc_one_star:
    ccref cc cc_star.
  Proof.
    rewrite <- cc_star_fold_r.
    rewrite <- cc_join_ub_r.
    rewrite <- cc_star_fold_r.
    rewrite <- cc_join_ub_l.
    rewrite cc_compose_id_left.
    reflexivity.
  Qed.
End STAR.

Global Instance cc_star_ref li:
  Proper (ccref ++> ccref) (@cc_star li).
Proof.
  intros cc cc' [f Hcc].
  exists
    (fix F ws q1 q2 :=
       match ws with
       | nil => nil
       | (w, q) :: ws' => (f w q1 q, q) :: F ws' q q2
       end).
  intros ws.
  induction ws as [ | [w q] ws IHws]; simpl.
  - intros q _ [].
    simpl; eauto.
  - intros q1 q2 [Hq1 Hq2].
    edestruct Hcc as (Hq1' & Hr1); eauto.
    edestruct IHws as (Hq2' & Hr2); eauto.
    clear Hq1 Hq2.
    simpl in *.
    split; eauto.
    intros r1 r2 (r & Hr1' & Hr2'); eauto.
Qed.


(** * Composition theorems *)

Require Import Axioms.
Require Import Coqlib.
Require Import Values.
Require Import Memory.

(** ** Composition lemmas *)

Global Instance compose_meminj_incr:
  Proper (inject_incr ++> inject_incr ++> inject_incr) compose_meminj.
Proof.
  intros f1 f2 Hf g1 g2 Hg b xb xdelta.
  unfold compose_meminj.
  destruct (f1 b) as [[b' delta] | ] eqn:Hb'; try discriminate.
  erewrite Hf by eauto.
  destruct (g1 b') as [[b'' delta'] | ] eqn:Hb''; try discriminate.
  erewrite Hg by eauto.
  tauto.
Qed.

Lemma compose_meminj_separated f12 f23 f12' f23' m1 m2 m3:
  Mem.inject f12 m1 m2 ->
  inject_incr f12 f12' ->
  inject_separated f12 f12' m1 m2 ->
  Mem.inject f23 m2 m3 ->
  inject_separated f23 f23' m2 m3 ->
  inject_separated (compose_meminj f12 f23) (compose_meminj f12' f23') m1 m3.
Proof.
  intros Hm12 Hincr12 Hsep12 Hm23 Hsep23 b1 b3 delta Hb1 Hb1'.
  unfold compose_meminj in *.
  destruct (f12 b1) as [[b2 delta12] | ] eqn:Hb2.
  (** If the new block was already mapped in [f12], we have a
    contradiction: it could not have been invalid in [m2]. *)
  - erewrite Hincr12 in Hb1' by eauto.
    destruct (f23  b2) as [[? delta23] | ] eqn:Hb3; try discriminate.
    destruct (f23' b2) as [[? delta23] | ] eqn:Hb3'; try discriminate.
    edestruct Hsep23 as [Hvalid2 _]; eauto.
    destruct Hvalid2.
    eapply Mem.valid_block_inject_2; eauto.
  (** Otherwise, it must not have been mapped in [f23] either,
    because that would imply [b2] is valid in [m2] as well. *)
  - destruct (f12' b1) as [[b2 delta12] | ] eqn:Hb2'; try discriminate.
    destruct (f23' b2) as [[?  delta23] | ] eqn:Hb3'; inv Hb1'.
    edestruct Hsep12 as [? Hvalid2]; eauto.
    edestruct Hsep23; eauto.
    destruct (f23 b2) as [[? ?] | ] eqn:?; eauto.
    destruct Hvalid2.
    eapply Mem.valid_block_inject_1; eauto.
Qed.

Lemma flat_inj_idemp thr:
  compose_meminj (Mem.flat_inj thr) (Mem.flat_inj thr) = Mem.flat_inj thr.
Proof.
  apply functional_extensionality; intros b.
  unfold compose_meminj, Mem.flat_inj.
  destruct Block.lt_dec eqn:Hb; eauto.
  rewrite Hb.
  reflexivity.
Qed.

(** ** Triangular diagrams *)

Lemma cc_extends_inject_triangle:
  ccref cc_inject_triangle (cc_extends_triangle @ cc_inject_triangle).
Proof.
  exists (fun f q1 q3 => (tt, f, q1)).
  intros f q1 q3 Hq.
  split.
  {
    simpl in Hq |- *.
    eauto.
  }
  intros [v1' m1'] [v3' m3'] ([v2' m2'] & Hr12 & Hr23).
  destruct Hq as [id sg vargs m Hvargs Hm].
  simpl in *.
  destruct Hr12 as [Hv12' Hm12'], Hr23 as (f' & Hv23' & Hm23' & Hincr & Hsep).
  eauto 10 using Mem.val_lessdef_inject_compose, Mem.extends_inject_compose.
Qed.

Lemma cc_inject_extends_triangle:
  ccref cc_inject_triangle (cc_inject_triangle @ cc_extends_triangle).
Proof.
  exists (fun f q1 q3 => (f, tt, q3)).
  intros f q1 q3 Hq.
  split.
  {
    simpl in Hq |- *.
    eauto.
  }
  intros [v1' m1'] [v3' m3'] ([v2' m2'] & Hr12 & Hr23).
  destruct Hq as [id sg vargs m Hvargs Hm].
  simpl in *.
  destruct Hr12 as (f' & Hv12' & Hm12' & Hincr & Hsep), Hr23 as [Hv23' Hm23'].
  eauto 10 using Mem.val_inject_lessdef_compose, Mem.inject_extends_compose.
Qed.

Lemma cc_inject_inject_triangle:
  ccref cc_inject_triangle (cc_inject_triangle @ cc_inject_triangle).
Proof.
  exists (fun f q3 q => (f, f, q)).
  intros f q3 q Hq.
  assert (q3 = q) by (destruct Hq; eauto); subst.
  simpl in *.
  split; eauto.
  destruct Hq as [id sg vargs m Hvargs Hm].
  simpl.
  intros [v1' m1'] [v3' m3'] ([v2' m2'] & H12 & H23).
  destruct H12 as (f12' & Hv12' & Hm12' & Hincr12 & Hsep12).
  destruct H23 as (f23' & Hv23' & Hm23' & Hincr23 & Hsep23).
  exists (compose_meminj f12' f23').
  split; eauto using val_inject_compose.
  split; eauto using Mem.inject_compose.
  split.
  - rewrite <- flat_inj_idemp.
    eapply compose_meminj_incr; eauto.
  - rewrite <- flat_inj_idemp.
    eapply compose_meminj_separated; eauto using Mem.neutral_inject.
Qed.

(** ** Relationship between rectangular and triangular diagrams *)

(** Triangular diagrams are a special case of the rectangular ones. *)

Lemma cc_inj_injt:
  ccref cc_inject_triangle cc_inject.
Proof.
  exists (fun _ q1 '(cq _ _ _ m) => Mem.flat_inj (Mem.nextblock m)).
  intros _ _ _ [id sg vargs m Hvargs Hm]; simpl.
  intuition.
  - destruct r2 as [vres2 m2'].
    destruct H as (f' & Hvres & Hm' & Hm1' & Hm2' & Hincr & Hsep).
    exists f'; intuition.
Qed.

Lemma cc_ext_extt:
  ccref cc_extends_triangle cc_extends.
Proof.
  exists (fun _ _ _ => tt).
  intros [] q _ []; simpl.
  intuition.
  - destruct q; constructor; intuition.
    induction cq_args; constructor; eauto.
    apply Mem.extends_refl.
  - destruct q as [vargs m], r2 as [vres2 m2'].
    simpl in *.
    tauto.
Qed.
