Require Export LogicalRelations.
Require Export List.
Require Export Globalenvs.
Require Export Events.
Require Export LanguageInterface.
Require Export Smallstep.

Require Import Axioms.
Require Import Coqlib.
Require Import Integers.
Require Import Values.
Require Import Memory.
Require Import CKLRAlgebra.
Require Import Extends.
Require Import Inject.
Require Import InjectNeutral.
Require Import InjectFootprint.

(** Algebraic structures on calling conventions. *)

(** * Refinement and equivalence *)

(** ** Definition *)

(** The following relation asserts that the calling convention [cc] is
  refined by the calling convention [cc'], meaning that any
  [cc']-simulation is also a [cc]-simulation. *)

Definition ccref {li1 li2} (cc cc': callconv li1 li2) :=
  forall w q1 q2,
    match_query cc w q1 q2 ->
    exists w',
      match_query cc' w' q1 q2 /\
      forall r1 r2,
        match_reply cc' w' r1 r2 ->
        match_reply cc w r1 r2.

Definition cceqv {li1 li2} (cc cc': callconv li1 li2) :=
  ccref cc cc' /\ ccref cc' cc.

Global Instance ccref_preo li1 li2:
  PreOrder (@ccref li1 li2).
Proof.
  split.
  - intros cc w q1 q2 Hq.
    eauto.
  - intros cc cc' cc'' H' H'' w q1 q2 Hq.
    edestruct H' as (w' & Hq' & Hr'); eauto.
    edestruct H'' as (w'' & Hq'' & Hr''); eauto.
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

(** To prove [forward_simulation_ccref] below, we need the axiom of
  choice. This is because to give the simulation relation [R'] for the
  new forward simulation, we need to extract the target world [w']
  from the existential in our [ccref] hypothesis. *)

Require Import Basics.
Require Import ClassicalChoice.

Inductive matching_query {li1 li2} (cc: callconv li1 li2) :=
  mqi w q1 q2: match_query cc w q1 q2 -> matching_query cc.

Lemma ccref_functional {li1 li2} (cc cc': callconv li1 li2):
  ccref cc cc' ->
  exists (f: matching_query cc -> ccworld cc'),
    forall w q1 q2 (Hq: match_query cc w q1 q2),
      match_query cc' (f (mqi cc w q1 q2 Hq)) q1 q2 /\
      forall r1 r2,
        match_reply cc' (f (mqi cc w q1 q2 Hq)) r1 r2 ->
        match_reply cc w r1 r2.
Proof.
  intros H. red in H.
  set (R := fun '(mqi w q1 q2 Hq) w' =>
         match_query cc' w' q1 q2 /\
         subrel (match_reply cc' w') (match_reply cc w)).
  assert (H': forall Q, exists w', R Q w') by (intros [w q1 q2 Hq]; eauto).
  apply choice in H'.
  destruct H' as (f & Hf).
  exists f.
  intros.
  specialize (Hf (mqi _ w q1 q2 Hq)).
  apply Hf.
Qed.

Global Instance forward_simulation_ccref {liA1 liB1 liA2 liB2}:
  Monotonic
    (@forward_simulation liA1 liB1 liA2 liB2)
    (ccref ++> ccref --> subrel).
Proof.
  intros ccA' ccA HA ccB' ccB HB L1 L2.
  apply ccref_functional in HA.
  apply ccref_functional in HB.
  revert HA HB.
  intros [fA HA] [fB HB] [I lt R H].
  set (R' := fun w i s1 s2 =>
               exists q1 q2 (Hq: match_query ccB w q1 q2),
                 R (fB (mqi _ w q1 q2 Hq)) i s1 s2 /\
                 forall r1 r2,
                   match_reply ccB' (fB (mqi _ w q1 q2 Hq)) r1 r2 ->
                   match_reply ccB w r1 r2).
  eexists I lt R'.
  destruct H.
  split; eauto.
  - intros w q1 q2 Hq s1 Hs1.
    destruct (HB w q1 q2 Hq) as (Hq' & Hr').
    edestruct fsim_match_initial_states as (i & s2 & Hs2 & Hs); eauto.
    exists i, s2; intuition eauto.
    exists q1, q2; intuition eauto.
  - intros w i s1 s2 (qB1 & qB2 & HqB & Hs & HrB) q1 AE1 Hs1.
    subst R'. simpl in *. edestruct (HB _ _ _ HqB) as [HBq HBr]; eauto.
    edestruct fsim_match_external as (wA' & q2 & AE2 & Hq & Hs2 & Hr); eauto.
    edestruct (HA _ _ _ Hq) as [HAq HAr]; eauto.
    exists (fA (mqi _ wA' q1 q2 Hq)), q2, AE2.
    intuition eauto.
    edestruct Hr as (j & s2' & Hs2' & Hs'); eauto.
    exists j, s2'; intuition eauto.
  - intros w i s1 s2 r1 (q1 & q2 & Hq & Hs & HrB) Hr1.
    edestruct (HB _ _ _ Hq) as [HBq HBr]; eauto.
    edestruct fsim_match_final_states as (r2 & Hr & Hr2); eauto.
  - intros w s1 t s1' Hstep i s2 (q1 & q2 & Hq & Hs & HrB).
    subst R'. simpl in *. edestruct (HB _ _ _ Hq) as [HBq HBr]; eauto.
    edestruct fsim_simulation as (i' & s2' & Hstep' & Hs'); eauto 10.
Qed.

Global Instance forward_simulation_ccref_params:
  Params (@forward_simulation) 4.


(** * Properties of [cc_compose] *)

(** Language interfaces and calling conventions form a category, with
  [cc_id] as the identity arrow and [cc_compose] as the composition. *)

Lemma cc_compose_id_left {li1 li2} (cc: callconv li1 li2):
  cceqv (cc_compose cc_id cc) cc.
Proof.
  split.
  - intros [[ ] w] q1 q3 (q2 & Hq12 & Hq23). simpl in *. subst.
    exists w; intuition eauto.
    eexists; eauto.
  - intros w q1 q2 Hq.
    exists (tt, w); split.
    + eexists; simpl; eauto.
    + intros r1 r3 (r2 & Hr12 & Hr23); simpl in *.
      congruence.
Qed.

Lemma cc_compose_id_right {li1 li2} (cc: callconv li1 li2):
  cceqv (cc_compose cc cc_id) cc.
Proof.
  split.
  - intros [w [ ]] q1 q3 (q2 & Hq12 & Hq23). simpl in *. subst.
    exists w; intuition eauto.
    eexists; eauto.
  - intros w q1 q2 Hq.
    exists (w, tt); split.
    + eexists; simpl; eauto.
    + intros r1 r3 (r2 & Hr12 & Hr23); simpl in *.
      congruence.
Qed.

Lemma cc_compose_assoc {A B C D} cc1 cc2 cc3:
  cceqv
    (@cc_compose A C D (cc_compose cc1 cc2) cc3)
    (@cc_compose A B D cc1 (cc_compose cc2 cc3)).
Proof.
  split.
  - intros [[w1 w2] w3] qa qd (qc & (qb & Hqab & Hqbc) & Hqcd).
    exists (w1, (w2, w3)). simpl in *. unfold rel_compose.
    split; eauto.
    intros ra rd (rb & Hrab & rc & Hrbc & Hrcd); eauto.
  - intros [w1 [w2 w3]] qa qd (qb & Hqab & qc & Hqbc & Hqcd).
    exists ((w1, w2), w3). simpl in *. unfold rel_compose.
    split; eauto.
    intros ra rd (rc & (rb & Hrab & Hrbc) & Hrcd); eauto.
Qed.

(** In addition, composition is monotonic under [cc_ref]. *)

Global Instance cc_compose_ref li1 li2 li3:
  Proper (ccref ++> ccref ++> ccref) (@cc_compose li1 li2 li3).
Proof.
  intros cc12 cc12' H12 cc23 cc23' H23 (w12, w23) q1 q3 (q2 & Hq12 & Hq23).
  simpl in *. unfold rel_compose.
  edestruct (H12 w12 q1 q2 Hq12) as (w12' & Hq12' & H12').
  edestruct (H23 w23 q2 q3 Hq23) as (w23' & Hq23' & H23').
  exists (w12', w23').
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
      ccworld := ccworld cc1 + ccworld cc2;
      match_senv := copair (match_senv cc1) (match_senv cc2);
      match_query := copair (match_query cc1) (match_query cc2);
      match_reply := copair (match_reply cc1) (match_reply cc2);
    |}.

  (** [cc_join] is the least upper bound with respect to [ccref]. *)

  Lemma cc_join_ub_l cc1 cc2:
    ccref cc1 (cc_join cc1 cc2).
  Proof.
    intros w q1 q2 Hq.
    exists (inl w).
    simpl; eauto.
  Qed.

  Lemma cc_join_ub_r cc1 cc2:
    ccref cc2 (cc_join cc1 cc2).
  Proof.
    intros w q1 q2 Hq.
    exists (inr w).
    simpl; eauto.
  Qed.

  Lemma cc_join_lub cc1 cc2 cc:
    ccref cc1 cc ->
    ccref cc2 cc ->
    ccref (cc_join cc1 cc2) cc.
  Proof.
    intros H1 H2 w q1 q2 Hq.
    destruct w; simpl in *; eauto.
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

Require Import KLR.

Section STAR.
  Context {li: language_interface} (cc: callconv li li).

  (** *** Definition *)

  Fixpoint klr_fold {W A} (R: klr W A A) (ws: list W) :=
    match ws with
      | nil => eq
      | w::ws => rel_compose (R w) (klr_fold R ws)
    end.

  Definition cc_star: callconv li li :=
    {|
      ccworld := list (ccworld cc);
      match_senv := klr_fold (match_senv cc);
      match_query := klr_fold (match_query cc);
      match_reply := klr_fold (match_reply cc);
    |}.

  (** *** Useful lemmas *)

  Lemma klr_fold_app_intro {W A} R (u v: list W) (x y z: A):
    klr_fold R u x y ->
    klr_fold R v y z ->
    klr_fold R (u ++ v) x z.
  Proof.
    revert x.
    induction u as [ | u us IHus]; simpl.
    - congruence.
    - intros x (x' & Hx & Hx'). eexists. eauto.
  Qed.

  Lemma klr_fold_app_elim {W A} R (u v: list W) (x z: A):
    klr_fold R (u ++ v) x z ->
    exists y, klr_fold R u x y /\ klr_fold R v y z.
  Proof.
    revert x.
    induction u as [ | u us IHus]; simpl.
    - firstorder.
    - intros x (x' & Hx & H).
      edestruct IHus as (y & Hx' & Hyz); eauto.
      exists y. split; eauto. exists x'; eauto.
  Qed.

  (** *** Properties *)

  Lemma cc_star_fold_l:
    ccref (1 + cc @ cc_star) cc_star.
  Proof.
    intros [[ ] | [w ws]] q1 q2 Hq; simpl.
    - exists nil.
      simpl; eauto.
    - exists (w :: ws).
      simpl; eauto.
  Qed.

  Lemma cc_star_fold_r:
    ccref (1 + cc_star @ cc) cc_star.
  Proof.
    intros [[ ] | [ws w]] q1 q3; simpl.
    - intros [ ].
      exists nil. simpl. tauto.
    - intros (q2 & Hqs & Hq).
      exists (ws ++ w :: nil).
      unfold rel_compose; split.
      + eapply klr_fold_app_intro; simpl; eauto.
        eexists; eauto.
      + intros r1 r2 Hr.
        edestruct (klr_fold_app_elim (match_reply cc)) as (r & Hr1 & Hr2); eauto.
        destruct Hr2 as (? & Hr2 & ?); simpl in *; subst. eauto.
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
  intros cc cc' Hcc ws.
  induction ws as [ | w ws IHws]; simpl.
  - intros q _ [ ].
    exists nil. simpl. eauto.
  - intros q1 q2 (q & Hq1 & Hq2).
    edestruct Hcc as (w' & Hq1' & Hr1); eauto.
    edestruct IHws as (ws' & Hq2' & Hr2); eauto.
    clear Hq1 Hq2.
    exists (w'::ws').
    simpl in *. unfold rel_compose in *.
    split; eauto.
    intros r1 r2 (r & Hr1' & Hr2'); eauto.
Qed.


(** * Composition theorems *)

Lemma match_c_query_dom f q1 q2:
  match_c_query inj f q1 q2 ->
  match_c_query inj (meminj_dom f) q1 q1.
Proof.
  destruct q1 as [fb1 sg1 vargs1 m1], q2 as [fb2 sg2 vargs2 m2]. simpl.
  intros [Hfb Hsg Hargs Hm]; simpl in *.
  constructor; simpl; eauto using block_inject_dom, mem_inject_dom.
  apply val_inject_list_rel.
  eapply val_inject_list_dom.
  apply val_inject_list_rel.
  eassumption.
Qed.

(** ** Rectangular diagrams *)

Lemma match_c_query_compose R12 R23 w12 w23:
  eqrel
    (match_c_query (R12 @ R23) (w12, w23))
    (rel_compose (match_c_query R12 w12) (match_c_query R23 w23)).
Proof.
  split.
  - intros [fb1 sg1 vargs1 m1] [fb3 sg3 vargs3 m3] [Hfb Hsg Hvargs Hm].
    simpl in *.
    apply block_inject_compose in Hfb.
    rewrite val_inject_compose in Hvargs. apply list_rel_compose in Hvargs.
    destruct Hfb as (fb2 & Hfb12 & Hfb23).
    destruct Hvargs as (vargs2 & Hvargs12 & Hvargs23).
    destruct Hm as (m2 & Hm12 & Hm23).
    exists (cq fb2 sg1 vargs2 m2); split; constructor; simpl; rauto.
  - intros [fb1 sg1 vargs1 m1] [fb3 sg3 vargs3 m3].
    intros ([fb2 sg2 vargs2 m2]&[Hfb12 Hsg12 Hv12 Hm12]&[Hfb23 Hsg23 Hv23 Hm23]).
    simpl in *.
    constructor; simpl.
    + apply block_inject_compose.
      eexists; split; eauto.
    + congruence.
    + rewrite val_inject_compose.
      apply list_rel_compose.
      eexists; split; eauto.
    + eexists; split; eauto.
Qed.

Lemma cc_c_ref:
  Monotonic (@cc_c) (subcklr ++> ccref).
Proof.
  intros Q R HQR. red in HQR |- *.
  intros w [fb1 sg1 vargs1 m1] [fb2 sg2 vargs2 m2] [Hfb Hsg Hvargs Hm].
  specialize (HQR w m1 m2 Hm) as (wr & HmR & Hincr & HQR').
  exists wr.
  simpl in *.
  split.
  - constructor; simpl; rauto.
  - intros [vres1 m1'] [vres2 m2'] (wr' & Hw' & Hvres & Hm'). simpl in *.
    specialize (HQR' wr' m1' m2' Hm' Hw') as (w' & HmQ' & HwQ' & Hincr').
    rauto.
Qed.

Lemma cc_c_compose R12 R23:
  cceqv (cc_c (R12 @ R23)) (cc_c R12 @ cc_c R23).
Proof.
  split.
  - intros [w12 w23] q1 q3 Hq.
    apply match_c_query_compose in Hq.
    exists (w12, w23).
    split; eauto.
    intros [vres1 m1'] [vres3 m3'] ([vres2 m2'] & H12 & H23).
    destruct H12 as (w12' & Hw12' & Hvres12 & Hm12').
    destruct H23 as (w23' & Hw23' & Hvres23 & Hm23').
    simpl in *.
    exists (w12', w23'); split; repeat rstep; simpl.
    + apply val_inject_compose. eexists; eauto.
    + eexists; eauto.
  - intros [w12 w23] q1 q3 Hq.
    apply match_c_query_compose in Hq.
    simpl in *.
    exists (w12, w23).
    split; eauto.
    intros [vres1 m1'] [vres3 m3'] ([w12' w23'] & [Hw12' Hw23'] & Hvres & Hm').
    red in Hvres. simpl in *.
    apply val_inject_compose in Hvres.
    destruct Hvres as (vres2 & Hvres12 & Hvres23).
    destruct Hm' as (m2' & Hm12' & Hm23').
    exists (vres2, m2'); split; rauto.
Qed.

(** ** Triangular diagrams *)

Lemma cc_c_tr_ref:
  Monotonic (@cc_c_tr) (subcklr ++> ccref).
Proof.
  intros Q R HQR. red in HQR |- *.
  intros w _ _ [[fb sg vargs m] Hw [Hfb Hsg Hvargs Hm]].
  simpl in *.
  specialize (HQR w m m Hm) as (wr & HmR & Hincr & HQR').
  exists wr.
  split.
  - constructor; simpl.
    + etransitivity; rauto.
    + constructor; simpl; rauto.
  - intros [vres1 m1'] [vres2 m2'] (w' & Hw' & Hvres & Hm'). simpl in *.
    specialize (HQR' w' m1' m2' Hm' Hw') as (wq' & HmQ' & HwQ' & Hincr').
    rauto.
Qed.

Lemma cc_c_tr_compose Q R:
  ccref (cc_c_tr Q @ cc_c_tr R) (cc_c_tr (Q @ R)).
Proof.
  intros [wq wr] q1 q3 (q2 & Hq12 & Hq23).
  simpl in *.
  destruct Hq12 as [q Hincr12 Hq12].
  destruct Hq23 as [q Hincr23 Hq23].
  exists (wq, wr). split.
  - constructor.
    + simpl.
      rewrite <- Hincr12, <- Hincr23.
      unfold inject_incr, Mem.flat_inj, compose_meminj.
      intros b b' delta.
      destruct Block.lt_dec eqn:Hb; inversion 1; subst.
      rewrite Hb.
      reflexivity.
    + apply match_c_query_compose.
      eexists; eauto.
  - intros [vres1 m1'] [vres3 m3'] ([w12' w23'] & [Hw12' Hw23'] & Hvres & Hm').
    red in Hvres. apply val_inject_compose in Hvres.
    destruct Hvres as (vres2 & Hvres12 & Hvres23).
    destruct Hm' as (m2' & Hm12' & Hm23').
    simpl in *.
    eexists; split; rauto.
Qed.

Global Instance flat_inject_id thr:
  Related (Mem.flat_inj thr) inject_id inject_incr.
Proof.
  intros b1 b2 delta.
  unfold Mem.flat_inj, inject_id.
  destruct Block.lt_dec; try discriminate.
  auto.
Qed.

Lemma compose_meminj_id_left f:
  compose_meminj inject_id f = f.
Proof.
  apply functional_extensionality. intros b.
  unfold compose_meminj, inject_id.
  destruct (f b) as [[b' delta] | ]; eauto.
Qed.

Lemma compose_meminj_id_right f:
  compose_meminj f inject_id = f.
Proof.
  apply functional_extensionality. intros b.
  unfold compose_meminj, inject_id.
  destruct (f b) as [[b' delta] | ]; eauto.
  replace (delta + 0) with delta by xomega; eauto.
Qed.

Lemma incr_flat_inj_eq f m1 m2:
  Mem.inject f m1 m2 ->
  inject_incr (Mem.flat_inj (Mem.nextblock m1)) f ->
  f = Mem.flat_inj (Mem.nextblock m1).
Proof.
  intros Hm Hf.
  apply functional_extensionality. intros b.
  unfold Mem.flat_inj in *.
  specialize (Hf b); simpl in Hf.
  destruct Block.lt_dec; eauto.
  destruct (f b) as [[b' delta] | ] eqn:Hb; eauto.
  elim n. eapply Mem.valid_block_inject_1; eauto.
Qed.

Lemma cc_extends_inject_triangle:
  ccref (cc_c_tr inj) (cc_c_tr ext @ cc_c_tr inj).
Proof.
  intros f _ _ [q Hf [Hfb Hsg Hvargs Hm]].
  exists (tt, f). simpl in *.
  eapply incr_flat_inj_eq in Hf; eauto; subst.
  split.
  - exists q.
    split; constructor; eauto.
    + rauto.
    + constructor; try reflexivity.
      rauto.
      apply Mem.extends_refl.
    + constructor; eauto.
  - intros r1 r3 (r2 & ([ ] & _ & [Hv12' Hm12']) & (f' & Hf' & [Hv23' Hm23'])).
    exists f'; split; eauto.
    split.
    + eapply (Mem.val_lessdef_inject_compose _ _ (fst r2)); eauto.
      apply val_inject_id; eauto.
    + eapply Mem.extends_inject_compose; eauto.
Qed.

Lemma cc_inject_extends_triangle:
  ccref (cc_c_tr inj) (cc_c_tr inj @ cc_c_tr ext).
Proof.
  intros f _ _ [q Hf [Hfb Hsg Hvargs Hm]].
  exists (f, tt). simpl in *.
  eapply incr_flat_inj_eq in Hf; eauto; subst.
  split.
  - exists q.
    split; constructor; eauto.
    + constructor; eauto.
    + rauto.
    + constructor; try reflexivity.
      rauto.
      apply Mem.extends_refl.
  - intros r1 r3 (r2 & (f' & Hf' & [Hv12' Hm12']) & ([ ] & _ & [Hv23' Hm23'])).
    exists f'; split; eauto.
    split.
    + eapply (Mem.val_inject_lessdef_compose _ _ (fst r2)); eauto.
      apply val_inject_id; eauto.
    + eapply Mem.inject_extends_compose; eauto.
Qed.

Lemma cc_inject_inject_triangle:
  ccref (cc_c_tr inj) (cc_c_tr inj @ cc_c_tr inj).
Proof.
  intros f _ _ [q Hf [Hfb Hsg Hvargs Hm]].
  exists (f, f). simpl in *.
  eapply incr_flat_inj_eq in Hf; eauto; subst.
  split.
  - exists q.
    refine ((fun x => conj x x) _).
    constructor; eauto.
    constructor; eauto.
  - intros r1 r3 (r2 & (f12&Hf12&[Hv12' Hm12']) & (f23&Hf23&[Hv23' Hm23'])).
    exists (compose_meminj f12 f23); split; eauto.
    + rewrite <- flat_inj_idemp. rauto.
    + split.
      * apply val_inject_compose. eexists; eauto.
      * eapply Mem.inject_compose; eauto.
Qed.

(** ** Relationship between rectangular and triangular diagrams *)

(** Triangular diagrams are a special case of the rectangular ones. *)

Lemma cc_c_tr_r R:
  ccref (cc_c_tr R) (cc_c R).
Proof.
  intros w _ _ [q Hq H].
  exists w; intuition eauto.
Qed.

(** More importantly, rectangular diagrams can absorb triangular ones
  in the following way. *)

Global Instance block_inject_refl:
  Reflexive (block_inject inject_id).
Proof.
  intro.
  exists 0.
  reflexivity.
Qed.

Global Instance mem_extends_refl:
  Reflexive Mem.extends.
Proof.
  intro. apply Mem.extends_refl.
Qed.

Lemma cc_extt_ext:
  ccref (cc_c ext) (cc_c_tr ext @ cc_c ext).
Proof.
  intros [ ] q1 q2 Hq.
  exists (tt, tt). simpl. split.
  - eexists; split; eauto.
    constructor; simpl.
    + rauto.
    + destruct q1. constructor; simpl; reflexivity.
  - intros r1 r3 (r2 & ([ ] & _ & Hv12' & Hm12') & ([ ] & _ & Hv23' & Hm23')).
    exists tt; split; [rauto | ]; split.
    + rewrite <- (compose_meminj_id_right inject_id).
      apply val_inject_compose. eexists; split; eauto.
    + eapply Mem.extends_extends_compose; eauto.
Qed.

Lemma match_c_query_injn_inj nb q1 q2:
  match_c_query injn nb q1 q2 <->
  match_c_query inj (Mem.flat_inj nb) q1 q2 /\
  Mem.nextblock (cq_mem q1) = nb /\
  Mem.nextblock (cq_mem q2) = nb.
Proof.
  split.
  - intros [Hfb Hsg Hvargs [Hm Hnb]].
    simpl in *. red in Hnb.
    destruct Hnb. split; eauto.
    constructor; eauto.
  - intros ([Hfb Hsg Hvargs Hm] & Hnb1 & Hnb2).
    constructor; simpl; eauto.
    split; eauto.
    red. rewrite Hnb1, Hnb2. constructor.
Qed.
