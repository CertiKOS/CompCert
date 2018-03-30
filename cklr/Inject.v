Require Import Axioms.
Require Import Events.
Require Export CKLR.
Require Import CKLRAlgebra.


(** * [Mem.inject] as a CKLR *)

Global Instance inject_incr_preo:
  PreOrder inject_incr.
Proof.
  split.
  - exact inject_incr_refl.
  - exact inject_incr_trans.
Qed.

Program Definition inj : cklr :=
  {|
    world := meminj;
    world_kf := {| acc := inject_incr |};
    mi f := f;
    match_mem := Mem.inject;
  |}.

Next Obligation. (* inject_incr vs. inject_incr *)
  rauto.
Qed.

Next Obligation. (* Mem.alloc *)
  intros f m1 m2 Hm lo hi.
  destruct (Mem.alloc m1 lo hi) as [m1' b1] eqn:Hm1'.
  edestruct Mem.alloc_parallel_inject
    as (f' & m2' & b2 & Hm2' & Hm' & Hf' & Hb2 & _);
    eauto using Zle_refl.
  rewrite Hm2'.
  exists f'; split; repeat rstep.
  assumption.
Qed.

Next Obligation. (* Mem.free *)
  intros f m1 m2 Hm [[b1 lo1] hi1] [[b2 lo2] hi2] Hr.
  simpl. red.
  destruct (Mem.free m1 b1 lo1 hi1) as [m1'|] eqn:Hm1'; [|rauto].
  inv Hr. inv H0.
  edestruct Mem.free_parallel_inject as (m2' & Hm2' & Hm'); eauto.
  replace (lo1 + delta + sz) with (lo1 + sz + delta) by xomega.
  rewrite Hm2'. rauto.
Qed.

Next Obligation. (* Mem.load *)
  intros f chunk m1 m2 Hm _ _ [b1 ofs1 b2 delta Hptr].
  simpl. red.
  destruct (Mem.load chunk m1 b1 ofs1) as [v1|] eqn:Hv1; [|rauto].
  edestruct Mem.load_inject as (v2 & Hv2 & Hv); eauto.
  rewrite Hv2. rauto.
Qed.

Next Obligation. (* Mem.store *)
  intros f chunk m1 m2 Hm _ _ [b1 ofs1 b2 delta Hptr] v1 v2 Hv.
  simpl. red.
  destruct (Mem.store chunk m1 b1 ofs1 v1) as [m1'|] eqn:Hm1'; [|rauto].
  edestruct Mem.store_mapped_inject as (m2' & Hm2' & Hm'); eauto.
  rewrite Hm2'. rauto.
Qed.

Next Obligation. (* Mem.loadbytes *)
  intros f m1 m2 Hm _ _ [b1 ofs1 b2 delta Hptr] sz.
  simpl. red.
  destruct (Mem.loadbytes m1 b1 ofs1 sz) as [vs1|] eqn:Hvs1; [|rauto].
  edestruct Mem.loadbytes_inject as (vs2 & Hvs2 & Hvs); eauto.
  rewrite Hvs2. rauto.
Qed.

Next Obligation. (* Mem.storebytes *)
  intros f m1 m2 Hm [b1 ofs1] [b2 ofs2] Hptr vs1 vs2 Hvs.
  simpl. red.
  destruct (Mem.storebytes m1 _ _ _) as [m1'|] eqn:Hm1'; [|constructor].
  assert (vs1 = nil \/ vs1 <> nil) as [Hvs1|Hvs1].
  { destruct vs1; constructor; congruence. }
  - subst. inv Hvs.
    edestruct (Mem.range_perm_storebytes m2 b2 ofs2 nil) as [m2' Hm2'].
    {
      intros ofs. simpl. xomega.
    }
    rewrite Hm2'.
    constructor.
    exists f; split; try rauto.
    eapply Mem.storebytes_empty_inject; eauto.
  - assert (ptr_inject f (b1, ofs1) (b2, ofs2)) as Hptr'.
    {
      destruct Hptr as [Hptr|Hptr]; eauto.
      inversion Hptr as [_ _ [xb1 xofs1 xb2 delta Hb]]; clear Hptr; subst.
      unfold ptrbits_unsigned.
      erewrite Mem.address_inject; eauto.
      apply Mem.storebytes_range_perm in Hm1'.
      eapply Hm1'.
      destruct vs1; try congruence.
      simpl. xomega.
    }
    inv Hptr'.
    edestruct Mem.storebytes_mapped_inject as (m2' & Hm2' & Hm'); eauto.
    rewrite Hm2'. rauto.
Qed.

Next Obligation. (* Mem.perm *)
  intros f m1 m2 Hm _ _ [b1 ofs1 b2 delta Hb] p k H.
  eapply Mem.perm_inject; eauto.
Qed.

Next Obligation. (* Mem.valid_block *)
  intros f m1 m2 Hm b1 b2 [delta Hb].
  split; intro.
  - eapply Mem.valid_block_inject_2; eauto.
  - eapply Mem.valid_block_inject_1; eauto.
Qed.

Next Obligation. (* Mem.meminj_no_overlap *)
  eapply Mem.mi_no_overlap; eauto.
Qed.

Next Obligation. (* representable *)
  rewrite <- (Ptrofs.unsigned_repr ofs1) by xomega.
  eapply Mem.mi_representable; eauto.
  rewrite Ptrofs.unsigned_repr by xomega.
  assumption.
Qed.

Next Obligation.
  eapply Mem.aligned_area_inject; eauto.
Qed.

Next Obligation. 
  eapply Mem.disjoint_or_equal_inject; eauto.
Qed.


(** * Useful theorems *)

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

(** ** The [meminj_dom] construction *)

(** The following injection is a sub-injection of [Mem.flat_inj],
  which contains only blocks mapped by the original injection [f].
  Like [Mem.flat_inj], it is a neutral element for composition
  with [f] on the left, but the fact that its domain and codomain
  correspond to the domain of [f] yields many desirable properties
  that do not hold for [Mem.flat_inj]. *)

Definition meminj_dom (f: meminj): meminj :=
  fun b => if f b then Some (b, 0) else None.

Lemma meminj_dom_compose f:
  compose_meminj (meminj_dom f) f = f.
Proof.
  apply functional_extensionality; intros b.
  unfold compose_meminj, meminj_dom.
  destruct (f b) as [[b' ofs] | ] eqn:Hfb; eauto.
  rewrite Hfb.
  replace (0 + ofs) with ofs by xomega.
  reflexivity.
Qed.

Lemma meminj_dom_idemp f:
  meminj_dom (meminj_dom f) = meminj_dom f.
Proof.
  eapply functional_extensionality; intro b.
  unfold meminj_dom.
  destruct (f b); eauto.
Qed.

Lemma val_inject_dom f v1 v2:
  Val.inject f v1 v2 ->
  Val.inject (meminj_dom f) v1 v1.
Proof.
  destruct 1; econstructor.
  - unfold meminj_dom.
    rewrite H.
    reflexivity.
  - rewrite Ptrofs.add_zero.
    reflexivity.
Qed.

Lemma memval_inject_dom f v1 v2:
  memval_inject f v1 v2 ->
  memval_inject (meminj_dom f) v1 v1.
Proof.
  destruct 1; econstructor.
  eapply val_inject_dom; eauto.
Qed.

Lemma val_inject_list_dom f vs1 vs2:
  Val.inject_list f vs1 vs2 ->
  Val.inject_list (meminj_dom f) vs1 vs1.
Proof.
  induction 1; constructor; eauto using val_inject_dom.
Qed.

Lemma mem_mem_inj_dom f m1 m2:
  Mem.mem_inj f m1 m2 ->
  Mem.mem_inj (meminj_dom f) m1 m1.
Proof.
  intros H.
  split.
  - unfold meminj_dom. intros b1 b2 delta ofs k p Hb1 Hp.
    destruct (f b1); inv Hb1.
    replace (ofs + 0) with ofs by xomega.
    auto.
  - unfold meminj_dom. intros b1 b2 delta chunk ofs p Hb1 Hrp.
    destruct (f b1) as [[b1' delta'] | ]; inv Hb1.
    eauto using Z.divide_0_r.
  - unfold meminj_dom at 1. intros b1 ofs b2 delta Hb1 Hp.
    destruct (f b1) as [[b1' delta'] | ] eqn:Hb1'; inv Hb1.
    replace (ofs + 0) with ofs by xomega.
    eapply memval_inject_dom.
    eapply Mem.mi_memval; eauto.
Qed.

Lemma mem_inject_dom f m1 m2:
  Mem.inject f m1 m2 ->
  Mem.inject (meminj_dom f) m1 m1.
Proof.
  intros H.
  split.
  - eapply mem_mem_inj_dom.
    eapply Mem.mi_inj; eauto.
  - unfold meminj_dom. intros.
    erewrite Mem.mi_freeblocks; eauto.
  - unfold meminj_dom; intros.
    destruct (f b) as [[b'' delta'] | ] eqn:Hb; inv H0.
    eapply Mem.valid_block_inject_1; eauto.
  - red. unfold meminj_dom. intros.
    destruct (f b1); inv H1.
    destruct (f b2); inv H2.
    eauto.
  - unfold meminj_dom. intros.
    destruct (f b); inv H0.
    split; try xomega.
    rewrite Z.add_0_r.
    apply Ptrofs.unsigned_range_2.
  - unfold meminj_dom. intros.
    destruct (f b1); inv H0.
    rewrite Z.add_0_r in H1; eauto.
Qed.

Lemma loc_unmapped_dom f b ofs:
  loc_unmapped (meminj_dom f) b ofs <->
  loc_unmapped f b ofs.
Proof.
  unfold meminj_dom, loc_unmapped.
  destruct (f b) as [[b' delta] | ].
  - split; discriminate.
  - reflexivity.
Qed.

(** ** CKLR composition theorems *)

Lemma inj_inj:
  subcklr inj (inj @ inj).
Proof.
  exists (fun f => (meminj_dom f, f)).
  exists (fun '(f12', f23') => compose_meminj f12' f23').
  simpl.
  intros f m1 m2 Hm.
  repeat apply conj.
  - exists m1; split; eauto using mem_inject_dom.
  - rewrite meminj_dom_compose.
    reflexivity.
  - intros [f12' f23'] m1' m3' (m2' & Hm12' & Hm23') [Hf12' Hf23']. simpl in *.
    repeat apply conj.
    + eapply Mem.inject_compose; eauto.
    + rewrite <- (meminj_dom_compose f). rauto.
    + reflexivity.
Qed.
