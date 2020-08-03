Require compcert.common.Memimpl.
Require MemoryX.

Import Coqlib.
Import Values.
Import Memimpl.
Import MemoryX.


(** Because we need the additional [storebytes_empty] property, we
have to modify the implementation of [storebytes]... *)

Definition is_empty {A: Type} (l: list A):
  {l = nil} + {l <> nil}.
Proof.
  destruct l; (left; congruence) || (right; congruence).
Defined.

Definition storebytes m b o l :=
  if is_empty l then Some m else Memimpl.Mem.storebytes m b o l.

(** ... and we have to again prove every property of [storebytes]
(fortunately, we can reuse the proofs in Memimpl, we just need to extend them)... *)

Ltac storebytes_tac thm :=
  simpl; intros;
  match goal with
    | H: storebytes ?m1 _ _ ?l = Some ?m2 |- _ =>
      unfold storebytes in H;
        destruct (is_empty l);
        [ | eapply thm; eassumption ];
        subst l;
        replace m2 with m1 in * by congruence;
        clear H;
        try congruence;
        unfold Memtype.Mem.range_perm, Memimpl.Mem.range_perm,
        Memtype.Mem.valid_access, Memimpl.Mem.valid_access;
        intuition (simpl in *; omega)
  end.

Lemma range_perm_storebytes:
   forall (m1 : Mem.mem) (b : block) (ofs : Z) (bytes : list memval),
   Mem.range_perm m1 b ofs (ofs + Z.of_nat (length bytes)) Cur Writable ->
   stack_access (Mem.stack m1) b ofs (ofs + Z.of_nat (length bytes)) ->
    exists m2 : Mem.mem, storebytes m1 b ofs bytes = Some m2.
Proof.
  unfold storebytes. intros.
  destruct (is_empty bytes); eauto using Mem.range_perm_storebytes'.
Qed.

Lemma encode_val_not_empty chunk v:
  encode_val chunk v <> nil.
Proof.
  generalize (encode_val_length chunk v). generalize (encode_val chunk v).
  destruct chunk; destruct l; compute; congruence.
Qed.

Lemma storebytes_store:
   forall (m1 : Mem.mem) (b : block) (ofs : Z) (chunk : AST.memory_chunk)
     (v : val) (m2 : Mem.mem),
   storebytes m1 b ofs (encode_val chunk v) = Some m2 ->
   (align_chunk chunk | ofs) -> Mem.store chunk m1 b ofs v = Some m2.
Proof.
  unfold storebytes. intros.
  destruct (is_empty (encode_val chunk v)); eauto using Mem.storebytes_store.
  edestruct encode_val_not_empty; eauto.
Qed.

Lemma store_storebytes:
   forall (m1 : Mem.mem) (b : block) (ofs : Z) (chunk : AST.memory_chunk)
     (v : val) (m2 : Mem.mem),
   Mem.store chunk m1 b ofs v = Some m2 ->
   storebytes m1 b ofs (encode_val chunk v) = Some m2.
Proof.
  unfold storebytes. intros.
  destruct (is_empty (encode_val chunk v)); eauto using Mem.store_storebytes.
  edestruct encode_val_not_empty; eauto.
Qed.

Lemma loadbytes_storebytes_same:
   forall (m1 : Mem.mem) (b : block) (ofs : Z) (bytes : list memval) (m2 : Mem.mem),
   storebytes m1 b ofs bytes = Some m2 ->
   Mem.loadbytes m2 b ofs (Z.of_nat (length bytes)) = Some bytes.
Proof.
  unfold storebytes. intros.
  destruct (is_empty bytes); eauto using Mem.loadbytes_storebytes_same.
  inv H. simpl.
  apply Mem.loadbytes_empty. omega.
Qed.

Lemma storebytes_concat: forall (m : Mem.mem) (b : block) (ofs : Z) (bytes1 : list memval)
         (m1 : Mem.mem) (bytes2 : list memval) (m2 : Mem.mem),
       storebytes m b ofs bytes1 = Some m1 ->
       storebytes m1 b (ofs + Z.of_nat (length bytes1)) bytes2 =
       Some m2 -> storebytes m b ofs (bytes1 ++ bytes2) = Some m2.
Proof.
  unfold storebytes at 1.
  intros until m2.
  case_eq (is_empty bytes1).
  {
    intros.
    subst. inv H0.
    simpl in *.
    replace (ofs + 0) with ofs in * by omega.
    assumption.
  }
  intros.
  unfold storebytes in *.
  destruct (is_empty bytes2).
  {
    inv H1.
    rewrite <- app_nil_end.
    rewrite H.
    assumption.
  }
  exploit (Mem.storebytes_concat m b ofs bytes1 m1 bytes2 m2); eauto.
  intros.
  destruct bytes1; try congruence. (** HERE transparently use is_empty *)
  assumption.
Qed.

Lemma storebytes_split:
   forall (m : Mem.mem) (b : block) (ofs : Z) (bytes1 bytes2 : list memval)
     (m2 : Mem.mem),
   storebytes m b ofs (bytes1 ++ bytes2) = Some m2 ->
   exists m1 : Mem.mem,
     storebytes m b ofs bytes1 = Some m1 /\
     storebytes m1 b (ofs + Z.of_nat (length bytes1)) bytes2 = Some m2.
Proof.
  unfold storebytes.
  intros.
  destruct (is_empty (bytes1 ++ bytes2)).
  {
    subst.
    inv H.
    destruct (app_eq_nil _ _ e). subst. simpl. eauto.
  }
  destruct (is_empty bytes1).
  {
    subst; simpl. replace (ofs + 0) with ofs in * by omega.
    simpl in *.
    destruct (is_empty bytes2); eauto.
    contradiction.
  }
  destruct (is_empty bytes2).
  {
    subst.
    rewrite <- app_nil_end in H. eauto.
  }
  eauto using Mem.storebytes_split.
Qed.

Lemma is_empty_list_forall2:
  forall (A B: Type) (P: A -> B -> Prop) l1 l2,
    list_forall2 P l1 l2 ->
    (l1 = nil <-> l2 = nil).
Proof.
  intros.
  inversion H; subst.
   tauto.
   split; discriminate.
Qed.

Lemma storebytes_within_extends:
   forall `{injperm: InjectPerm} (m1 m2 : Mem.mem) (b : block) (ofs : Z) (bytes1 : list memval)
     (m1' : Mem.mem) (bytes2 : list memval),
   Mem.extends m1 m2 ->
   storebytes m1 b ofs bytes1 = Some m1' ->
   list_forall2 memval_lessdef bytes1 bytes2 ->
   exists m2' : Mem.mem,
     storebytes m2 b ofs bytes2 = Some m2' /\ Mem.extends m1' m2'.
Proof.
  unfold storebytes.
  intros.
  destruct (is_empty bytes1); destruct (is_empty bytes2); eauto using Mem.storebytes_within_extends.
  * inv H0. eauto.
  * apply is_empty_list_forall2 in H1. exfalso; tauto.
  * apply is_empty_list_forall2 in H1. exfalso; tauto.
Qed.

Lemma storebytes_mapped_inject:
   forall  `{injperm: InjectPerm} (f : meminj) g (m1 : Mem.mem) (b1 : block) (ofs : Z)
     (bytes1 : list memval) (n1 m2 : Mem.mem) (b2 : block)
     (delta : Z) (bytes2 : list memval),
   Mem.inject f g m1 m2 ->
   storebytes m1 b1 ofs bytes1 = Some n1 ->
   f b1 = Some (b2, delta) ->
   list_forall2 (memval_inject f) bytes1 bytes2 ->
   exists n2 : Mem.mem,
     storebytes m2 b2 (ofs + delta) bytes2 = Some n2 /\
     Mem.inject f g n1 n2.
Proof.
  unfold storebytes.
  intros.
  destruct (is_empty bytes1); destruct (is_empty bytes2); eauto using Mem.storebytes_mapped_inject.
  * inv H0. eauto.
  * apply is_empty_list_forall2 in H2. exfalso; tauto.
  * apply is_empty_list_forall2 in H2. exfalso; tauto.
Qed.

Lemma storebytes_empty_inject:
   forall `{injperm: InjectPerm} (f : meminj) g (m1 : Mem.mem) (b1 : block) (ofs1 : Z)
     (m1' m2 : Mem.mem) (b2 : block) (ofs2 : Z) (m2' : Mem.mem),
   Mem.inject f g m1 m2 ->
   storebytes m1 b1 ofs1 nil = Some m1' ->
   storebytes m2 b2 ofs2 nil = Some m2' -> Mem.inject f g m1' m2'.
Proof.
  unfold storebytes; simpl; congruence.
Qed.

Lemma storebytes_unchanged_on:
   forall (P : block -> Z -> Prop) (m : Mem.mem) (b : block)
     (ofs : Z) (bytes : list memval) (m' : Mem.mem),
   storebytes m b ofs bytes = Some m' ->
   (forall i : Z, ofs <= i < ofs + Z.of_nat (length bytes) -> ~ P b i) ->
   Mem.unchanged_on P m m'.
Proof.
  unfold storebytes. intros.
  destruct (is_empty bytes); eauto using Mem.storebytes_unchanged_on.
  inv H. eapply Mem.unchanged_on_refl.
Qed.

(** Additional proof not present in CompCert *)

Lemma storebytes_empty:
  forall m b ofs m',
    storebytes m b ofs nil = Some m'
    -> m' = m.
Proof.
  unfold storebytes. intros.
  destruct (is_empty nil); congruence.
Qed.

(** Because we need the additional [free_range] property, we
have to modify the implementation of [free]... *)

Definition free (m: Mem.mem) (b: block) (lo hi: Z): option Mem.mem :=
  if zle hi lo then Some m else Mem.free m b lo hi.

(** ... and we have to again prove every property of [free]
(fortunately, we can reuse the proofs in Memimpl, we just need to extend them)... *)

Ltac free_tac thm :=
  simpl;
  intros;
  match goal with
    | H: free ?m1 _ ?lo ?hi = Some ?m2 |- _ =>
      unfold free in H;
        destruct (zle hi lo);
        try (eapply thm; eassumption);
        try replace m2 with m1 in * by congruence;
        try congruence;
        unfold Mem.range_perm, Memtype.Mem.range_perm, Mem.valid_access, Memtype.Mem.valid_access;
        try intuition omega
  end.

Lemma range_perm_free:
  forall m1 b lo hi,
  Mem.range_perm m1 b lo hi Cur Freeable ->
  exists m2: Mem.mem, free m1 b lo hi = Some m2.
Proof.
  unfold free. intros.
  destruct (zle hi lo); eauto using Mem.range_perm_free'.
Qed.

Lemma free_parallel_extends:
  forall  `{injperm: InjectPerm} (m1 m2 : Mem.mem) (b : block) (lo hi : Z) (m1' : Mem.mem),
    inject_perm_condition Freeable ->
   Mem.extends m1 m2 ->
   free m1 b lo hi = Some m1' ->
   exists m2' : Mem.mem, free m2 b lo hi = Some m2' /\ Mem.extends m1' m2'.
Proof.
  unfold free. intros until 2.
  destruct (zle hi lo). 
  inversion 1; subst; eauto.
  eapply Mem.free_parallel_extends; eauto.
Qed.

(** Additional proof not present in CompCert *)

Lemma free_range:
  forall m1 m1' b lo hi,
    free m1 b lo hi = Some m1' ->
    (lo < hi)%Z \/ m1' = m1.
Proof.
  unfold free. intros.
  destruct (zle hi lo).
   right; congruence.
  left; omega.
Qed.

(** Because we need the additional [inject_neutral_incr] property, we
have to modify the implementation of [inject_neutral]... *)

Definition inject_neutral  `{injperm: InjectPerm} (thr: block) (m: Mem.mem) :=
  Mem.inject_neutral thr m /\  (forall b, Ple thr b -> ~ in_stack (Mem.stack m) b /\ forall o k p, ~ Mem.perm m b o k p).

(** ... and we have to again prove every property of [inject_neutral]
(fortunately, we can reuse the proofs in Memimpl, we just need to extend them)... *)

Theorem neutral_inject  `{injperm: InjectPerm}:
  forall m, inject_neutral (Mem.nextblock m) m -> Mem.inject (Mem.flat_inj (Mem.nextblock m)) (flat_frameinj (length (Mem.stack m))) m m.
Proof.
  destruct 1; eauto using Mem.neutral_inject.
Qed.

Theorem empty_inject_neutral  `{injperm: InjectPerm}:
  forall thr, inject_neutral thr Mem.empty.
Proof.
  split; eauto using Mem.empty_inject_neutral, Mem.perm_empty.
Qed.

Theorem alloc_inject_neutral `{injperm: InjectPerm}:
  forall thr m lo hi b m',
  Mem.alloc m lo hi = (m', b) ->
  inject_neutral thr m ->
  Plt (Mem.nextblock m) thr ->
  inject_neutral thr m'.
Proof.
  inversion 2; subst.
  split; eauto using Mem.alloc_inject_neutral.
  intros.
  specialize (H2 _ H4); destruct H2 as (NIN & NPERM).
  erewrite Mem.alloc_stack; eauto. split; auto.
  intros. intro. eapply Mem.perm_valid_block in H2. unfold Mem.valid_block in *.
  apply Mem.nextblock_alloc in H. rewrite H in H2. xomega.
Qed.

Theorem store_inject_neutral `{injperm: InjectPerm}:
  forall chunk m b ofs v m' thr,
  Mem.store chunk m b ofs v = Some m' ->
  inject_neutral thr m ->
  Plt b thr ->
  Val.inject (Mem.flat_inj thr) v v ->
  inject_neutral thr m'.
Proof.
  inversion 2; subst.
  split; eauto using Mem.store_inject_neutral.
  intros b0 PLE; specialize (H2 _ PLE); destruct H2 as (NIN & NPERM);
    split; [intro IN| intros o k p PERM].
  erewrite Mem.store_stack in IN; eauto.
  eapply NPERM; eauto using Mem.perm_store_2.
Qed.

Theorem drop_inject_neutral `{injperm: InjectPerm}:
  forall m b lo hi p m' thr,
  Mem.drop_perm m b lo hi p = Some m' ->
  inject_neutral thr m ->
  Plt b thr ->
  inject_neutral thr m'.
Proof.
  inversion 2; subst.
  split; eauto using Mem.drop_inject_neutral.
  intros b0 PLE; specialize (H2 _ PLE); destruct H2 as (NIN & NPERM);
    split; [intro IN| intros o k pp PERM].
  erewrite Mem.drop_perm_stack in IN; eauto.
  eapply NPERM; eauto using Mem.perm_drop_4.
Qed.

(** Additional proof not present in CompCert *)


(* Lemma frame_inject_incr_thr `{injperm: InjectPerm}: *)
(*   forall thr thr' m f, *)
(*     Ple thr thr' -> *)
(*     frame_inject' (Mem.flat_inj thr) m f f -> *)
(*     frame_inject' (Mem.flat_inj thr') m f f. *)
(* Proof. *)
(*   intros thr thr' n f PLE FI. *)
(*   inv FI; split; auto. *)
(*   - eapply Forall_impl. 2: exact frame_inject_inj. simpl. unfold Mem.flat_inj; simpl; intros. *)
(*     repeat destr_in H0. *)
(*     eapply H; eauto. destr. omega. *)
(*   - eapply frame_inject_with_info; eauto. *)
(*     + unfold Mem.flat_inj. destr. *)
(*     + unfold Mem.flat_inj. intros b' delta. destr. *)
(*   - eapply frame_inject_without_info; eauto. *)
(*     unfold Mem.flat_inj. intros b b' delta. destr. *)
(* Qed. *)

Theorem inject_neutral_incr `{injperm: InjectPerm}:
  forall m thr, inject_neutral thr m -> forall thr', Ple thr thr' -> inject_neutral thr' m.
Proof.
  intros ? ? [[] PERM].
  split.
  - split.
    + unfold Mem.flat_inj. intros until p.
      destruct (plt b1 thr'); try discriminate. injection 1; intros until 2; subst. intro.
      eapply mi_perm.
      2: eassumption.
      unfold Mem.flat_inj.
      destruct (plt b2 thr). reflexivity.
      specialize (PERM b2). trim PERM.  xomega. destruct PERM as (NIN & NPERM).
      eapply NPERM in H1. easy.
    + unfold Mem.flat_inj. intros until p.
      destruct (plt b1 thr'); try discriminate. injection 1; intros until 2; subst. intro. exists 0; omega.
    + unfold Mem.flat_inj. intros until delta.
      destruct (plt b1 thr'); try discriminate.
      injection 1; intros until 2; subst.
      intro. eapply memval_inject_incr.
      * eapply mi_memval. 2: assumption. unfold Mem.flat_inj.
        destruct (plt b2 thr).
        reflexivity.
        specialize (PERM b2). trim PERM.  xomega. destruct PERM as (NIN & NPERM).
        eapply NPERM in H1. easy.
      * unfold inject_incr. unfold Mem.flat_inj. intros until delta.
        destruct (plt b thr); try discriminate.
        injection 1; intros until 2; subst.
        destruct (plt b' thr'); try reflexivity.
        xomega.
    + eapply stack_inject_incr. 3: eauto.
      * unfold Mem.flat_inj; red; intros. repeat destr_in H0. destr. xomega.
      *  unfold Mem.flat_inj. intros b b' delta INJ1 INJ2.
         destr_in INJ1. repeat destr_in INJ2.
         split; intros.
         apply PERM. xomega.
         eapply PERM in H1; eauto. easy. xomega.
  - intros. eapply PERM. xomega.
Qed.

Theorem free_inject_neutral':
  forall  `{injperm: InjectPerm} m b lo hi m' thr,
  Mem.free m b lo hi = Some m' ->
  inject_neutral thr m ->
  Plt b thr ->
  inject_neutral thr m'.
Proof.
  intros until 1. intros [? PERM]. intros PLT.
  exploit Mem.free_left_inj; eauto. intro INJ.
  exploit Mem.free_right_inj; eauto.
  - intros until p. unfold Mem.flat_inj. destruct (plt b' thr); try discriminate.
    injection 1; intros until 2; subst. replace (ofs + 0) with ofs by omega. intros.
    eapply Mem.perm_free_2; eauto.
  - intro INJ2. split.
    erewrite <- Mem.free_stack in INJ2; eauto.
    intros b0 PLE; specialize (PERM _ PLE); destruct PERM as (NIN & NPERM).
    erewrite Mem.free_stack; eauto. split; auto.
    intros o k p P; eapply NPERM; eauto using Mem.perm_free_3.
Qed.

Theorem storebytes_inject_neutral' `{injperm: InjectPerm}:
  forall m b o l m' thr,
  Mem.storebytes m b o l = Some m' ->
  list_forall2 (memval_inject (Mem.flat_inj thr)) l l ->
  Plt b thr ->
  inject_neutral thr m ->
  inject_neutral thr m'.
Proof.
  inversion 4; subst.
  unfold Mem.inject_neutral in H3.
  generalize H. intro STORE.
  eapply Mem.storebytes_mapped_inj in STORE; eauto.
  Focus 3.
   unfold Mem.flat_inj. destruct (plt b thr); try reflexivity. contradiction.
  destruct STORE as (m2 & STORE & INJ).
  replace (o + 0) with o in * by omega.
  replace m2 with m' in * by congruence.
  split; auto.
  erewrite <- Mem.storebytes_stack in INJ; eauto.
  intros b0 PLE; specialize (H4 _ PLE); destruct H4 as (NIN & NPERM).
  erewrite Mem.storebytes_stack; eauto. split; auto.
  intros o0 k p P; eapply Mem.perm_storebytes_2 in P; eauto. eapply NPERM; eauto.
  unfold Mem.meminj_no_overlap.
  unfold Mem.flat_inj. intros.
  destruct (plt b1 thr); try discriminate.
  destruct (plt b2 thr); try discriminate.
  left; congruence.
Qed.

(** Extra properties about drop_perm and extends *)

Theorem drop_perm_right_extends `{injperm: InjectPerm}:
  forall m1 m2 b lo hi p m2',
  Mem.extends m1 m2 ->
  Mem.drop_perm m2 b lo hi p = Some m2' ->
  (forall ofs k p, Mem.perm m1 b ofs k p -> lo <= ofs < hi -> False) ->
  Mem.extends m1 m2'.
Proof.
  intros. inv H. constructor.
  - rewrite (Mem.nextblock_drop _ _ _ _ _ _ H0). auto.
  - eapply Mem.drop_outside_inj; eauto.
    unfold inject_id; intros. inv H. eapply H1; eauto. omega.
  - intros b0 ofs k p0 H.
    eapply mext_perm_inv; eauto. eapply Mem.perm_drop_4; eauto.
  - erewrite Mem.drop_perm_stack; eauto.
Qed.

Theorem drop_perm_parallel_extends `{injperm: InjectPerm}:
  forall m1 m2 b lo hi p m1',
    Mem.extends m1 m2 ->
    Mem.drop_perm m1 b lo hi p = Some m1' ->
    inject_perm_condition Freeable ->
    exists m2',
      Mem.drop_perm m2 b lo hi p = Some m2'
      /\ Mem.extends m1' m2'.
Proof.
  intros.
  inv H.
  exploit Mem.drop_mapped_inj; eauto.
  3: unfold inject_id; reflexivity. rewrite ! Z.add_0_r.
  - red; intros. replace ofs with (ofs + 0) by omega. eapply Mem.mi_perm; eauto. reflexivity.
    unfold Mem.drop_perm in H0; destr_in H0. eapply r. omega.
  - unfold Mem.meminj_no_overlap. unfold inject_id. intros; left; congruence.
  - replace (lo + 0) with lo by omega.
    replace (hi + 0) with hi by omega.
    destruct 1 as [m2' [FREE INJ]]. exists m2'; split; auto.
    constructor; auto.
    rewrite (Mem.nextblock_drop _ _ _ _ _ _ H0).
    rewrite (Mem.nextblock_drop _ _ _ _ _ _ FREE). auto.
    erewrite Mem.drop_perm_stack; eauto.
    intros b0 ofs k p0 H.
    exploit Mem.perm_drop_4; eauto.
    intro K. apply mext_perm_inv in K.
    destruct K.
    + destruct (andb (Pos.eqb b0 b) (andb (Z.leb lo ofs) (Z.ltb ofs hi))) eqn:BOOL.
      * repeat rewrite Bool.andb_true_iff in BOOL.
        rewrite Pos.eqb_eq in BOOL.
        rewrite Z.leb_le in BOOL.
        rewrite Z.ltb_lt in BOOL.
        destruct BOOL; subst.
        exploit Mem.perm_drop_2; eauto.
        intro.
        left. eapply Mem.perm_implies; eauto. eapply Mem.perm_drop_1; eauto.
      * rewrite <- not_true_iff_false in BOOL.
        repeat rewrite Bool.andb_true_iff in BOOL.
        rewrite Pos.eqb_eq in BOOL.
        rewrite Z.leb_le in BOOL.
        rewrite Z.ltb_lt in BOOL.
        left. eapply Mem.perm_drop_3; eauto.
        revert BOOL. clear.
        intros.
        assert (( ~ (lo <= ofs) ) <-> ofs < lo) by omega.
        assert (( ~ (ofs < hi) ) <-> hi <= ofs) by omega.
        tauto.
    + right.
      intro U.
      apply H2.
      eapply Mem.perm_drop_4; eauto.
    + rewrite (Mem.drop_perm_stack _ _ _ _ _ _ FREE),
      (Mem.drop_perm_stack _ _ _ _ _ _ H0); auto.
Qed.

(** Additional property about unchanged_on, to prove transitivity
    of ec_mem_extends *)

Lemma unchanged_on_trans_strong (P Q: _ -> _ -> Prop) m1 m2 m3:
  (forall b, Mem.valid_block m1 b -> forall o, P b o -> Q b o) ->
  Mem.unchanged_on P m1 m2 ->
  Mem.unchanged_on Q m2 m3 ->
  Mem.unchanged_on P m1 m3.
Proof.
  inversion 2; subst.
  inversion 1; subst.
  constructor.
  + xomega.
  + intros b ofs k p H3 H4.
    rewrite unchanged_on_perm by auto.
    apply unchanged_on_perm0. eauto.
    unfold Mem.valid_block in *; xomega.
  + intros b ofs H3 H4.
    generalize (Mem.perm_valid_block _ _ _ _ _ H4). intro H5.
    generalize H4. intro H4_.
    rewrite unchanged_on_perm in H4_ by eauto.
    etransitivity.
     eapply unchanged_on_contents0; eauto.
    eauto.
Qed.

(** ... and we need to repackage instances for the CompCert memory model. *)

Lemma perm_free_2 `{injperm: InjectPerm}:
   forall (m1 : Mem.mem) (bf : block) (lo hi : Z) (m2 : Mem.mem),
   free m1 bf lo hi = Some m2 ->
   forall (ofs : Z) (k : perm_kind) (p : permission),
   lo <= ofs < hi -> ~ Mem.perm m2 bf ofs k p.
Proof.
  free_tac Mem.perm_free_2.
Qed.

Lemma perm_free_3 `{injperm: InjectPerm}:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  forall b ofs k p,
  Mem.perm m2 b ofs k p -> Mem.perm m1 b ofs k p.
Proof.
  free_tac Mem.perm_free_3.
Qed.

Global Instance memory_model_ops: Mem.MemoryModelOps Mem.mem.
Proof.
  econstructor.
  exact Mem.empty.
  exact Mem.alloc.
  exact free.
  exact Mem.load.
  exact Mem.store.
  exact Mem.loadbytes.
  exact storebytes.
  exact Mem.drop_perm.
  exact Mem.nextblock.
  exact Mem.perm.
  exact Mem.valid_pointer.
  intro; exact Mem.extends.
  intro; exact Mem.magree.
  intro; exact Mem.inject.
  intro; exact Mem.weak_inject.
  intro; exact inject_neutral.
  exact Mem.unchanged_on.
  exact Mem.unchanged_on.
  exact Mem.stack.
  exact Mem.push_new_stage.
  exact Mem.tailcall_stage.
  exact Mem.record_stack_blocks.
  exact Mem.unrecord_stack_block.
Defined. (** Qed does not work here, need transparent definitions for MemoryModel* *)

Lemma perm_free_list:
  forall l m m' b ofs k p,
    Memtype.Mem.free_list m l = Some m' ->
    Mem.perm m' b ofs k p ->
    Mem.perm m b ofs k p /\
    (forall lo hi, In (b, lo, hi) l -> lo <= ofs < hi -> False).
Proof.
  Opaque free.
  induction l; simpl; intros.
  inv H. auto.
  destruct a as [[b1 lo1] hi1].
  destruct (free m b1 lo1 hi1) as [m1|] eqn:E; try discriminate.
  exploit IHl; eauto. intros [A B].
  split.  eapply perm_free_3; eauto.
  intros. destruct H1. inv H1.
  elim (perm_free_2 _ _ _ _ _ E ofs k p). auto. auto.
  eauto.
  Transparent free.
Qed.

Lemma free_left_inject `{injperm: InjectPerm}:
  forall f g m1 m2 b lo hi m1',
  Mem.inject f g m1 m2 ->
  free m1 b lo hi = Some m1' ->
  Mem.inject f g m1' m2.
Proof.
  free_tac Mem.free_left_inject.
Qed.

Lemma free_list_left_inject `{injperm: InjectPerm}:
  forall f g m2 l m1 m1',
    Mem.inject f g m1 m2 ->
    Memtype.Mem.free_list m1 l = Some m1' ->
    Mem.inject f g m1' m2.
Proof.
  Opaque free.
  induction l; simpl; intros.
  inv H0. auto.
  destruct a as [[b lo] hi].
  destruct (free m1 b lo hi) as [m11|] eqn:E; try discriminate.
  apply IHl with m11; auto. eapply free_left_inject; eauto.
  Transparent free.
Qed.

Lemma free_right_inject `{injperm: InjectPerm}:
  forall f g m1 m2 b lo hi m2',
  Mem.inject f g m1 m2 ->
  free m2 b lo hi = Some m2' ->
  (forall b1 delta ofs k p,
    f b1 = Some(b, delta) -> Mem.perm m1 b1 ofs k p ->
    lo <= ofs + delta < hi -> False) ->
  Mem.inject f g m1 m2'.
Proof.
  free_tac Mem.free_right_inject.
Qed.

Lemma free_inject `{injperm: InjectPerm}:
  forall (f : meminj) g
    (m1 : Mem.mem) (l : list (block * Z * Z))
     (m1' m2 : Mem.mem) (b : block) (lo hi : Z) (m2' : Mem.mem),
   Mem.inject f g m1 m2 ->
   Memtype.Mem.free_list m1 l = Some m1' ->
   Memtype.Mem.free m2 b lo hi = Some m2' ->
   (forall (b1 : block) (delta ofs : Z) (k : perm_kind) (p : permission),
    f b1 = Some (b, delta) ->
    Mem.perm m1 b1 ofs k p ->
    lo <= ofs + delta < hi ->
    exists lo1 hi1 : Z, In (b1, lo1, hi1) l /\ lo1 <= ofs < hi1) ->
   Mem.inject f g m1' m2'.
Proof.
  intros.
  eapply free_right_inject; eauto.
  eapply free_list_left_inject; eauto.
  intros. exploit perm_free_list; eauto. intros [A B].
  exploit H2; eauto. intros [lo1 [hi1 [C D]]]. eauto.
Qed.

Lemma free_unchanged_on:
   forall (P : block -> Z -> Prop) (m : Mem.mem) (b : block)
     (lo hi : Z) (m' : Mem.mem),
     free m b lo hi = Some m' ->
   (forall i : Z, lo <= i < hi -> ~ P b i) -> Mem.unchanged_on P m m'.
Proof.
  unfold free. intros.
  destruct (zle hi lo); eauto using Mem.free_unchanged_on.
  inv H. apply Memimpl.Mem.unchanged_on_refl.
Qed.

Lemma magree_free:
  forall `{injperm: InjectPerm} (m1 m2 : Mem.mem) (P Q : Memtype.Mem.locset) (b : block) (lo hi : Z) (m1' : Mem.mem),
    Memtype.Mem.magree m1 m2 P ->
    inject_perm_condition Freeable ->
    Memtype.Mem.free m1 b lo hi = Some m1' ->
    (forall (b' : block) (i : Z), Q b' i -> b' <> b \/ ~ lo <= i < hi -> P b' i) ->
    exists m2' : Mem.mem, Memtype.Mem.free m2 b lo hi = Some m2' /\ Memtype.Mem.magree m1' m2' Q.
Proof.
  simpl; intros.
  unfold free.
  free_tac Mem.magree_free.
  eexists; split; eauto.
  eapply Mem.magree_monotone; eauto. intros; eapply H2; eauto. right; omega.
Qed.

Lemma free_parallel_inject:
  forall `{injperm: InjectPerm} (f : meminj) g (m1 m2 : Mem.mem) (b : block) (lo hi : Z) (m1' : Mem.mem)
    (b' : block) (delta : Z),
    inject_perm_condition Freeable ->
    Memtype.Mem.inject f g m1 m2 ->
    Memtype.Mem.free m1 b lo hi = Some m1' ->
    f b = Some (b', delta) ->
    exists m2' : Mem.mem,
      Memtype.Mem.free m2 b' (lo + delta) (hi + delta) = Some m2' /\ Memtype.Mem.inject f g m1' m2'.
Proof.
  simpl; intros.
  unfold free.
  free_tac Mem.free_parallel_inject.
  rewrite zle_true. eexists; split; eauto. omega.
  rewrite zle_false. eapply Mem.free_parallel_inject; eauto. simpl; auto. omega.
Qed.

Lemma magree_storebytes_parallel:
  forall  `{injperm: InjectPerm} (m1 m2 : Mem.mem) (P Q : Memtype.Mem.locset) (b : block) (ofs : Z)
    (bytes1 : list memval) (m1' : Mem.mem) (bytes2 : list memval),
    Mem.magree m1 m2 P ->
    storebytes m1 b ofs bytes1 = Some m1' ->
    (forall (b' : block) (i : Z),
        Q b' i -> b' <> b \/ i < ofs \/ ofs + Z.of_nat (length bytes1) <= i -> P b' i) ->
    list_forall2 memval_lessdef bytes1 bytes2 ->
    exists m2' : Mem.mem, storebytes m2 b ofs bytes2 = Some m2' /\ Mem.magree m1' m2' Q.
Proof.
  simpl; intros.
  unfold storebytes in *.
  destruct (is_empty bytes1). inv H0. inv H2.
  simpl. eexists; split; eauto.
  eapply Mem.magree_monotone; eauto. intros; eapply H1; eauto. simpl. right; omega.
  exploit Mem.magree_storebytes_parallel. eauto. eauto. eauto. eauto. inv H2. simpl. congruence.
  simpl. eauto.
Qed.

Lemma free_list_adt:
  forall (m : Mem.mem) (bl : list (block * Z * Z)) (m' : Mem.mem),
    Memtype.Mem.free_list m bl = Some m' -> Mem.stack m' = Mem.stack m.
Proof.
  intros m bl; revert m; induction bl; simpl; intros; eauto.
  inv H; eauto.
  destruct a, p. destruct free eqn:?; try discriminate.
  unfold free in Heqo. destruct (zle z z0); auto.
  inv Heqo. eauto.
  erewrite IHbl. eapply Mem.free_stack; eauto. eauto.
Qed.

Lemma freelist_no_abstract:
  forall bl, Mem.stack_unchanged (fun m1 m2 => Memtype.Mem.free_list m1 bl = Some m2).
Proof.
  red. induction bl; simpl; intros; eauto; autospe.
  auto.
  free_tac Mem.free_no_abstract. 
  eapply Mem.free_no_abstract in Heqo. simpl in *. congruence.
Qed.

Lemma record_stack_blocks_inject_neutral:
  forall (injperm : InjectPerm) (thr : block) (m : Mem.mem) fi (m' : Mem.mem),
  inject_neutral thr m ->
  Mem.record_stack_blocks m fi = Some m' ->
  Forall (fun b => Plt b thr) (map fst (frame_adt_blocks fi)) ->
  inject_neutral thr m'.
Proof.
  intros injperm thr m fi m' [IN PERM] RSB PLT. split; auto.
  eapply Mem.record_stack_blocks_inject_neutral; eauto.
  intros b PLE.
  specialize (PERM _ PLE). destruct PERM as (NIN & NPERM).
  split.
  - edestruct Mem.record_stack_blocks_stack_original as (ff & r & EQ). eauto.
    erewrite Mem.record_stack_blocks_stack; eauto. rewrite in_stack_cons; simpl. rewrite in_frames_cons.
    rewrite EQ in *.
    intros [A|A]. destruct A as (fa & EQQ & A); inv EQQ.
    rewrite Forall_forall in PLT; apply PLT in A. xomega.
    apply NIN. rewrite in_stack_cons; auto.
  - exploit Memimpl.Mem.record_stack_blocks_mem_unchanged. eauto. intros (A & B & C & D).
    intros; rewrite B. eauto.
Qed.

Lemma unrecord_stack_block_inject_neutral:
  forall (injperm : InjectPerm) (thr : block) (m m' : Mem.mem),
    inject_neutral thr m -> Mem.unrecord_stack_block m = Some m' -> inject_neutral thr m'.
Proof.
  intros injperm thr m m' [IN P] RSB; split; auto.
  - eapply Mem.unrecord_stack_block_inject_neutral; eauto.
  - intros. exploit Memimpl.Mem.unrecord_stack_block_mem_unchanged. eauto.
    intros (A & B & C & D).
    specialize (P _ H); destruct P as (NIN & NPERM).
    split; intros.
    + edestruct Mem.unrecord_stack; eauto. rewrite H0 in NIN; simpl in NIN.
      rewrite in_stack_cons in NIN; intuition.
    + rewrite B; eauto.
Qed.

Global Instance memory_model: Mem.MemoryModel Mem.mem.
Proof.
  constructor.
  exact  Mem.valid_not_valid_diff.
  exact  Mem.perm_implies.
  exact  Mem.perm_cur_max.
  exact  Mem.perm_cur.
  exact  Mem.perm_max.
  exact  Mem.perm_valid_block.
  exact  Mem.range_perm_implies.
  exact  Mem.range_perm_cur.
  exact  Mem.range_perm_max.
  exact  Mem.valid_access_implies.
  exact  Mem.valid_access_valid_block.
  exact  Mem.valid_access_perm.
  exact  Mem.valid_pointer_nonempty_perm.
  exact  Mem.valid_pointer_valid_access.
  exact  Mem.weak_valid_pointer_spec.
  exact  Mem.valid_pointer_implies.
  exact  Mem.nextblock_empty.
  exact  Mem.perm_empty.
  exact  Mem.valid_access_empty.
  exact  Mem.valid_access_load.
  exact  Mem.load_valid_access.
  exact  Mem.load_type.
  exact  Mem.load_cast.
  exact  Mem.load_int8_signed_unsigned.
  exact  Mem.load_int16_signed_unsigned.
  exact  Mem.loadv_int64_split.
  exact  Mem.range_perm_loadbytes.
  exact  Mem.loadbytes_range_perm.
  exact  Mem.loadbytes_load.
  exact  Mem.load_loadbytes.
  exact  Mem.loadbytes_length.
  exact  Mem.loadbytes_empty.
  exact  Mem.loadbytes_concat.
  exact  Mem.loadbytes_split.
  exact  Mem.nextblock_store.
  exact  Mem.store_valid_block_1.
  exact  Mem.store_valid_block_2.
  exact  Mem.perm_store_1.
  exact  Mem.perm_store_2.
  exact  Mem.valid_access_store'.
  exact  Mem.store_valid_access_1.
  exact  Mem.store_valid_access_2.
  exact  Mem.store_valid_access_3.
  exact  Mem.load_store_similar.
  exact  Mem.load_store_similar_2.
  exact  Mem.load_store_same.
  exact  Mem.load_store_other.
  exact  Mem.load_store_pointer_overlap.
  exact  Mem.load_store_pointer_mismatch.
  exact  Mem.load_pointer_store.
  exact Mem.maybe_store_val.
  exact  Mem.loadbytes_store_same.
  exact  Mem.loadbytes_store_other.
  exact  Mem.store_signed_unsigned_8.
  exact  Mem.store_signed_unsigned_16.
  exact  Mem.store_int8_zero_ext.
  exact  Mem.store_int8_sign_ext.
  exact  Mem.store_int16_zero_ext.
  exact  Mem.store_int16_sign_ext.
  exact  Mem.storev_int64_split.
  exact range_perm_storebytes.
  now storebytes_tac Mem.storebytes_range_perm.
  {
    simpl. unfold storebytes. intros m1 b ofs bytes m2.
    destr. subst. simpl. intros; eapply lo_ge_hi_stack_access. omega.
    intros; eapply Mem.storebytes_stack_access_3; eauto.
  }
  now storebytes_tac Mem.perm_storebytes_1.
  now storebytes_tac Mem.perm_storebytes_2.
  now storebytes_tac Mem.storebytes_valid_access_1.
  now storebytes_tac Mem.storebytes_valid_access_2.
  now storebytes_tac Mem.nextblock_storebytes.
  now storebytes_tac Mem.storebytes_valid_block_1.
  now storebytes_tac Mem.storebytes_valid_block_2.
  exact  storebytes_store.
  exact  store_storebytes.
  exact  loadbytes_storebytes_same.
  now storebytes_tac Mem.loadbytes_storebytes_disjoint.
  now storebytes_tac Mem.loadbytes_storebytes_other.
  now storebytes_tac Mem.load_storebytes_other.
  exact  storebytes_concat.
  exact  storebytes_split.
  exact  Mem.alloc_result.
  exact  Mem.nextblock_alloc.
  exact  Mem.valid_block_alloc.
  exact  Mem.fresh_block_alloc.
  exact  Mem.valid_new_block.
  exact  Mem.valid_block_alloc_inv.
  exact  Mem.perm_alloc_1.
  exact  Mem.perm_alloc_2.
  exact  Mem.perm_alloc_3.
  exact  Mem.perm_alloc_4.
  exact  Mem.perm_alloc_inv.
  exact  Mem.valid_access_alloc_other.
  exact  Mem.valid_access_alloc_same.
  exact  Mem.valid_access_alloc_inv.
  exact  Mem.load_alloc_unchanged.
  exact  Mem.load_alloc_other.
  exact  Mem.load_alloc_same.
  exact  Mem.load_alloc_same'.
  exact  Mem.loadbytes_alloc_unchanged.
  exact  Mem.loadbytes_alloc_same.
  exact range_perm_free.
  now free_tac Mem.free_range_perm.
  now free_tac Mem.nextblock_free.
  now free_tac Mem.valid_block_free_1.
  now free_tac Mem.valid_block_free_2.
  now free_tac Mem.perm_free_1.
  exact  perm_free_2.
  exact  perm_free_3.
  now free_tac Mem.valid_access_free_1.
  now free_tac Mem.valid_access_free_2.
  now free_tac Mem.valid_access_free_inv_1.
  now free_tac Mem.valid_access_free_inv_2.
  now free_tac Mem.load_free.
  now free_tac Mem.loadbytes_free_2.
  exact  Mem.nextblock_drop.
  exact  Mem.drop_perm_valid_block_1.
  exact  Mem.drop_perm_valid_block_2.
  exact  Mem.range_perm_drop_1.
  exact  Mem.range_perm_drop_2'.
  exact  Mem.perm_drop_1.
  exact  Mem.perm_drop_2.
  exact  Mem.perm_drop_3.
  exact  Mem.perm_drop_4.
  exact  Mem.loadbytes_drop.
  exact  Mem.load_drop.
  intros; eapply Mem.empty_weak_inject; eauto.
  intros; eapply Mem.weak_inject_to_inject; eauto.
  intros; eapply Mem.store_mapped_weak_inject; eauto.
  intros; eapply Mem.alloc_left_mapped_weak_inject; eauto.
  intros; eapply Mem.alloc_left_unmapped_weak_inject; eauto.
  intros; eapply Mem.drop_parallel_weak_inject; eauto.
  intros; eapply Mem.drop_extended_parallel_weak_inject; eauto.
  intro; exact  Mem.extends_refl.
  intro; exact  Mem.load_extends.
  intro; exact  Mem.loadv_extends.
  intro; exact  Mem.loadbytes_extends.
  intro; exact  Mem.store_within_extends.
  intro; exact  Mem.store_outside_extends.
  intro; exact  Mem.storev_extends.
  intro; exact storebytes_within_extends.
  {
    simpl. unfold storebytes. intros injperm m1 m2 b ofs bytes2 m2'.
    destr. simpl. 
    intros; eapply Mem.storebytes_outside_extends; eauto.
  }
  intro; exact  Mem.alloc_extends.
  intro; now free_tac Mem.free_left_extends.
  intro; now free_tac Mem.free_right_extends.
  intros; eapply free_parallel_extends; eauto.
  intro; exact  Mem.valid_block_extends.
  intro; exact  Mem.perm_extends.
  intro; exact  Mem.valid_access_extends.
  intro; exact  Mem.valid_pointer_extends.
  intro; exact  Mem.weak_valid_pointer_extends.
  intro; exact  Mem.drop_extends.
  intro; exact  Mem.ma_perm.
  intro; exact  Mem.magree_monotone.
  intro; exact  Mem.mextends_agree.
  intro; exact  Mem.magree_extends.
  intro; exact  Mem.magree_loadbytes.
  intro; exact  Mem.magree_load.
  simpl.
  intro; exact magree_storebytes_parallel.
  intro; now storebytes_tac Mem.magree_storebytes_left.
  intro; exact  Mem.magree_store_left.
  intro; exact  magree_free.
  intro; exact  Mem.magree_valid_access.
  intro; exact  Mem.mi_no_overlap.
  intro; exact Mem.delta_pos.
  intro; exact  Mem.valid_block_inject_1.
  intro; exact  Mem.valid_block_inject_2.
  intro; exact  Mem.perm_inject.
  intro; exact  Mem.range_perm_inject.
  intro; exact  Mem.valid_access_inject.
  intro; exact  Mem.valid_pointer_inject.
  intro; exact  Mem.valid_pointer_inject'.
  intro; exact  Mem.weak_valid_pointer_inject.
  intro; exact  Mem.weak_valid_pointer_inject'.
  intro; exact  Mem.address_inject.
  intro; exact  Mem.address_inject'.
  intro; exact  Mem.valid_pointer_inject_no_overflow.
  intro; exact  Mem.weak_valid_pointer_inject_no_overflow.
  intro; exact  Mem.valid_pointer_inject_val.
  intro; exact  Mem.weak_valid_pointer_inject_val.
  intro; exact  Mem.inject_no_overlap.
  intro; exact  Mem.different_pointers_inject.
  intro; exact  Mem.disjoint_or_equal_inject.
  intro; exact  Mem.aligned_area_inject.
  intro; exact  Mem.load_inject.
  intro; exact  Mem.loadv_inject.
  intro; exact  Mem.loadbytes_inject.
  intro; exact  Mem.store_mapped_inject.
  intro; exact  Mem.store_unmapped_inject.
  intro; exact  Mem.store_outside_inject.
  intros; eapply Mem.store_right_inject; eauto.
  intro; exact  Mem.storev_mapped_inject.
  intro; exact  storebytes_mapped_inject.
  intro; now storebytes_tac Mem.storebytes_unmapped_inject.
  intro; now storebytes_tac Mem.storebytes_outside_inject.
  intro; exact  storebytes_empty_inject.
  intro; exact  Mem.alloc_right_inject.
  intro; exact  Mem.alloc_left_unmapped_inject.
  intro; exact  Mem.alloc_left_mapped_inject.
  intro; exact  Mem.alloc_parallel_inject.
  intro; exact  free_inject.
  intro; exact  free_left_inject.
  intro; exact  free_list_left_inject.
  intro; exact  free_right_inject.
  intros; eapply free_parallel_inject; eauto.
  intros; eapply Mem.drop_parallel_inject; eauto.
  intros; eapply Mem.drop_extended_parallel_inject; eauto.
  intro; exact  Mem.drop_outside_inject.
  intro; exact  Mem.drop_right_inject.
  intros; eapply Mem.self_inject; eauto.
  {
    inversion 1. inv mi_inj. inv mi_stack_blocks. 
    split. eapply stack_inject_aux_length_l; eauto.
    eapply stack_inject_aux_length_r; eauto.
  }
  intro; exact  Memimpl.Mem.extends_inject_compose.
  intro; exact Memimpl.Mem.extends_extends_compose.
  intro; exact  neutral_inject.
  intro; exact  empty_inject_neutral.
  reflexivity.
  intro; exact  alloc_inject_neutral.
  intro; exact  store_inject_neutral.
  intro; exact  drop_inject_neutral.
  intros; eapply Mem.drop_perm_stack; eauto.
  tauto.
  exact Mem.unchanged_on_nextblock.
  exact  Mem.unchanged_on_refl .
  exact Mem.unchanged_on_trans.
  exact Mem.unchanged_on_trans.
  exact  Mem.perm_unchanged_on .
  exact  Mem.perm_unchanged_on_2 .
  exact  Mem.loadbytes_unchanged_on_1 .
  exact  Mem.loadbytes_unchanged_on .
  exact  Mem.load_unchanged_on_1 .
  exact  Mem.load_unchanged_on .
  exact  Mem.store_unchanged_on .
  exact  storebytes_unchanged_on .
  exact  Mem.alloc_unchanged_on .
  exact  free_unchanged_on .
  exact Mem.drop_perm_unchanged_on.
  exact  Mem.unchanged_on_implies.
  exact  Mem.unchanged_on_implies.
  intros; eapply Mem.inject_unchanged_on; eauto.
  intros; eapply Mem.store_no_abstract; eauto.
  red; storebytes_tac Mem.storebytes_no_abstract; eauto.
  intros; eapply Mem.alloc_no_abstract; eauto.
  red; free_tac Mem.free_no_abstract; eauto.
  {
    red; induction bl; simpl; intros. congruence.
    repeat destr_in H.
    eapply IHbl in H1. simpl in *. rewrite H1.
    free_tac Mem.free_no_abstract.
  }
  intros; eapply Mem.drop_perm_no_abstract; eauto.
  simpl. intros; eapply Mem.record_stack_block_inject_left'; eauto.
  {
    simpl. intros. eapply Mem.record_stack_block_inject; simpl in *; eauto.
  }
  { intros; eapply Mem.record_stack_blocks_extends; eauto. }
  intros; eapply Mem.record_stack_blocks_mem_unchanged; eauto.
  {
    simpl; intros.
    eapply Mem.record_stack_blocks_stack; eauto.
  }
  exact record_stack_blocks_inject_neutral; eauto.
  simpl. intros; eapply Mem.unrecord_stack_block_inject_parallel; eauto.
  simpl. intros; eapply Mem.unrecord_stack_block_inject_left; eauto. intuition.
  intros; eapply Mem.unrecord_stack_block_extends; eauto.
  intros; eapply Mem.unrecord_stack_block_mem_unchanged; eauto.
  intros; eapply Mem.unrecord_stack; eauto.
  intros; eapply Mem.unrecord_stack_block_succeeds; eauto.
  simpl. exact unrecord_stack_block_inject_neutral; eauto.
  intros; eapply Mem.public_stack_access_extends; eauto.
  intros; eapply Mem.public_stack_access_inject; eauto.
  intros; eapply Mem.public_stack_access_magree; eauto.
  intros; eapply Mem.in_frames_valid; eauto.
  intros; eapply Mem.is_stack_top_extends; eauto.
  intros; eapply Mem.is_stack_top_inject; eauto.
  intros. simpl. eapply Mem.stack_inv_below_limit, Mem.mem_stack_inv.
  intros; eapply Mem.record_stack_block_inject_left_zero'; eauto.
  (* red in FI. specialize (FI _ (or_introl eq_refl) HP); auto. *)
  intros; eapply Mem.unrecord_stack_block_inject_left_zero; eauto.
  intros; eapply Mem.stack_inv_norepet, Mem.mem_stack_inv.
  intros; eapply Mem.mem_inject_ext'; eauto.
  intros; eapply Mem.record_stack_block_inject_flat; eauto.
  intros; eapply Mem.unrecord_stack_block_inject_parallel_flat; eauto.

  intros; eapply Mem.record_stack_blocks_stack_original; eauto.
  
  reflexivity. 
  simpl. Transparent Mem.load.
  unfold Mem.load, Mem.push_new_stage. simpl. intros; repeat destruct Mem.valid_access_dec; auto.
  exfalso; apply n. destruct v as (v1 & v2 & v3); repeat split; eauto. inversion 1.
  exfalso; apply n. destruct v as (v1 & v2 & v3); repeat split; eauto. inversion 1.
  intros; eapply Mem.inject_push_new_stage; eauto.
  intros; eapply Mem.inject_push_new_stage_left; eauto.
  intros; eapply Mem.inject_push_new_stage_right; eauto.
  reflexivity.
  reflexivity. reflexivity.
  
  apply Mem.wf_stack_mem.
  apply Mem.stack_perm.
  apply Mem.record_stack_blocks_top_noperm.

  
  simpl; intros; eapply Mem.extends_push_new_stage; eauto.
  simpl; intros; eapply Mem.push_new_stage_mem_unchanged; eauto.
  simpl; intros; eapply Mem.tailcall_stage_mem_unchanged; eauto.
    
  apply Mem.unrecord_push.
  
  simpl.
  unfold storebytes. intros m b o bytes m1 m2 SB1 SB2.
  destr_in SB1. inv SB1. inv SB2. apply Mem.unrecord_push.
  eapply Mem.push_storebytes_unrecord; eauto.
  intros; eapply Mem.push_store_unrecord; eauto.

  intros; eapply Mem.magree_push_new_stage; eauto.
  intros; eapply Mem.unrecord_stack_block_magree; eauto.
  intros; eapply Mem.tailcall_stage_magree; eauto.
 
  intros; eapply Mem.loadbytes_push.

  eapply Mem.tailcall_stage_tc.
  apply Mem.tailcall_stage_perm.
  eapply Mem.tailcall_stage_tl_stack.
  intro; eapply Mem.tailcall_stage_extends.
  intro; eapply Mem.tailcall_stage_inject.
  eapply Mem.tailcall_stage_stack_equiv.
  eapply Mem.tailcall_stage_same_length_pos.
  eapply Mem.tailcall_stage_nextblock.
  intro; eapply Mem.inject_new_stage_left_tailcall_right.
  intro; eapply Mem.inject_tailcall_leftnew_stage_right.
  intro; eapply Mem.tailcall_stage_inject_left.
  intro; eapply Mem.tailcall_stage_right_extends.
  apply Mem.tailcall_stage_stack_eq.
Qed.

(** Here we expose the additional properties that we need, and most of
which are actually already proved in the original CompCert
implementation. *)

Global Instance memory_model_x: Mem.MemoryModelX Mem.mem.
Proof.
  constructor.
  typeclasses eauto.
  exact Memimpl.Mem.extends_extends_compose.
  intros; eapply Memimpl.Mem.inject_extends_compose; eauto.
  intros; eapply Memimpl.Mem.inject_compose; eauto.
  exact Memimpl.Mem.extends_inject_compose.
  apply inject_neutral_incr.
  now free_tac free_inject_neutral'.
  intro; apply drop_perm_right_extends.
  intros; eapply drop_perm_parallel_extends; eauto.
  intro; now storebytes_tac storebytes_inject_neutral'.
  exact free_range.
  exact storebytes_empty.
  exact unchanged_on_trans_strong.
Qed.
