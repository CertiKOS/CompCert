Require Export LogicalRelations.
Require Import KLR.
Require Import OptionRel.
Require Import BoolRel.
Require Import Coqlib.
Require Import Integers.
Require Import Floats.
Require Export Values.
Require Import Memory.
Require Import CKLR.


(** * Complementary injection relations *)

(** ** Definitions *)

(** [Should bring over the definitions in CKLR.v, and maybe inject /
  lessdef from Values.v? => would need to make the comparison
  signatures independent from [match_mem]. *)

(** ** Properties *)

(** *** Basic properties *)

Global Instance inject_refl:
  Reflexive (Val.inject inject_id).
Proof.
  intros v. destruct v; econstructor.
  - reflexivity.
  - rewrite Ptrofs.add_zero.
    reflexivity.
Qed.

(** *** Functionality *)

Lemma ptr_inject_functional f ptr ptr1 ptr2:
  ptr_inject f ptr ptr1 ->
  ptr_inject f ptr ptr2 ->
  ptr1 = ptr2.
Proof.
  intros [b ofs b1 delta1 Hb1] Hb2'.
  inversion Hb2' as [xb xofs b2 delta2 Hb2]; clear Hb2'; subst.
  congruence.
Qed.

Lemma ptrbits_inject_functional f ptr ptr1 ptr2:
  ptrbits_inject f ptr ptr1 ->
  ptrbits_inject f ptr ptr2 ->
  ptr1 = ptr2.
Proof.
  intros [b ofs b1 delta1 Hb1] Hb2'.
  inversion Hb2' as [xb xofs b2 delta2 Hb2]; clear Hb2'; subst.
  congruence.
Qed.

Lemma ptrrange_inject_functional f ptr ptr1 ptr2:
  ptrrange_inject f ptr ptr1 ->
  ptrrange_inject f ptr ptr2 ->
  ptr1 = ptr2.
Proof.
  intros Hptr1 Hptr2.
  destruct Hptr1 as [b ofs b1 ofs1 sz1 H1].
  inversion Hptr2 as [xb xofs b2 ofs2 sz2]; clear Hptr2; subst.
  pose proof (ptr_inject_functional f (b, ofs) (b1, ofs1) (b2, ofs2) H1 H).
  assert (sz1 = sz2).
  {
    eapply Z.add_reg_l; eauto.
  }
  congruence.
Qed.

Lemma block_inject_functional f b b1 b2:
  block_inject f b b1 ->
  block_inject f b b2 ->
  b1 = b2.
Proof.
  intros [d1 Hb1] [d2 Hb2].
  congruence.
Qed.

Lemma block_sameofs_inject_functional f b b1 b2:
  block_inject_sameofs f b b1 ->
  block_inject_sameofs f b b2 ->
  b1 = b2.
Proof.
  unfold match_block_sameofs.
  congruence.
Qed.

(** *** Shift-invariance *)

Lemma ptr_inject_shift f b1 ofs1 b2 ofs2 delta:
  ptr_inject f (b1, ofs1) (b2, ofs2) ->
  ptr_inject f (b1, ofs1 + delta)%Z (b2, ofs2 + delta)%Z.
Proof.
  inversion 1; subst.
  rewrite <- Z.add_assoc.
  rewrite (Z.add_comm delta0 delta).
  rewrite Z.add_assoc.
  constructor; eauto.
Qed.

Lemma ptrbits_inject_shift f b1 ofs1 b2 ofs2 delta:
  ptrbits_inject f (b1, ofs1) (b2, ofs2) ->
  ptrbits_inject f (b1, Ptrofs.add ofs1 delta) (b2, Ptrofs.add ofs2 delta).
Proof.
  inversion 1; subst.
  rewrite Ptrofs.add_assoc.
  rewrite (Ptrofs.add_commut (Ptrofs.repr _)).
  rewrite <- Ptrofs.add_assoc.
  constructor; eauto.
Qed.

Lemma ptrrange_inject_shift f b1 ofs1 sz1 b2 ofs2 sz2 delta:
  ptrrange_inject f (b1, ofs1, sz1) (b2, ofs2, sz2) ->
  ptrrange_inject f (b1, ofs1 + delta, sz1)%Z (b2, ofs2 + delta, sz2)%Z.
Proof.
  inversion 1; subst.
  replace (ofs1 + sz)%Z with ((ofs1 + delta) + (sz - delta))%Z by omega.
  replace (ofs2 + sz)%Z with ((ofs2 + delta) + (sz - delta))%Z by omega.
  constructor.
  eapply ptr_inject_shift; eauto.
Qed.

(** See also [val_offset_ptr_inject] below. *)

(** *** Relationships between [foo_inject] relations *)

(** We call each lemma [foo_bar_inject] that establishes [bar_inject]
  from a [foo_inject] premise. When this can be done in several ways,
  we add a suffix to disambiguate. *)

Lemma ptr_ptrbits_repr_inject f b1 ofs1 b2 ofs2:
  ptr_inject f (b1, ofs1) (b2, ofs2) ->
  ptrbits_inject f (b1, Ptrofs.repr ofs1) (b2, Ptrofs.repr ofs2).
Proof.
  inversion 1; subst.
  rewrite add_repr.
  constructor.
  assumption.
Qed.

Lemma ptr_ptrbits_unsigned_inject f b1 ofs1 b2 ofs2:
  ptr_inject f (b1, Ptrofs.unsigned ofs1) (b2, Ptrofs.unsigned ofs2) ->
  ptrbits_inject f (b1, ofs1) (b2, ofs2).
Proof.
  intros H.
  rewrite <- (Ptrofs.repr_unsigned ofs1), <- (Ptrofs.repr_unsigned ofs2).
  apply ptr_ptrbits_repr_inject; eauto.
Qed.

Lemma ptr_ptrrange_inject f b1 lo1 hi1 b2 lo2 hi2:
  ptr_inject f (b1, lo1) (b2, lo2) ->
  hi1 - lo1 = hi2 - lo2 ->
  ptrrange_inject f (b1, lo1, hi1) (b2, lo2, hi2).
Proof.
  intros Hlo Hhi.
  replace hi1 with (lo1 + (hi1 - lo1))%Z by omega.
  replace hi2 with (lo2 + (hi1 - lo1))%Z by omega.
  constructor; eauto.
Qed.

Lemma ptr_block_inject f b1 ofs1 b2 ofs2:
  ptr_inject f (b1, ofs1) (b2, ofs2) ->
  block_inject f b1 b2.
Proof.
  inversion 1.
  red.
  eauto.
Qed.

Lemma ptr_block_sameofs_inject f b1 b2 ofs:
  ptr_inject f (b1, ofs) (b2, ofs) ->
  block_inject_sameofs f b1 b2.
Proof.
  inversion 1.
  assert (delta = 0) by omega.
  red.
  congruence.
Qed.

Lemma ptrbits_block_inject f b1 ofs1 b2 ofs2:
  ptrbits_inject f (b1, ofs1) (b2, ofs2) ->
  block_inject f b1 b2.
Proof.
  inversion 1.
  red.
  eauto.
Qed.

Lemma ptrrange_ptr_inject f ptr1 hi1 ptr2 hi2:
  ptrrange_inject f (ptr1, hi1) (ptr2, hi2) ->
  ptr_inject f ptr1 ptr2.
Proof.
  inversion 1.
  assumption.
Qed.

Lemma block_ptr_inject f b1 b2 ofs1:
  block_inject f b1 b2 ->
  exists ofs2, ptr_inject f (b1, ofs1) (b2, ofs2).
Proof.
  intros [delta H].
  exists (ofs1 + delta)%Z.
  constructor; eauto.
Qed.

Lemma block_ptrbits_inject f b1 b2 ofs1:
  block_inject f b1 b2 ->
  exists ofs2, ptrbits_inject f (b1, ofs1) (b2, ofs2).
Proof.
  intros [delta H].
  exists (Ptrofs.add ofs1 (Ptrofs.repr delta)).
  constructor; eauto.
Qed.

Lemma block_ptrrange_inject f b1 b2 lo1 hi1:
  block_inject f b1 b2 ->
  exists lo2 hi2, ptrrange_inject f (b1, lo1, hi1) (b2, lo2, hi2).
Proof.
  intros [delta H].
  exists (lo1 + delta)%Z, ((lo1 + delta) + (hi1 - lo1))%Z.
  pattern hi1 at 1.
  replace hi1 with (lo1 + (hi1 - lo1))%Z by omega.
  constructor.
  constructor.
  assumption.
Qed.

Lemma block_sameofs_ptr_inject f b1 ofs1 b2 ofs2:
  block_inject_sameofs f b1 b2 ->
  ofs1 = ofs2 ->
  ptr_inject f (b1, ofs1) (b2, ofs2).
Proof.
  intros Hb Hofs.
  red in Hb.
  destruct Hofs.
  pattern ofs1 at 2.
  replace ofs1 with (ofs1 + 0)%Z by omega.
  constructor; eauto.
Qed.

Lemma block_sameofs_ptrbits_inject f b1 ofs1 b2 ofs2:
  block_inject_sameofs f b1 b2 ->
  ofs1 = ofs2 ->
  ptrbits_inject f (b1, ofs1) (b2, ofs2).
Proof.
  intros Hb Hofs.
  red in Hb.
  destruct Hofs.
  pattern ofs1 at 2.
  replace ofs1 with (Ptrofs.add ofs1 (Ptrofs.repr 0%Z)).
  - constructor; eauto.
  - change (Ptrofs.repr 0) with Ptrofs.zero.
    apply Ptrofs.add_zero.
Qed.

Lemma block_sameofs_ptrrange_inject f b1 lo1 hi1 b2 lo2 hi2:
  block_inject_sameofs f b1 b2 ->
  lo1 = lo2 ->
  hi1 = hi2 ->
  ptrrange_inject f (b1, lo1, hi1) (b2, lo2, hi2).
Proof.
  intros Hb Hlo Hhi.
  red in Hb.
  subst.
  eapply ptr_ptrrange_inject; eauto.
  eapply block_sameofs_ptr_inject; eauto.
Qed.

Global Instance block_sameofs_block_inject f:
  Related (block_inject_sameofs f) (block_inject f) subrel.
Proof.
  inversion 1.
  red.
  eauto.
Qed.


(** * Relational properties *)

(** ** Basic value constructors *)

Global Instance Vundef_inject f v:
  Related (@Vundef) v (Val.inject f).
Proof.
  constructor.
Qed.

Global Instance Vint_inject mi:
  Monotonic Vint (- ==> Val.inject mi).
Proof.
  constructor.
Qed.

Global Instance Vlong_inject mi:
  Monotonic Vlong (- ==> Val.inject mi).
Proof.
  constructor.
Qed.

Global Instance Vfloat_inject mi:
  Monotonic Vfloat (- ==> Val.inject mi).
Proof.
  constructor.
Qed.

Global Instance Vsingle_inject mi:
  Monotonic Vsingle (- ==> Val.inject mi).
Proof.
  constructor.
Qed.

Global Instance Vptr_inject f:
  Monotonic (@Vptr) (% ptrbits_inject f ++> Val.inject f).
Proof.
  intros _ _ [b1 ofs1 b2 delta].
  econstructor; eauto.
Qed.

Global Instance Vzero_inject f:
  Monotonic (@Vzero) (Val.inject f).
Proof.
  unfold Vzero; rauto.
Qed.

Global Instance Vone_inject f:
  Monotonic (@Vone) (Val.inject f).
Proof.
  unfold Vone; rauto.
Qed.

Global Instance Vmone_inject f:
  Monotonic (@Vmone) (Val.inject f).
Proof.
  unfold Vmone; rauto.
Qed.

Global Instance Vtrue_inject f:
  Monotonic (@Vtrue) (Val.inject f).
Proof.
  unfold Vtrue; rauto.
Qed.

Global Instance Vfalse_inject f:
  Monotonic (@Vfalse) (Val.inject f).
Proof.
  unfold Vfalse; rauto.
Qed.

Global Instance Vnullptr_inject f:
  Monotonic Vnullptr (Val.inject f).
Proof.
  unfold Vnullptr; rauto.
Qed.

Global Instance Vptrofs_inject f:
  Monotonic Vptrofs (- ==> Val.inject f).
Proof.
  unfold Vptrofs; rauto.
Qed.

(** ** Typing predicates *)

Global Instance val_has_type_inject f:
  Monotonic (@Val.has_type) (Val.inject f --> - ==> impl).
Proof.
  unfold Val.has_type.
  intros x y Hxy ty H.
  destruct Hxy, ty; tauto.
Qed.

Global Instance val_has_type_list_inject f:
  Monotonic (@Val.has_type_list) (Val.inject_list f --> - ==> impl).
Proof.
  induction 1; simpl; rauto.
Qed.

Global Instance val_has_opttype_inject f:
  Monotonic (@Val.has_opttype) (Val.inject f --> option_le eq ++> impl).
Proof.
  unfold Val.has_opttype; repeat rstep.
  intros Hx; subst.
  inversion H; subst.
  destruct y1; constructor.
Qed.

(** ** Interpretation as a boolean *)

Global Instance val_bool_of_val_inject f:
  Monotonic (@Val.bool_of_val) (Val.inject f ++> set_le Bool.leb).
Proof.
  intros v1 v2 Hv b1 Hb1.
  destruct Hb1. inv Hv. eexists. split; [constructor|].
  rauto.
Qed.

(** ** Arithmetic operations *)

Global Instance val_neg_match f:
  Monotonic (@Val.neg) (Val.inject f ++> Val.inject f).
Proof.
  unfold Val.neg. rauto.
Qed.

Global Instance val_negf_inject f:
  Monotonic (@Val.negf) (Val.inject f ++> Val.inject f).
Proof.
  unfold Val.negf. rauto.
Qed.

Global Instance val_absf_inject f:
  Monotonic (@Val.absf) (Val.inject f ++> Val.inject f).
Proof.
  unfold Val.absf. rauto.
Qed.

Global Instance val_negfs_inject f:
  Monotonic (@Val.negfs) (Val.inject f ++> Val.inject f).
Proof.
  unfold Val.negfs. rauto.
Qed.

Global Instance val_absfs_inject f:
  Monotonic (@Val.absfs) (Val.inject f ++> Val.inject f).
Proof.
  unfold Val.absfs. rauto.
Qed.

Global Instance val_maketotal_inject f:
  Monotonic (@Val.maketotal) (option_le (Val.inject f) ++> Val.inject f).
Proof.
  unfold Val.maketotal. rauto.
Qed.

Global Instance val_intoffloat_inject f:
  Monotonic (@Val.intoffloat) (Val.inject f ++> option_le (Val.inject f)).
Proof.
  unfold Val.intoffloat. rauto.
Qed.

Global Instance val_intuoffloat_inject f:
  Monotonic (@Val.intuoffloat) (Val.inject f ++> option_le (Val.inject f)).
Proof.
  unfold Val.intuoffloat. rauto.
Qed.

Global Instance val_floatofint_inject f:
  Monotonic (@Val.floatofint) (Val.inject f ++> option_le (Val.inject f)).
Proof.
  unfold Val.floatofint. rauto.
Qed.

Global Instance val_floatofintu_inject f:
  Monotonic (@Val.floatofintu) (Val.inject f ++> option_le (Val.inject f)).
Proof.
  unfold Val.floatofintu. rauto.
Qed.

Global Instance val_intofsingle_inject f:
  Monotonic (@Val.intofsingle) (Val.inject f ++> option_le (Val.inject f)).
Proof.
  unfold Val.intofsingle. rauto.
Qed.

Global Instance val_intuofsingle_inject f:
  Monotonic (@Val.intuofsingle) (Val.inject f ++> option_le (Val.inject f)).
Proof.
  unfold Val.intuofsingle. rauto.
Qed.

Global Instance val_singleofint_inject f:
  Monotonic (@Val.singleofint) (Val.inject f ++> option_le (Val.inject f)).
Proof.
  unfold Val.singleofint. rauto.
Qed.

Global Instance val_singleofintu_inject f:
  Monotonic (@Val.singleofintu) (Val.inject f ++> option_le (Val.inject f)).
Proof.
  unfold Val.singleofintu. rauto.
Qed.

Global Instance val_negint_inject f:
  Monotonic (@Val.negint) (Val.inject f ++> Val.inject f).
Proof.
  unfold Val.negint. rauto.
Qed.

Global Instance val_notint_inject f:
  Monotonic (@Val.notint) (Val.inject f ++> Val.inject f).
Proof.
  unfold Val.notint. rauto.
Qed.

Global Instance val_of_bool_inject f:
  Monotonic (@Val.of_bool) (- ==> Val.inject f).
Proof.
  unfold Val.of_bool. rauto.
Qed.

Global Instance val_boolval_inject f:
  Monotonic (@Val.boolval) (Val.inject f ++> Val.inject f).
Proof.
  unfold Val.boolval. rauto.
Qed.

Global Instance val_notbool_inject f:
  Monotonic (@Val.notbool) (Val.inject f ++> Val.inject f).
Proof.
  unfold Val.notbool. rauto.
Qed.

Global Instance val_zero_ext_inject f:
  Monotonic (@Val.zero_ext) (- ==> Val.inject f ++> Val.inject f).
Proof.
  unfold Val.zero_ext. rauto.
Qed.

Global Instance val_sign_ext_inject f:
  Monotonic (@Val.sign_ext) (- ==> Val.inject f ++> Val.inject f).
Proof.
  unfold Val.sign_ext. rauto.
Qed.

Global Instance val_singleoffloat_inject f:
  Monotonic (@Val.singleoffloat) (Val.inject f ++> Val.inject f).
Proof.
  unfold Val.singleoffloat. rauto.
Qed.

Global Instance val_add_inject f:
  Monotonic (@Val.add) (Val.inject f ++> Val.inject f ++> Val.inject f).
Proof.
  repeat intro; apply Val.add_inject; eauto.
Qed.

Global Instance val_sub_inject f:
  Monotonic (@Val.sub) (Val.inject f ++> Val.inject f ++> Val.inject f).
Proof.
  repeat intro; apply Val.sub_inject; eauto.
Qed.

Global Instance val_mul_inject f:
  Monotonic (@Val.mul) (Val.inject f ++> Val.inject f ++> Val.inject f).
Proof.
  unfold Val.mul. rauto.
Qed.

Global Instance val_mulhs_inject f:
  Monotonic (@Val.mulhs) (Val.inject f ++> Val.inject f ++> Val.inject f).
Proof.
  unfold Val.mulhs. rauto.
Qed.

Global Instance val_mulhu_inject f:
  Monotonic (@Val.mulhu) (Val.inject f ++> Val.inject f ++> Val.inject f).
Proof.
  unfold Val.mulhu. rauto.
Qed.

Global Instance val_divs_inject f:
  Monotonic
    (@Val.divs)
    (Val.inject f ++> Val.inject f ++> option_le (Val.inject f)).
Proof.
  unfold Val.divs. rauto.
Qed.

Global Instance val_mods_inject f:
  Monotonic
    (@Val.mods)
    (Val.inject f ++> Val.inject f ++> option_le (Val.inject f)).
Proof.
  unfold Val.mods. rauto.
Qed.

Global Instance val_divu_inject f:
  Monotonic
    (@Val.divu)
    (Val.inject f ++> Val.inject f ++> option_le (Val.inject f)).
Proof.
  unfold Val.divu. rauto.
Qed.

Global Instance val_modu_inject f:
  Monotonic
    (@Val.modu)
    (Val.inject f ++> Val.inject f ++> option_le (Val.inject f)).
Proof.
  unfold Val.modu. rauto.
Qed.

Global Instance val_add_carry f:
  Monotonic
    (@Val.add_carry)
    (Val.inject f ++> Val.inject f ++> Val.inject f ++> Val.inject f).
Proof.
  unfold Val.add_carry. rauto.
Qed.

Global Instance val_sub_overflow_inject f:
  Monotonic
    (@Val.sub_overflow)
    (Val.inject f ++> Val.inject f ++> Val.inject f).
Proof.
  unfold Val.sub_overflow. rauto.
Qed.

Global Instance val_negative_inject f:
  Monotonic (@Val.negative) (Val.inject f ++> Val.inject f).
Proof.
  unfold Val.negative. rauto.
Qed.

Global Instance val_and_inject f:
  Monotonic (@Val.and) (Val.inject f ++> Val.inject f ++> Val.inject f).
Proof.
  unfold Val.and. rauto.
Qed.

Global Instance val_or_inject f:
  Monotonic (@Val.or) (Val.inject f ++> Val.inject f ++> Val.inject f).
Proof.
  unfold Val.or. rauto.
Qed.

Global Instance val_xor_inject f:
  Monotonic (@Val.xor) (Val.inject f ++> Val.inject f ++> Val.inject f).
Proof.
  unfold Val.xor. rauto.
Qed.

Global Instance val_shl_inject f:
  Monotonic (@Val.shl) (Val.inject f ++> Val.inject f ++> Val.inject f).
Proof.
  unfold Val.shl. rauto.
Qed.

Global Instance val_shr_inject f:
  Monotonic (@Val.shr) (Val.inject f ++> Val.inject f ++> Val.inject f).
Proof.
  unfold Val.shr. rauto.
Qed.

Global Instance val_shr_carry_inject f:
  Monotonic (@Val.shr_carry) (Val.inject f ++> Val.inject f ++> Val.inject f).
Proof.
  unfold Val.shr_carry. rauto.
Qed.

Global Instance val_shrx_inject f:
  Monotonic
    (@Val.shrx)
    (Val.inject f ++> Val.inject f ++> option_le (Val.inject f)).
Proof.
  unfold Val.shrx. rauto.
Qed.

Global Instance val_shru_inject f:
  Monotonic (@Val.shru) (Val.inject f ++> Val.inject f ++> Val.inject f).
Proof.
  unfold Val.shru. rauto.
Qed.

Global Instance val_rolm_inject f:
  Monotonic (@Val.rolm) (Val.inject f ++> - ==> - ==> Val.inject f).
Proof.
  unfold Val.rolm. rauto.
Qed.

Global Instance val_ror_inject f:
  Monotonic (@Val.ror) (Val.inject f ++> Val.inject f ++> Val.inject f).
Proof.
  unfold Val.ror. rauto.
Qed.

Global Instance val_addf_inject f:
  Monotonic (@Val.addf) (Val.inject f ++> Val.inject f ++> Val.inject f).
Proof.
  unfold Val.addf. rauto.
Qed.

Global Instance val_subf_inject f:
  Monotonic (@Val.subf) (Val.inject f ++> Val.inject f ++> Val.inject f).
Proof.
  unfold Val.subf. rauto.
Qed.

Global Instance val_mulf_inject f:
  Monotonic (@Val.mulf) (Val.inject f ++> Val.inject f ++> Val.inject f).
Proof.
  unfold Val.mulf. rauto.
Qed.

Global Instance val_divf_inject f:
  Monotonic (@Val.divf) (Val.inject f ++> Val.inject f ++> Val.inject f).
Proof.
  unfold Val.divf. rauto.
Qed.

Global Instance val_floatofwords_inject f:
  Monotonic
    (@Val.floatofwords)
    (Val.inject f ++> Val.inject f ++> Val.inject f).
Proof.
  unfold Val.floatofwords. rauto.
Qed.

(** ** Operations on 64-bit integers *)

Global Instance val_longofwords_inject f:
  Monotonic (@Val.longofwords) (Val.inject f ++> Val.inject f ++> Val.inject f).
Proof.
  unfold Val.longofwords. rauto.
Qed.

Global Instance val_loword_inject f:
  Monotonic (@Val.loword) (Val.inject f ++> Val.inject f).
Proof.
  unfold Val.loword. rauto.
Qed.

Global Instance val_hiword_inject f:
  Monotonic (@Val.hiword) (Val.inject f ++> Val.inject f).
Proof.
  unfold Val.hiword. rauto.
Qed.

Global Instance val_negl_inject f:
  Monotonic (@Val.negl) (Val.inject f ++> Val.inject f).
Proof.
  unfold Val.negl. rauto.
Qed.

Global Instance val_notl_inject f:
  Monotonic (@Val.notl) (Val.inject f ++> Val.inject f).
Proof.
  unfold Val.notl. rauto.
Qed.

Global Instance val_longofint_inject f:
  Monotonic (@Val.longofint) (Val.inject f ++> Val.inject f).
Proof.
  unfold Val.longofint. rauto.
Qed.

Global Instance val_longofintu_inject f:
  Monotonic (@Val.longofintu) (Val.inject f ++> Val.inject f).
Proof.
  unfold Val.longofintu. rauto.
Qed.

Global Instance val_longoffloat_inject f:
  Monotonic (@Val.longoffloat) (Val.inject f ++> option_le (Val.inject f)).
Proof.
  unfold Val.longoffloat. rauto.
Qed.

Global Instance val_longuoffloat_inject f:
  Monotonic (@Val.longuoffloat) (Val.inject f ++> option_le (Val.inject f)).
Proof.
  unfold Val.longuoffloat. rauto.
Qed.

Global Instance val_floatoflong_inject f:
  Monotonic (@Val.floatoflong) (Val.inject f ++> option_le (Val.inject f)).
Proof.
  unfold Val.floatoflong. rauto.
Qed.

Global Instance val_floatoflongu_inject f:
  Monotonic (@Val.floatoflongu) (Val.inject f ++> option_le (Val.inject f)).
Proof.
  unfold Val.floatoflongu. rauto.
Qed.

Global Instance val_singleoflong_inject f:
  Monotonic (@Val.singleoflong) (Val.inject f ++> option_le (Val.inject f)).
Proof.
  unfold Val.singleoflong. rauto.
Qed.

Global Instance val_singleoflongu_inject f:
  Monotonic (@Val.singleoflongu) (Val.inject f ++> option_le (Val.inject f)).
Proof.
  unfold Val.singleoflongu. rauto.
Qed.

Global Instance val_addl_inject f:
  Monotonic (@Val.addl) (Val.inject f ++> Val.inject f ++> Val.inject f).
Proof.
  repeat intro; apply Val.addl_inject; eauto.
Qed.

Global Instance val_subl_inject f:
  Monotonic (@Val.subl) (Val.inject f ++> Val.inject f ++> Val.inject f).
Proof.
  repeat intro; apply Val.subl_inject; eauto.
Qed.

Global Instance val_mull_inject f:
  Monotonic (@Val.mull) (Val.inject f ++> Val.inject f ++> Val.inject f).
Proof.
  unfold Val.mull. rauto.
Qed.

Global Instance val_mull'_inject f:
  Monotonic (@Val.mull') (Val.inject f ++> Val.inject f ++> Val.inject f).
Proof.
  unfold Val.mull'. rauto.
Qed.

Global Instance val_mullhs_inject f:
  Monotonic (@Val.mullhs) (Val.inject f ++> Val.inject f ++> Val.inject f).
Proof.
  unfold Val.mullhs. rauto.
Qed.

Global Instance val_mullhu_match f:
  Monotonic (@Val.mullhu) (Val.inject f ++> Val.inject f ++> Val.inject f).
Proof.
  unfold Val.mullhu. rauto.
Qed.

Global Instance val_divls_inject f:
  Monotonic
    (@Val.divls)
    (Val.inject f ++> Val.inject f ++> option_le (Val.inject f)).
Proof.
  unfold Val.divls. rauto.
Qed.

Global Instance val_modls_inject f:
  Monotonic
    (@Val.modls)
    (Val.inject f ++> Val.inject f ++> option_le (Val.inject f)).
Proof.
  unfold Val.modls. rauto.
Qed.

Global Instance val_divlu_inject f:
  Monotonic
    (@Val.divlu)
    (Val.inject f ++> Val.inject f ++> option_le (Val.inject f)).
Proof.
  unfold Val.divlu. rauto.
Qed.

Global Instance val_modlu_inject f:
  Monotonic
    (@Val.modlu)
    (Val.inject f ++> Val.inject f ++> option_le (Val.inject f)).
Proof.
  unfold Val.modlu. rauto.
Qed.

Global Instance val_andl_inject f:
  Monotonic (@Val.andl) (Val.inject f ++> Val.inject f ++> Val.inject f).
Proof.
  unfold Val.andl. rauto.
Qed.

Global Instance val_orl_inject f:
  Monotonic (@Val.orl) (Val.inject f ++> Val.inject f ++> Val.inject f).
Proof.
  unfold Val.orl. rauto.
Qed.

Global Instance val_xorl_inject f:
  Monotonic (@Val.xorl) (Val.inject f ++> Val.inject f ++> Val.inject f).
Proof.
  unfold Val.xorl. rauto.
Qed.

Global Instance val_shll_inject f:
  Monotonic (@Val.shll) (Val.inject f ++> Val.inject f ++> Val.inject f).
Proof.
  unfold Val.shll. rauto.
Qed.

Global Instance val_shrl_inject f:
  Monotonic (@Val.shrl) (Val.inject f ++> Val.inject f ++> Val.inject f).
Proof.
  unfold Val.shrl. rauto.
Qed.

Global Instance val_shrlu_inject f:
  Monotonic (@Val.shrlu) (Val.inject f ++> Val.inject f ++> Val.inject f).
Proof.
  unfold Val.shrlu. rauto.
Qed.

(** ** Comparisons *)

(** *** Prerequisites *)

(** Comparisons involving pointers are tricky. This is because the
  result may be true, false, or undefined depending on whether the
  pointers being compared are valid, and whether they're in the same
  block. In case we actually end up comparing offsets of related
  pointers, we have to handle the complications introduced by
  modular arithmetic. *)

(** Block comparisons are mostly straightforward to handle. *)

Global Instance match_ptrbits_block_rstep f b1 b2 ofs1 ofs2:
  RStep
    (ptrbits_inject f (b1, ofs1) (b2, ofs2))
    (block_inject f b1 b2) | 100.
Proof.
  red.
  apply ptrbits_block_inject.
Qed.

Global Instance eq_block_rel f:
  Monotonic
    (@eq_block)
    (forallr b1 b1' : block_inject f,
     forallr b2 b2' : block_inject f,
     sumbool_le).
Proof.
  intros b1 b2 Hb b1' b2' Hb'.
  destruct (eq_block b1 b1'); repeat rstep.
  destruct (eq_block b2 b2'); repeat rstep.
  elim n.
  subst.
  eapply block_inject_functional; eauto.
Qed.

(** Offset comparisons are more involved. *)

Section PTROFS_CMP.
  Lemma ptrofs_eq_Z_eqb x y:
    Ptrofs.eq x y = Z.eqb (Ptrofs.unsigned x) (Ptrofs.unsigned y).
  Proof.
    apply eq_iff_eq_true.
    rewrite Z.eqb_eq.
    unfold Ptrofs.eq.
    clear; destruct (zeq _ _); intuition congruence.
  Qed.

  Lemma Z_eqb_shift x y d:
    Z.eqb (x + d) (y + d) = Z.eqb x y.
  Proof.
    apply eq_iff_eq_true.
    repeat rewrite Z.eqb_eq.
    omega.
  Qed.

  Lemma ptrofs_ltu_Z_ltb x y:
    Ptrofs.ltu x y = Z.ltb (Ptrofs.unsigned x) (Ptrofs.unsigned y).
  Proof.
    apply eq_iff_eq_true.
    rewrite Z.ltb_lt.
    unfold Ptrofs.ltu.
    clear; destruct (zlt _ _); intuition congruence.
  Qed.

  Lemma Z_ltb_shift x y d:
    Z.ltb (x + d) (y + d) = Z.ltb x y.
  Proof.
    apply eq_iff_eq_true.
    repeat rewrite Z.ltb_lt.
    omega.
  Qed.

  Definition Z_cmpb c :=
    match c with
      | Ceq => Z.eqb
      | Cle => fun x y => negb (Z.ltb y x)
      | Cgt => fun x y => Z.ltb y x
      | Cge => fun x y => negb (Z.ltb x y)
      | Cne => fun x y => negb (Z.eqb x y)
      | Clt => Z.ltb
    end.

  Lemma ptrofs_cmpu_Z_cmpb c u v:
    Ptrofs.cmpu c u v = Z_cmpb c (Ptrofs.unsigned u) (Ptrofs.unsigned v).
  Proof.
    destruct c; simpl;
    rewrite ?ptrofs_eq_Z_eqb, ?ptrofs_ltu_Z_ltb;
    reflexivity.
  Qed.

  Lemma Z_cmpb_shift c x y d:
    Z_cmpb c (x + d) (y + d) = Z_cmpb c x y.
  Proof.
    destruct c;
    simpl;
    rewrite ?Z_eqb_shift, ?Z_ltb_shift;
    reflexivity.
  Qed.
End PTROFS_CMP.

Global Instance ptrofs_eq_rintro f xb1 xb2 xofs1 xofs2 yb1 yb2 yofs1 yofs2:
  RIntro
    (ptrbits_inject f (xb1, xofs1) (xb2, xofs2) /\
     ptrbits_inject f (yb1, yofs1) (yb2, yofs2) /\
     xb1 = yb1)
    eq
    (Ptrofs.eq xofs1 yofs1)
    (Ptrofs.eq xofs2 yofs2).
Proof.
  intros (Hx & Hy & Hb).
  inversion Hx.
  inversion Hy.
  subst.
  assert (delta0 = delta) by congruence; subst.
  rewrite Ptrofs.translate_eq.
  reflexivity.
Qed.

Global Instance ptrofs_ltu_rintro R w m1 m2 xb1 xb2 xofs1 xofs2 yb1 yb2 yofs1 yofs2:
  RIntro
    (match_mem R w m1 m2 /\
     match_ptrbits R w (xb1, xofs1) (xb2, xofs2) /\
     match_ptrbits R w (yb1, yofs1) (yb2, yofs2) /\
     xb1 = yb1 /\
     Mem.weak_valid_pointer m1 xb1 (Ptrofs.unsigned xofs1) = true /\
     Mem.weak_valid_pointer m1 xb1 (Ptrofs.unsigned yofs1) = true)
    eq
    (Ptrofs.ltu xofs1 yofs1)
    (Ptrofs.ltu xofs2 yofs2).
Proof.
  intros (Hm & Hx & Hy & Hb & Hxv & Hyv).
  inversion Hx.
  inversion Hy.
  subst.
  assert (delta0 = delta) by congruence; subst.
  rewrite !ptrofs_ltu_Z_ltb.
  eapply (cklr_weak_valid_pointer_address_inject_weak R w) in H0; [ | eauto].
  destruct H0 as (delta' & Hdelta').
  rewrite !Hdelta' by eauto.
  rewrite Z_ltb_shift.
  reflexivity.
Qed.

Global Instance ptrofs_cmpu_rintro R w m1 m2 c xb1 xb2 xofs1 xofs2 yb1 yb2 yofs1 yofs2:
  RIntro
    (match_mem R w m1 m2 /\
     match_ptrbits R w (xb1, xofs1) (xb2, xofs2) /\
     match_ptrbits R w (yb1, yofs1) (yb2, yofs2) /\
     xb1 = yb1 /\
     Mem.weak_valid_pointer m1 xb1 (Ptrofs.unsigned xofs1) = true /\
     Mem.weak_valid_pointer m1 xb1 (Ptrofs.unsigned yofs1) = true)
    eq
    (Ptrofs.cmpu c xofs1 yofs1)
    (Ptrofs.cmpu c xofs2 yofs2).
Proof.
  intros (Hm & Hx & Hy & Hb & Hxv & Hyv).
  inversion Hx.
  inversion Hy.
  subst.
  assert (delta0 = delta) by congruence; subst.
  eapply (cklr_weak_valid_pointer_address_inject_weak R w) in H0; [ | eauto].
  destruct H0 as (delta' & Hdelta').
  rewrite !ptrofs_cmpu_Z_cmpb.
  rewrite !Hdelta' by eauto.
  rewrite Z_cmpb_shift.
  reflexivity.
Qed.

(** One last complication is that [Val.cmpu] and [Val.cmplu] can
  formally accept an arbitrary [valid_pointer] predicate, but our
  proof relies on the fact that they are actually passed
  [Mem.valid_pointer] applied to related memories. Thankfully, we
  can express this constraint with the relation
  [(match_mem R p) !! Mem.valid_pointer]. We also use the following
  instance of [RStep] to automatically fold the derived
  [weak_valid_pointer] into the actual [Mem.weak_valid_pointer] that
  we know things about. *)

Lemma fold_weak_valid_pointer_rstep Rb m1 m2 b1 b2 ofs1 ofs2:
  RStep
    (Rb (Mem.weak_valid_pointer m1 b1 ofs1)
        (Mem.weak_valid_pointer m2 b2 ofs2))
    (Rb (Mem.valid_pointer m1 b1 ofs1 || Mem.valid_pointer m1 b1 (ofs1 - 1))
        (Mem.valid_pointer m2 b2 ofs2 || Mem.valid_pointer m2 b2 (ofs2 - 1))).
Proof.
  intros H.
  exact H.
Qed.

Hint Extern 1
  (RStep _ (_ (Mem.valid_pointer _ _ _ || Mem.valid_pointer _ _ _)
              (Mem.valid_pointer _ _ _ || Mem.valid_pointer _ _ _))) =>
  eapply fold_weak_valid_pointer_rstep : typeclass_instances.

(** *** Comparison operations *)

Global Instance val_cmp_bool_inject f:
  Monotonic
    Val.cmp_bool
    (- ==> Val.inject f ++> Val.inject f ++> option_le eq).
Proof.
  unfold Val.cmp_bool. rauto.
Qed.

(*
Local Instance ptrbits_inject_rintro f b1 b2 delta ofs1 ofs2:
  RIntro
    (f b1 = Some (b2, delta) /\ ofs2 = Ptrofs.add ofs1 (Ptrofs.repr delta))
    (ptrbits_inject f) (b1, ofs1) (b2, ofs2).
Proof.
  intros [Hb Hofs].
  subst. constructor. assumption.
Qed.
*)

Global Instance val_cmpu_bool_inject R w:
  Monotonic
    (@Val.cmpu_bool)
    ((match_mem R w) !! Mem.valid_pointer ++> - ==>
     Val.inject (mi R w) ++> Val.inject (mi R w) ++> option_le eq).
Proof.
  intros ? ? H.
  destruct H.
  unfold Val.cmpu_bool.

  repeat rstep.
  - destruct b4.
    + rdestruct_remember.
      repeat rstep;
      subst;
      repeat match goal with
        | H: _ && _ = true |- _ =>
          apply andb_true_iff in H;
          destruct H
      end;
      assumption.
    + subst.
      destruct (Mem.valid_pointer x b1 (Ptrofs.unsigned ofs1) &&
                Mem.valid_pointer x b0 (Ptrofs.unsigned ofs0)) eqn:Hvp.
      * generalize Hvp.
        transport Hvp.
        intros Hvp'.
        setoid_rewrite Hvp.
        assert (ofs2 <> ofs3).
        {
          apply andb_prop in Hvp.
          apply andb_prop in Hvp'.
          destruct Hvp, Hvp'.
          eapply (cklr_different_pointers_inject R w) in n; eauto.
          destruct n; try congruence.
        }
        destruct x0; simpl; repeat rstep;
        rewrite Ptrofs.eq_false; eauto.
      * rauto.

  - destruct b4.
    + subst.
      destruct (Mem.valid_pointer x b1 (Ptrofs.unsigned ofs1) &&
                Mem.valid_pointer x b0 (Ptrofs.unsigned ofs0)) eqn:Hvp.
      * generalize Hvp.
        transport Hvp.
        intros Hvp'.
        setoid_rewrite Hvp.
        assert (ofs3 <> ofs2).
        {
          apply andb_prop in Hvp.
          apply andb_prop in Hvp'.
          destruct Hvp, Hvp'.
          eapply (cklr_different_pointers_inject R w) in H7; eauto.
          destruct H7; try congruence.
        }
        destruct x0; simpl; repeat rstep;
        rewrite Ptrofs.eq_false; eauto.
      * rauto.
    + repeat rstep.
Qed.

Global Instance val_cmpf_bool_inject f:
  Monotonic
    (@Val.cmpf_bool)
    (- ==> Val.inject f ++> Val.inject f ++> option_le eq).
Proof.
  unfold Val.cmpf_bool. rauto.
Qed.

Global Instance val_cmpl_bool_inject f:
  Monotonic
    (@Val.cmpl_bool)
    (- ==> Val.inject f ++> Val.inject f ++> option_le eq).
Proof.
  unfold Val.cmpl_bool. rauto.
Qed.

Global Instance val_cmplu_bool_inject R w:
  Monotonic
    (@Val.cmplu_bool)
    ((match_mem R w) !! Mem.valid_pointer ++> - ==>
     Val.inject (mi R w) ++> Val.inject (mi R w) ++> option_le eq).
Proof.
  intros ? ? H.
  destruct H.
  unfold Val.cmplu_bool.

  repeat rstep.
  - destruct b4.
    + rdestruct_remember.
      repeat rstep;
      subst;
      repeat match goal with
        | H: _ && _ = true |- _ =>
          apply andb_true_iff in H;
          destruct H
      end;
      assumption.
    + subst.
      destruct (Mem.valid_pointer x b1 (Ptrofs.unsigned ofs1) &&
                Mem.valid_pointer x b0 (Ptrofs.unsigned ofs0)) eqn:Hvp.
      * generalize Hvp.
        transport Hvp.
        intros Hvp'.
        setoid_rewrite Hvp.
        assert (ofs2 <> ofs3).
        {
          apply andb_prop in Hvp.
          apply andb_prop in Hvp'.
          destruct Hvp, Hvp'.
          eapply (cklr_different_pointers_inject R w) in n; try eassumption.
          destruct n; try congruence.
        }
        destruct x0; simpl; repeat rstep;
        rewrite Ptrofs.eq_false; eauto.
      * rauto.

  - destruct b4.
    + subst.
      destruct (Mem.valid_pointer x b1 (Ptrofs.unsigned ofs1) &&
                Mem.valid_pointer x b0 (Ptrofs.unsigned ofs0)) eqn:Hvp.
      * generalize Hvp.
        transport Hvp.
        intros Hvp'.
        setoid_rewrite Hvp.
        assert (ofs2 <> ofs3).
        {
          apply andb_prop in Hvp.
          apply andb_prop in Hvp'.
          destruct Hvp, Hvp'.
          eapply (cklr_different_pointers_inject R w) in H6; try eassumption.
          destruct H6; try congruence.
        }
        destruct x0; simpl; repeat rstep;
        rewrite Ptrofs.eq_false; eauto.
      * rauto.
    + repeat rstep.
Qed.

Global Instance val_of_optbool_inject f:
  Monotonic (@Val.of_optbool) (option_le eq ++> Val.inject f).
Proof.
  unfold Val.of_optbool. rauto.
Qed.

Global Instance val_cmp_inject f:
  Monotonic (@Val.cmp) (- ==> Val.inject f ++> Val.inject f ++> Val.inject f).
Proof.
  unfold Val.cmp. rauto.
Qed.

Global Instance val_cmpu_inject R w:
  Monotonic
    (@Val.cmpu)
    ((match_mem R w) !! Mem.valid_pointer ++>
     - ==> Val.inject (mi R w) ++> Val.inject (mi R w) ++> Val.inject (mi R w)).
Proof.
  unfold Val.cmpu. rauto.
Qed.

Global Instance val_cmpf_inject f:
  Monotonic (@Val.cmpf) (- ==> Val.inject f ++> Val.inject f ++> Val.inject f).
Proof.
  unfold Val.cmpf. rauto.
Qed.

Global Instance val_cmpl_inject f:
  Monotonic
    (@Val.cmpl)
    (- ==> Val.inject f ++> Val.inject f ++> option_le (Val.inject f)).
Proof.
  unfold Val.cmpl. rauto.
Qed.

Global Instance val_cmplu_inject R w:
  Monotonic
    Val.cmplu
    ((match_mem R w) !! Mem.valid_pointer ++> - ==> Val.inject (mi R w) ++>
     Val.inject (mi R w) ++> option_le (Val.inject (mi R w))).
Proof.
  unfold Val.cmplu. rauto.
Qed.

Global Instance val_maskzero_bool_inject f:
  Monotonic
    Val.maskzero_bool
    (Val.inject f ++> - ==> option_le eq).
Proof.
  unfold Val.maskzero_bool. rauto.
Qed.

Global Instance val_offset_ptr_inject f:
  Monotonic
    Val.offset_ptr
    (Val.inject f ++> - ==> Val.inject f).
Proof.
  unfold Val.offset_ptr. repeat rstep.
  eauto using ptrbits_inject_shift.
Qed.

Global Instance val_load_result_inject f:
  Monotonic (@Val.load_result) (- ==> Val.inject f ++> Val.inject f).
Proof.
  unfold Val.load_result. rauto.
Qed.
