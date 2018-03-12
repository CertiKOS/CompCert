Require Export LogicalRelations.
Require Import KLR.
Require Import OptionRel.
Require Import BoolRel.
Require Export Coqlib.
Require Export Integers.
Require Export AST.
Require Export Values.
Require Export Memory.


(** * Complementary injection relations *)

(** XXX should this go to Valuesrel.v or something such? *)

(** ** Definitions *)

(** Compcert usually passes pointers around as separate block and
  offset arguments. Since we can't relate those independently
  (because the offset shift is specific to each block), we instead
  relate (block, offset) pairs and use [rel_curry] to construct our
  [Monotonicity] relations.

  Relating pointers is complicated because of the interaction
  between the abstract [Z] offsets that are used by the memory model
  and the [ptrofs] concrete machine representations that are used to
  build [val]ues. The basic relation [match_ptr] relates abstract
  pointers in the obvious way, while [match_ptrbits] relates
  concrete pointers as is done in [Val.inject]. *)

Inductive ptr_inject (f: meminj): relation (block * Z) :=
  ptr_inject_intro b1 ofs1 b2 delta:
    f b1 = Some (b2, delta) ->
    ptr_inject f (b1, ofs1) (b2, ofs1 + delta).

Hint Constructors ptr_inject.

Inductive ptrbits_inject (f: meminj): relation (block * ptrofs) :=
  ptrbits_inject_intro b1 ofs1 b2 delta:
    f b1 = Some (b2, delta) ->
    ptrbits_inject f (b1, ofs1) (b2, Ptrofs.add ofs1 (Ptrofs.repr delta)).

Hint Constructors ptrbits_inject.

Global Instance Vptr_inject f:
  Monotonic (@Vptr) (% ptrbits_inject f ++> Val.inject f).
Proof.
  intros _ _ [b1 ofs1 b2 delta].
  econstructor; eauto.
Qed.

(** For [Mem.free] we need to relate a whole range of abstract
  pointers in the form of an (ofs, lo, hi) triple. *)

Inductive ptrrange_inject (f: meminj): relation (block * Z * Z) :=
  ptrrange_inject_intro b1 ofs1 b2 ofs2 sz:
    RIntro
      (ptr_inject f (b1, ofs1) (b2, ofs2))
      (ptrrange_inject f) (b1, ofs1, ofs1+sz) (b2, ofs2, ofs2+sz).

Hint Constructors ptrrange_inject.
Global Existing Instance ptrrange_inject_intro.

(** For operations that manipulate blocks, we can use the two
  relations below: the weaker [match_block] relates two blocks
  according to [cklr_meminj], no matter what the offset shift
  is. The stronger [match_block_sameofs] only relates blocks that
  correspond to one another with no shift in offset. *)

Definition block_inject (f: meminj) b1 b2 :=
  exists delta, f b1 = Some (b2, delta).

Definition block_inject_sameofs (f: meminj) b1 b2 :=
  f b1 = Some (b2, 0%Z).

Hint Unfold block_inject.
Hint Unfold block_inject_sameofs.

(* When going from [Z] to [ptrofs] (using [Ptrofs.repr]), there is no
  problem going also from [ptr_inject] to [ptrbits_inject]. However,
  when converting from machine pointer related by [ptrbits_inject]
  to abstract pointers with [Z] offsets (using [Ptrofs.unsigned]),
  we cannot easily establish that the results are related by
  [ptr_inject], since there may in fact be a discrepency of k·2^n
  between the correct target pointer obtained by adding [delta] and
  that obtained through [Ptrofs.unsigned].

  The compiler proofs deal with this through a property of memory
  injections, which ensures that representable, valid pointers in the
  source memory correspond to representable target pointers as well.
  Whenever a memory operation succeeds on a pointer retreived from a
  machine value, we can then deduce that a corresponding target
  machine pointer will be the correct one.

  In the relational framework we integrate this approach by defining a
  third relation [rptr_inject], which asserts that two (abtract, [Z])
  pointer are related by a memory injection, *under the condition*
  that the memory injection preserve the representability of the
  source pointer. *)

Definition rptr_preserved (f: meminj) (ptr: block * Z): Prop :=
  let '(b, ofs) := ptr in
  forall b' delta,
    f b = Some (b', delta) ->
    0 <= ofs <= Ptrofs.max_unsigned ->
    delta >= 0 /\ 0 <= ofs + delta <= Ptrofs.max_unsigned.

Definition rptr_inject (f: meminj): relation (block * Z) :=
  rel_impl (lsat (rptr_preserved f)) (ptr_inject f).

(** ** Coqrel support *)

(** Destruct [Val.inject] in terms of [ptrbits_inject]. *)

Global Instance val_inject_rdestruct f:
  RDestruct
    (Val.inject f)
    (fun P =>
       (forall n, P (Vint n) (Vint n)) /\
       (forall n, P (Vlong n) (Vlong n)) /\
       (forall x, P (Vfloat x) (Vfloat x)) /\
       (forall x, P (Vsingle x) (Vsingle x)) /\
       (forall b1 ofs1 b2 ofs2,
         ptrbits_inject f (b1, ofs1) (b2, ofs2) ->
         P (Vptr b1 ofs1) (Vptr b2 ofs2)) /\
       (forall v, P Vundef v)).
Proof.
  intros v1 v2 Hv P (Hint & Hlong & Hfloat & Hsingle & Hptr & Hundef).
  destruct Hv; eauto.
  eapply Hptr.
  subst.
  constructor; eauto.
Qed.

(** CompCert's [inject_incr] can be expressed as [- ==> option_le eq]
  in coqrel, as illustrated by the following instance. *)

Global Instance inject_incr_option_le:
  Related inject_incr (- ==> option_le eq)%rel subrel.
Proof.
  intros f g Hfg b.
  destruct (f b) as [[b' ofs] | ] eqn:Hb; try constructor.
  apply Hfg in Hb.
  rewrite Hb. rauto.
Qed.

(** Note that the instance above is not sufficient to ensure that
  [inject_incr] properties can be used by the monotonicity
  tactic. This is because [subrel] is only looped in after [RElim] has
  been performed, but we only know how to do that with
  [(- ==> option_le eq)]. Hence the following instance: *)

Lemma inject_incr_relim (f g: meminj) (b1 b2: block) P Q:
  RElim (option_le eq) (f b1) (g b2) P Q ->
  RElim inject_incr f g (b1 = b2 /\ P) Q.
Proof.
  intros H Hfg [Hb HP].
  apply inject_incr_option_le in Hfg.
  relim Hfg; eauto.
Qed.

Hint Extern 1 (RElim inject_incr _ _ _ _) =>
  eapply inject_incr_relim : typeclass_instances.

Lemma inject_incr_rintro f g:
  RIntro (forall b, option_le eq (f b) (g b)) inject_incr f g.
Proof.
  intros H b b1' delta1 Hb1.
  specialize (H b).
  transport Hb1.
  congruence.
Qed.

(** ** Compatibility with [inject_incr] *)

Global Instance ptr_inject_incr:
  Monotonic (@ptr_inject) (inject_incr ++> subrel).
Proof.
  intros p1 p2 Hp ptr1 ptr2 Hptr.
  destruct Hptr as [b1 ofs1 b2 delta Hb].
  transport Hb; subst.
  constructor; eauto.
Qed.

Global Instance ptrbits_inject_incr:
  Monotonic (@ptrbits_inject) (inject_incr ++> subrel).
Proof.
  intros p1 p2 Hp ptr1 ptr2 Hptr.
  destruct Hptr as [b1 ofs1 b2 delta Hb].
  transport Hb; subst.
  constructor; eauto.
Qed.

Global Instance rptr_preserved_incr:
  Monotonic (@rptr_preserved) (inject_incr --> - ==> impl).
Proof.
  intros g f Hfg [b ofs] Hptr b' delta Hb Hofs.
  eapply Hptr; eauto.
Qed.

Global Instance rptr_inject_incr:
  Monotonic (@rptr_inject) (inject_incr ++> subrel).
Proof.
  unfold rptr_inject. rauto.
Qed.

Global Instance ptrrange_inject_incr:
  Monotonic (@ptrrange_inject) (inject_incr ++> subrel).
Proof.
  intros p1 p2 Hp ptr1 ptr2 Hptr.
  destruct Hptr as [b1 ofs1 b2 ofs2 sz Hb].
  constructor; eauto.
  revert Hb.
  apply ptr_inject_incr.
  assumption.
Qed.

Global Instance block_inject_incr:
  Monotonic (@block_inject) (inject_incr ++> subrel).
Proof.
  intros p1 p2 Hp b1 b2 [delta Hb].
  transport Hb; subst.
  eexists; eauto.
Qed.

Global Instance block_inject_sameofs_incr:
  Monotonic (@block_inject_sameofs) (inject_incr ++> subrel).
Proof.
  intros p1 p2 Hp b1 b2 Hb.
  transport Hb; subst.
  eauto.
Qed.

Global Instance val_inject_incr:
  Monotonic (@Val.inject) (inject_incr ++> subrel).
Proof.
  intros w w' Hw x y Hxy.
  destruct Hxy; econstructor; eauto.
Qed.

Global Instance memval_inject_incr:
  Monotonic (@memval_inject) (inject_incr ++> subrel).
Proof.
  intros w w' Hw x y Hxy.
  destruct Hxy; constructor; eauto.
Qed.


(** * Compcert Kripke simulation relations *)

(** ** Definition *)

(** A CompCert KLR specifies a set for worlds, a transitive
  accessibility relation between them, and world-indexed relations for
  all the basic ingredients CompCert states are built out of: values,
  memory states, etc. From these components, it is possible to build
  up simulation relations for complex types such as [Clight.state] or
  [Asm.state] in a uniform way over all possible KLRs, and
  compositionally prove very general relational parametricity
  properties for the functions that manipulate them.

  The relations on values are all derived from the memory injection
  [mi w] associated to a world [w]. In addition, the KLR specifies a
  relation [match_mem] over memory states, which may be much richer
  than the usual memory extension and injection relations. While
  "peripheral" relations ([match_val], etc.) will be monotonic in the
  world (so that existing relationaships between environments,
  register maps, etc. can be carried along when we transition to a
  successor world), this is not necessarily the case for the relation
  on memories: the memory state is expected to be the core of all
  states and to drive the transitions between worlds.

  The basic relation components should be compatible with the basic
  memory operations, so that they satisfy the relational properties
  enumerated below. *)

Record cklr :=
  {
    world: Type;
    acc: rel world world;
    cklr_kf: KripkeFrame world := {| acc := acc; winit w := True |};

    mi: world -> meminj;
    match_val: klr val val := fun w => Val.inject (mi w);
    match_memval: klr memval memval := fun w => memval_inject (mi w);
    match_block: klr block block := fun w => block_inject (mi w);
    match_block_sameofs: klr block block := fun w => block_inject_sameofs (mi w);
    match_ptr: klr (block * Z) (block * Z) := fun w => ptr_inject (mi w);
    match_ptrbits: klr _ _ := fun w => ptrbits_inject (mi w);
    match_ptrrange: klr _ _ := fun w => ptrrange_inject (mi w);
    match_rptr: klr _ _ := fun w => rptr_inject (mi w);
    match_mem: klr mem mem;

    acc_preorder:
      PreOrder acc;

    mi_acc:
      Monotonic mi (acc ++> inject_incr);

    cklr_alloc:
      Monotonic
        (@Mem.alloc)
        ([] match_mem ++> - ==> - ==> <> match_mem * match_block_sameofs);

    cklr_free:
      Monotonic
        (@Mem.free)
        ([] match_mem ++> %% match_ptrrange ++> k1 option_le (<> match_mem));

    cklr_load:
      Monotonic
        (@Mem.load)
        ([] - ==> match_mem ++> % match_ptr ++> k1 option_le match_val);

    cklr_store:
      Monotonic
        (@Mem.store)
        ([] - ==> match_mem ++> % match_ptr ++> match_val ++>
         k1 option_le (<> match_mem));

    cklr_loadbytes:
      Monotonic
        (@Mem.loadbytes)
        ([] match_mem ++> % match_ptr ++> - ==>
         k1 option_le (k1 list_rel match_memval));

    cklr_storebytes:
      Monotonic
        (@Mem.storebytes)
        ([] match_mem ++> % match_ptr ++> k1 list_rel match_memval ++>
         k1 option_le (<> match_mem));

    cklr_storebytes_empty:
      Monotonic
        (@Mem.storebytes)
        ([] match_mem ++> % k ⊤ ++> k (req nil) ++>
         k1 option_le (<> match_mem));

    cklr_perm:
      Monotonic
        (@Mem.perm)
        ([] match_mem ++> % match_ptr ++> - ==> - ==> k impl);

    cklr_valid_block:
      Monotonic
        (@Mem.valid_block)
        ([] match_mem ++> match_block ++> k iff);

    cklr_no_overlap w m1 m2:
      match_mem w m1 m2 ->
      Mem.meminj_no_overlap (mi w) m1;

    cklr_representable w m1 m2 b1 ofs1:
      match_mem w m1 m2 ->
      Mem.perm m1 b1 ofs1 Max Nonempty \/
      Mem.perm m1 b1 (ofs1 - 1) Max Nonempty ->
      rptr_preserved (mi w) (b1, ofs1);

    (* similar to Mem.aligned_area_inject for memory injections.
       Needed by Clight assign_of (By_copy) and memcpy. *)
    cklr_aligned_area_inject:
      forall w m m' b ofs al sz b' delta,
        match_mem w m m' ->
        (al = 1 \/ al = 2 \/ al = 4 \/ al = 8) ->
        sz > 0 ->
        (al | sz) ->
        Mem.range_perm m b ofs (ofs + sz) Cur Nonempty ->
        (al | ofs) ->
        mi w b = Some (b', delta) ->
        (al | ofs + delta);

    (* similar to Mem.disjoint_or_equal_inject for memory injections.
       Needed by Clight assign_of (By_copy) and memcpy. *)
    cklr_disjoint_or_equal_inject:
      forall w m m' b1 b1' delta1 b2 b2' delta2 ofs1 ofs2 sz,
        match_mem w m m' ->
        mi w b1 = Some (b1', delta1) ->
        mi w b2 = Some (b2', delta2) ->
        Mem.range_perm m b1 ofs1 (ofs1 + sz) Max Nonempty ->
        Mem.range_perm m b2 ofs2 (ofs2 + sz) Max Nonempty ->
        sz > 0 ->
        b1 <> b2 \/
        ofs1 = ofs2 \/
        ofs1 + sz <= ofs2 \/ ofs2 + sz <= ofs1 ->
        b1' <> b2' \/
        (ofs1 + delta1 = ofs2 + delta2)%Z \/
        ofs1 + delta1 + sz <= ofs2 + delta2 \/
        ofs2 + delta2 + sz <= ofs1 + delta1
  }.

Hint Unfold match_val.
Hint Unfold match_memval.
Hint Unfold match_block.
Hint Unfold match_block_sameofs.
Hint Unfold match_ptr.
Hint Unfold match_ptrbits.
Hint Unfold match_ptrrange.
Hint Unfold match_rptr.

Global Existing Instances cklr_kf.
Global Existing Instances acc_preorder.
Global Existing Instances mi_acc.
Global Instance mi_acc_params: Params (@mi) 2.

Global Existing Instances cklr_alloc.
Local Existing Instances cklr_free.
Local Existing Instances cklr_load.
Local Existing Instances cklr_store.
Local Existing Instances cklr_loadbytes.
Local Existing Instances cklr_storebytes.
Local Existing Instances cklr_perm.
Global Existing Instances cklr_valid_block.

(** Since [winit] is hard-coded as [True] in our [KripkeFrame],
  we can use the following hint to discharge it. *)

Global Instance cklr_winit_rstep R (w: world R):
  RStep True (winit (KripkeFrame := cklr_kf R) w).
Proof.
  exact (fun H => H).
Qed.

(** ** Some derived properties *)

Global Instance match_block_sameofs_match_ptr R w b1 b2 o:
  RExists
    (match_block_sameofs R w b1 b2)
    (match_ptr R w) (b1, o) (b2, o).
Proof.
  intros H.
  replace o with (o + 0)%Z at 2 by omega.
  constructor.
  assumption.
Qed.

Global Instance match_block_sameofs_match_ptrbits R w b1 b2 o:
  RExists
    (match_block_sameofs R w b1 b2)
    (match_ptrbits R w) (b1, o) (b2, o).
Proof.
  intros H.
  replace o with (Ptrofs.add o Ptrofs.zero) at 2
    by (rewrite Ptrofs.add_zero; reflexivity).
  constructor.
  assumption.
Qed.

(** *** Machine pointers *)

(** When comparing two weakly valid pointers of the same block
  using Val.cmpu, we need to compare their offsets, and so
  comparing the injected offsets must have the same result. To
  this end, it is necessary to show that all weakly valid
  pointers be shifted by the same mathematical (not machine)
  integer amount. *)

Lemma cklr_weak_valid_pointer_address_inject:
  forall R w m1 m2 b1 b2 delta ofs1,
    match_mem R w m1 m2 ->
    mi R w b1 = Some (b2, delta) ->
    Mem.weak_valid_pointer m1 b1 (Ptrofs.unsigned ofs1) = true ->
    Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta)) =
    Ptrofs.unsigned ofs1 + delta.
Proof.
  intros.
  pose proof (Ptrofs.unsigned_range_2 ofs1).
  edestruct (cklr_representable R w m1 m2 b1 (Ptrofs.unsigned ofs1)); eauto.
  {
    rewrite !Mem.weak_valid_pointer_spec, !Mem.valid_pointer_nonempty_perm in H1.
    intuition eauto using Mem.perm_cur_max.
  }
  rewrite Ptrofs.add_unsigned.
  rewrite !Ptrofs.unsigned_repr.
  - reflexivity.
  - xomega.
  - rewrite Ptrofs.unsigned_repr by xomega.
    assumption.
Qed.

(* Similar to [Mem.address_inject]; needed by Clight assign_of
  (By_copy), memcpy, and likely other places. *)

Lemma cklr_address_inject R w m1 m2 b1 ofs1 b2 delta pe:
  match_mem R w m1 m2 ->
  Mem.perm m1 b1 (Ptrofs.unsigned ofs1) Cur pe ->
  mi R w b1 = Some (b2, delta) ->
  Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta)) =
  Ptrofs.unsigned ofs1 + delta.
Proof.
  intros.
  eapply cklr_weak_valid_pointer_address_inject; eauto.
  apply Mem.valid_pointer_implies.
  apply Mem.valid_pointer_nonempty_perm.
  eapply Mem.perm_implies; eauto.
  constructor.
Qed.

(** *** Compatibility with the accessibility relation *)

Global Instance match_ptr_acc:
  Monotonic (@match_ptr) (forallr - @ R, acc R ++> subrel).
Proof.
  unfold match_ptr. rauto.
Qed.

Global Instance match_ptrbits_acc:
  Monotonic (@match_ptrbits) (forallr - @ R, acc R ++> subrel).
Proof.
  unfold match_ptrbits. rauto.
Qed.

Global Instance match_ptrrange_acc:
  Monotonic (@match_ptrrange) (forallr - @ R, acc R ++> subrel).
Proof.
  unfold match_ptrrange. rauto.
Qed.

Global Instance match_block_acc:
  Monotonic (@match_block) (forallr - @ R, acc R ++> subrel).
Proof.
  unfold match_block. rauto.
Qed.

Global Instance match_block_sameofs_acc:
  Monotonic (@match_block_sameofs) (forallr - @ R, acc R ++> subrel).
Proof.
  unfold match_block_sameofs. rauto.
Qed.

Global Instance match_val_acc:
  Monotonic (@match_val) (forallr - @ R, acc R ++> subrel).
Proof.
  unfold match_val. rauto.
Qed.

Global Instance match_memval_acc:
  Monotonic (@match_memval) (forallr - @ R, acc R ++> subrel).
Proof.
  unfold match_memval. rauto.
Qed.

(** *** Functionality *)

Lemma match_ptr_functional R w ptr ptr1 ptr2:
  match_ptr R w ptr ptr1 ->
  match_ptr R w ptr ptr2 ->
  ptr1 = ptr2.
Proof.
  intros [b ofs b1 delta1 Hb1] Hb2'.
  inversion Hb2' as [xb xofs b2 delta2 Hb2]; clear Hb2'; subst.
  congruence.
Qed.

Lemma match_ptrbits_functional R w ptr ptr1 ptr2:
  match_ptrbits R w ptr ptr1 ->
  match_ptrbits R w ptr ptr2 ->
  ptr1 = ptr2.
Proof.
  intros [b ofs b1 delta1 Hb1] Hb2'.
  inversion Hb2' as [xb xofs b2 delta2 Hb2]; clear Hb2'; subst.
  congruence.
Qed.

Lemma match_ptrrange_functional R w ptr ptr1 ptr2:
  match_ptrrange R w ptr ptr1 ->
  match_ptrrange R w ptr ptr2 ->
  ptr1 = ptr2.
Proof.
  intros Hptr1 Hptr2.
  destruct Hptr1 as [b ofs b1 ofs1 sz1 H1].
  inversion Hptr2 as [xb xofs b2 ofs2 sz2]; clear Hptr2; subst.
  pose proof (match_ptr_functional R w (b, ofs) (b1, ofs1) (b2, ofs2) H1 H).
  assert (sz1 = sz2).
  {
    eapply Z.add_reg_l; eauto.
  }
  congruence.
Qed.

Lemma match_block_functional R w b b1 b2:
  match_block R w b b1 ->
  match_block R w b b2 ->
  b1 = b2.
Proof.
  intros [d1 Hb1] [d2 Hb2].
  congruence.
Qed.

Lemma match_block_sameofs_functional R w b b1 b2:
  match_block_sameofs R w b b1 ->
  match_block_sameofs R w b b2 ->
  b1 = b2.
Proof.
  unfold match_block_sameofs.
  congruence.
Qed.

(** *** Shift-invariance *)

Lemma match_ptr_shift R w b1 ofs1 b2 ofs2 delta:
  match_ptr R w (b1, ofs1) (b2, ofs2) ->
  match_ptr R w (b1, ofs1 + delta)%Z (b2, ofs2 + delta)%Z.
Proof.
  inversion 1; subst.
  rewrite <- Z.add_assoc.
  rewrite (Z.add_comm delta0 delta).
  rewrite Z.add_assoc.
  constructor; eauto.
Qed.

Lemma match_ptrbits_shift R w b1 ofs1 b2 ofs2 delta:
  match_ptrbits R w (b1, ofs1) (b2, ofs2) ->
  match_ptrbits R w (b1, Ptrofs.add ofs1 delta) (b2, Ptrofs.add ofs2 delta).
Proof.
  inversion 1; subst.
  rewrite Ptrofs.add_assoc.
  rewrite (Ptrofs.add_commut (Ptrofs.repr _)).
  rewrite <- Ptrofs.add_assoc.
  constructor; eauto.
Qed.

Lemma match_ptrrange_shift R w b1 ofs1 sz1 b2 ofs2 sz2 delta:
  match_ptrrange R w (b1, ofs1, sz1) (b2, ofs2, sz2) ->
  match_ptrrange R w (b1, ofs1 + delta, sz1)%Z (b2, ofs2 + delta, sz2)%Z.
Proof.
  inversion 1; subst.
  replace (ofs1 + sz)%Z with ((ofs1 + delta) + (sz - delta))%Z by omega.
  replace (ofs2 + sz)%Z with ((ofs2 + delta) + (sz - delta))%Z by omega.
  constructor.
  eapply match_ptr_shift; eauto.
Qed.

(** *** Relationships between [match_foo] relations *)

(** We call each lemma [match_foo_bar] that establishes [match_bar]
  from a [match_foo] premise. When this can be done in several ways,
  we add a suffix to disambiguate. *)

Lemma add_repr ofs1 delta:
  Ptrofs.repr (ofs1 + delta) =
  Ptrofs.add (Ptrofs.repr ofs1) (Ptrofs.repr delta).
Proof.
    rewrite Ptrofs.add_unsigned.
    auto using Ptrofs.eqm_samerepr,
    Ptrofs.eqm_add, Ptrofs.eqm_unsigned_repr.
Qed.    

Lemma match_ptr_ptrbits_repr R w b1 ofs1 b2 ofs2:
  match_ptr R w (b1, ofs1) (b2, ofs2) ->
  match_ptrbits R w (b1, Ptrofs.repr ofs1) (b2, Ptrofs.repr ofs2).
Proof.
  inversion 1; subst.
  rewrite add_repr.
  constructor.
  assumption.
Qed.

Lemma match_ptr_ptrbits_unsigned R w b1 ofs1 b2 ofs2:
  match_ptr R w (b1, Ptrofs.unsigned ofs1) (b2, Ptrofs.unsigned ofs2) ->
  match_ptrbits R w (b1, ofs1) (b2, ofs2).
Proof.
  intros H.
  rewrite <- (Ptrofs.repr_unsigned ofs1), <- (Ptrofs.repr_unsigned ofs2).
  apply match_ptr_ptrbits_repr; eauto.
Qed.

Lemma match_ptr_ptrrange R w b1 lo1 hi1 b2 lo2 hi2:
  match_ptr R w (b1, lo1) (b2, lo2) ->
  hi1 - lo1 = hi2 - lo2 ->
  match_ptrrange R w (b1, lo1, hi1) (b2, lo2, hi2).
Proof.
  intros Hlo Hhi.
  replace hi1 with (lo1 + (hi1 - lo1))%Z by omega.
  replace hi2 with (lo2 + (hi1 - lo1))%Z by omega.
  constructor; eauto.
Qed.

Lemma match_ptr_block R w b1 ofs1 b2 ofs2:
  match_ptr R w (b1, ofs1) (b2, ofs2) ->
  match_block R w b1 b2.
Proof.
  inversion 1.
  red. red.
  eauto.
Qed.

Lemma match_ptr_block_sameofs R w b1 b2 ofs:
  match_ptr R w (b1, ofs) (b2, ofs) ->
  match_block_sameofs R w b1 b2.
Proof.
  inversion 1.
  assert (delta = 0) by omega.
  red.
  congruence.
Qed.

Global Instance match_ptr_rptr_acc:
  Related (@match_ptr) (@match_rptr) (forallr - @ R, acc R ++> subrel)%rel.
Proof.
  intros R w1 w2 Hw ptr1 ptr2 Hptr.
  unfold match_ptr, match_rptr, rptr_inject in *. rauto.
Qed.

Lemma match_ptrbits_ptr R w m1 m2 b1 o1 b2 o2 pe:
  match_mem R w m1 m2 ->
  match_ptrbits R w (b1, o1) (b2, o2) ->
  Mem.perm m1 b1 (Ptrofs.unsigned o1) Cur pe ->
  match_ptr R w (b1, Ptrofs.unsigned o1) (b2, Ptrofs.unsigned o2).
Proof.
  intros H H0 H1.
  inversion H0; subst.
  erewrite cklr_address_inject; eauto.
Qed.

Lemma match_ptrbits_block R w b1 ofs1 b2 ofs2:
  match_ptrbits R w (b1, ofs1) (b2, ofs2) ->
  match_block R w b1 b2.
Proof.
  inversion 1.
  red. red.
  eauto.
Qed.

Lemma match_ptrbits_rptr_unsigned R w b1 ofs1 b2 ofs2:
  RIntro
    (match_ptrbits R w (b1, ofs1) (b2, ofs2))
    (match_rptr R w) (b1, Ptrofs.unsigned ofs1) (b2, Ptrofs.unsigned ofs2).
Proof.
  intros Hptr Hinrange. red in Hinrange.
  inv Hptr.
  pose proof (Ptrofs.unsigned_range_2 ofs1) as Hofs1.
  edestruct Hinrange as [Hdelta Hofs']; eauto.
  replace (Ptrofs.unsigned (Ptrofs.add _ _)) with (Ptrofs.unsigned ofs1 + delta).
  - constructor; eauto.
  - rewrite Ptrofs.add_unsigned.
    rewrite (Ptrofs.unsigned_repr delta) by xomega.
    rewrite Ptrofs.unsigned_repr by xomega.
    reflexivity.
Qed.

Hint Extern 1 (RIntro _ (match_rptr _ _) (_, Ptrofs.unsigned _) _) =>
  eapply match_ptrbits_rptr_unsigned : typeclass_instances.

Hint Extern 1 (RIntro _ (match_rptr _ _) _ (_, Ptrofs.unsigned _)) =>
  eapply match_ptrbits_rptr_unsigned : typeclass_instances.

Lemma match_ptrrange_ptr R w ptr1 hi1 ptr2 hi2:
  match_ptrrange R w (ptr1, hi1) (ptr2, hi2) ->
  match_ptr R w ptr1 ptr2.
Proof.
  inversion 1.
  assumption.
Qed.

Lemma match_block_ptr R w b1 b2 ofs1:
  match_block R w b1 b2 ->
  exists ofs2, match_ptr R w (b1, ofs1) (b2, ofs2).
Proof.
  intros [delta H].
  exists (ofs1 + delta)%Z.
  constructor; eauto.
Qed.

Lemma match_block_ptrbits R w b1 b2 ofs1:
  match_block R w b1 b2 ->
  exists ofs2, match_ptrbits R w (b1, ofs1) (b2, ofs2).
Proof.
  intros [delta H].
  exists (Ptrofs.add ofs1 (Ptrofs.repr delta)).
  constructor; eauto.
Qed.

Lemma match_block_ptrrange R w b1 b2 lo1 hi1:
  match_block R w b1 b2 ->
  exists lo2 hi2, match_ptrrange R w (b1, lo1, hi1) (b2, lo2, hi2).
Proof.
  intros [delta H].
  exists (lo1 + delta)%Z, ((lo1 + delta) + (hi1 - lo1))%Z.
  pattern hi1 at 1.
  replace hi1 with (lo1 + (hi1 - lo1))%Z by omega.
  constructor.
  constructor.
  assumption.
Qed.

Lemma match_block_sameofs_ptr R w b1 ofs1 b2 ofs2:
  match_block_sameofs R w b1 b2 ->
  ofs1 = ofs2 ->
  match_ptr R w (b1, ofs1) (b2, ofs2).
Proof.
  intros Hb Hofs.
  red in Hb.
  destruct Hofs.
  pattern ofs1 at 2.
  replace ofs1 with (ofs1 + 0)%Z by omega.
  constructor; eauto.
Qed.

Lemma match_block_sameofs_ptrbits R w b1 ofs1 b2 ofs2:
  match_block_sameofs R w b1 b2 ->
  ofs1 = ofs2 ->
  match_ptrbits R w (b1, ofs1) (b2, ofs2).
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

Lemma match_block_sameofs_ptrrange R w b1 lo1 hi1 b2 lo2 hi2:
  match_block_sameofs R w b1 b2 ->
  lo1 = lo2 ->
  hi1 = hi2 ->
  match_ptrrange R w (b1, lo1, hi1) (b2, lo2, hi2).
Proof.
  intros Hb Hlo Hhi.
  red in Hb.
  subst.
  eapply match_ptr_ptrrange; eauto.
  eapply match_block_sameofs_ptr; eauto.
Qed.

Global Instance match_block_sameofs_block R w:
  Related (match_block_sameofs R w) (match_block R w) subrel.
Proof.
  inversion 1.
  red. red.
  eauto.
Qed.

(** If we have a valid pointer on the left-hand side, then [match_rptr]
  can be promoted to [match_ptr]. This is used below to strengthen the
  relational properties of most memory operations so that they only
  require [match_rptr] for ther hypotheses. *)

Lemma match_rptr_ptr R w m1 m2 b1 ofs1 b2 ofs2:
  match_mem R w m1 m2 ->
  match_rptr R w (b1, ofs1) (b2, ofs2) ->
  Mem.weak_valid_pointer m1 b1 ofs1 = true ->
  match_ptr R w (b1, ofs1) (b2, ofs2).
Proof.
  intros Hm Hptr Hptr1.
  apply Hptr. red.
  eapply cklr_representable; eauto.
  apply Mem.weak_valid_pointer_spec in Hptr1.
  rewrite !Mem.valid_pointer_nonempty_perm in Hptr1.
  intuition eauto using Mem.perm_implies, Mem.perm_cur_max.
Qed.

Lemma match_rptr_ptr_valid_access R w m1 m2 b1 ofs1 b2 ofs2 chunk pe:
  match_mem R w m1 m2 ->
  match_rptr R w (b1, ofs1) (b2, ofs2) ->
  Mem.valid_access m1 chunk b1 ofs1 pe ->
  match_ptr R w (b1, ofs1) (b2, ofs2).
Proof.
  intros Hm Hptr Hptr1.
  eapply match_rptr_ptr; eauto.
  apply Mem.valid_pointer_implies.
  apply Mem.valid_pointer_nonempty_perm.
  eapply Mem.valid_access_perm in Hptr1.
  eapply Mem.perm_implies; eauto.
  constructor.
Qed.

(** *** Miscellaneous *)

Lemma match_val_weaken_to_undef R w v1 v2:
  match_val R w v1 v2 ->
  match_val R w Vundef v2.
Proof.
  intros Hv.
  destruct Hv; try rauto.
Admitted. (* need the match_val hints *)

(* Machine pointer version of [cklr_no_overlap]. This is similar to
  [Mem.different_pointers_inject], and is necessary for comparing
  valid pointers of different memory blocks that inject into the same
  block. *)

Lemma cklr_different_pointers_inject R w:
  forall m m' b1 ofs1 b2 ofs2 b1' ofs1' b2' ofs2',
    match_mem R w m m' ->
    b1 <> b2 ->
    Mem.valid_pointer m b1 (Ptrofs.unsigned ofs1) = true ->
    Mem.valid_pointer m b2 (Ptrofs.unsigned ofs2) = true ->
    match_ptrbits R w (b1, ofs1) (b1', ofs1') ->
    match_ptrbits R w (b2, ofs2) (b2', ofs2') ->
    b1' <> b2' \/ ofs1' <> ofs2'.
Proof.
  intros until ofs2'.
  intros Hm Hb Hptr1 Hptr2 Hptr1' Hptr2'.
  eapply match_ptrbits_rptr_unsigned, match_rptr_ptr in Hptr1';
    eauto using Mem.valid_pointer_implies.
  eapply match_ptrbits_rptr_unsigned, match_rptr_ptr in Hptr2';
    eauto using Mem.valid_pointer_implies.
  eapply Mem.valid_pointer_nonempty_perm in Hptr1.
  eapply Mem.valid_pointer_nonempty_perm in Hptr2.
  inv Hptr1'. inv Hptr2'.
  edestruct cklr_no_overlap; eauto using Mem.perm_implies, Mem.perm_cur_max.
  right.
  congruence.
Qed.

(** ** Properties of derived memory operations *)

Global Instance cklr_loadv R:
  Monotonic
    (@Mem.loadv)
    ([] - ==> match_mem R ++> match_val R ++> k1 option_le (match_val R)).
Proof.
  repeat red.
  intros w Hw a x y H x0 y0 H0.
  inversion H0; subst; simpl; try now constructor.
  destruct (Mem.load a x _ (Ptrofs.unsigned _)) eqn:LOAD; try now constructor.
  rewrite <- LOAD.
  repeat rstep.
  eapply match_ptrbits_ptr; eauto.
  eapply Mem.load_valid_access; eauto.
  generalize (size_chunk_pos a); omega.
Qed.

Global Instance cklr_storev R:
  Monotonic
    (@Mem.storev)
    ([] - ==> match_mem R ++> match_val R ++> match_val R ++>
     k1 option_le (<> match_mem R)).
Proof.
  intros w Hw a x y H x0 y0 H0 x1 y1 H1.
  destruct (Mem.storev a x _ _) eqn:STORE; [ | rauto ].
  rewrite <- STORE.
  inversion H0; subst; simpl; try rauto.
  simpl in STORE.
  repeat rstep.
  eapply match_ptrbits_ptr; eauto.
  eapply Mem.store_valid_access_3; eauto.
  generalize (size_chunk_pos a); omega.
Qed.

(** Maybe it's possible to prove [cklr_storebytes] from [cklr_store]
  as well. But if it is, it's tricky. *)

Global Instance cklr_free_list R:
  Monotonic
    (@Mem.free_list)
    ([] match_mem R ++> k1 list_rel (match_ptrrange R) ++>
     k1 option_le (<> match_mem R)).
Proof.
  intros w Hw m1 m2 Hm l1 l2 Hl.
  revert w l2 Hl Hw m1 m2 Hm.
  induction l1; inversion 1; subst; simpl Mem.free_list; intros.
  - rauto.
  - rstep.
    rstep; rstep.
    rstep; rstep.
    + destruct H4 as (w' & Hw' & H4).
      destruct (IHl1 w' y0 rauto I x y1 rauto) as [? ? (w'' & Hw'' & H) | ];
      rauto.
    + rauto.
Qed.

Local Instance mem_valid_pointer_match R w:
  Monotonic
    (@Mem.valid_pointer)
    (match_mem R w ++> % match_ptr R w ++> Bool.leb).
Proof.
  intros m1 m2 Hm [b1 ofs1] [b2 ofs2] Hp.
  simpl.
  destruct (Mem.valid_pointer m1 b1 ofs1) eqn:Hp1; simpl; eauto.
  revert Hp1.
  rewrite !Mem.valid_pointer_nonempty_perm.
  repeat rstep.
Qed.

Local Instance mem_weak_valid_pointer_match R w:
  Monotonic
    (@Mem.weak_valid_pointer)
    (match_mem R w ++> % match_ptr R w ++> Bool.leb).
Proof.
  intros m1 m2 Hm [b1 ofs1] [b2 ofs2] Hp.
  simpl.
  unfold Mem.weak_valid_pointer.
  repeat rstep.
  apply match_ptr_shift.
  assumption.
Qed.

(** ** Strengthened properties for memory operations *)

Definition ptrrange_perm m k p: relation _ :=
  lsat (fun r => match r with (b, lo, hi) => Mem.range_perm m b lo hi k p end).

Global Instance cklr_free_perm R w:
  Monotonic
    (@Mem.free)
    (forallr m1 m2 : match_mem R w,
       %% rel_impl (ptrrange_perm m1 Cur Freeable) (match_ptrrange R w) ++>
       option_le ((<> match_mem R)%klr w)).
Proof.
  rstep.
  repeat rstep.
  destruct x as [[b1 lo1] hi1], y as [[b2 lo2] hi2]; simpl.
  destruct (Mem.free v1 b1 lo1 hi1) eqn:Hfree; repeat rstep.
  assert (ptrrange_perm v1 Cur Freeable (b1, lo1, hi1) (b2, lo2, hi2)).
  {
    eapply Mem.free_range_perm.
    eassumption.
  }
  rewrite <- Hfree.
  rauto.
Qed.

(** We can restate the monotonicity properties for most memory
  operations using [match_rptr] instead of [match_ptr]. *)

Global Instance cklr_perm_rptr R w:
  Monotonic
    (@Mem.perm)
    (match_mem R w ++> % match_rptr R w ++> - ==> - ==> impl).
Proof.
  intros m1 m2 Hm [b1 ofs1] [b2 ofs2] Hptr k p.
  simpl. intros H. generalize H. repeat rstep.
  eapply Hptr. red.
  eapply cklr_representable; eauto.
  left.
  eapply Mem.perm_implies with (p1 := p); [ | constructor].
  destruct k; eauto using Mem.perm_cur_max.
Qed.

Global Instance cklr_load_rptr R:
  Monotonic
    (@Mem.load)
    ([] - ==> match_mem R ++> % match_rptr R ++> k1 option_le (match_val R)).
Proof.
  intros w Hw chunk m1 m2 Hm [b1 ofs1] [b2 ofs2] Hptr.
  simpl. red.
  destruct (Mem.load chunk m1 b1 ofs1) as [v1 | ] eqn:Hload; try rauto.
  rewrite <- Hload.
  eapply match_rptr_ptr_valid_access in Hptr; eauto with mem.
  rauto.
Qed.

Global Instance cklr_store_rptr R:
  Monotonic
    (@Mem.store)
    ([] - ==> match_mem R ++> % match_rptr R ++> match_val R ++>
     k1 option_le (<> match_mem R)).
Proof.
  intros w Hw chunk m1 m2 Hm [b1 ofs1] [b2 ofs2] Hptr v1 v2 Hv.
  simpl.
  destruct (Mem.store chunk m1 b1 ofs1 v1) as [m1' | ] eqn:Hm1'; [ | rauto].
  rewrite <- Hm1'.
  eapply match_rptr_ptr_valid_access in Hptr; eauto with mem.
  rauto.
Qed.

Global Instance cklr_loadbytes_rptr R:
  Monotonic
    (@Mem.loadbytes)
    ([] match_mem R ++> % match_rptr R ++> - ==>
     k1 option_le (k1 list_rel (match_memval R))).
Proof.
  intros w Hw m1 m2 Hm [b1 ofs1] [b2 ofs2] Hptr sz.
  simpl.
  assert (sz <= 0 \/ 0 < sz) as [Hsz | Hsz] by xomega.
  - rewrite !Mem.loadbytes_empty by assumption.
    rauto.
  - destruct (Mem.loadbytes m1 b1 ofs1 sz) eqn:H; [ | rauto].
    rewrite <- H.
    apply Mem.loadbytes_range_perm in H.
    eapply match_rptr_ptr_valid_access in Hptr; eauto.
    + rauto.
    + split.
      * instantiate (2 := Mint8unsigned). simpl.
        intros ofs Hofs. eapply H. xomega.
      * simpl.
        apply Z.divide_1_l.
Qed.

Global Instance cklr_storebytes_rptr R:
  Monotonic
    (@Mem.storebytes)
    ([] match_mem R ++> % match_rptr R ++> k1 list_rel (match_memval R) ++>
     k1 option_le (<> match_mem R)).
Proof.
  intros w Hw m1 m2 Hm [b1 ofs1] [b2 ofs2] Hptr vs1 vs2 Hvs.
  simpl.
  destruct vs1 as [ | v1 vs1].
  - inv Hvs.
    pose proof (cklr_storebytes_empty R).
    rauto.
  - destruct (Mem.storebytes m1 b1 ofs1 _) eqn:H; [ | rauto].
    rewrite <- H.
    apply Mem.storebytes_range_perm in H.
    eapply match_rptr_ptr_valid_access in Hptr; eauto.
    + rauto.
    + split.
      * instantiate (2 := Mint8unsigned). simpl.
        intros ofs Hofs. eapply H. simpl length. xomega.
      * simpl.
        apply Z.divide_1_l.
Qed.

Global Instance valid_pointer_match R w:
  Monotonic
    (@Mem.valid_pointer)
    (match_mem R w ++> % match_rptr R w ++> Bool.leb).
Proof.
  intros m1 m2 Hm [b1 ofs1] [b2 ofs2] Hptr.
  simpl.
  destruct (Mem.valid_pointer m1 _ _) eqn:H1.
  - eapply match_rptr_ptr in Hptr; eauto using Mem.valid_pointer_implies.
    transport H1.
    rewrite H1.
    reflexivity.
  - rauto.
Qed.

Global Instance weak_valid_pointer_match R w:
  Monotonic
    (@Mem.weak_valid_pointer)
    (match_mem R w ++> % match_rptr R w ++> Bool.leb).
Proof.
  intros m1 m2 Hm [b1 ofs1] [b2 ofs2] Hptr.
  simpl.
  destruct (Mem.weak_valid_pointer m1 _ _) eqn:Hwvp1.
  - eapply match_rptr_ptr in Hptr; eauto.
    transport Hwvp1.
    rewrite Hwvp1.
    reflexivity.
  - rauto.
Qed.

Global Instance valid_pointer_weaken_match R w:
  Related
    (@Mem.valid_pointer)
    (@Mem.weak_valid_pointer)
    (match_mem R w ++> % match_rptr R w ++> Bool.leb).
Proof.
  intros m1 m2 Hm [b1 ofs1] [b2 ofs2] H.
  simpl.
  transitivity (Mem.weak_valid_pointer m1 b1 ofs1).
  - unfold Mem.weak_valid_pointer.
    destruct (Mem.valid_pointer m1 b1 ofs1); simpl; eauto.
  - rauto.
Qed.


(** * Tactics *)

(** Here we define some tactics which may be useful when building up
  on our simulation relation tookits. *)

(* Inverse hypothese for some relations when the left-hand side has a
  specific form. For now, we use an ad-hoc tactic, but maybe we could
  find a way to strengthen the relators associated with [nil], [cons],
  [Vint], [Vptr], etc. to express the properties used here. *)

Ltac inverse_hyps :=
  repeat
    lazymatch goal with
      | H: list_rel ?R (?x :: ?xs) ?yl |- _ =>
        inversion H; clear H; subst
      | H: list_rel ?R nil ?yl |- _ =>
        inversion H; clear H; subst
      | H: match_val ?R ?p (Vint _) ?y |- _ =>
        inversion H; clear H; subst
      | H: match_val ?R ?p (Vlong _) ?y |- _ =>
        inversion H; clear H; subst
      | H: match_val ?R ?p (Vfloat _) ?y |- _ =>
        inversion H; clear H; subst
      | H: match_val ?R ?p (Vsingle _) ?y |- _ =>
        inversion H; clear H; subst
      | H: match_val ?R ?p (Vptr _ _) ?y |- _ =>
        inversion H; clear H; subst
    end.

(** Another common need is to solve a goal which consists in [set_rel]
  used in conjunction with an inductive type. The [deconstruct] tactic
  destructs a hypothesis [H], and for each generated subgoal passes
  the corresponding constructor to the continuation k. *)

Ltac head m :=
  lazymatch m with
    | ?x _ => head x
    | ?x => constr:(x)
  end.

Ltac deconstruct H k :=
  let HH := fresh in
  destruct H eqn:HH;
  lazymatch type of HH with
    | _ = ?cc =>
      let c := head cc in
      clear HH; k c
  end.

(** We can use that to build a systematic way to solve goals which
  related two elements of an inductive type with [set_rel]. Namely,
  destruct the hypothesis which states the left-hand side is in the
  set, then for each branch transport all of the premises and apply
  the same constructor again. *)

Ltac solve_set_rel :=
  lazymatch goal with
    | |- set_le _ _ _ =>
      let H := fresh in
      let reconstruct c :=
        idtac "Using constructor" c;
        clear H;
        split_hyps;
        inverse_hyps;
        transport_hyps;
        try (eexists; split; [eapply c; eauto | repeat rstep]) in
      intros ? H;
      deconstruct H reconstruct
    | |- impl _ _ =>
      let H := fresh in
      let reconstruct c :=
        idtac "Using constructor" c;
        clear H;
        split_hyps;
        inverse_hyps;
        transport_hyps;
        try (eapply c; eauto) in
      intros H;
      deconstruct H reconstruct
    | |- _ =>
      intro; solve_set_rel
  end.

(** This can be useful when [rel_curry] is involved *)
Ltac eexpair :=
  lazymatch goal with
    | |- @ex (prod ?T1 ?T2) _ =>
      let xv := fresh in evar (xv: T1);
      let x := eval red in xv in clear xv;
      let yv := fresh in evar (yv: T2);
      let y := eval red in yv in clear yv;
      exists (x, y); simpl
  end.
