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
    match_mem: klr mem mem;

    acc_preorder:
      PreOrder acc;

    mi_acc:
      Monotonic mi (acc ++> - ==> option_le eq);

    cklr_alloc:
      Monotonic
        (@Mem.alloc)
        ([] match_mem ++> - ==> - ==> <> match_mem * match_block);

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

    cklr_perm:
      Monotonic
        (@Mem.perm)
        ([] match_mem ++> % match_ptr ++> - ==> - ==> k impl);

    cklr_valid_block:
      Monotonic
        (@Mem.valid_block)
        ([] match_mem ++> match_block ++> k iff);

    (* similar to Mem.different_pointers_inject. Necessary for
       comparing valid pointers of different memory blocks that inject
       into the same block. *)
    cklr_different_pointers_inject:
      forall w m m' b1 ofs1 b2 ofs2 b1' delta1 b2' delta2,
        match_mem w m m' ->
        b1 <> b2 ->
        Mem.valid_pointer m b1 (Ptrofs.unsigned ofs1) = true ->
        Mem.valid_pointer m b2 (Ptrofs.unsigned ofs2) = true ->
        mi w b1 = Some (b1', delta1) ->
        mi w b2 = Some (b2', delta2) ->
        b1' <> b2' \/
        Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta1)) <>
        Ptrofs.unsigned (Ptrofs.add ofs2 (Ptrofs.repr delta2));

    (* similar to Mem.weak_valid_pointer_inject_val, but cannot be deduced
       from Mem.address_inject. Needed for Val.cmpu* *)
    cklr_weak_valid_pointer_inject_val:
      forall w m1 m2 b1 ofs1 b2 ofs2,
        match_mem w m1 m2 ->
        Mem.weak_valid_pointer m1 b1 (Ptrofs.unsigned ofs1) = true ->
        match_ptrbits w (b1, ofs1) (b2, ofs2) ->
        Mem.weak_valid_pointer m2 b2 (Ptrofs.unsigned ofs2) = true;

    (** When comparing two weakly valid pointers of the same block
     using Val.cmpu, we need to compare their offsets, and so
     comparing the injected offsets must have the same result. To
     this end, it is necessary to show that all weakly valid
     pointers be shifted by the same mathematical (not machine)
     integer amount. However, contrary to the situation with
     Mem.address_inject for valid pointers, here for weakly valid
     pointers we do not know whether this amount is delta. The best
     we know, thanks to Mem.weak_valid_pointer_inject_no_overflow,
     is that Ptrofs.unsigned (Ptrofs.repr delta) works, but proving
     composition would be much harder than for the following
     weak version:
    *)
    cklr_weak_valid_pointer_address_inject_weak:
      forall w m1 m2 b1 b2 delta,
        match_mem w m1 m2 ->
        mi w b1 = Some (b2, delta) ->
        exists delta',
          forall ofs1,
            Mem.weak_valid_pointer m1 b1 (Ptrofs.unsigned ofs1) = true ->
            Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta)) =
            (Ptrofs.unsigned ofs1 + delta')%Z;

    (* similar to Mem.address_inject for memory injections.
       Needed at least by Clight assign_of (By_copy) and memcpy,
       but I guess at many other places. *)
    cklr_address_inject:
      forall w m1 m2 b1 ofs1 b2 delta pe,
        match_mem w m1 m2 ->
        Mem.perm m1 b1 (Ptrofs.unsigned ofs1) Cur pe ->
        mi w b1 = Some (b2, delta) ->
        Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta)) =
        (Ptrofs.unsigned ofs1 + delta)%Z;

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

Global Existing Instances acc_preorder.
Global Existing Instances mi_acc.
Global Instance mi_acc_params: Params (@mi) 2.

Global Existing Instances cklr_alloc.
Local  Existing Instances cklr_free. (* strengthened version below *)
Global Existing Instances cklr_load.
Global Existing Instances cklr_store.
Global Existing Instances cklr_loadbytes.
Global Existing Instances cklr_storebytes.
Global Existing Instances cklr_perm.
Global Existing Instances cklr_valid_block.

(** Since [winit] is hard-coded as [True] in our [KripkeFrame], we use
  the following hint to discharge it. *)

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
  RIntro
    (match_block_sameofs R w b1 b2)
    (match_ptrbits R w) (b1, o) (b2, o).
Proof.
  intros H.
  replace o with (Ptrofs.add o Ptrofs.zero) at 2
    by (rewrite Ptrofs.add_zero; reflexivity).
  constructor.
  assumption.
Qed.

(** *** Compatibility with the accessibility relation *)

(** XXX: do we want to state those in terms of inject_incr/foo_inject?
  Would that work? *)

Global Instance match_ptr_acc R:
  Monotonic (match_ptr R) (acc R ++> subrel).
Proof.
  intros p1 p2 Hp ptr1 ptr2 Hptr.
  destruct Hptr as [b1 ofs1 b2 delta Hb].
Typeclasses Opaque k1.
  transport Hb; subst.
  constructor; eauto.
Qed.

Global Instance match_ptr_acc_params:
  Params (@match_ptr) 3.

Global Instance match_ptrbits_acc R:
  Monotonic (match_ptrbits R) (acc R ++> subrel).
Proof.
  intros p1 p2 Hp ptr1 ptr2 Hptr.
  destruct Hptr as [b1 ofs1 b2 delta Hb].
  transport Hb; subst.
  constructor; eauto.
Qed.

Global Instance match_ptrbits_acc_params:
  Params (@match_ptrbits) 3.

Global Instance match_ptrrange_acc R:
  Monotonic (match_ptrrange R) (acc R ++> subrel).
Proof.
  intros p1 p2 Hp ptr1 ptr2 Hptr.
  destruct Hptr as [b1 ofs1 b2 ofs2 sz Hb].
  constructor; eauto.
  revert Hb.
  apply match_ptr_acc.
  assumption.
Qed.

Global Instance match_ptrrange_acc_params:
  Params (@match_ptrrange) 3.

Global Instance match_block_acc R:
  Monotonic (match_block R) (acc R ++> subrel).
Proof.
  intros p1 p2 Hp b1 b2 [delta Hb].
  transport Hb; subst.
  eexists; eauto.
Qed.

Global Instance match_block_acc_params:
  Params (@match_block) 3.

Global Instance match_block_sameofs_acc R:
  Monotonic (match_block_sameofs R) (acc R ++> subrel).
Proof.
  intros p1 p2 Hp b1 b2 Hb.
  transport Hb; subst.
  eauto.
Qed.

Global Instance match_block_sameofs_acc_params:
  Params (@match_block_sameofs) 3.

Global Instance match_val_acc R:
  Monotonic (match_val R) (acc R ++> subrel).
Proof.
  intros w w' Hw x y Hxy.
  destruct Hxy; econstructor; eauto.
  transport H. subst. assumption.
Qed.

Global Instance match_val_acc_params:
  Params (@match_val) 3.

Global Instance match_memval_acc R:
  Monotonic (match_memval R) (acc R ++> subrel).
Proof.
  intros w w' Hw x y Hxy.
  destruct Hxy; constructor; eauto.
  destruct H; econstructor; eauto.
  transport H. subst. assumption.
Qed.

Global Instance match_memval_acc_params:
  Params (@match_memval) 3.

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

(** *** Miscellaneous *)

Lemma match_val_weaken_to_undef R w v1 v2:
  match_val R w v1 v2 ->
  match_val R w Vundef v2.
Proof.
  intros Hv.
  destruct Hv; try rauto.
Admitted. (* need the match_val hints *)

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

(** When pointers are extracted from Compcert [val]ues, they use
  machine integers and we know related values contain pointers that
  are related by [match_ptrbits]. Often we then convert this machine
  pointer with offset [ofs] into an mathematical pointer with offset
  [Ptrofs.unsigned ofs]. This is made explicit for our block-offset
  pair pointers using the following function. *)

Definition ptrofbits (p: block * ptrofs) :=
  let '(b, ofs) := p in (b, Ptrofs.unsigned ofs).

(** Unfortunately we can't establish that the results of this
  process are related by [match_ptr] without proving the side
  conditions of [match_ptrbits_ptr]. However if the side-conditions
  can't be proved directly from the context, we can use the relation
  [match_ptrbits !! ptrofbits] to remember that they were
  constructed in this way instead.

  For many memory operations this is enough, because the success of
  whichever memory operation we will use the pointer with will be
  sufficient to prove the side-conditions for [match_ptrbits_ptr]. *)

Global Instance match_ptrofbits_rintro R w b1 ofs1 b2 ofs2:
  RIntro
    (match_ptrbits R w (b1, ofs1) (b2, ofs2))
    ((match_ptrbits R w) !! ptrofbits)
    (b1, Ptrofs.unsigned ofs1)
    (b2, Ptrofs.unsigned ofs2).
Proof.
  intros H.
  change (b1, Ptrofs.unsigned ofs1) with (ptrofbits (b1, ofs1)).
  change (b2, Ptrofs.unsigned ofs2) with (ptrofbits (b2, ofs2)).
  constructor; eauto.
Qed.

Global Instance valid_pointer_match R w:
  Monotonic
    (@Mem.valid_pointer)
    (match_mem R w ++> % (match_ptrbits R w) !! ptrofbits ++> Bool.leb).
Proof.
  intros m1 m2 Hm _ _ [[b1 ofs1] [b2 ofs2] H].
  simpl.
  destruct (Mem.valid_pointer m1 _ _) eqn:H1.
  - assert (match_ptr R w (b1, Ptrofs.unsigned ofs1) (b2, Ptrofs.unsigned ofs2)).
    {
      eapply match_ptrbits_ptr; repeat rstep.
      eapply Mem.valid_pointer_nonempty_perm; eauto.
    }
    transport H1.
    rewrite H1.
    constructor.
  - destruct (Mem.valid_pointer m2 _ _) eqn:H2; repeat rstep.
Qed.

Global Instance weak_valid_pointer_match R w:
  Monotonic
    Mem.weak_valid_pointer
    (match_mem R w ++> % (match_ptrbits R w) !! ptrofbits ++> Bool.leb).
Proof.
  intros m1 m2 Hm _ _ [[b1 ofs1] [b2 ofs2] Hptr].
  unfold uncurry; simpl.
  destruct (Mem.weak_valid_pointer m1 _ _) eqn:Hwvp1.
  - erewrite (cklr_weak_valid_pointer_inject_val R w); eauto.
    constructor.
  - rauto.
Qed.

Global Instance valid_pointer_weaken_match R w:
  Related
    Mem.valid_pointer
    Mem.weak_valid_pointer
    (match_mem R w ++> % (match_ptrbits R w) !! ptrofbits ++> Bool.leb).
Proof.
  intros m1 m2 Hm _ _ [[b1 ofs1] [b2 ofs2] H]. unfold uncurry; simpl.
  transitivity (Mem.weak_valid_pointer m1 b1 (Ptrofs.unsigned ofs1)).
  - unfold Mem.weak_valid_pointer.
    destruct (Mem.valid_pointer m1 b1 (Ptrofs.unsigned ofs1)); simpl; eauto.
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
