(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris                                  *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Assertions on memory states, in the style of separation logic *)

(** This library defines a number of useful logical assertions about
  CompCert memory states, such as "block [b] at offset [ofs] contains
  value [v]".  Assertions can be grouped using a separating conjunction
  operator in the style of separation logic.  

  Currently, this library is used only in module [Stackingproof]
  to reason about the shapes of stack frames generated during the
  [Stacking] pass.

  This is not a full-fledged separation logic because there is no
  program logic (Hoare triples) to speak of.  Also, there is no general
  frame rule; instead, a weak form of the frame rule is provided
  by the lemmas that help us reason about the logical assertions. *)

Require Import Setoid Program.Basics.
Require Import Coqlib Decidableplus.
Require Import AST_old Integers Values_old Memory_old Events_old Globalenvs_old.

Section WITHMEM.
  Existing Instance inject_perm_all.
  Context `{memory_model_prf: Mem.MemoryModel}.

(** * Assertions about memory *)

(** An assertion is composed of:
- a predicate over memory states (of type [mem -> Prop])
- a set of (block, offset) memory locations that represents the memory footprint of the assertion
- a proof that the predicate is invariant by changes of memory outside of the footprint
- a proof that the footprint contains only valid memory blocks.

This presentation (where the footprint is part of the assertion) makes
it possible to define separating conjunction without explicitly
defining a separation algebra over CompCert memory states (i.e. the
notion of splitting a memory state into two disjoint halves).  *)

Record massert : Type := {
  m_pred : mem -> Prop;
  m_footprint: block -> Z -> Prop;
  m_invar_weak: bool;
  m_invar_stack: bool;
  m_invar: forall m m', m_pred m -> (if m_invar_weak then Mem.strong_unchanged_on else Mem.unchanged_on) m_footprint m m' ->
                   (m_invar_stack = true -> Mem.stack m' = Mem.stack m) ->
                   m_pred m';
  m_valid: forall m b ofs, m_pred m -> m_footprint b ofs -> Mem.valid_block m b
}.

Notation "m |= p" := (m_pred p m) (at level 74, no associativity) : sep_scope.

(** Implication and logical equivalence between memory predicates *)

Definition massert_imp (P Q: massert) : Prop :=
  (m_invar_weak Q = true -> m_invar_weak P = true) /\
  (m_invar_stack Q = true -> m_invar_stack P = true) /\
  (forall m, m_pred P m -> m_pred Q m) /\ (forall b ofs, m_footprint Q b ofs -> m_footprint P b ofs).
Definition massert_eqv (P Q: massert) : Prop :=
  massert_imp P Q /\ massert_imp Q P.

Remark massert_imp_refl: forall p, massert_imp p p.
Proof.
  unfold massert_imp; auto.
Qed.

Remark massert_imp_trans: forall p q r, massert_imp p q -> massert_imp q r -> massert_imp p r.
Proof.
  unfold massert_imp; clear; intros; firstorder auto.
Qed.

Remark massert_eqv_refl: forall p, massert_eqv p p.
Proof.
  unfold massert_eqv, massert_imp; clear; intros. tauto.
Qed.

Remark massert_eqv_sym: forall p q, massert_eqv p q -> massert_eqv q p.
Proof.
  unfold massert_eqv, massert_imp; clear; intros. tauto.
Qed.

Remark massert_eqv_trans: forall p q r, massert_eqv p q -> massert_eqv q r -> massert_eqv p r.
Proof.
  unfold massert_eqv, massert_imp; clear; intros. firstorder auto.
Qed.

(** Record [massert_eqv] and [massert_imp] as relations so that they can be used by rewriting tactics. *)
Global Add Relation massert massert_imp
  reflexivity proved by massert_imp_refl
  transitivity proved by massert_imp_trans
as massert_imp_prel.

Global Add Relation massert massert_eqv
  reflexivity proved by massert_eqv_refl
  symmetry proved by massert_eqv_sym
  transitivity proved by massert_eqv_trans
as massert_eqv_prel.

Global Add Morphism m_pred
  with signature massert_imp ==> eq ==> impl
  as m_pred_morph_1.
Proof.
  intros P Q [? [A [B C]]]. auto.
Qed.

Global Add Morphism m_pred
  with signature massert_eqv ==> eq ==> iff
  as m_pred_morph_2.
Proof.
  intros P Q [[? [A [B B']]] [? [C [D D']]]]. split; auto.
Qed.

Hint Resolve massert_imp_refl massert_eqv_refl.

(** * Separating conjunction *)

Definition disjoint_footprint (P Q: massert) : Prop :=
  forall b ofs, m_footprint P b ofs -> m_footprint Q b ofs -> False.

Program Definition sepconj (P Q: massert) : massert := {|
  m_pred := fun m => m_pred P m /\ m_pred Q m /\ disjoint_footprint P Q;
  m_footprint := fun b ofs => m_footprint P b ofs \/ m_footprint Q b ofs;
  m_invar_weak := m_invar_weak P || m_invar_weak Q;
  m_invar_stack := m_invar_stack P || m_invar_stack Q
|}.
Next Obligation.
  repeat split; auto.
  + apply (m_invar P) with m; auto.
    destruct (m_invar_weak P); simpl in *.
    - eapply Mem.strong_unchanged_on_implies; eauto. simpl; auto.
    - destruct (m_invar_weak Q).
      * eapply Mem.strong_unchanged_on_weak.
        eapply Mem.strong_unchanged_on_implies; eauto. simpl; auto.
      * eapply Mem.unchanged_on_implies; eauto. simpl; auto.
    - intro A; rewrite A in H1; apply H1. reflexivity.
  + apply (m_invar Q) with m; auto.
    destruct (m_invar_weak Q); try rewrite orb_true_r in *.
    - eapply Mem.strong_unchanged_on_implies; eauto. simpl; auto.
    - destruct (m_invar_weak P); simpl in *.
      * eapply Mem.strong_unchanged_on_weak.
        eapply Mem.strong_unchanged_on_implies; eauto. simpl; auto.
      * eapply Mem.unchanged_on_implies; eauto. simpl; auto.
    - intro A; rewrite A in H1; apply H1. rewrite orb_true_r. reflexivity.
Qed.
Next Obligation.
  destruct H0; [eapply (m_valid P) | eapply (m_valid Q)]; eauto.
Qed.

Global Add Morphism sepconj
  with signature massert_imp ==> massert_imp ==> massert_imp
  as sepconj_morph_1.
Proof.
  intros P1 P2 [I [A B]] Q1 Q2 [J [C D]].
  red; simpl; split; [ | split ] ; intros.
  - rewrite Bool.orb_true_iff in * |- * . tauto.
  - rewrite Bool.orb_true_iff in * |- * . tauto.
  - intuition auto. red; intros. apply (H6 b ofs); auto. 
Qed.

Global Add Morphism sepconj
  with signature massert_eqv ==> massert_eqv ==> massert_eqv
  as sepconj_morph_2.
Proof.
  intros. destruct H, H0. split; apply sepconj_morph_1; auto. 
Qed.

Infix "**" := sepconj (at level 60, right associativity) : sep_scope.

Local Open Scope sep_scope.

Lemma sep_imp:
  forall P P' Q Q' m, 
  m |= P ** Q -> massert_imp P P' -> massert_imp Q Q' -> m |= P' ** Q'.
Proof.
  intros. rewrite <- H0, <- H1; auto.
Qed.

Lemma sep_comm_1:
  forall P Q,  massert_imp (P ** Q) (Q ** P).
Proof.
  unfold massert_imp; simpl; split; [ | split] ; intros.
  - rewrite Bool.orb_true_iff in * |- * . tauto.
  - rewrite Bool.orb_true_iff in * |- * . tauto.
  - intuition auto. red; intros; eapply H2; eauto.
Qed.

Lemma sep_comm:
  forall P Q, massert_eqv (P ** Q) (Q ** P).
Proof.
  intros; split; apply sep_comm_1.
Qed.

Lemma sep_assoc_1:
  forall P Q R, massert_imp ((P ** Q) ** R) (P ** (Q ** R)).
Proof.
  intros. unfold massert_imp, sepconj, disjoint_footprint; simpl. clear. firstorder auto.
  repeat rewrite Bool.orb_true_iff in * |- * ; tauto.
  repeat rewrite Bool.orb_true_iff in * |- * ; tauto.
Qed.

Lemma sep_assoc_2:
  forall P Q R, massert_imp (P ** (Q ** R)) ((P ** Q) ** R).
Proof.
  intros. unfold massert_imp, sepconj, disjoint_footprint; simpl; clear; firstorder auto.
  repeat rewrite Bool.orb_true_iff in * |- * ; tauto.
  repeat rewrite Bool.orb_true_iff in * |- * ; tauto.
Qed.

Lemma sep_assoc:
  forall P Q R, massert_eqv ((P ** Q) ** R) (P ** (Q ** R)).
Proof.
  intros; split. apply sep_assoc_1. apply sep_assoc_2.
Qed.

Lemma sep_swap:
  forall P Q R, massert_eqv (P ** Q ** R) (Q ** P ** R).
Proof.
  intros. rewrite <- sep_assoc. rewrite (sep_comm P). rewrite sep_assoc. reflexivity.
Qed.

Definition sep_swap12 := sep_swap.

Lemma sep_swap23:
  forall P Q R S, massert_eqv (P ** Q ** R ** S) (P ** R ** Q ** S).
Proof.
  intros. rewrite (sep_swap Q). reflexivity.
Qed.

Lemma sep_swap34:
  forall P Q R S T, massert_eqv (P ** Q ** R ** S ** T) (P ** Q ** S ** R ** T).
Proof.
  intros. rewrite (sep_swap R). reflexivity.
Qed.

Lemma sep_swap45:
  forall P Q R S T U, massert_eqv (P ** Q ** R ** S ** T ** U) (P ** Q ** R ** T ** S ** U).
Proof.
  intros. rewrite (sep_swap S). reflexivity.
Qed.

Definition sep_swap2 := sep_swap.

Lemma sep_swap3:
  forall P Q R S, massert_eqv (P ** Q ** R ** S) (R ** Q ** P ** S).
Proof.
  intros. rewrite sep_swap. rewrite (sep_swap P). rewrite sep_swap. reflexivity.
Qed.

Lemma sep_swap4:
  forall P Q R S T, massert_eqv (P ** Q ** R ** S ** T) (S ** Q ** R ** P ** T).
Proof.
  intros. rewrite sep_swap. rewrite (sep_swap3 P). rewrite sep_swap. reflexivity.
Qed.

Lemma sep_swap5:
  forall P Q R S T U, massert_eqv (P ** Q ** R ** S ** T ** U) (T ** Q ** R ** S ** P ** U).
Proof.
  intros. rewrite sep_swap. rewrite (sep_swap4 P). rewrite sep_swap. reflexivity.
Qed.

Lemma sep_drop:
  forall P Q m, m |= P ** Q -> m |= Q.
Proof.
  simpl; intros. tauto.
Qed.

Lemma sep_drop2:
  forall P Q R m, m |= P ** Q ** R -> m |= P ** R.
Proof.
  intros. rewrite sep_swap in H. eapply sep_drop; eauto.
Qed. 

Lemma sep_proj1:
  forall Q P m, m |= P ** Q -> m |= P.
Proof.
  intros. destruct H; auto.
Qed.

Lemma sep_proj2:
  forall P Q m, m |= P ** Q -> m |= Q.
Proof sep_drop.

Definition sep_pick1 := sep_proj1.

Lemma sep_pick2: 
  forall P Q R m, m |= P ** Q ** R -> m |= Q.
Proof.
  intros. eapply sep_proj1; eapply sep_proj2; eauto.
Qed.

Lemma sep_pick3: 
  forall P Q R S m, m |= P ** Q ** R ** S -> m |= R.
Proof.
  intros. eapply sep_pick2; eapply sep_proj2; eauto.
Qed.

Lemma sep_pick4: 
  forall P Q R S T m, m |= P ** Q ** R ** S ** T -> m |= S.
Proof.
  intros. eapply sep_pick3; eapply sep_proj2; eauto.
Qed.

Lemma sep_pick5: 
  forall P Q R S T U m, m |= P ** Q ** R ** S ** T ** U -> m |= T.
Proof.
  intros. eapply sep_pick4; eapply sep_proj2; eauto.
Qed.

Lemma sep_preserved:
  forall m m' P Q,
  m |= P ** Q ->
  (m |= P -> m' |= P) ->
  (m |= Q -> m' |= Q) ->
  m' |= P ** Q.
Proof.
  simpl; intros. intuition auto.
Qed.

(** * Basic memory assertions. *)

(** Pure logical assertion *)

Program Definition pure (P: Prop) : massert := {|
  m_pred := fun m => P;
  m_footprint := fun b ofs => False;
  m_invar_weak := false;
  m_invar_stack := false;
|}.
Next Obligation.
  tauto.
Qed.

Lemma sep_pure:
  forall P Q m, m |= pure P ** Q <-> P /\ m |= Q.
Proof.
  simpl; intros. intuition auto. red; simpl; tauto.
Qed.

(** A range of bytes, with full permissions and unspecified contents. *)

Program Definition range (b: block) (lo hi: Z) : massert := {|
  m_pred := fun m =>
       0 <= lo /\ hi <= Ptrofs.modulus
       /\ (forall i k p, lo <= i < hi -> Mem.perm m b i k p);
  m_footprint := fun b' ofs' => b' = b /\ lo <= ofs' < hi
  ;
  m_invar_weak := false  ;
  m_invar_stack := false
|}.
Next Obligation.
  split; auto. split; auto. intros. eapply Mem.perm_unchanged_on; eauto. simpl; auto.
Qed.
Next Obligation.
  apply Mem.perm_valid_block with ofs Cur Freeable; auto.
Qed.

Lemma alloc_rule:
  forall m lo hi b m' P,
  Mem.alloc m lo hi = (m', b) ->
  0 <= lo -> hi <= Ptrofs.modulus ->
  m |= P ->
  m_invar_stack P = false ->
  m' |= range b lo hi ** P.
Proof.
  intros; simpl. split; [|split]. 
- split; auto. split; auto. intros.
  apply Mem.perm_implies with Freeable; auto with mem.
  eapply Mem.perm_alloc_2; eauto.
- apply (m_invar P) with m; auto.
  destruct (m_invar_weak P).
  + eapply Mem.alloc_strong_unchanged_on; eauto.
  + eapply Mem.alloc_unchanged_on; eauto.
  + congruence.
- red; simpl. intros. destruct H4; subst b0.
  eelim Mem.fresh_block_alloc; eauto. eapply (m_valid P); eauto.
Qed.

Lemma range_split:
  forall b lo hi P mid m,
  lo <= mid <= hi ->
  m |= range b lo hi ** P ->
  m |= range b lo mid ** range b mid hi ** P.
Proof.
  intros. rewrite <- sep_assoc. eapply sep_imp; eauto. 
  split; [ | split; [|split]]; simpl; intros; try assumption.
  - intuition auto; try omega.
    + apply H5; omega.
    + apply H5; omega.
    + red; simpl; intros; omega.
  - intuition omega.
Qed.

Lemma range_drop_left:
  forall b lo hi P mid m,
  lo <= mid <= hi ->
  m |= range b lo hi ** P ->
  m |= range b mid hi ** P.
Proof.
  intros. apply sep_drop with (range b lo mid). apply range_split; auto.
Qed.

Lemma range_drop_right:
  forall b lo hi P mid m,
  lo <= mid <= hi ->
  m |= range b lo hi ** P ->
  m |= range b lo mid ** P.
Proof.
  intros. apply sep_drop2 with (range b mid hi). apply range_split; auto.
Qed.

Lemma range_split_2:
  forall b lo hi P mid al m,
    lo <= align mid al <= hi ->
    al > 0 ->
    m |= range b lo hi ** P ->
    m |= range b lo mid ** range b (align mid al) hi ** P.
Proof.
  intros. rewrite <- sep_assoc. eapply sep_imp; eauto.
  assert (mid <= align mid al) by (apply align_le; auto).
  split; [ | split; [ | split ] ] ; simpl; intros; try assumption.
  - intuition auto; try (apply H7; omega); try omega.
    red; simpl; intros; omega.
  - intuition omega.
Qed.

Lemma range_preserved:
  forall m m' b lo hi,
  m |= range b lo hi ->
  (forall i k p, lo <= i < hi -> Mem.perm m b i k p -> Mem.perm m' b i k p) ->
  m' |= range b lo hi.
Proof.
  intros. destruct H as (A & B & C). simpl; intuition auto.
Qed.

(** A memory area that contains a value sastifying a given predicate *)

Program Definition contains (chunk: memory_chunk) (b: block) (ofs: Z) (spec: val -> Prop) : massert := {|
  m_pred := fun m =>
       0 <= ofs <= Ptrofs.max_unsigned
       (* /\ (Mem.valid_access m chunk b ofs Freeable) *)
       /\  Mem.range_perm m b ofs (ofs + size_chunk chunk) Cur Freeable
       /\ (align_chunk chunk | ofs)
       /\ exists v, Mem.load chunk m b ofs = Some v /\ spec v;
  m_footprint := fun b' ofs' => b' = b /\ ofs <= ofs' < ofs + size_chunk chunk
  ;
  m_invar_weak := false
  ;
  m_invar_stack := false
|}.
Next Obligation.
  rename H4 into v. split;[|split;[|split]]; auto.
- red; intros; eapply Mem.perm_unchanged_on; eauto. simpl; auto.
- exists v. split; auto. eapply Mem.load_unchanged_on; eauto. simpl; auto.
Qed.
Next Obligation.
  eauto with mem. 
Qed. 

Lemma contains_no_overflow:
  forall spec m chunk b ofs,
  m |= contains chunk b ofs spec ->
  0 <= ofs <= Ptrofs.max_unsigned.
Proof.
  intros. simpl in H. tauto.
Qed.

Lemma load_rule:
  forall spec m chunk b ofs,
  m |= contains chunk b ofs spec ->
  exists v, Mem.load chunk m b ofs = Some v /\ spec v.
Proof.
  intros. destruct H as (D & E & AL & v & F & G).
  exists v; auto.
Qed.

Lemma loadv_rule:
  forall spec m chunk b ofs,
  m |= contains chunk b ofs spec ->
  exists v, Mem.loadv chunk m (Vptr b (Ptrofs.repr ofs)) = Some v /\ spec v.
Proof.
  intros. exploit load_rule; eauto. intros (v & A & B). exists v; split; auto.
  simpl. rewrite Ptrofs.unsigned_repr; auto. eapply contains_no_overflow; eauto.
Qed.

Lemma store_rule:
  forall chunk m b ofs v (spec1 spec: val -> Prop) P,
    m |= contains chunk b ofs spec1 ** P ->
    stack_access (Mem.stack m) b ofs (ofs + size_chunk chunk) ->
  spec (Val.load_result chunk v) ->
  exists m',
  Mem.store chunk m b ofs v = Some m' /\ m' |= contains chunk b ofs spec ** P.
Proof.
  intros. destruct H as (A & B & C). destruct A as (D & E & v0 & F & G).
  assert (H: Mem.valid_access m chunk b ofs Freeable).
  {
    split;[|split]; eauto.
  }
  assert (H2: Mem.valid_access m chunk b ofs Writable).
  {
    eauto with mem.
  }
  destruct (Mem.valid_access_store _ _ _ _ v H2) as [m' STORE].
  exists m'; split; auto. simpl. intuition auto.
- eapply Mem.store_valid_access_1; eauto.
- exists (Val.load_result chunk v); split; auto. eapply Mem.load_store_same; eauto. 
- apply (m_invar P) with m; auto. 
  destruct (m_invar_weak P).
  + eapply Mem.store_strong_unchanged_on; eauto.
    intros; red; intros. apply (C b i); simpl; auto.
  + eapply Mem.store_unchanged_on; eauto.
    intros; red; intros. apply (C b i); simpl; auto.
  + intros.
    eapply Mem.store_stack_blocks; eauto.
Qed.

Lemma storev_rule:
  forall chunk m b ofs v (spec1 spec: val -> Prop) P,
    m |= contains chunk b ofs spec1 ** P ->
    stack_access (Mem.stack m) b ofs (ofs + size_chunk chunk) ->
  spec (Val.load_result chunk v) ->
  exists m',
  Mem.storev chunk m (Vptr b (Ptrofs.repr ofs)) v = Some m' /\ m' |= contains chunk b ofs spec ** P.
Proof.
  intros. exploit store_rule; eauto. intros (m' & A & B). exists m'; split; auto.
  simpl. rewrite Ptrofs.unsigned_repr; auto. eapply contains_no_overflow. eapply sep_pick1; eauto.
Qed.

Lemma range_contains:
  forall chunk b ofs P m,
  m |= range b ofs (ofs + size_chunk chunk) ** P ->
  (align_chunk chunk | ofs) ->
  stack_access (Mem.stack m) b ofs (ofs + size_chunk chunk) ->
  m |= contains chunk b ofs (fun v => True) ** P.
Proof.
  intros. destruct H as (A & B & C). destruct A as (D & E & F).
  split; [|split].
- assert (Mem.valid_access m chunk b ofs Freeable).
  { split; auto. red; auto. }
  split. generalize (size_chunk_pos chunk). unfold Ptrofs.max_unsigned. omega.
  split; [|split]; auto.
  apply H.
  destruct (Mem.valid_access_load m chunk b ofs) as [v LOAD].
  eauto with mem.
  exists v; auto.
- auto.
- auto.
Qed.

Lemma contains_imp:
  forall (spec1 spec2: val -> Prop) chunk b ofs,
  (forall v, spec1 v -> spec2 v) ->
  massert_imp (contains chunk b ofs spec1) (contains chunk b ofs spec2).
Proof.
  intros; split; [| split; [ | split ]] ; simpl; intros.
  - assumption.
  - assumption.
  - intuition auto. destruct H5 as (v & A & B). exists v; auto.
  - auto.
Qed.

Program Definition contains_ra (b: block) (ofs: Z) (ra: val) : massert := {|
  m_pred := fun m =>
       0 <= ofs <= Ptrofs.max_unsigned
       /\  Mem.range_perm m b ofs (ofs + size_chunk Mptr) Cur Freeable
       /\ (align_chunk Mptr | ofs)
       /\ Mem.loadbytesv Mptr m (Vptr b (Ptrofs.repr ofs)) = Some ra;
  m_footprint := fun b' ofs' => b' = b /\ ofs <= ofs' < ofs + size_chunk Mptr;
  m_invar_weak := false;
  m_invar_stack := false;
|}.
Next Obligation.
  destr_in H4. clear H1.
  repeat apply conj; auto.
- red; intros; eapply Mem.perm_unchanged_on; eauto. simpl; auto.
- erewrite Mem.loadbytes_unchanged_on; eauto.  simpl.  rewrite Ptrofs.unsigned_repr by omega. auto. 
Qed.
Next Obligation.
  eauto with mem. 
Qed. 

(** A memory area that contains a given value *)

Definition hasvalue (chunk: memory_chunk) (b: block) (ofs: Z) (v: val) : massert :=
  contains chunk b ofs (fun v' => v' = v).

Lemma store_rule':
  forall chunk m b ofs v (spec1: val -> Prop) P,
    m |= contains chunk b ofs spec1 ** P ->
    stack_access (Mem.stack m) b ofs (ofs + size_chunk chunk) ->
    exists m',
  Mem.store chunk m b ofs v = Some m' /\ m' |= hasvalue chunk b ofs (Val.load_result chunk v) ** P.
Proof.
  intros. eapply store_rule; eauto. 
Qed.

Lemma storev_rule':
  forall chunk m b ofs v (spec1: val -> Prop) P,
    m |= contains chunk b ofs spec1 ** P ->
    stack_access (Mem.stack m) b ofs (ofs + size_chunk chunk) ->
    exists m',
      Mem.storev chunk m (Vptr b (Ptrofs.repr ofs)) v = Some m' /\ m' |= hasvalue chunk b ofs (Val.load_result chunk v) ** P.
Proof.
  intros. eapply storev_rule; eauto.
Qed.

(** Non-separating conjunction *)

Program Definition mconj (P Q: massert) : massert := {|
  m_pred := fun m => m_pred P m /\ m_pred Q m;
  m_footprint := fun b ofs => m_footprint P b ofs \/ m_footprint Q b ofs
  ;
  m_invar_weak := m_invar_weak P || m_invar_weak Q;
  m_invar_stack := m_invar_stack P || m_invar_stack Q;
|}.
Next Obligation.
  repeat split; auto.
  + apply (m_invar P) with m; auto.
    destruct (m_invar_weak P); simpl in *.
    - eapply Mem.strong_unchanged_on_implies; eauto. simpl; auto.
    - destruct (m_invar_weak Q).
      * apply Mem.strong_unchanged_on_weak.
        eapply Mem.strong_unchanged_on_implies; eauto. simpl; auto.
      * eapply Mem.unchanged_on_implies; eauto. simpl; auto.
    - intros; apply H1. rewrite H3; reflexivity.        
  + apply (m_invar Q) with m; auto.
    destruct (m_invar_weak Q); try rewrite orb_true_r in *.
    - eapply Mem.strong_unchanged_on_implies; eauto. simpl; auto.
    - destruct (m_invar_weak P); simpl in *.
      * apply Mem.strong_unchanged_on_weak.
        eapply Mem.strong_unchanged_on_implies; eauto. simpl; auto.
      * eapply Mem.unchanged_on_implies; eauto. simpl; auto.
    - intros; apply H1. rewrite H3, orb_true_r; reflexivity.
Qed.
Next Obligation.
  destruct H0; [eapply (m_valid P) | eapply (m_valid Q)]; eauto.
Qed.

Lemma mconj_intro:
  forall P Q R m,
  m |= P ** R -> m |= Q ** R -> m |= mconj P Q ** R.
Proof.
  intros. destruct H as (A & B & C). destruct H0 as (D & E & F).
  split; [|split].
- simpl; auto.
- auto.
- red; simpl; intros. destruct H; [eelim C | eelim F]; eauto.
Qed.

Lemma mconj_proj1:
  forall P Q R m, m |= mconj P Q ** R -> m |= P ** R.
Proof.
  intros. destruct H as (A & B & C); simpl in A.
  simpl. intuition auto.
  red; intros; eapply C; eauto; simpl; auto.
Qed.

Lemma mconj_proj2:
  forall P Q R m, m |= mconj P Q ** R -> m |= Q ** R.
Proof.
  intros. destruct H as (A & B & C); simpl in A.
  simpl. intuition auto.
  red; intros; eapply C; eauto; simpl; auto.
Qed.

Lemma frame_mconj:
  forall P P' Q R m m',
  m |= mconj P Q ** R ->
  m' |= P' ** R ->
  m' |= Q ->
  m' |= mconj P' Q ** R.
Proof.
  intros. destruct H as (A & B & C); simpl in A.
  destruct H0 as (D & E & F).
  simpl. intuition auto. 
  red; simpl; intros. destruct H2. eapply F; eauto. eapply C; simpl; eauto.
Qed.

Global Add Morphism mconj
  with signature massert_imp ==> massert_imp ==> massert_imp
  as mconj_morph_1.
Proof.
  intros P1 P2 [I [A B]] Q1 Q2 [J [C D]].
  red; simpl; intuition auto.
  repeat rewrite Bool.orb_true_iff in * |- * . tauto.
  repeat rewrite Bool.orb_true_iff in * |- * . tauto.
Qed.

Global Add Morphism mconj
  with signature massert_eqv ==> massert_eqv ==> massert_eqv
  as mconj_morph_2.
Proof.
  intros. destruct H, H0. split; apply mconj_morph_1; auto. 
Qed.

(** The image of a memory injection *)

Program Definition minjection (j: meminj) g (m0: mem) : massert := {|
  m_pred := fun m => Mem.inject j g m0 m;
  m_footprint := fun b ofs => exists b0 delta, j b0 = Some(b, delta) /\ Mem.perm m0 b0 (ofs - delta) Max Nonempty;
  m_invar_weak := true;
  m_invar_stack := true;
|}.
Next Obligation.
  eapply Mem.inject_strong_unchanged_on; eauto.
Qed.
Next Obligation.
  eapply Mem.valid_block_inject_2; eauto.
Qed.

Lemma loadv_parallel_rule:
  forall j g m1 m2 chunk addr1 v1 addr2,
  m2 |= minjection j g m1 ->
  Mem.loadv chunk m1 addr1 = Some v1 ->
  Val.inject j addr1 addr2 ->
  exists v2, Mem.loadv chunk m2 addr2 = Some v2 /\ Val.inject j v1 v2.
Proof.
  intros. simpl in H. eapply Mem.loadv_inject; eauto.
Qed.

Lemma storev_parallel_rule:
  forall j g m1 m2 P chunk addr1 v1 m1' addr2 v2,
  m2 |= minjection j g m1 ** P ->
  Mem.storev chunk m1 addr1 v1 = Some m1' ->
  Val.inject j addr1 addr2 ->
  Val.inject j v1 v2 ->
  exists m2', Mem.storev chunk m2 addr2 v2 = Some m2' /\ m2' |= minjection j g m1' ** P.
Proof.
  intros. destruct H as (A & B & C). simpl in A.
  exploit Mem.storev_mapped_inject; eauto. intros (m2' & STORE & INJ).
  inv H1; simpl in STORE; try discriminate.
  assert (VALID: Mem.valid_access m1 chunk b1 (Ptrofs.unsigned ofs1) Writable)
    by eauto with mem.
  assert (EQ: Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta)) = Ptrofs.unsigned ofs1 + delta).
  { eapply Mem.address_inject'; eauto with mem. }
  exists m2'; split; auto.
  split; [|split].
- exact INJ.
- apply (m_invar P) with m2; auto.
  cut (Mem.strong_unchanged_on (m_footprint P) m2 m2').
  {
    destruct (m_invar_weak P); auto using Mem.strong_unchanged_on_weak.
  }
  eapply Mem.store_strong_unchanged_on; eauto.
  intros; red; intros. eelim C; eauto. simpl.
  exists b1, delta; split; auto. destruct VALID as [V1 V2]. 
  apply Mem.perm_cur_max. apply Mem.perm_implies with Writable; auto with mem. 
  apply V1. omega.
  intros; eapply Mem.store_stack_blocks; eauto.
- red; simpl; intros. destruct H1 as (b0 & delta0 & U & V).
  eelim C; eauto. simpl. exists b0, delta0; eauto with mem.
Qed.

Lemma alloc_parallel_rule:
  forall m1 sz1 m1' b1 m2 sz2 m2' b2 P j g lo hi delta,
    m2 |= minjection j g m1 ** P ->
    Mem.alloc m1 0 sz1 = (m1', b1) ->
    Mem.alloc m2 0 sz2 = (m2', b2) ->
    (8 | delta) ->
    lo = delta ->
    hi = delta + Zmax 0 sz1 ->
    0 <= sz2 <= Ptrofs.max_unsigned ->
    0 <= delta -> hi <= sz2 ->
    exists j',
      m2' |= range b2 0 lo ** range b2 hi sz2 ** minjection j' g m1' ** P
      /\ inject_incr j j'
      /\ j' b1 = Some(b2, delta)
      /\ (forall b, b <> b1 -> j' b = j b).
Proof.
  intros until delta; intros SEP ALLOC1 ALLOC2 ALIGN LO HI RANGE1 RANGE2 RANGE3.
  assert (RANGE4: lo <= hi) by xomega.
  assert (FRESH1: ~Mem.valid_block m1 b1) by (eapply Mem.fresh_block_alloc; eauto).
  assert (FRESH2: ~Mem.valid_block m2 b2) by (eapply Mem.fresh_block_alloc; eauto).
  destruct SEP as (INJ & SP & DISJ). simpl in INJ.
  exploit Mem.alloc_left_mapped_inject.
  - eapply Mem.alloc_right_inject; eauto. 
  - eexact ALLOC1.
  - instantiate (1 := b2). eauto with mem.
  - instantiate (1 := delta). xomega.
  - intros. assert (0 <= ofs < sz2) by (eapply Mem.perm_alloc_3; eauto). omega.
  - intros. apply Mem.perm_implies with Freeable; auto with mem. 
    eapply Mem.perm_alloc_2; eauto. xomega.
  - red; intros. apply Zdivides_trans with 8; auto. 
    exists (8 / align_chunk chunk). destruct chunk; reflexivity.
  - intros. elim FRESH2. eapply Mem.valid_block_inject_2; eauto.
  - intros fi IFS o k pp PERM IPC. erewrite Mem.alloc_stack_blocks in IFS. 2: eauto.
    exfalso; apply FRESH2. apply Mem.in_frames_valid. eapply in_stack'_in_stack; eauto.
  - intros (j' & INJ' & J1 & J2 & J3).
    exists j'; split; auto.
    rewrite <- ! sep_assoc.
    split; [|split].
    + simpl. intuition auto; try (unfold Ptrofs.max_unsigned in *; omega).
      * apply Mem.perm_implies with Freeable; auto with mem.
        eapply Mem.perm_alloc_2; eauto. omega. 
      (* * red; right; red; erewrite Mem.alloc_get_frame_info_fresh; eauto. *)
      * apply Mem.perm_implies with Freeable; auto with mem.
        eapply Mem.perm_alloc_2; eauto. omega. 
      (* * red; right; red; erewrite Mem.alloc_get_frame_info_fresh; eauto. *)
      * red; simpl; intros. destruct H1, H2. omega.
      * red; simpl; intros.
        assert (b = b2) by tauto. subst b.
        assert (0 <= ofs < lo \/ hi <= ofs < sz2) by tauto. clear H1.
        destruct H2 as (b0 & delta0 & D & E).
        eapply Mem.perm_alloc_inv in E; eauto. 
        destruct (eq_block b0 b1).
        subst b0. rewrite J2 in D. inversion D; clear D; subst delta0. xomega.
        rewrite J3 in D by auto. elim FRESH2. eapply Mem.valid_block_inject_2; eauto. 
    + apply (m_invar P) with m2; auto.
      cut (Mem.strong_unchanged_on (m_footprint P) m2 m2').
      {
        destruct (m_invar_weak P); auto using Mem.strong_unchanged_on_weak.
      }
      eapply Mem.alloc_strong_unchanged_on; eauto.
      intros; eapply Mem.alloc_stack_blocks; eauto.
    + red; simpl; intros.
      assert (VALID: Mem.valid_block m2 b) by (eapply (m_valid P); eauto).
      destruct H as [A | (b0 & delta0 & A & B)].
      * assert (b = b2) by tauto. subst b. contradiction.
      * eelim DISJ; eauto. simpl. 
        eapply Mem.perm_alloc_inv in B; eauto. 
        destruct (eq_block b0 b1).
        subst b0. rewrite J2 in A. inversion A; clear A; subst b delta0. contradiction.
        rewrite J3 in A by auto. exists b0, delta0; auto.
Qed.

Lemma free_parallel_rule:
  forall j g m1 b1 sz1 m1' m2 b2 sz2 lo hi delta P,
  m2 |= range b2 0 lo ** range b2 hi sz2 ** minjection j g m1 ** P ->
  Mem.free m1 b1 0 sz1 = Some m1' ->
  inject_perm_condition Freeable ->
  j b1 = Some (b2, delta) ->
  lo = delta -> hi = delta + Zmax 0 sz1 ->
  exists m2',
     Mem.free m2 b2 0 sz2 = Some m2'
  /\ m2' |= minjection j g m1' ** P.
Proof.
  intros. rewrite <- ! sep_assoc in H. 
  destruct H as (A & B & C).
  destruct A as (D & E & F).
  destruct D as (J & K & L).
  destruct J as (_ & _ & J). destruct K as (_ & _ & K).
  simpl in E.
  assert (PERM: Mem.range_perm m2 b2 0 sz2 Cur Freeable).
  { red; intros. 
    destruct (zlt ofs lo). apply J; omega.
    destruct (zle hi ofs). apply K; omega.
    replace ofs with ((ofs - delta) + delta) by omega.
    eapply Mem.perm_inject; eauto. 
    eapply Mem.free_range_perm; eauto. xomega. 
  }
  destruct (Mem.range_perm_free _ _ _ _ PERM) as [m2' FREE].
  exists m2'; split; auto. split; [|split].
- simpl. eapply Mem.free_right_inject; eauto. eapply Mem.free_left_inject; eauto.
  intros. apply (F b2 (ofs + delta0)).
+ simpl.
  destruct (zlt (ofs + delta0) lo). intuition auto.
  destruct (zle hi (ofs + delta0)). intuition auto. 
  destruct (eq_block b0 b1).
* subst b0. rewrite H2 in H; inversion H; clear H; subst delta0.
  eelim (Mem.perm_free_2 m1); eauto. xomega.
* exploit Mem.mi_no_overlap; eauto. 
  apply Mem.perm_max with k. apply Mem.perm_implies with p; auto with mem. 
  eapply Mem.perm_free_3; eauto.
  apply Mem.perm_cur_max. apply Mem.perm_implies with Freeable; auto with mem. 
  eapply (Mem.free_range_perm m1); eauto. 
  instantiate (1 := ofs + delta0 - delta). xomega. 
  intros [X|X]. congruence. omega. 
+ simpl. exists b0, delta0; split; auto. 
  replace (ofs + delta0 - delta0) with ofs by omega.
  apply Mem.perm_max with k. apply Mem.perm_implies with p; auto with mem. 
  eapply Mem.perm_free_3; eauto.
- apply (m_invar P) with m2; auto.
  cut (Mem.strong_unchanged_on (m_footprint P) m2 m2').
  {
    destruct (m_invar_weak P); auto using Mem.strong_unchanged_on_weak.
  }
  eapply Mem.free_strong_unchanged_on; eauto.
  intros; red; intros. eelim C; eauto. simpl. 
  destruct (zlt i lo). intuition auto.
  destruct (zle hi i). intuition auto.
  right; exists b1, delta; split; auto. 
  apply Mem.perm_cur_max. apply Mem.perm_implies with Freeable; auto with mem.
  eapply Mem.free_range_perm; eauto. xomega.
  intros; eapply Mem.free_stack_blocks; eauto.
- red; simpl; intros. eelim C; eauto. 
  simpl. right. destruct H as (b0 & delta0 & U & V). 
  exists b0, delta0; split; auto. 
  eapply Mem.perm_free_3; eauto. 
Qed.

(** Preservation of a global environment by a memory injection *)

Inductive globalenv_preserved {F V: Type} (ge: Genv.t F V) (j: meminj) (bound: block) : Prop :=
  | globalenv_preserved_intro
      (DOMAIN: forall b, Plt b bound -> j b = Some(b, 0))
      (IMAGE: forall b1 b2 delta, j b1 = Some(b2, delta) -> Plt b2 bound -> b1 = b2)
      (SYMBOLS: forall id b, Genv.find_symbol ge id = Some b -> Plt b bound)
      (FUNCTIONS: forall b fd, Genv.find_funct_ptr ge b = Some fd -> Plt b bound)
      (VARINFOS: forall b gv, Genv.find_var_info ge b = Some gv -> Plt b bound).

Program Definition globalenv_inject {F V: Type} (ge: Genv.t F V) (j: meminj) : massert := {|
  m_pred := fun m => exists bound, Ple bound (Mem.nextblock m) /\ globalenv_preserved ge j bound;
  m_footprint := fun b ofs => False;
  m_invar_weak := false;
  m_invar_stack := false;
|}.
Next Obligation.
  rename H into bound. exists bound; split; auto. eapply Ple_trans; eauto. eapply Mem.unchanged_on_nextblock; eauto.
Qed.
Next Obligation.
  tauto.
Qed.

Lemma globalenv_inject_preserves_globals:
  forall (F V: Type) (ge: Genv.t F V) j m,
  m |= globalenv_inject ge j ->
  meminj_preserves_globals ge j.
Proof.
  intros. destruct H as (bound & A & B). destruct B.
  split; [|split]; intros.
- eauto.
- eauto.
- symmetry; eauto.
Qed.

Lemma globalenv_inject_incr:
  forall j m0 (F V: Type) (ge: Genv.t F V) m j' P,
  inject_incr j j' ->
  inject_separated j j' m0 m ->
  m |= globalenv_inject ge j ** P ->
  m |= globalenv_inject ge j' ** P.
Proof.
  intros. destruct H1 as (A & B & C). destruct A as (bound & D & E).
  split; [|split]; auto.
  exists bound; split; auto. 
  inv E; constructor; intros.
- eauto.
- destruct (j b1) as [[b0 delta0]|] eqn:JB1.
+ erewrite H in H1 by eauto. inv H1. eauto.
+ exploit H0; eauto. intros (X & Y). elim Y. apply Plt_le_trans with bound; auto.
- eauto.
- eauto.
- eauto.
Qed.

Context `{external_calls_ops: !ExternalCallsOps mem}.
Context `{symbols_inject'_instance: !SymbolsInject}.
Context `{external_calls_props: !ExternalCallsProps mem}.
Context `{enable_builtins_instance: !EnableBuiltins mem}.
Context `{external_calls_prf: !ExternalCalls mem}.

Lemma external_call_parallel_rule:
  forall (F V: Type) ef (ge: Genv.t F V) vargs1 m1 t vres1 m1' m2 j g P vargs2,
  m_invar_weak P = false ->
  external_call ef ge vargs1 m1 t vres1 m1' ->
  m2 |= minjection j g m1 ** globalenv_inject ge j ** P ->
  Val.inject_list j vargs1 vargs2 ->
  exists j' vres2 m2',
     external_call ef ge vargs2 m2 t vres2 m2'
  /\ Val.inject j' vres1 vres2
  /\ m2' |= minjection j' g m1' ** globalenv_inject ge j' ** P
  /\ inject_incr j j'
  /\ inject_separated j j' m1 m2.
Proof.
  intros until vargs2; intros INV_STRONG CALL SEP ARGS.
  destruct SEP as (A & B & C). simpl in A.
  exploit external_call_mem_inject; eauto.
  eapply globalenv_inject_preserves_globals. eapply sep_pick1; eauto.
  intros (j' & vres2 & m2' & CALL' & RES & INJ' & UNCH1 & UNCH2 & INCR & ISEP).
  assert (MAXPERMS: forall b ofs p,
            Mem.valid_block m1 b -> Mem.perm m1' b ofs Max p -> Mem.perm m1 b ofs Max p).
  { intros. eapply external_call_max_perm; eauto. }
  exists j', vres2, m2'; intuition auto.
  split; [|split].
- exact INJ'.
- apply m_invar with (m0 := m2).
+ apply globalenv_inject_incr with j m1; auto.
+ simpl. rewrite INV_STRONG.
  eapply Mem.unchanged_on_implies; eauto.
  intros; red; intros; red; intros.
  eelim C; simpl; eauto.
+ symmetry; eapply external_call_stack_blocks; eauto.
- red; intros. destruct H as (b0 & delta & J' & E).
  destruct (j b0) as [[b' delta'] | ] eqn:J.
+ erewrite INCR in J' by eauto. inv J'. 
  eelim C; eauto. simpl. exists b0, delta; split; auto. apply MAXPERMS; auto. 
  eapply Mem.valid_block_inject_1; eauto.
+ exploit ISEP; eauto. intros (X & Y). elim Y. eapply m_valid; eauto.
Qed.  

Lemma alloc_parallel_rule_2:
  forall (F V: Type) (ge: Genv.t F V) m1 sz1 m1' b1 m2 sz2 m2' b2 P j g lo hi delta,
  m2 |= minjection j g m1 ** globalenv_inject ge j ** P ->
  Mem.alloc m1 0 sz1 = (m1', b1) ->
  Mem.alloc m2 0 sz2 = (m2', b2) ->
  (8 | delta) ->
  lo = delta ->
  hi = delta + Zmax 0 sz1 ->
  0 <= sz2 <= Ptrofs.max_unsigned ->
  0 <= delta -> hi <= sz2 ->
  exists j',
     m2' |= range b2 0 lo ** range b2 hi sz2 ** minjection j' g m1' ** globalenv_inject ge j' ** P
  /\ inject_incr j j'
  /\ j' b1 = Some(b2, delta)
  /\ inject_separated j j' m1 m2 .
Proof.
  intros. 
  set (j1 := fun b => if eq_block b b1 then Some(b2, delta) else j b).
  assert (X: inject_incr j j1).
  { unfold j1; red; intros. destruct (eq_block b b1); auto. 
    subst b. eelim Mem.fresh_block_alloc. eexact H0. 
    eapply Mem.valid_block_inject_1. eauto. apply sep_proj1 in H. apply H. }
  assert (Y: inject_separated j j1 m1 m2).
  { unfold j1; red; intros. destruct (eq_block b0 b1). 
  - inversion H9; clear H9; subst b3 delta0 b0. split; eapply Mem.fresh_block_alloc; eauto.
  - congruence. }
  rewrite sep_swap in H. eapply globalenv_inject_incr with (j' := j1) in H; eauto. rewrite sep_swap in H.
  clear X Y.
  exploit alloc_parallel_rule; eauto. 
  intros (j' & A & B & C & D).
  exists j'; split; auto.
  rewrite sep_swap4 in A. rewrite sep_swap4. apply globalenv_inject_incr with j1 m1; auto.
- red; unfold j1; intros. destruct (eq_block b b1). congruence. rewrite D; auto.
- red; unfold j1; intros. destruct (eq_block b0 b1). congruence. rewrite D in H9 by auto. congruence.
- split; auto.
  split; auto.
  red. intros b0 b3 delta0 H8 H9.
  destruct (peq b0 b1).
  + subst.
    rewrite C in H9. inversion H9. subst delta0 b3.
    eauto with mem.
  + rewrite D in H9; congruence.
Qed.

Lemma alloc_parallel_rule_2_flat:
  forall (F V: Type) (ge: Genv.t F V) m1 sz1 m1' b1 m2 sz2 m2' b2 P j lo hi delta,
  m2 |= minjection j (flat_frameinj (length (Mem.stack m1))) m1 ** globalenv_inject ge j ** P ->
  Mem.alloc m1 0 sz1 = (m1', b1) ->
  Mem.alloc m2 0 sz2 = (m2', b2) ->
  (8 | delta) ->
  lo = delta ->
  hi = delta + Zmax 0 sz1 ->
  0 <= sz2 <= Ptrofs.max_unsigned ->
  0 <= delta -> hi <= sz2 ->
  exists j',
     m2' |= range b2 0 lo ** range b2 hi sz2 ** minjection j' (flat_frameinj (length (Mem.stack m1'))) m1' ** globalenv_inject ge j' ** P
  /\ inject_incr j j'
  /\ j' b1 = Some(b2, delta)
  /\ inject_separated j j' m1 m2 .
Proof.
  intros.
  edestruct alloc_parallel_rule_2 as (j' & SEP & INCR & JNEW & JSEP); eauto.
  exists j'; split; eauto.
  rewrite sep_swap3 in SEP |- *.
  eapply sep_imp; eauto.
  red; simpl; intros.
  split; auto.
  split; auto.
  split; auto.
  repeat rewrite_stack_blocks. auto.
Qed.

Lemma record_stack_block_parallel_rule:
  forall m1 m1' m2 j P fi b b' delta n,
    j b = Some (b', delta) ->
    m_invar_stack P = false ->
    m2 |= minjection j (flat_frameinj (length (Mem.stack m1))) m1 ** P ->
    forall (NIN: ~ in_stack (Mem.stack m2) b') fa finone,
      frame_adt_blocks fa = (b,finone)::nil ->
      frame_adt_size fa = Z.max 0 n ->
      Mem.record_stack_blocks m1 fa  = Some m1' ->
      (forall o, 0 <= o < frame_size finone -> Mem.perm m1 b o Cur Writable) ->
      (forall (ofs : Z) (k : perm_kind) (p : permission),
       Mem.perm m1 b ofs k p ->
       frame_public fi (ofs + delta)) ->
    (forall (ofs : Z) (k : perm_kind) (p : permission),
        Mem.perm m2 b' ofs k p -> 0 <= ofs < frame_size fi) ->
    (forall bb delta0, j bb = Some (b', delta0) -> bb = b) ->
    forall fa',
      fa' = {| frame_adt_blocks := (b',fi)::nil;
               frame_adt_size := Z.max 0 n;
               frame_adt_blocks_norepet := norepet_1 _;
               frame_adt_size_pos:= Z.le_max_l _ _

            |} ->
      (top_tframe_tc (Mem.stack m2)) ->
      stack_equiv (Mem.stack m1) (Mem.stack m2) ->
    exists m2',
      Mem.record_stack_blocks m2 fa' = Some m2' /\
      m2' |= minjection j (flat_frameinj (length (Mem.stack m1'))) m1' ** P.
Proof.
  intros m1 m1' m2 j P fi b b' delta n FB INVAR MINJ NIN fa finone (* PUB *) fablocks fasize
         RSB1 PERM0 PERM1 PERM2 UNIQ fa' fa'eq TTNP SEQ.
  destruct MINJ as (MINJ & PM & DISJ).
  Check Mem.record_push_inject_flat.
  edestruct (Mem.record_push_inject_flat _ _ _ MINJ fa fa') as (m2' & RSB2 & MINJ'); simpl in *.
  - setoid_rewrite Forall_forall.  intros. destruct x.  simpl in *.
    rewrite fablocks in H. simpl in H. destruct H; try easy. inv H.
    simpl in *. rewrite FB in H0; inv H0.
    eexists; split; eauto.
    constructor.
    + intros.
      erewrite PERM1; eauto.
      red. destr. 
    + intros. eapply PERM2. eapply Mem.perm_inject. eauto. eauto. eauto.
      apply inject_perm_condition_writable. constructor.
  - intros. unfold in_frame in H0. subst. simpl in *. destruct H0; try easy. subst. congruence.
  - red; unfold in_frame; simpl. subst; simpl. intros ? [B|[]]. subst. simpl in *; eapply Mem.valid_block_inject_2; eauto. 
  - subst; simpl in *; intros ? ? ? ? ? [B|[]]. inv B. eauto.
  - intros. subst. simpl in *. unfold in_frame, get_frame_blocks. setoid_rewrite fablocks. simpl. 
    split; intros [B|[]]; left; subst. congruence. eapply UNIQ in H. auto.
  - subst; simpl in *; congruence. 
  - eauto.
  - eauto.
  - apply stack_equiv_tail in SEQ. apply stack_equiv_fsize in SEQ. omega.
  - eexists; split; eauto.
    split; [|split].
    + simpl in *. auto.  
    + eapply m_invar. eauto.
      * 
        destruct (m_invar_weak P); eauto using Mem.strong_unchanged_on_weak.
        eapply Mem.record_stack_block_unchanged_on; eauto.
        eapply Mem.strong_unchanged_on_weak, Mem.record_stack_block_unchanged_on; eauto.
      * congruence.
    + red; intros. eapply DISJ; eauto.
      simpl in *. decompose [ex and] H.
      repeat eexists; eauto.
      eapply Mem.record_stack_block_perm in H3. 2: eauto. auto.
Qed.

Lemma record_stack_block_parallel_rule_2:
  forall m1 m1' m2 j P fi b b' delta n,
    j b = Some (b', delta) ->
    m_invar_stack P = false ->
    m2 |= minjection j (flat_frameinj (length (Mem.stack m1))) m1 ** P ->
    forall (NIN: ~ in_stack (Mem.stack m2) b') sz,
      Mem.record_stack_blocks m1 (make_singleton_frame_adt b sz n) = Some m1' ->
      (forall o, 0 <= o < sz -> Mem.perm m1 b o Cur Writable) ->
      (forall (ofs : Z) (k : perm_kind) (p : permission),
       Mem.perm m1 b ofs k p ->
       frame_public fi (ofs + delta)) ->
    (forall (ofs : Z) (k : perm_kind) (p : permission),
        Mem.perm m2 b' ofs k p -> 0 <= ofs < frame_size fi) ->
    (forall bb delta0, j bb = Some (b', delta0) -> bb = b) ->
    (top_tframe_tc (Mem.stack m2 )) ->
    stack_equiv (Mem.stack m1) (Mem.stack m2) ->
    exists m2',
      Mem.record_stack_blocks m2 (make_singleton_frame_adt' b' fi n) = Some m2' /\
      m2' |= minjection j (flat_frameinj (length (Mem.stack m1'))) m1' ** P.
Proof.
  intros m1 m1' m2 j P fi b b' delta n H H0 H1 NIN sz H2 H3 H4 H5 H6 TTNP SEQ.
  edestruct record_stack_block_parallel_rule as (m2' & RSB & INJ); eauto.
  reflexivity. reflexivity.
  simpl. intros. rewrite Zmax_spec in H7. destr_in H7. omega. eauto.  
Qed.

Lemma push_rule:
  forall j g m1 m2 P,
    m2 |= minjection j g m1 ** P ->
    m_invar_stack P = false ->
    Mem.push_new_stage m2 |= minjection j (1%nat :: g) (Mem.push_new_stage m1) ** P.
Proof.
  intros j g m1 m2 P (INJ & RP & DISJ).
  split;[|split].
  apply Mem.push_new_stage_inject.
  apply INJ.
  eapply m_invar. eauto.
  generalize (Mem.push_new_stage_unchanged_on (m_footprint P) m2).
  destruct (m_invar_weak P); eauto using Mem.strong_unchanged_on_weak.
  congruence.
  red; simpl; intros.
  destruct H0 as (b0 & delta & JB & PERM).
  rewrite Mem.push_new_stage_perm in PERM.
  eapply DISJ; eauto.
  exists b0, delta; split; eauto.
Qed.

Lemma push_rule_2:
  forall j g m1 m2 P Q,
    m2 |= mconj (minjection j g m1) Q ** P ->
    m_invar_stack P = false ->
    m_invar_stack Q = false ->
    Mem.push_new_stage m2 |= mconj (minjection j (1%nat:: g) (Mem.push_new_stage m1)) Q ** P.
Proof.
  intros j g m1 m2 P Q SEP FALSE1 FALSE2.
  eapply frame_mconj. apply SEP.
  apply mconj_proj1 in SEP.
  apply push_rule in SEP.
  eapply sep_imp. apply SEP.
  red; split; auto. split; auto. auto.
  eapply m_invar. apply mconj_proj2 in SEP. apply SEP.
  destr.
  eapply Mem.push_new_stage_unchanged_on.
  eapply Mem.strong_unchanged_on_weak, Mem.push_new_stage_unchanged_on.
  simpl. congruence.
Qed.

Lemma unrecord_stack_block_parallel_rule:
  forall m1 m1' m2 j g P,
    m_invar_stack P = false ->
    m2 |= minjection j (1%nat::g) m1 ** P ->
    Mem.unrecord_stack_block m1 = Some m1' ->
    exists m2', Mem.unrecord_stack_block m2 = Some m2' /\
           m2' |= minjection j g m1' ** P.
Proof.
  intros m1 m1' m2 j g P (* fi b b' delta FB *) INVAR MINJ RSB.
  exploit Mem.unrecord_stack_block_inject_parallel; eauto. apply MINJ.
  intros (m2' & UNRECORD & INJ).
  eexists; split; eauto.
  destruct MINJ as (MINJ & PM & DISJ).
  split; [|split].
  - simpl in *. auto.
  - eapply m_invar. eauto.
    exploit Mem.unrecord_stack_block_unchanged_on. eauto.
    destruct (m_invar_weak P); eauto using Mem.strong_unchanged_on_weak.
    congruence.
  - red; intros. eapply DISJ. 2: eauto. simpl in H |- *.
    decompose [ex and] H.
    repeat eexists;  eauto.
    eapply Mem.unrecord_stack_block_perm; eauto.
Qed.

Lemma pop_frame_parallel_rule:
  forall (j : meminj) g (m1 : mem) (b1 : block) (sz1 sz2 : Z) (m1' m1'' m2 : mem) (b2 : block) (lo hi delta n : Z) (P : massert),
    m_invar_stack P = false ->
    m2 |= range b2 0 lo ** range b2 hi sz2 ** minjection j (1%nat::g) m1 ** P ->
    Mem.free m1 b1 0 sz1 = Some m1' ->
    Mem.unrecord_stack_block m1' = Some m1'' ->
    j b1 = Some (b2, delta) ->
    lo = delta -> hi = delta + Z.max 0 sz1 ->
    exists m2_ m2',
      Mem.free m2 b2 0 sz2 = Some m2_ /\
      Mem.unrecord_stack_block m2_ = Some m2'
      /\ m2' |= minjection j g m1'' ** P.
Proof.
  intros j g m1 b1 sz1 sz2 m1' m1'' m2 b2 lo hi delta n P INVAR SEP FREE UNRECORD JB LOEQ HIEQ.
  exploit free_parallel_rule; eauto.
  simpl. auto.
  intros (m2' & FREE' & SEP').
  exploit unrecord_stack_block_parallel_rule; eauto.
  repeat rewrite_stack_blocks. auto.
  intros (m2'0 & UNRECORD' & SEP'').
  eexists; eexists; eauto.
Qed.

End WITHMEM.

Notation "m |= p" := (m_pred p m) (at level 74, no associativity) : sep_scope.

Hint Resolve massert_imp_refl massert_eqv_refl.

Infix "**" := sepconj (at level 60, right associativity) : sep_scope.
