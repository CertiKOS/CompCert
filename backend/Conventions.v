(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Function calling conventions and other conventions regarding the use of
    machine registers and stack slots. *)

Require Import Coqlib.
Require Import AST.
Require Import Locations.
Require Export Conventions1.

(** The processor-dependent and EABI-dependent definitions are in
    [arch/abi/Conventions1.v].  This file adds various processor-independent
    definitions and lemmas. *)

Lemma loc_arguments_acceptable_2:
  forall s l,
  In l (regs_of_rpairs (loc_arguments s)) -> loc_argument_acceptable l.
Proof.
  intros until l. generalize (loc_arguments_acceptable s). generalize (loc_arguments s).
  induction l0 as [ | p pl]; simpl; intros.
- contradiction.
- rewrite in_app_iff in H0. destruct H0.
  exploit H; eauto. destruct p; simpl in *; intuition congruence.
  apply IHpl; auto.
Qed.

(** ** Location of function parameters *)

(** A function finds the values of its parameter in the same locations
  where its caller stored them, except that the stack-allocated arguments,
  viewed as [Outgoing] slots by the caller, are accessed via [Incoming]
  slots (at the same offsets and types) in the callee. *)

Definition parameter_of_argument (l: loc) : loc :=
  match l with
  | S Outgoing n ty => S Incoming n ty
  | _ => l
  end.

Definition loc_parameters (s: signature) : list (rpair loc) :=
  List.map (map_rpair parameter_of_argument) (loc_arguments s).

Lemma incoming_slot_in_parameters:
  forall ofs ty sg,
  In (S Incoming ofs ty) (regs_of_rpairs (loc_parameters sg)) ->
  In (S Outgoing ofs ty) (regs_of_rpairs (loc_arguments sg)).
Proof.
  intros.
  replace (regs_of_rpairs (loc_parameters sg)) with (List.map parameter_of_argument (regs_of_rpairs (loc_arguments sg))) in H.
  change (S Incoming ofs ty) with (parameter_of_argument (S Outgoing ofs ty)) in H.
  exploit list_in_map_inv. eexact H. intros [x [A B]]. simpl in A.
  exploit loc_arguments_acceptable_2; eauto. unfold loc_argument_acceptable; intros.
  destruct x; simpl in A; try discriminate.
  destruct sl; try contradiction.
  inv A. auto.
  unfold loc_parameters. generalize (loc_arguments sg). induction l as [ | p l]; simpl; intros.
  auto.
  rewrite map_app. f_equal; auto. destruct p; auto.
Qed.

(** * Tail calls *)

(** A tail-call is possible for a signature if the corresponding
    arguments are all passed in registers. *)

(** A tail-call is possible for a signature if the corresponding
    arguments are all passed in registers. *)

Definition tailcall_possible (s: signature) : Prop :=
  forall l, In l (regs_of_rpairs (loc_arguments s)) ->
  match l with R _ => True | S _ _ _ => False end.

(** Decide whether a tailcall is possible. *)

Definition tailcall_is_possible (sg: signature) : bool :=
  List.forallb
    (fun l => match l with R _ => true | S _ _ _ => false end)
    (regs_of_rpairs (loc_arguments sg)).

Lemma tailcall_is_possible_correct:
  forall s, tailcall_is_possible s = true -> tailcall_possible s.
Proof.
  unfold tailcall_is_possible; intros. rewrite forallb_forall in H.
  red; intros. apply H in H0. destruct l; [auto|discriminate].
Qed.

Lemma zero_size_arguments_tailcall_possible:
  forall sg, size_arguments sg = 0 -> tailcall_possible sg.
Proof.
  intros; red; intros. exploit loc_arguments_acceptable_2; eauto.
  unfold loc_argument_acceptable.
  destruct l; intros. auto. destruct sl; try contradiction. destruct H1.
  generalize (loc_arguments_bounded _ _ _ H0).
  generalize (typesize_pos ty). omega.
Qed.

(** * Calling convention *)

Require Import LanguageInterface.
Require Import Invariant.
Require Import CKLR.
Require Import String.
Require Import Values.
Require Import Memory.

(** Languages with [locset]s (currently LTL and Linear) use the
  following interface and calling convention. We need to keep the
  signature until Linear because it determines the stack layout used
  by the Linear to Mach calling convention to map locations to memory
  addresses. *)

Record locset_query :=
  lq {
    lq_fb: block;
    lq_sg: signature;
    lq_rs: Locmap.t;
    lq_mem: mem;
  }.

Canonical Structure li_locset: language_interface :=
  {|
    query := locset_query;
    reply := Locmap.t * mem;
  |}.

Record match_locset_query (R: cklr) (w: world R) (q1 q2: locset_query) :=
  {
    match_lq_fb: block_inject (mi R w) (lq_fb q1) (lq_fb q2);
    match_lq_sg: lq_sg q1 = lq_sg q2;
    match_lq_rs: (- ==> Val.inject (mi R w))%rel (lq_rs q1) (lq_rs q2);
    match_lq_mem: match_mem R w (lq_mem q1) (lq_mem q2);
  }.

Definition cc_locset (R: cklr): callconv li_locset li_locset :=
  {|
    ccworld := world R;
    match_senv := Events.symbols_inject @@ [mi R];
    match_query := match_locset_query R;
    match_reply := <> (- ==> Val.inject @@ [mi R]) * match_mem R;
  |}.

(** Triangular diagrams *)

Inductive match_locset_query_tr (R: cklr) (w: world R) q: locset_query -> Prop :=
  match_locset_query_tr_intro:
    inject_incr (Mem.flat_inj (Mem.nextblock (lq_mem q))) (mi R w) ->
    match_locset_query R w q q ->
    match_locset_query_tr R w q q.

Definition cc_locset_tr R: callconv li_locset li_locset :=
  {|
    ccworld := world R;
    match_senv := Events.symbols_inject @@ [mi R];
    match_query := match_locset_query_tr R;
    match_reply := <> (- ==> Val.inject @@ [mi R]) * match_mem R;
  |}.

(** Typing *)

Definition locset_wt: invariant li_locset :=
  {|
    query_inv q := forall l, Val.has_type (lq_rs q l) (Loc.type l);
    reply_inv q r := forall l, Val.has_type (fst r l) (Loc.type l);
  |}.

(** We now define the calling convention between C and locset languages. *)

Definition callee_save_loc (l: loc) :=
  match l with
  | R r => is_callee_save r = true
  | S sl ofs ty => sl <> Outgoing
  end.

Definition agree_callee_save (ls1 ls2: Locmap.t) : Prop :=
  forall l, callee_save_loc l -> ls1 l = ls2 l.

Inductive cc_alloc_mq: _ -> c_query -> locset_query -> Prop :=
  cc_alloc_mq_intro id sg args rs m:
    args = map (fun p => Locmap.getpair p rs) (loc_arguments sg) ->
    cc_alloc_mq (sg, rs) (cq id sg args m) (lq id sg rs m).

Inductive cc_alloc_mr: _ -> reply li_c -> reply li_locset -> Prop :=
  cc_alloc_mr_intro sg rs res rs' m':
    agree_callee_save rs rs' ->
    Locmap.getpair (map_rpair R (loc_result sg)) rs' = res ->
    cc_alloc_mr (sg, rs) (res, m') (rs', m').

Definition cc_alloc: callconv li_c li_locset :=
  {|
    ccworld := signature * Locmap.t;
    match_senv w := eq;
    match_query := cc_alloc_mq;
    match_reply := cc_alloc_mr;
  |}.

Definition alloc_sg (w: ccworld cc_alloc) := fst w.
Definition alloc_rs (w: ccworld cc_alloc) := snd w.

Lemma match_cc_alloc fb sg args rs m:
  args = map (fun p => Locmap.getpair p rs) (loc_arguments sg) ->
  exists w,
    match_query cc_alloc w (cq fb sg args m) (lq fb sg rs m) /\
    forall vres m1' rs' m2',
      match_reply cc_alloc w (vres, m1') (rs', m2') ->
      agree_callee_save rs rs' /\
      Locmap.getpair (map_rpair R (loc_result sg)) rs' = vres /\
      m1' = m2'.
Proof.
  intros Hargs.
  exists (sg, rs). split.
  - constructor; eauto.
  - intros vres m1' rs' m2' Hr.
    inv Hr. eauto.
Qed.

Lemma match_query_cc_alloc (P: _ -> _ -> _ -> _ -> Prop):
  (forall id sg args rs m,
   args = map (fun p => Locmap.getpair p rs) (loc_arguments sg) ->
   P sg rs (cq id sg args m) (lq id sg rs m)) ->
  (forall w q1 q2, match_query cc_alloc w q1 q2 ->
   P (alloc_sg w) (alloc_rs w) q1 q2).
Proof.
  intros H w q1 q2 Hq.
  destruct Hq as [id sg args rs m]; simpl.
  eauto.
Qed.

Lemma match_reply_cc_alloc w vres rs' m':
  agree_callee_save (snd w) rs' ->
  Locmap.getpair (map_rpair R (loc_result (fst w))) rs' = vres ->
  match_reply cc_alloc w (vres, m') (rs', m').
Proof.
  intros H Hvres.
  destruct w as [sg rs].
  constructor; eauto.
Qed.

Ltac inv_alloc_query :=
  let w := fresh "w" in
  let q1 := fresh "q1" in
  let q2 := fresh "q2" in
  let Hq := fresh "Hq" in
  intros w q1 q2 Hq;
  pattern (alloc_sg w), (alloc_rs w), q1, q2;
  revert w q1 q2 Hq;
  apply match_query_cc_alloc.

(* XXX may be needed later
Lemma locmap_setpair_getpair p ls l:
  Val.lessdef
    (Locmap.get l (Locmap.setpair p (Locmap.getpair (map_rpair R p) ls) ls))
    (Locmap.get l ls).
Proof.
  unfold Locmap.setpair, Locmap.getpair.
  destruct p; simpl.
  - destruct (Loc.eq (R r) l); subst.
    + setoid_rewrite Locmap.gss; eauto.
    + setoid_rewrite Locmap.gso; eauto.
      simpl. destruct l; eauto; congruence.
  - destruct (Loc.eq (R rlo) l); subst.
    + setoid_rewrite Locmap.gss; eauto.
      apply val_loword_longofwords.
    + setoid_rewrite Locmap.gso; eauto.
      * destruct (Loc.eq (R rhi) l); subst.
        setoid_rewrite Locmap.gss. apply val_hiword_longofwords.
        setoid_rewrite Locmap.gso; eauto. destruct l; simpl; eauto; congruence.
      * destruct l; simpl; eauto; congruence.
Qed.
*)
