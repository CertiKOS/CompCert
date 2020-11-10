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
Require Import Values.
Require Import Memory.
Require Import LanguageInterface.
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


(** * Callee-save locations *)

(** We classify locations as either
- callee-save, i.e. preserved across function calls:
  callee-save registers, [Local] and [Incoming] stack slots;
- caller-save, i.e. possibly modified by a function call:
  non-callee-save registers, [Outgoing] stack slots.

Concerning [Outgoing] stack slots: several ABIs allow a function to modify
the stack slots used for passing parameters to this function.
The code currently generated by CompCert never does so, but the code
generated by other compilers often does so (e.g. GCC for x86-32).
Hence, CompCert-generated code must not assume that [Outgoing] stack slots
are preserved across function calls, because they might not be preserved
if the called function was compiled by another compiler. 
*)

Definition callee_save_loc (l: loc) :=
  match l with
  | R r => is_callee_save r = true
  | S sl ofs ty => sl <> Outgoing
  end.

Definition agree_callee_save (ls1 ls2: Locmap.t) : Prop :=
  forall l, callee_save_loc l -> ls1 l = ls2 l.

(** * Assigning result locations *)

(** Useful lemmas to reason about the result of an external call. *)

Lemma locmap_get_set_loc_result:
  forall sg v rs l,
  match l with R r => is_callee_save r = true | S _ _ _ => True end ->
  Locmap.setpair (loc_result sg) v rs l = rs l.
Proof.
  intros. apply Locmap.gpo. 
  assert (X: forall r, is_callee_save r = false -> Loc.diff l (R r)).
  { intros. destruct l; simpl. congruence. auto. }
  generalize (loc_result_caller_save sg). destruct (loc_result sg); simpl; intuition auto.
Qed.

Lemma locmap_get_set_loc_result_callee_save:
  forall sg v rs l,
  callee_save_loc l ->
  Locmap.setpair (loc_result sg) v rs l = rs l.
Proof.
  intros. apply locmap_get_set_loc_result. 
  red in H; destruct l; auto.
Qed.


(** * Language interface for locations *)

(** Languages with [locset]s (currently LTL and Linear) use the
  following interface. We need to keep the C-level signature until
  Linear because it determines the stack layout used by the Linear
  to Mach calling convention to map locations to memory addresses. *)

Record locset_query :=
  lq {
    lq_vf: val;
    lq_sg: signature;
    lq_rs: Locmap.t;
    lq_mem: mem;
  }.

Record locset_reply :=
  lr {
    lr_rs: Locmap.t;
    lr_mem: mem;
  }.

Canonical Structure li_locset: language_interface :=
  {|
    query := locset_query;
    reply := locset_reply;
    entry := lq_vf;
  |}.

(** * Calling convention *)

(** We first define the calling convention between C and locset
  languages, which relates the C-level argument list to the contents
  of the locations. The Kripke world keeps track of the signature and
  initial values registers, so that the return value can be
  interpreted in the correct way and the preservation of callee-save
  registers can be enforced. *)

Inductive cc_alloc_mq: signature * Locmap.t -> c_query -> locset_query -> Prop :=
  cc_alloc_mq_intro vf sg args rs m:
    args = (map (fun p => Locmap.getpair p rs) (loc_arguments sg)) ->
    cc_alloc_mq (sg, rs) (cq vf sg args m) (lq vf sg rs m).

Inductive cc_alloc_mr: signature * Locmap.t -> c_reply -> locset_reply -> Prop :=
  cc_alloc_mr_intro sg rs res rs' m:
    res = (Locmap.getpair (map_rpair R (loc_result sg)) rs') ->
    agree_callee_save rs rs' ->
    cc_alloc_mr (sg, rs) (cr res m) (lr rs' m).

Program Definition cc_alloc: callconv li_c li_locset :=
  {|
    match_senv w := eq;
    match_query := cc_alloc_mq;
    match_reply := cc_alloc_mr;
  |}.

(** The extension convention is used by the Tunneling proof. *)

Inductive cc_locset_ext_query: locset_query -> locset_query -> Prop :=
  cc_locset_ext_query_intro vf sg ls1 ls2 m1 m2:
    (forall l, Val.lessdef (ls1 l) (ls2 l)) ->
    Mem.extends m1 m2 ->
    cc_locset_ext_query (lq vf sg ls1 m1) (lq vf sg ls2 m2).

Inductive cc_locset_ext_reply: locset_reply -> locset_reply -> Prop :=
  cc_locset_ext_reply_intro ls1 ls2 m1 m2:
    (forall l, Val.lessdef (ls1 l) (ls2 l)) ->
    Mem.extends m1 m2 ->
    cc_locset_ext_reply (lr ls1 m1) (lr ls2 m2).

Program Definition cc_locset_ext :=
  {|
    ccworld := unit;
    match_senv w := eq;
    match_query w := cc_locset_ext_query;
    match_reply w := cc_locset_ext_reply;
  |}.
