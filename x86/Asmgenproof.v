(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*                  Xavier Leroy, INRIA Paris                          *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Correctness proof for x86-64 generation: main proof. *)

Require Import Coqlib Errors.
Require Import Integers Floats AST Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Op Locations Mach Conventions Asm.
Require Import Asmgen Asmgenproof0 Asmgenproof1.

(** * Calling convention *)

Inductive cc_asmgen_mq: _ -> query li_mach -> query li_asm -> Prop :=
  | cc_asmgen_mq_intro id ms m1 rs m2 sp:
      valid_blockv m2 sp ->
      rs#PC = Vptr (Block.glob id) Ptrofs.zero ->
      rs#RA <> Vundef ->
      agree ms sp rs ->
      Mem.extends m1 m2 ->
      cc_asmgen_mq (sp, rs#RA, Mem.nextblock m2) (mq id sp rs#RA ms m1) (rs, m2).

Definition cc_asmgen_mr: _ -> reply li_mach -> reply li_asm -> _ :=
  fun '(sp, ra, nb) '(ms', m1') '(rs', m2') =>
    rs'#PC = ra /\
    agree ms' sp rs' /\
    Mem.extends m1' m2' /\
    Block.le nb (Mem.nextblock m2').

Definition cc_asmgen: callconv li_mach li_asm :=
  {|
    match_senv w := eq;
    match_query := cc_asmgen_mq;
    match_reply := cc_asmgen_mr;
  |}.

Lemma match_cc_asmgen id sp ms m1 rs m2:
  valid_blockv m2 sp ->
  rs#PC = Vptr (Block.glob id) Ptrofs.zero ->
  rs#RA <> Vundef ->
  agree ms sp rs ->
  Mem.extends m1 m2 ->
  exists w,
    match_query cc_asmgen w (mq id sp rs#RA ms m1) (rs, m2) /\
    forall ms' m1' rs' m2',
      match_reply cc_asmgen w (ms', m1') (rs', m2') ->
      rs'#PC = rs#RA /\
      agree ms' sp rs' /\
      Mem.extends m1' m2' /\
      Block.le (Mem.nextblock m2) (Mem.nextblock m2').
Proof.
  intros.
  exists (sp, rs#RA, Mem.nextblock m2). simpl. split.
  - constructor; eauto.
  - intuition eauto.
Qed.

(** * .. *)

Definition match_prog (p: Mach.program) (tp: Asm.program) :=
  match_program (fun _ f tf => transf_fundef f = OK tf) eq p tp.

Lemma transf_program_match:
  forall p tp, transf_program p = OK tp -> match_prog p tp.
Proof.
  intros. eapply match_transform_partial_program; eauto.
Qed.

Section PRESERVATION.

Variable prog: Mach.program.
Variable tprog: Asm.program.
Hypothesis TRANSF: match_prog prog tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof (Genv.find_symbol_match TRANSF).

Lemma senv_preserved:
  Senv.equiv ge tge.
Proof (Genv.senv_match TRANSF).

Lemma functions_translated:
  forall b f,
  Genv.find_funct_ptr ge b = Some f ->
  exists tf,
  Genv.find_funct_ptr tge b = Some tf /\ transf_fundef f = OK tf.
Proof (Genv.find_funct_ptr_transf_partial TRANSF).

Lemma functions_transl:
  forall fb f tf,
  Genv.find_funct_ptr ge fb = Some (Internal f) ->
  transf_function f = OK tf ->
  Genv.find_funct_ptr tge fb = Some (Internal tf).
Proof.
  intros. exploit functions_translated; eauto. intros [tf' [A B]].
  monadInv B. rewrite H0 in EQ; inv EQ; auto.
Qed.

(** * Properties of control flow *)

Lemma transf_function_no_overflow:
  forall f tf,
  transf_function f = OK tf -> list_length_z (fn_code tf) <= Ptrofs.max_unsigned.
Proof.
  intros. monadInv H. destruct (zlt Ptrofs.max_unsigned (list_length_z (fn_code x))); monadInv EQ0.
  omega.
Qed.

Lemma exec_straight_exec:
  forall fb f c ep tf tc c' rs m rs' m' sp0,
  transl_code_at_pc ge (rs PC) fb f c ep tf tc ->
  exec_straight sp0 tge tf tc rs m c' rs' m' ->
  plus step tge (State rs m (Some sp0)) E0 (State rs' m' (Some sp0)).
Proof.
  intros. inv H.
  eapply exec_straight_steps_1; eauto.
  eapply transf_function_no_overflow; eauto.
  eapply functions_transl; eauto.
Qed.

Lemma exec_straight_at:
  forall fb f c ep tf tc c' ep' tc' rs m rs' m' sp0,
  transl_code_at_pc ge (rs PC) fb f c ep tf tc ->
  transl_code f c' ep' = OK tc' ->
  exec_straight sp0 tge tf tc rs m tc' rs' m' ->
  transl_code_at_pc ge (rs' PC) fb f c' ep' tf tc'.
Proof.
  intros. inv H.
  exploit exec_straight_steps_2; eauto.
  eapply transf_function_no_overflow; eauto.
  eapply functions_transl; eauto.
  intros [ofs' [PC' CT']].
  rewrite PC'. constructor; auto.
Qed.

(** The following lemmas show that the translation from Mach to Asm
  preserves labels, in the sense that the following diagram commutes:
<<
                          translation
        Mach code ------------------------ Asm instr sequence
            |                                          |
            | Mach.find_label lbl       find_label lbl |
            |                                          |
            v                                          v
        Mach code tail ------------------- Asm instr seq tail
                          translation
>>
  The proof demands many boring lemmas showing that Asm constructor
  functions do not introduce new labels.

  In passing, we also prove a "is tail" property of the generated Asm code.
*)

Section TRANSL_LABEL.

Remark mk_mov_label:
  forall rd rs k c, mk_mov rd rs k = OK c -> tail_nolabel k c.
Proof.
  unfold mk_mov; intros.
  destruct rd; try discriminate; destruct rs; TailNoLabel.
Qed.
Hint Resolve mk_mov_label: labels.

Remark mk_shrximm_label:
  forall n k c, mk_shrximm n k = OK c -> tail_nolabel k c.
Proof.
  intros. monadInv H; TailNoLabel.
Qed.
Hint Resolve mk_shrximm_label: labels.

Remark mk_shrxlimm_label:
  forall n k c, mk_shrxlimm n k = OK c -> tail_nolabel k c.
Proof.
  intros. monadInv H. destruct (Int.eq n Int.zero); TailNoLabel.
Qed.
Hint Resolve mk_shrxlimm_label: labels.

Remark mk_intconv_label:
  forall f r1 r2 k c, mk_intconv f r1 r2 k = OK c ->
  (forall r r', nolabel (f r r')) ->
  tail_nolabel k c.
Proof.
  unfold mk_intconv; intros. TailNoLabel.
Qed.
Hint Resolve mk_intconv_label: labels.

Remark mk_storebyte_label:
  forall addr r k c, mk_storebyte addr r k = OK c -> tail_nolabel k c.
Proof.
  unfold mk_storebyte; intros. TailNoLabel.
Qed.
Hint Resolve mk_storebyte_label: labels.

Remark loadind_label:
  forall base ofs ty dst k c,
  loadind base ofs ty dst k = OK c ->
  tail_nolabel k c.
Proof.
  unfold loadind; intros. destruct ty; try discriminate; destruct (preg_of dst); TailNoLabel.
Qed.

Remark storeind_label:
  forall base ofs ty src k c,
  storeind src base ofs ty k = OK c ->
  tail_nolabel k c.
Proof.
  unfold storeind; intros. destruct ty; try discriminate; destruct (preg_of src); TailNoLabel.
Qed.

Remark mk_setcc_base_label:
  forall xc rd k,
  tail_nolabel k (mk_setcc_base xc rd k).
Proof.
  intros. destruct xc; simpl; destruct (ireg_eq rd RAX); TailNoLabel.
Qed.

Remark mk_setcc_label:
  forall xc rd k,
  tail_nolabel k (mk_setcc xc rd k).
Proof.
  intros. unfold mk_setcc. destruct (Archi.ptr64 || low_ireg rd).
  apply mk_setcc_base_label.
  eapply tail_nolabel_trans. apply mk_setcc_base_label. TailNoLabel.
Qed.

Remark mk_jcc_label:
  forall xc lbl' k,
  tail_nolabel k (mk_jcc xc lbl' k).
Proof.
  intros. destruct xc; simpl; TailNoLabel.
Qed.

Remark transl_cond_label:
  forall cond args k c,
  transl_cond cond args k = OK c ->
  tail_nolabel k c.
Proof.
  unfold transl_cond; intros.
  destruct cond; TailNoLabel.
  destruct (Int.eq_dec n Int.zero); TailNoLabel.
  destruct (Int64.eq_dec n Int64.zero); TailNoLabel.
  destruct c0; simpl; TailNoLabel.
  destruct c0; simpl; TailNoLabel.
  destruct c0; simpl; TailNoLabel.
  destruct c0; simpl; TailNoLabel.
Qed.

Remark transl_op_label:
  forall op args r k c,
  transl_op op args r k = OK c ->
  tail_nolabel k c.
Proof.
  unfold transl_op; intros. destruct op; TailNoLabel.
  destruct (Int.eq_dec n Int.zero); TailNoLabel.
  destruct (Int64.eq_dec n Int64.zero); TailNoLabel.
  destruct (Float.eq_dec n Float.zero); TailNoLabel.
  destruct (Float32.eq_dec n Float32.zero); TailNoLabel.
  destruct (normalize_addrmode_64 x) as [am' [delta|]]; TailNoLabel.
  eapply tail_nolabel_trans. eapply transl_cond_label; eauto. eapply mk_setcc_label.
Qed.

Remark transl_load_label:
  forall chunk addr args dest k c,
  transl_load chunk addr args dest k = OK c ->
  tail_nolabel k c.
Proof.
  intros. monadInv H. destruct chunk; TailNoLabel.
Qed.

Remark transl_store_label:
  forall chunk addr args src k c,
  transl_store chunk addr args src k = OK c ->
  tail_nolabel k c.
Proof.
  intros. monadInv H. destruct chunk; TailNoLabel.
Qed.

Lemma transl_instr_label:
  forall f i ep k c,
  transl_instr f i ep k = OK c ->
  match i with Mlabel lbl => c = Plabel lbl :: k | _ => tail_nolabel k c end.
Proof.
Opaque loadind.
  unfold transl_instr; intros; destruct i; TailNoLabel.
  eapply loadind_label; eauto.
  eapply storeind_label; eauto.
  eapply loadind_label; eauto.
  eapply tail_nolabel_trans; eapply loadind_label; eauto.
  eapply transl_op_label; eauto.
  eapply transl_load_label; eauto.
  eapply transl_store_label; eauto.
  destruct s0; TailNoLabel.
  destruct s0; TailNoLabel.
  eapply tail_nolabel_trans. eapply transl_cond_label; eauto. eapply mk_jcc_label.
Qed.

Lemma transl_instr_label':
  forall lbl f i ep k c,
  transl_instr f i ep k = OK c ->
  find_label lbl c = if Mach.is_label lbl i then Some k else find_label lbl k.
Proof.
  intros. exploit transl_instr_label; eauto.
  destruct i; try (intros [A B]; apply B).
  intros. subst c. simpl. auto.
Qed.

Lemma transl_code_label:
  forall lbl f c ep tc,
  transl_code f c ep = OK tc ->
  match Mach.find_label lbl c with
  | None => find_label lbl tc = None
  | Some c' => exists tc', find_label lbl tc = Some tc' /\ transl_code f c' false = OK tc'
  end.
Proof.
  induction c; simpl; intros.
  inv H. auto.
  monadInv H. rewrite (transl_instr_label' lbl _ _ _ _ _ EQ0).
  generalize (Mach.is_label_correct lbl a).
  destruct (Mach.is_label lbl a); intros.
  subst a. simpl in EQ. exists x; auto.
  eapply IHc; eauto.
Qed.

Lemma transl_find_label:
  forall lbl f tf,
  transf_function f = OK tf ->
  match Mach.find_label lbl f.(Mach.fn_code) with
  | None => find_label lbl tf.(fn_code) = None
  | Some c => exists tc, find_label lbl tf.(fn_code) = Some tc /\ transl_code f c false = OK tc
  end.
Proof.
  intros. monadInv H. destruct (zlt Ptrofs.max_unsigned (list_length_z (fn_code x))); inv EQ0.
  monadInv EQ. simpl. eapply transl_code_label; eauto. rewrite transl_code'_transl_code in EQ0; eauto.
Qed.

End TRANSL_LABEL.

(** A valid branch in a piece of Mach code translates to a valid ``go to''
  transition in the generated PPC code. *)

Lemma find_label_goto_label:
  forall f tf lbl rs m c' b ofs,
  Genv.find_funct_ptr ge b = Some (Internal f) ->
  transf_function f = OK tf ->
  rs PC = Vptr b ofs ->
  Mach.find_label lbl f.(Mach.fn_code) = Some c' ->
  exists tc', exists rs',
    goto_label tf lbl rs m = Next rs' m
  /\ transl_code_at_pc ge (rs' PC) b f c' false tf tc'
  /\ forall r, r <> PC -> rs'#r = rs#r.
Proof.
  intros. exploit (transl_find_label lbl f tf); eauto. rewrite H2.
  intros [tc [A B]].
  exploit label_pos_code_tail; eauto. instantiate (1 := 0).
  intros [pos' [P [Q R]]].
  exists tc; exists (rs#PC <- (Vptr b (Ptrofs.repr pos'))).
  split. unfold goto_label. rewrite P. rewrite H1. auto.
  split. rewrite Pregmap.gss. constructor; auto.
  rewrite Ptrofs.unsigned_repr. replace (pos' - 0) with pos' in Q.
  auto. omega.
  generalize (transf_function_no_overflow _ _ H0). omega.
  intros. apply Pregmap.gso; auto.
Qed.

(** Existence of return addresses *)

Lemma return_address_exists:
  forall f sg ros c, is_tail (Mcall sg ros :: c) f.(Mach.fn_code) ->
  exists ra, return_address_offset f c ra.
Proof.
  intros. eapply Asmgenproof0.return_address_exists; eauto.
- intros. exploit transl_instr_label; eauto.
  destruct i; try (intros [A B]; apply A). intros. subst c0. repeat constructor.
- intros. monadInv H0.
  destruct (zlt Ptrofs.max_unsigned (list_length_z (fn_code x))); inv EQ0.
  monadInv EQ. rewrite transl_code'_transl_code in EQ0.
  exists x; exists true; split; auto. unfold fn_code. repeat constructor.
- exact transf_function_no_overflow.
Qed.

(** * Proof of semantic preservation *)

(** Semantic preservation is proved using simulation diagrams
  of the following form.
<<
           st1 --------------- st2
            |                   |
           t|                  *|t
            |                   |
            v                   v
           st1'--------------- st2'
>>
  The invariant is the [match_states] predicate below, which includes:
- The PPC code pointed by the PC register is the translation of
  the current Mach code sequence.
- Mach register values and PPC register values agree.
*)

Section IN_WORLD.

Context (w: ccworld cc_asmgen).
Let sp0 := fst (fst w).
Let ra0 := snd (fst w).
Let nb0 := snd w.

Inductive match_states: Mach.state -> Asm.state -> Prop :=
  | match_states_intro:
      forall s fb sp c ep ms m m' rs f tf tc
        (NB: Block.le nb0 (Mem.nextblock m'))
        (STACKS: match_stack sp0 ra0 ge s)
        (FIND: Genv.find_funct_ptr ge fb = Some (Internal f))
        (MEXT: Mem.extends m m')
        (AT: transl_code_at_pc ge (rs PC) fb f c ep tf tc)
        (SPLT: block_lt (parent_sp s) sp)
        (SPVB: valid_blockv m' sp)
        (AG: agree ms sp rs)
        (AXP: ep = true -> rs#RAX = parent_sp s),
      match_states (Mach.State s fb sp c ms m)
                   (Asm.State rs m' (Some sp0))
  | match_states_call:
      forall s fb ms m m' rs
        (NB: Block.le nb0 (Mem.nextblock m'))
        (STACKS: match_stack sp0 ra0 ge s)
        (MEXT: Mem.extends m m')
        (SPVB: valid_blockv m' (parent_sp s))
        (AG: agree ms (parent_sp s) rs)
        (ATPC: rs PC = Vptr fb Ptrofs.zero)
        (ATLR: rs RA = parent_ra s),
      match_states (Mach.Callstate s fb ms m)
                   (Asm.State rs m' (Some sp0))
  | match_states_return:
      forall s ms m m' rs sp ra fb f c tf tc
        (NB: Block.le nb0 (Mem.nextblock m'))
        (SF: Genv.find_funct_ptr ge fb = Some (Internal f))
        (TF: transl_code_at_pc ge ra fb f c false tf tc)
        (SPLT: block_lt (parent_sp s) sp)
        (SPVB: valid_blockv m' sp)
        (STACKS: match_stack sp0 ra0 ge s)
        (MEXT: Mem.extends m m')
        (AG: agree ms sp rs)
        (ATPC: rs PC = ra),
      match_states (Mach.Returnstate (Stackframe fb sp ra c :: s) ms m)
                   (Asm.State rs m' (Some sp0))
  | match_states_final:
      forall s ms m rs m'
        (NB: Block.le nb0 (Mem.nextblock m'))
        (MEXT: Mem.extends m m')
        (AG: agree ms sp0 rs)
        (ATPC: rs PC = ra0),
      match_states (Mach.Returnstate (Parent sp0 ra0 :: s) ms m)
                   (Asm.State rs m' None).

Lemma exec_instr_nextblock f i rs m rs' m':
  exec_instr tge sp0 f i rs m = Next rs' m' ->
  Block.le (Mem.nextblock m) (Mem.nextblock m').
Proof.
  destruct i; simpl;
  try (unfold exec_load; destruct (Mem.loadv _ _ _));
  try (unfold exec_store; destruct (eval_addrmode _ _ _); simpl);
  unfold goto_label;
  repeat
    match goal with
      | |- match ?x with _ => _ end = Next _ _ -> _ =>
        let H := fresh in
        destruct x eqn:H;
        try apply Mem.nextblock_free in H;
        try apply Mem.nextblock_store in H;
        try apply Mem.nextblock_alloc in H
    end;
  inversion 1;
  try (replace (Mem.nextblock m) with (Mem.nextblock m') by congruence);
  try apply Block.le_refl.
  - replace (Mem.nextblock m') with (Block.succ (Mem.nextblock m)) by congruence.
    blomega.
Qed.

Lemma exec_straight_nextblock tf c rs m k rs' m':
  exec_straight sp0 tge tf c rs m k rs' m' ->
  Block.le (Mem.nextblock m) (Mem.nextblock m').
Proof.
  induction 1; eauto using exec_instr_nextblock.
  eapply Block.le_trans; eauto using exec_instr_nextblock.
Qed.

Lemma valid_blockv_lt m p1 p2:
  valid_blockv m p2 ->
  block_lt p1 p2 ->
  valid_blockv m p1.
Proof.
  intros Hp2 Hp.
  destruct Hp2. inv Hp. constructor.
  unfold Mem.valid_block in *. blomega.
Qed.

Lemma exec_straight_steps:
  forall s fb f rs1 i c ep tf tc m1' m2 m2' sp ms2,
  match_stack sp0 ra0 ge s ->
  Mem.extends m2 m2' ->
  Genv.find_funct_ptr ge fb = Some (Internal f) ->
  transl_code_at_pc ge (rs1 PC) fb f (i :: c) ep tf tc ->
  block_lt (parent_sp s) sp ->
  valid_blockv m1' sp ->
  Block.le nb0 (Mem.nextblock m1') ->
  (forall k c (TR: transl_instr f i ep k = OK c),
   exists rs2,
       exec_straight sp0 tge tf c rs1 m1' k rs2 m2'
    /\ agree ms2 sp rs2
    /\ (it1_is_parent ep i = true -> rs2#RAX = parent_sp s)) ->
  exists st',
  plus step tge (State rs1 m1' (Some sp0)) E0 st' /\
  match_states (Mach.State s fb sp c ms2 m2) st'.
Proof.
  intros. inversion H2. subst. monadInv H10.
  exploit H6; eauto. intros [rs2 [A [B C]]].
  exists (State rs2 m2' (Some sp0)); split.
  eapply exec_straight_exec; eauto.
  econstructor; eauto.
  apply exec_straight_nextblock in A; eapply Block.le_trans; eauto.
  eapply exec_straight_at; eauto.
  eauto using valid_blockv_nextblock, exec_straight_nextblock.
Qed.

Lemma exec_straight_steps_goto:
  forall s fb f rs1 i c ep tf tc m1' m2 m2' sp ms2 lbl c',
  match_stack sp0 ra0 ge s ->
  Mem.extends m2 m2' ->
  Genv.find_funct_ptr ge fb = Some (Internal f) ->
  Mach.find_label lbl f.(Mach.fn_code) = Some c' ->
  transl_code_at_pc ge (rs1 PC) fb f (i :: c) ep tf tc ->
  it1_is_parent ep i = false ->
  block_lt (parent_sp s) sp ->
  valid_blockv m1' sp ->
  Block.le nb0 (Mem.nextblock m1') ->
  (forall k c (TR: transl_instr f i ep k = OK c),
   exists jmp, exists k', exists rs2,
       exec_straight sp0 tge tf c rs1 m1' (jmp :: k') rs2 m2'
    /\ agree ms2 sp rs2
    /\ exec_instr tge sp0 tf jmp rs2 m2' = goto_label tf lbl rs2 m2') ->
  exists st',
  plus step tge (State rs1 m1' (Some sp0)) E0 st' /\
  match_states (Mach.State s fb sp c' ms2 m2) st'.
Proof.
  intros. inversion H3. subst. monadInv H12.
  exploit H8; eauto. intros [jmp [k' [rs2 [A [B C]]]]].
  generalize (functions_transl _ _ _ H10 H11); intro FN.
  generalize (transf_function_no_overflow _ _ H11); intro NOOV.
  exploit exec_straight_steps_2; eauto.
  intros [ofs' [PC2 CT2]].
  exploit find_label_goto_label; eauto.
  intros [tc' [rs3 [GOTO [AT' OTH]]]].
  exists (State rs3 m2' (Some sp0)); split.
  eapply plus_right'.
  eapply exec_straight_steps_1; eauto.
  econstructor; eauto.
  eapply find_instr_tail. eauto.
  rewrite C. eexact GOTO.
  traceEq.
  econstructor; eauto.
  eapply Block.le_trans; eauto using exec_straight_nextblock.
  eauto using valid_blockv_nextblock, exec_straight_nextblock.
  apply agree_exten with rs2; auto with asmgen.
  congruence.
Qed.

Lemma alloc_sp_fresh m p lo hi m' stk ofs:
  valid_blockv m p ->
  Mem.alloc m lo hi = (m', stk) ->
  block_lt p (Vptr stk ofs).
Proof.
  intros Hm Hstk.
  apply Mem.alloc_result in Hstk.
  destruct Hm.
  constructor.
  subst. assumption.
Qed.

(** We need to show that, in the simulation diagram, we cannot
  take infinitely many Mach transitions that correspond to zero
  transitions on the PPC side.  Actually, all Mach transitions
  correspond to at least one Asm transition, except the
  transition from [Mach.Returnstate] to [Mach.State].
  So, the following integer measure will suffice to rule out
  the unwanted behaviour. *)

Definition measure (s: Mach.state) : nat :=
  match s with
  | Mach.State _ _ _ _ _ _ => 0%nat
  | Mach.Callstate _ _ _ _ => 0%nat
  | Mach.Returnstate _ _ _ => 1%nat
  end.

(** This is the simulation diagram.  We prove it by case analysis on the Mach transition. *)

Theorem step_simulation:
  forall S1 t S2, Mach.step return_address_offset ge S1 t S2 ->
  forall S1' (MS: match_states S1 S1'),
  (exists S2', plus step tge S1' t S2' /\ match_states S2 S2')
  \/ (measure S2 < measure S1 /\ t = E0 /\ match_states S2 S1')%nat.
Proof.
  induction 1; intros; inv MS.

- (* Mlabel *)
  left; eapply exec_straight_steps; eauto; intros.
  monadInv TR. econstructor; split. apply exec_straight_one. simpl; eauto. auto.
  split. apply agree_nextinstr; auto. simpl; congruence.

- (* Mgetstack *)
  unfold load_stack in H.
  exploit Mem.loadv_extends; eauto. intros [v' [A B]].
  rewrite (sp_val _ _ _ AG) in A.
  left; eapply exec_straight_steps; eauto. intros. simpl in TR.
  exploit loadind_correct; eauto. intros [rs' [P [Q R]]].
  exists rs'; split. eauto.
  split. eapply agree_set_mreg; eauto. congruence.
  simpl; congruence.

- (* Msetstack *)
  unfold store_stack in H.
  assert (Val.lessdef (rs src) (rs0 (preg_of src))). eapply preg_val; eauto.
  exploit Mem.storev_extends; eauto. intros [m2' [A B]].
  left; eapply exec_straight_steps; eauto.
  rewrite (sp_val _ _ _ AG) in A. intros. simpl in TR.
  exploit storeind_correct; eauto. intros [rs' [P Q]].
  exists rs'; split. eauto.
  split. eapply agree_undef_regs; eauto.
  simpl; intros. rewrite Q; auto with asmgen.
Local Transparent destroyed_by_setstack.
  destruct ty; simpl; intuition congruence.

- (* Mgetparam *)
  assert (f0 = f) by congruence; subst f0.
  unfold load_stack in *.
  exploit Mem.loadv_extends. eauto. eexact H0. auto.
  intros [parent' [A B]]. rewrite (sp_val _ _ _ AG) in A.
  exploit lessdef_parent_sp; eauto. clear B; intros B; subst parent'.
  exploit Mem.loadv_extends. eauto. eexact H1. auto.
  intros [v' [C D]].
Opaque loadind.
  left; eapply exec_straight_steps; eauto; intros.
  assert (DIFF: negb (mreg_eq dst AX) = true -> IR RAX <> preg_of dst).
    intros. change (IR RAX) with (preg_of AX). red; intros.
    unfold proj_sumbool in H1. destruct (mreg_eq dst AX); try discriminate.
    elim n. eapply preg_of_injective; eauto.
  destruct ep; simpl in TR.
(* RAX contains parent *)
  exploit loadind_correct. eexact TR.
  instantiate (2 := rs0). rewrite AXP; eauto.
  intros [rs1 [P [Q R]]].
  exists rs1; split. eauto.
  split. eapply agree_set_mreg. eapply agree_set_mreg; eauto. congruence. auto.
  simpl; intros. rewrite R; auto.
(* RAX does not contain parent *)
  monadInv TR.
  exploit loadind_correct. eexact EQ0. eauto. intros [rs1 [P [Q R]]]. simpl in Q.
  exploit loadind_correct. eexact EQ. instantiate (2 := rs1). rewrite Q. eauto.
  intros [rs2 [S [T U]]].
  exists rs2; split. eapply exec_straight_trans; eauto.
  split. eapply agree_set_mreg. eapply agree_set_mreg; eauto. congruence. auto.
  simpl; intros. rewrite U; auto.

- (* Mop *)
  assert (eval_operation tge sp op rs##args m = Some v).
    rewrite <- H. apply eval_operation_preserved. exact symbols_preserved.
  exploit eval_operation_lessdef. eapply preg_vals; eauto. eauto. eexact H0.
  intros [v' [A B]]. rewrite (sp_val _ _ _ AG) in A.
  left; eapply exec_straight_steps; eauto; intros. simpl in TR.
  exploit transl_op_correct; eauto. intros [rs2 [P [Q R]]].
  assert (S: Val.lessdef v (rs2 (preg_of res))) by (eapply Val.lessdef_trans; eauto).
  exists rs2; split. eauto.
  split. eapply agree_set_undef_mreg; eauto.
  simpl; congruence.

- (* Mload *)
  assert (eval_addressing tge sp addr rs##args = Some a).
    rewrite <- H. apply eval_addressing_preserved. exact symbols_preserved.
  exploit eval_addressing_lessdef. eapply preg_vals; eauto. eexact H1.
  intros [a' [A B]]. rewrite (sp_val _ _ _ AG) in A.
  exploit Mem.loadv_extends; eauto. intros [v' [C D]].
  left; eapply exec_straight_steps; eauto; intros. simpl in TR.
  exploit transl_load_correct; eauto. intros [rs2 [P [Q R]]].
  exists rs2; split. eauto.
  split. eapply agree_set_undef_mreg; eauto. congruence.
  simpl; congruence.

- (* Mstore *)
  assert (eval_addressing tge sp addr rs##args = Some a).
    rewrite <- H. apply eval_addressing_preserved. exact symbols_preserved.
  exploit eval_addressing_lessdef. eapply preg_vals; eauto. eexact H1.
  intros [a' [A B]]. rewrite (sp_val _ _ _ AG) in A.
  assert (Val.lessdef (rs src) (rs0 (preg_of src))). eapply preg_val; eauto.
  exploit Mem.storev_extends; eauto. intros [m2' [C D]].
  left; eapply exec_straight_steps; eauto.
  intros. simpl in TR.
  exploit transl_store_correct; eauto. intros [rs2 [P Q]].
  exists rs2; split. eauto.
  split. eapply agree_undef_regs; eauto.
  simpl; congruence.

- (* Mcall *)
  assert (f0 = f) by congruence.  subst f0.
  inv AT.
  assert (NOOV: list_length_z tf.(fn_code) <= Ptrofs.max_unsigned).
    eapply transf_function_no_overflow; eauto.
  destruct ros as [rf|fid]; simpl in H; monadInv H5.
+ (* Indirect call *)
  assert (rs rf = Vptr f' Ptrofs.zero).
    destruct (rs rf); try discriminate.
    revert H; predSpec Ptrofs.eq Ptrofs.eq_spec i Ptrofs.zero; intros; congruence.
  assert (rs0 x0 = Vptr f' Ptrofs.zero).
    exploit ireg_val; eauto. rewrite H5; intros LD; inv LD; auto.
  generalize (code_tail_next_int _ _ _ _ NOOV H6). intro CT1.
  assert (TCA: transl_code_at_pc ge (Vptr fb (Ptrofs.add ofs Ptrofs.one)) fb f c false tf x).
    econstructor; eauto.
  exploit return_address_offset_correct; eauto. intros; subst ra.
  left; econstructor; split.
  apply plus_one. eapply exec_step_internal. eauto.
  eapply functions_transl; eauto. eapply find_instr_tail; eauto.
  simpl. eauto.
  econstructor; eauto.
  econstructor; eauto.
  simpl. eapply agree_exten; eauto. intros. Simplifs.
  Simplifs. rewrite <- H2. auto.
+ (* Direct call *)
  generalize (code_tail_next_int _ _ _ _ NOOV H6). intro CT1.
  assert (TCA: transl_code_at_pc ge (Vptr fb (Ptrofs.add ofs Ptrofs.one)) fb f c false tf x).
    econstructor; eauto.
  exploit return_address_offset_correct; eauto. intros; subst ra.
  left; econstructor; split.
  apply plus_one. eapply exec_step_internal. eauto.
  eapply functions_transl; eauto. eapply find_instr_tail; eauto.
  simpl. unfold Genv.symbol_address. rewrite symbols_preserved. rewrite H. eauto.
  econstructor; eauto.
  econstructor; eauto.
  simpl. eapply agree_exten; eauto. intros. Simplifs.
  Simplifs. rewrite <- H2. auto.

- (* Mtailcall *)
  assert (f0 = f) by congruence.  subst f0.
  inv AT.
  assert (NOOV: list_length_z tf.(fn_code) <= Ptrofs.max_unsigned).
    eapply transf_function_no_overflow; eauto.
  rewrite (sp_val _ _ _ AG) in *. unfold load_stack in *.
  exploit Mem.loadv_extends. eauto. eexact H1. auto. simpl. intros [parent' [A B]].
  exploit Mem.loadv_extends. eauto. eexact H2. auto. simpl. intros [ra' [C D]].
  exploit lessdef_parent_sp; eauto. intros. subst parent'. clear B.
  exploit lessdef_parent_ra; eauto. intros. subst ra'. clear D.
  exploit Mem.free_parallel_extends; eauto. intros [m2' [E F]].
  destruct ros as [rf|fid]; simpl in H; monadInv H7.
+ (* Indirect call *)
  assert (rs rf = Vptr f' Ptrofs.zero).
    destruct (rs rf); try discriminate.
    revert H; predSpec Ptrofs.eq Ptrofs.eq_spec i Ptrofs.zero; intros; congruence.
  assert (rs0 x0 = Vptr f' Ptrofs.zero).
    exploit ireg_val; eauto. rewrite H7; intros LD; inv LD; auto.
  generalize (code_tail_next_int _ _ _ _ NOOV H8). intro CT1.
  left; econstructor; split.
  eapply plus_left. eapply exec_step_internal. eauto.
  eapply functions_transl; eauto. eapply find_instr_tail; eauto.
  simpl. replace (chunk_of_type Tptr) with Mptr in * by (unfold Tptr, Mptr; destruct Archi.ptr64; auto).
  rewrite C. rewrite A. rewrite <- (sp_val _ _ _ AG). rewrite E. eauto.
  apply star_one. eapply exec_step_internal.
  transitivity (Val.offset_ptr rs0#PC Ptrofs.one). auto. rewrite <- H4. simpl. eauto.
  eapply functions_transl; eauto. eapply find_instr_tail; eauto.
  simpl. eauto. traceEq.
  econstructor; eauto.
  apply Mem.nextblock_free in E. congruence.
  apply Mem.nextblock_free in E.
    eapply valid_blockv_nextblock; eauto.
    eapply valid_blockv_lt; eauto.
    rewrite E. apply Block.le_refl.
  apply agree_set_other; auto. apply agree_nextinstr. apply agree_set_other; auto.
  eapply agree_change_sp; eauto. eapply parent_sp_def; eauto.
  Simplifs. rewrite Pregmap.gso; auto.
  generalize (preg_of_not_SP rf). rewrite (ireg_of_eq _ _ EQ1). congruence.
+ (* Direct call *)
  generalize (code_tail_next_int _ _ _ _ NOOV H8). intro CT1.
  left; econstructor; split.
  eapply plus_left. eapply exec_step_internal. eauto.
  eapply functions_transl; eauto. eapply find_instr_tail; eauto.
  simpl. replace (chunk_of_type Tptr) with Mptr in * by (unfold Tptr, Mptr; destruct Archi.ptr64; auto).
  rewrite C. rewrite A. rewrite <- (sp_val _ _ _ AG). rewrite E. eauto.
  apply star_one. eapply exec_step_internal.
  transitivity (Val.offset_ptr rs0#PC Ptrofs.one). auto. rewrite <- H4. simpl. eauto.
  eapply functions_transl; eauto. eapply find_instr_tail; eauto.
  simpl. eauto. traceEq.
  econstructor; eauto.
  apply Mem.nextblock_free in E. congruence.
  apply Mem.nextblock_free in E.
    eapply valid_blockv_nextblock; eauto.
    eapply valid_blockv_lt; eauto.
    rewrite E. apply Block.le_refl.
  apply agree_set_other; auto. apply agree_nextinstr. apply agree_set_other; auto.
  eapply agree_change_sp; eauto. eapply parent_sp_def; eauto.
  rewrite Pregmap.gss. unfold Genv.symbol_address. rewrite symbols_preserved. rewrite H. auto.

- (* Mbuiltin *)
  inv AT. monadInv H4.
  exploit functions_transl; eauto. intro FN.
  generalize (transf_function_no_overflow _ _ H3); intro NOOV.
  exploit builtin_args_match; eauto. intros [vargs' [P Q]].
  exploit external_call_mem_extends; eauto.
  intros [vres' [m2' [A [B [C D]]]]].
  left. econstructor; split. apply plus_one.
  eapply exec_step_builtin. eauto. eauto.
  eapply find_instr_tail; eauto.
  erewrite <- sp_val by eauto.
  eapply eval_builtin_args_preserved with (ge1 := ge); eauto. exact symbols_preserved.
  eapply external_call_symbols_preserved; eauto. apply senv_preserved. auto.
  eauto.
  econstructor; eauto.
  apply Mem.unchanged_on_nextblock in D. eapply Block.le_trans; eassumption.
  instantiate (2 := tf); instantiate (1 := x).
  unfold nextinstr_nf, nextinstr. rewrite Pregmap.gss.
  rewrite undef_regs_other. rewrite set_res_other. rewrite undef_regs_other_2.
  rewrite <- H1. simpl. econstructor; eauto.
  eapply code_tail_next_int; eauto.
  rewrite preg_notin_charact. intros. auto with asmgen.
  auto with asmgen.
  simpl; intros. intuition congruence.
  apply external_call_nextblock in A. eapply valid_blockv_nextblock; eauto.
  apply agree_nextinstr_nf. eapply agree_set_res; auto.
  eapply agree_undef_regs; eauto. intros; apply undef_regs_other_2; auto.
  congruence.

- (* Mgoto *)
  assert (f0 = f) by congruence. subst f0.
  inv AT. monadInv H4.
  exploit find_label_goto_label; eauto. intros [tc' [rs' [GOTO [AT2 INV]]]].
  left; exists (State rs' m' (Some sp0)); split.
  apply plus_one. econstructor; eauto.
  eapply functions_transl; eauto.
  eapply find_instr_tail; eauto.
  simpl; eauto.
  econstructor; eauto.
  eapply agree_exten; eauto with asmgen.
  congruence.

- (* Mcond true *)
  assert (f0 = f) by congruence. subst f0.
  exploit eval_condition_lessdef. eapply preg_vals; eauto. eauto. eauto. intros EC.
  left; eapply exec_straight_steps_goto; eauto.
  intros. simpl in TR.
  destruct (transl_cond_correct sp0 tge tf cond args _ _ rs0 m' TR)
  as [rs' [A [B C]]].
  rewrite EC in B.
  destruct (testcond_for_condition cond); simpl in *.
(* simple jcc *)
  exists (Pjcc c1 lbl); exists k; exists rs'.
  split. eexact A.
  split. eapply agree_exten; eauto.
  simpl. rewrite B. auto.
(* jcc; jcc *)
  destruct (eval_testcond c1 rs') as [b1|] eqn:TC1;
  destruct (eval_testcond c2 rs') as [b2|] eqn:TC2; inv B.
  destruct b1.
  (* first jcc jumps *)
  exists (Pjcc c1 lbl); exists (Pjcc c2 lbl :: k); exists rs'.
  split. eexact A.
  split. eapply agree_exten; eauto.
  simpl. rewrite TC1. auto.
  (* second jcc jumps *)
  exists (Pjcc c2 lbl); exists k; exists (nextinstr rs').
  split. eapply exec_straight_trans. eexact A.
  eapply exec_straight_one. simpl. rewrite TC1. auto. auto.
  split. eapply agree_exten; eauto.
  intros; Simplifs.
  simpl. rewrite eval_testcond_nextinstr. rewrite TC2.
  destruct b2; auto || discriminate.
(* jcc2 *)
  destruct (eval_testcond c1 rs') as [b1|] eqn:TC1;
  destruct (eval_testcond c2 rs') as [b2|] eqn:TC2; inv B.
  destruct (andb_prop _ _ H3). subst.
  exists (Pjcc2 c1 c2 lbl); exists k; exists rs'.
  split. eexact A.
  split. eapply agree_exten; eauto.
  simpl. rewrite TC1; rewrite TC2; auto.

- (* Mcond false *)
  exploit eval_condition_lessdef. eapply preg_vals; eauto. eauto. eauto. intros EC.
  left; eapply exec_straight_steps; eauto. intros. simpl in TR.
  destruct (transl_cond_correct sp0 tge tf cond args _ _ rs0 m' TR)
  as [rs' [A [B C]]].
  rewrite EC in B.
  destruct (testcond_for_condition cond); simpl in *.
(* simple jcc *)
  econstructor; split.
  eapply exec_straight_trans. eexact A.
  apply exec_straight_one. simpl. rewrite B. eauto. auto.
  split. apply agree_nextinstr. eapply agree_exten; eauto.
  simpl; congruence.
(* jcc ; jcc *)
  destruct (eval_testcond c1 rs') as [b1|] eqn:TC1;
  destruct (eval_testcond c2 rs') as [b2|] eqn:TC2; inv B.
  destruct (orb_false_elim _ _ H1); subst.
  econstructor; split.
  eapply exec_straight_trans. eexact A.
  eapply exec_straight_two. simpl. rewrite TC1. eauto. auto.
  simpl. rewrite eval_testcond_nextinstr. rewrite TC2. eauto. auto. auto.
  split. apply agree_nextinstr. apply agree_nextinstr. eapply agree_exten; eauto.
  simpl; congruence.
(* jcc2 *)
  destruct (eval_testcond c1 rs') as [b1|] eqn:TC1;
  destruct (eval_testcond c2 rs') as [b2|] eqn:TC2; inv B.
  exists (nextinstr rs'); split.
  eapply exec_straight_trans. eexact A.
  apply exec_straight_one. simpl.
  rewrite TC1; rewrite TC2.
  destruct b1. simpl in *. subst b2. auto. auto.
  auto.
  split. apply agree_nextinstr. eapply agree_exten; eauto.
  rewrite H1; congruence.

- (* Mjumptable *)
  assert (f0 = f) by congruence. subst f0.
  inv AT. monadInv H6.
  exploit functions_transl; eauto. intro FN.
  generalize (transf_function_no_overflow _ _ H5); intro NOOV.
  set (rs1 := rs0 #RAX <- Vundef #RDX <- Vundef).
  exploit (find_label_goto_label f tf lbl rs1); eauto.
  intros [tc' [rs' [A [B C]]]].
  exploit ireg_val; eauto. rewrite H. intros LD; inv LD.
  left; econstructor; split.
  apply plus_one. econstructor; eauto.
  eapply find_instr_tail; eauto.
  simpl. rewrite <- H9.  unfold Mach.label in H0; unfold label; rewrite H0. eexact A.
  econstructor; eauto.
Transparent destroyed_by_jumptable.
  apply agree_undef_regs with rs0; auto.
  simpl; intros. destruct H8. rewrite C by auto with asmgen. unfold rs1; Simplifs.
  congruence.

- (* Mreturn *)
  assert (f0 = f) by congruence. subst f0.
  inv AT.
  assert (NOOV: list_length_z tf.(fn_code) <= Ptrofs.max_unsigned).
    eapply transf_function_no_overflow; eauto.
  rewrite (sp_val _ _ _ AG) in *. unfold load_stack in *.
  replace (chunk_of_type Tptr) with Mptr in * by (unfold Tptr, Mptr; destruct Archi.ptr64; auto).
  exploit Mem.loadv_extends. eauto. eexact H0. auto. simpl. intros [parent' [A B]].
  exploit lessdef_parent_sp; eauto. intros. subst parent'. clear B.
  exploit Mem.loadv_extends. eauto. eexact H1. auto. simpl. intros [ra' [C D]].
  exploit lessdef_parent_ra; eauto. intros. subst ra'. clear D.
  exploit Mem.free_parallel_extends; eauto. intros [m2' [E F]].
  monadInv H6.
  exploit code_tail_next_int; eauto. intro CT1.
  pose (sp0' := if Val.eq (parent_sp s) sp0 then None else Some sp0).
  left. eexists (State _ _ sp0'). split.
  eapply plus_left. eapply exec_step_internal. eauto.
  eapply functions_transl; eauto. eapply find_instr_tail; eauto.
  simpl. rewrite C. rewrite A. rewrite <- (sp_val _ _ _ AG). rewrite E. eauto.
  apply star_one.
  assert (Hpc': nextinstr rs0 PC = Vptr fb (Ptrofs.add ofs Ptrofs.one)).
  {
    change (nextinstr rs0 PC) with (Val.offset_ptr rs0#PC Ptrofs.one).
    rewrite <- H3. reflexivity.
  }
  {
    destruct (Val.eq _ _) as [Hsp|Hsp] eqn:HHsp; subst sp0'.
    + econstructor; eauto.
      eapply functions_transl; eauto.
      eapply find_instr_tail; eauto.
    + eapply exec_step_internal; eauto.
      eapply functions_transl; eauto.
      eapply find_instr_tail; eauto.
      simpl. change (nextinstr _ RSP) with (parent_sp s). rewrite HHsp.
      reflexivity.
  }
  traceEq.
  {
    destruct STACKS.
    - simpl in sp0'.
      destruct (Val.eq _ _); [ | congruence].
      eapply match_states_final; eauto.
      apply Mem.nextblock_free in E; congruence.
      apply agree_set_other; auto.
      apply agree_nextinstr.
      apply agree_set_other; auto.
      eapply agree_change_sp; eauto.
    - simpl in sp0'.
      destruct (Val.eq _ _).
      eelim (block_lt_neq sp0 sp); eauto using init_sp_block_lt; fail.
      econstructor; eauto.
      apply Mem.nextblock_free in E; congruence.
      apply Mem.nextblock_free in E.
        eapply valid_blockv_nextblock; eauto.
        eapply valid_blockv_lt; eauto.
        rewrite E. eapply Block.le_refl.
      apply agree_set_other; auto.
      apply agree_nextinstr.
      apply agree_set_other; auto.
      eapply agree_change_sp; eauto.
      eapply block_lt_def; eauto.
  }

- (* internal function *)
  exploit functions_translated; eauto. intros [tf [A B]]. monadInv B.
  generalize EQ; intros EQ'. monadInv EQ'.
  destruct (zlt Ptrofs.max_unsigned (list_length_z (fn_code x0))); inv EQ1.
  monadInv EQ0. rewrite transl_code'_transl_code in EQ1.
  unfold store_stack in *.
  exploit Mem.alloc_extends. eauto. eauto. apply Z.le_refl. apply Z.le_refl.
  intros [m1' [C D]].
  exploit Mem.storev_extends. eexact D. eexact H1. eauto. eauto.
  intros [m2' [F G]].
  exploit Mem.storev_extends. eexact G. eexact H2. eauto. eauto.
  intros [m3' [P Q]].
  left; econstructor; split.
  apply plus_one. econstructor; eauto.
  simpl. rewrite Ptrofs.unsigned_zero. simpl. eauto.
  simpl. rewrite C. simpl in F, P.
  replace (chunk_of_type Tptr) with Mptr in F, P by (unfold Tptr, Mptr; destruct Archi.ptr64; auto).
  rewrite (sp_val _ _ _ AG) in F. rewrite F.
  rewrite ATLR. rewrite P. eauto.
  econstructor; eauto.
  {
    apply Mem.nextblock_alloc in C.
    apply Mem.nextblock_store in F.
    apply Mem.nextblock_store in P.
    replace (Mem.nextblock m3') with (Block.succ (Mem.nextblock m')) by congruence.
    blomega.
  }
  unfold nextinstr. rewrite Pregmap.gss. repeat rewrite Pregmap.gso; auto with asmgen.
  rewrite ATPC. simpl. constructor; eauto.
  unfold fn_code. eapply code_tail_next_int. simpl in g. omega.
  constructor.
  eapply alloc_sp_fresh; eauto.
  {
    apply Mem.nextblock_alloc in C.
    apply Mem.nextblock_store in F.
    apply Mem.nextblock_store in P.
    apply Mem.alloc_result in H0.
    subst stk sp.
    constructor.
    unfold Mem.valid_block.
    erewrite Mem.mext_next; eauto.
    replace (Mem.nextblock m3') with (Block.succ (Mem.nextblock m')) by congruence.
    blomega.
  }
  apply agree_nextinstr. eapply agree_change_sp; eauto.
Transparent destroyed_at_function_entry.
  apply agree_undef_regs with rs0; eauto.
  simpl; intros. apply Pregmap.gso; auto with asmgen. tauto.
  congruence.
  intros. Simplifs. eapply agree_sp; eauto.

- (* external function *)
  exploit functions_translated; eauto.
  intros [tf [A B]]. simpl in B. inv B.
  exploit extcall_arguments_match; eauto.
  intros [args' [C D]].
  exploit external_call_mem_extends; eauto.
  intros [res' [m2' [P [Q [R S]]]]].
  left; econstructor; split.
  apply plus_one. eapply exec_step_external; eauto.
  eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  destruct STACKS.
  + (* top-level return -- through tail call of external, presumably *)
    assert (Hsp: rs0 SP = sp0) by eauto using agree_sp.
    destruct (Val.eq _ _); [ | congruence].
    econstructor; eauto.
    apply Mem.unchanged_on_nextblock in S. eapply Block.le_trans; eauto.
    apply agree_set_other; auto. apply agree_set_pair; auto.
    apply agree_undef_caller_save_regs; auto. 
  + (* internal return *)
    simpl in AG. (*rewrite <- (agree_sp rs sp rs0 AG) in H4.*)
    destruct (Val.eq _ _).
    {
      rewrite (agree_sp rs sp rs0 AG) in e.
      eelim (block_lt_neq sp0 sp); eauto using init_sp_block_lt.
    }
    econstructor; eauto.
    apply Mem.unchanged_on_nextblock in S. eapply Block.le_trans; eauto.
    eapply valid_blockv_nextblock, Mem.unchanged_on_nextblock; eauto.
    apply agree_set_other; auto. apply agree_set_pair; auto.
    apply agree_undef_caller_save_regs; auto. 

- (* return *)
  simpl in *.
  right. split. omega. split. auto.
  econstructor; eauto. congruence.
Qed.

End IN_WORLD.

Lemma transf_initial_states:
  forall w q1 q2, match_query cc_asmgen w q1 q2 ->
  forall st1, Mach.initial_state ge q1 st1 ->
  exists st2, Asm.initial_state tge q2 st2 /\ match_states w st1 st2.
Proof.
  intros _ _ _ [fb ms m1 rs m2 sp Hsp Hpc Hra Hrs Hm].
  intros st1 Hst1. inv Hst1.
  exists (State rs m2 (Some sp)).
  pose proof Hrs as []; subst.
  split.
  - edestruct functions_translated as (tf & Htf & Hf); eauto.
    monadInv Hf.
    econstructor; eauto.
  - econstructor; eauto.
    simpl. apply Block.le_refl.
    simpl. constructor; eauto.
Qed.

Lemma transf_external:
  forall w st1 st2 q1,
    match_states w st1 st2 ->
    Mach.at_external ge st1 q1 ->
    exists wA q2,
      match_query cc_asmgen wA q1 q2 /\
      Asm.at_external tge st2 q2 /\
      forall r1 r2 st1',
        match_reply cc_asmgen wA r1 r2 ->
        Mach.after_external ge st1 r1 st1' ->
        exists st2',
          Asm.after_external st2 r2 st2' /\
          match_states w st1' st2'.
Proof.
  intros w st1 st2 q1 Hst Hst1.
  destruct w as [[sp0 ra0] nb0].
  destruct Hst1 as [fb id sg s ms m Hfb].
  inversion Hst; clear Hst. subst s0 fb0 m0 ms0 st2. cbn [fst snd] in *.
  edestruct match_cc_asmgen as (wA & Hq & H); eauto.
  - rewrite ATLR. eapply parent_ra_def; eauto.
  - rewrite ATLR in Hq.
    eexists _, _; intuition.
    + eauto.
    + edestruct functions_translated as (tf & Htf & Hftf); eauto.
      inv Hftf.
      econstructor; eauto.
    + inv Hq. destruct r1 as [rs1 m1], r2 as [rs2 m2].
      edestruct H as (Hpc' & Hrs' & Hm' & Hnb); eauto.
      inv H1.
      eexists; intuition.
      econstructor.
      erewrite agree_sp; eauto.
      destruct STACKS; simpl in *.
      * destruct (Val.eq _ _); try congruence.
        constructor; eauto.
        simpl. eapply Block.le_trans; eauto.
        rewrite Hpc', ATLR. reflexivity.
      * destruct (Val.eq _ _).
        eelim (block_lt_neq sp0 sp); eauto using init_sp_block_lt.
        econstructor; eauto.
        simpl. eapply Block.le_trans; eauto.
        eapply valid_blockv_nextblock; eauto.
        rewrite Hpc', ATLR. reflexivity.
Qed.

Lemma transf_final_states:
  forall w st1 st2 r1, match_states w st1 st2 -> Mach.final_state st1 r1 ->
  exists r2, match_reply cc_asmgen w r1 r2 /\ Asm.final_state tge st2 r2.
Proof.
  intros [[ra0 sp0] nb0] st1 st2 r1 Hst Hr1.
  destruct Hr1. inv Hst. simpl in *.
  eexists (_, _). split; econstructor; eauto.
Qed.

Theorem transf_program_correct:
  forward_simulation cc_asmgen cc_asmgen
    (Mach.semantics return_address_offset prog)
    (Asm.semantics tprog).
Proof.
  eapply forward_simulation_star with (measure := measure).
  apply senv_preserved.
  { destruct 1. cbn. rewrite H0.
    apply (Genv.block_is_internal_transf_partial TRANSF).
    clear. intros. destruct f, tf; try discriminate. auto. }
  eexact transf_initial_states.
  eexact transf_external.
  eexact transf_final_states.
  intros. apply step_simulation; auto.
Qed.

End PRESERVATION.
