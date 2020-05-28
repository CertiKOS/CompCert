(* *******************  *)
(* Author: Yuting Wang  *)
(* Date:   Dec 2, 2019 *)
(* *******************  *)

Require Import Coqlib Errors.
Require Import Integers Floats AST Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Op Locations Mach Conventions Asm RealAsm.
Require Import Symbtablegen.
Require Import RelocProgram RelocProgSemantics.
Import ListNotations.
Require AsmFacts.

Open Scope Z_scope.

Ltac monadInvX1 H :=
  let monadInvX H :=  
      monadInvX1 H ||
                 match type of H with
                 | (?F _ _ _ _ _ _ _ _ = OK _) =>
                   ((progress simpl in H) || unfold F in H); monadInvX1 H
                 | (?F _ _ _ _ _ _ _ = OK _) =>
                   ((progress simpl in H) || unfold F in H); monadInvX1 H
                 | (?F _ _ _ _ _ _ = OK _) =>
                   ((progress simpl in H) || unfold F in H); monadInvX1 H
                 | (?F _ _ _ _ _ = OK _) =>
                   ((progress simpl in H) || unfold F in H); monadInvX1 H
                 | (?F _ _ _ _ = OK _) =>
                   ((progress simpl in H) || unfold F in H); monadInvX1 H
                 | (?F _ _ _ = OK _) =>
                   ((progress simpl in H) || unfold F in H); monadInvX1 H
                 | (?F _ _ = OK _) =>
                   ((progress simpl in H) || unfold F in H); monadInvX1 H
                 | (?F _ = OK _) =>
                   ((progress simpl in H) || unfold F in H); monadInvX1 H
                 end
  in

  match type of H with
  | (OK _ = OK _) =>
      inversion H; clear H; try subst
  | (Error _ = OK _) =>
      discriminate
  | (bind ?F ?G = OK ?X) =>
      let x := fresh "x" in (
      let EQ1 := fresh "EQ" in (
      let EQ2 := fresh "EQ" in (
      destruct (bind_inversion F G H) as [x [EQ1 EQ2]];
      clear H;
      try (monadInvX EQ1);
      try (monadInvX1 EQ2))))
  | (bind2 ?F ?G = OK ?X) =>
      let x1 := fresh "x" in (
      let x2 := fresh "x" in (
      let EQ1 := fresh "EQ" in (
      let EQ2 := fresh "EQ" in (
      destruct (bind2_inversion F G H) as [x1 [x2 [EQ1 EQ2]]];
      clear H;
      try (monadInvX EQ1);
      try (monadInvX1 EQ2)))))
  | (match ?X with left _ => _ | right _ => assertion_failed end = OK _) =>
      destruct X eqn:?; [try (monadInvX1 H) | discriminate]
  | (match (negb ?X) with true => _ | false => assertion_failed end = OK _) =>
      destruct X as [] eqn:?; [discriminate | try (monadInvX1 H)]
  | (match ?X with true => _ | false => assertion_failed end = OK _) =>
      destruct X as [] eqn:?; [try (monadInvX1 H) | discriminate]
  | (mmap ?F ?L = OK ?M) =>
      generalize (mmap_inversion F L H); intro
  | (match ?X with Some _ => _ | None => _ end = _) =>
      let EQ := fresh "EQ" in (
      destruct X eqn:EQ; try (monadInvX1 H))
  | (match ?X with pair _ _ => _ end = OK _) =>
      let EQ := fresh "EQ" in (
      destruct X eqn:EQ; try (monadInvX1 H))
  end.

Ltac monadInvX H :=
  monadInvX1 H ||
  match type of H with
  | (?F _ _ _ _ _ _ _ _ = OK _) =>
      ((progress simpl in H) || unfold F in H); monadInvX1 H
  | (?F _ _ _ _ _ _ _ = OK _) =>
      ((progress simpl in H) || unfold F in H); monadInvX1 H
  | (?F _ _ _ _ _ _ = OK _) =>
      ((progress simpl in H) || unfold F in H); monadInvX1 H
  | (?F _ _ _ _ _ = OK _) =>
      ((progress simpl in H) || unfold F in H); monadInvX1 H
  | (?F _ _ _ _ = OK _) =>
      ((progress simpl in H) || unfold F in H); monadInvX1 H
  | (?F _ _ _ = OK _) =>
      ((progress simpl in H) || unfold F in H); monadInvX1 H
  | (?F _ _ = OK _) =>
      ((progress simpl in H) || unfold F in H); monadInvX1 H
  | (?F _ = OK _) =>
      ((progress simpl in H) || unfold F in H); monadInvX1 H
  end.  

Lemma alignw_le : forall x, x <= align x alignw.
Proof.
  intros x. apply align_le. unfold alignw. omega.
Qed.


Lemma divides_align : forall y x,
    y > 0 -> (y | x) -> align x y = x.
Proof.
  intros y x GT DV.
  unfold align. red in DV. destruct DV as [z DV].
  subst. replace (z * y + y - 1) with (z * y + (y - 1)) by omega.
  erewrite Int.Zdiv_shift; eauto.
  erewrite Z_div_mult; eauto. rewrite Z_mod_mult.
  rewrite zeq_true. rewrite Z.add_0_r. auto.
Qed.

Lemma align_idempotent : forall v x,
    x > 0 -> align (align v x) x = align v x.
Proof.
  intros v x H. eapply divides_align; eauto.
  apply align_divides. auto.
Qed.

Lemma alignw_divides:
  forall z,
    (alignw | align z alignw).
Proof.
  intros. apply align_divides. unfold alignw; omega.
Qed.


(** Properties about Symbol Environments *)
Lemma add_external_global_pres_senv :
  forall e (ge : Genv.t) extfuns,
  Genv.genv_senv (add_external_global extfuns ge e) = Genv.genv_senv ge.
Proof.
  intros. unfold add_external_global.
  destr.
Qed.

Lemma add_external_globals_pres_senv :
  forall stbl (ge : Genv.t) extfuns,
  Genv.genv_senv (add_external_globals extfuns ge stbl) = Genv.genv_senv ge.
Proof.
  induction stbl; intros.
  - simpl. auto.
  - simpl. erewrite IHstbl; eauto.
    rewrite add_external_global_pres_senv. auto.
Qed.

Lemma transf_prog_pres_senv: forall p tp,
  transf_program p = OK tp -> 
  Globalenvs.Genv.to_senv (Globalenvs.Genv.globalenv p) = Genv.genv_senv (globalenv tp).
Proof.
  intros p tp TF.
  unfold transf_program in TF.
  destr_in TF. destr_in TF.
  destruct p0.
  destr_in TF.
  inv TF. cbn.
  rewrite add_external_globals_pres_senv.
  cbn. auto.
Qed.




(** * Main Preservaiton Proofs *)
Section PRESERVATION.

Context `{external_calls_prf: ExternalCalls}.
Existing Instance inject_perm_all.

Local Existing Instance mem_accessors_default.

(** Default frame injection *)
Definition def_frame_inj m := (flat_frameinj (length (Mem.stack m))).

Lemma store_pres_def_frame_inj : forall chunk m1 b ofs v m1',
    Mem.store chunk m1 b ofs v = Some m1' ->
    def_frame_inj m1 = def_frame_inj m1'.
Proof.
  unfold def_frame_inj. intros.
  repeat erewrite Mem.push_new_stage_stack. simpl.
  exploit Mem.store_stack_blocks; eauto. intros. rewrite H0.
  auto.
Qed.

Lemma storev_pres_def_frame_inj : forall chunk m1 v1 v2 m1',
    Mem.storev chunk m1 v1 v2 = Some m1' ->
    def_frame_inj m1= def_frame_inj m1'.
Proof.
  intros until m1'. unfold Mem.storev.
  destruct v1; try congruence.
  intros STORE.
  eapply store_pres_def_frame_inj; eauto.
Qed.


Lemma store_mapped_inject' : 
  forall (f : meminj) (chunk : memory_chunk) 
    (m1 : mem) (b1 : block) (ofs : Z) (v1 : val) 
    (n1 m2 : mem) (b2 : block) (delta : Z) (v2 : val),
    Mem.inject f (def_frame_inj m1) m1 m2 ->
    Mem.store chunk m1 b1 ofs v1 = Some n1 ->
    f b1 = Some (b2, delta) ->
    Val.inject f v1 v2 ->
    exists n2 : mem,
      Mem.store chunk m2 b2 (ofs + delta) v2 = Some n2 /\
      Mem.inject f (def_frame_inj n1) n1 n2.
Proof.
  intros. exploit Mem.store_mapped_inject; eauto. 
  intros (n2 & STORE & MINJ).
  eexists. split. eauto.
  erewrite <- store_pres_def_frame_inj; eauto.
Qed.

Theorem storev_mapped_inject':
  forall f chunk m1 a1 v1 n1 m2 a2 v2,
  Mem.inject f (def_frame_inj m1) m1 m2 ->
  Mem.storev chunk m1 a1 v1 = Some n1 ->
  Val.inject f a1 a2 ->
  Val.inject f v1 v2 ->
  exists n2,
    Mem.storev chunk m2 a2 v2 = Some n2 /\ Mem.inject f (def_frame_inj n1) n1 n2.
Proof.
  intros. exploit Mem.storev_mapped_inject; eauto. 
  intros (n2 & STORE & MINJ).
  eexists. split. eauto.
  erewrite <- storev_pres_def_frame_inj; eauto.
Qed.


(** Assumption about external calls.
    These should be merged into common properties about external calls later. *)
Axiom external_call_inject : forall ge j vargs1 vargs2 m1 m2 m1' vres1 t ef,
    Val.inject_list j vargs1 vargs2 ->
    Mem.inject j (def_frame_inj m1) m1 m2 ->
    external_call ef ge vargs1 m1 t vres1 m1' ->
    exists j' vres2 m2',
      external_call ef ge vargs2 m2 t vres2 m2' /\
      Val.inject j' vres1 vres2 /\ Mem.inject j' (def_frame_inj m1') m1' m2' /\
      inject_incr j j' /\
      inject_separated j j' m1 m2.

Axiom  external_call_valid_block: forall ef ge vargs m1 t vres m2 b,
    external_call ef ge vargs m1 t vres m2 -> Mem.valid_block m1 b -> Mem.valid_block m2 b.


(** Transformation *)
Variable prog: Asm.program.
Variable tprog: program.

Let ge := Genv.globalenv prog.
Let tge := globalenv tprog.

Definition match_prog (p: Asm.program) (tp: program) :=
  transf_program p = OK tp.

Hypothesis TRANSF: match_prog prog tprog.

  

(** ** Definitions of Matching States *)

Definition glob_block_valid (m:mem) := 
  forall b g, Globalenvs.Genv.find_def ge b = Some g -> Mem.valid_block m b.

Definition regset_inject (j:meminj) (rs rs' : regset) : Prop :=
  forall r, Val.inject j (rs r) (rs' r).

(** Properties about the memory injection from RealAsm to Relocatable Programs *)   Record match_inj (j: meminj) : Type :=
  {
    (** Preservation of finding of instruction *)
    agree_inj_instrs:
      forall b b' f ofs ofs' i,
        Globalenvs.Genv.find_funct_ptr ge b = Some (Internal f) -> 
        Asm.find_instr (Ptrofs.unsigned ofs) (Asm.fn_code f) = Some i ->
        j b = Some (b', ofs') -> 
        Genv.find_instr tge (Vptr b' (Ptrofs.add ofs (Ptrofs.repr ofs'))) = Some i;

    (** Preservation of finding of global symbols *)
    agree_inj_globs:
      forall id b,
        Globalenvs.Genv.find_symbol ge id = Some b ->
        exists b' ofs', Genv.find_symbol tge id = Some (b', ofs') /\
                   j b = Some (b', Ptrofs.unsigned ofs');

    (** Preservation of finding of external functions *)
    agree_inj_ext_funct:
      forall b f ofs b',
        Globalenvs.Genv.find_funct_ptr ge b = Some (External f) ->
        j b = Some (b', ofs) ->
        Genv.find_ext_funct tge (Vptr b' (Ptrofs.repr ofs)) = Some f;

    (** Preservation of finding of internal functions *)
    agree_inj_int_funct:
      forall b f ofs b' ofs',
        Globalenvs.Genv.find_funct_ptr ge b = Some (Internal f) ->
        j b = Some (b', ofs) ->
        Genv.find_ext_funct tge (Vptr b' ofs') = None;
  }.


(** Match States *)
Inductive match_states: state -> state -> Prop :=
| match_states_intro: forall (j:meminj) (rs: regset) (m: mem) (rs': regset) (m':mem)
                        (MINJ: Mem.inject j (def_frame_inj m) m m')
                        (MATCHINJ: match_inj j)
                        (RSINJ: regset_inject j rs rs')
                        (GBVALID: glob_block_valid m),
    match_states (State rs m) (State rs' m').


(** ** Matching of the Initial States *)
Lemma transf_initial_states : forall rs (SELF: forall j, forall r : PregEq.t, Val.inject j (rs r) (rs r)) st1,
    RealAsm.initial_state prog rs st1  ->
    exists st2, initial_state tprog rs st2 /\ match_states st1 st2.
Proof.
  Admitted.


(** ** Simulation of Single Step Execution *)

Lemma eval_builtin_args_inject : forall j m m' rs rs' sp sp' args vargs
    (MATCHINJ: match_inj j)
    (MINJ: Mem.inject j (def_frame_inj m) m m')
    (RSINJ: regset_inject j rs rs')
    (VINJ: Val.inject j sp sp')
    (EVALBI: Events.eval_builtin_args ge rs sp m args vargs),
    exists vargs', eval_builtin_args _ tge rs' sp' m' args vargs' /\
             Val.inject_list j vargs vargs'.
Proof.
Admitted.

Lemma inject_pres_match_sminj : 
  forall j j' m1 m2 (ms: match_inj j), 
    glob_block_valid m1 -> inject_incr j j' -> inject_separated j j' m1 m2 -> 
    match_inj j'.
Proof.
Admitted.

Lemma regset_inject_incr : forall j j' rs rs',
    regset_inject j rs rs' ->
    inject_incr j j' ->
    regset_inject j' rs rs'.
Proof.
  unfold inject_incr, regset_inject. intros.
  specialize (H r).
  destruct (rs r); inversion H; subst; auto.
  eapply Val.inject_ptr. apply H0. eauto. auto.
Qed.

Lemma undef_regs_pres_inject : forall j rs rs' regs,
  regset_inject j rs rs' ->
  regset_inject j (Asm.undef_regs regs rs) (Asm.undef_regs regs rs').
Proof.
  unfold regset_inject. intros. apply AsmFacts.val_inject_undef_regs.
  auto.
Qed.    

Lemma Pregmap_gsspec_alt : forall (A : Type) (i j : Pregmap.elt) (x : A) (m : Pregmap.t A),
    (m # j <- x) i  = (if Pregmap.elt_eq i j then x else m i).
Proof.
  intros. apply Pregmap.gsspec.
Qed.

Lemma regset_inject_expand : forall j rs1 rs2 v1 v2 r,
  regset_inject j rs1 rs2 ->
  Val.inject j v1 v2 ->
  regset_inject j (rs1 # r <- v1) (rs2 # r <- v2).
Proof.
  intros. unfold regset_inject. intros.
  repeat rewrite Pregmap_gsspec_alt. 
  destruct (Pregmap.elt_eq r0 r); auto.
Qed.

Lemma set_res_pres_inject : forall res j rs1 rs2,
    regset_inject j rs1 rs2 ->
    forall vres1 vres2,
    Val.inject j vres1 vres2 ->
    regset_inject j (set_res res vres1 rs1) (set_res res vres2 rs2).
Proof.
  induction res; auto; simpl; unfold regset_inject; intros.
  - rewrite Pregmap_gsspec_alt. destruct (Pregmap.elt_eq r x); subst.
    + rewrite Pregmap.gss. auto.
    + rewrite Pregmap.gso; auto.
  - exploit (Val.hiword_inject j vres1 vres2); eauto. intros. 
    exploit (Val.loword_inject j vres1 vres2); eauto. intros.
    apply IHres2; auto.
Qed.

Lemma set_pair_pres_inject : forall j rs1 rs2 v1 v2 loc,
    regset_inject j rs1 rs2 ->
    Val.inject j v1 v2 ->
    regset_inject j (set_pair loc v1 rs1) (set_pair loc v2 rs2).
Proof.
  intros. unfold set_pair, Asm.set_pair. destruct loc; simpl.
  - apply regset_inject_expand; auto.
  - apply regset_inject_expand; auto.
    apply regset_inject_expand; auto.
    apply Val.hiword_inject; auto.
    apply Val.loword_inject; auto.
Qed.

Lemma extcall_arguments_inject : forall rs1 rs2 m1 m2 ef args1 j,
    Asm.extcall_arguments rs1 m1 (ef_sig ef) args1 ->
    Mem.inject j (def_frame_inj m1) m1 m2 ->
    regset_inject j rs1 rs2 ->
    exists args2,
      Val.inject_list j args1 args2 /\
      Asm.extcall_arguments rs2 m2 (ef_sig ef) args2.
Proof.
Admitted.

(** The internal step preserves the invariant *)
Lemma exec_instr_step : forall j rs1 rs2 m1 m2 rs1' m1' i ofs f b
                        (MINJ: Mem.inject j (def_frame_inj m1) m1 m2)
                        (MATCHSMINJ: match_inj j)
                        (RSINJ: regset_inject j rs1 rs2)
                        (GBVALID: glob_block_valid m1),
    rs1 PC = Vptr b ofs ->
    Globalenvs.Genv.find_funct_ptr ge b = Some (Internal f) ->
    Asm.find_instr (Ptrofs.unsigned ofs) (Asm.fn_code f) = Some i ->
    RealAsm.exec_instr ge f i rs1 m1 = Next rs1' m1' ->
    exists rs2' m2',
      exec_instr tge i rs2 m2 = Next rs2' m2' /\
      match_states (State rs1' m1') (State rs2' m2').
Proof.
Admitted.

Theorem step_simulation:
  forall S1 t S2,
    RealAsm.step ge S1 t S2 ->
    forall S1' (MS: match_states S1 S1'),
    exists S2',
      step tge S1' t S2' /\
      match_states S2 S2'.
Proof.
  destruct 1; intros; inv MS.

  - (* Internal step *)
    unfold regset_inject in RSINJ. generalize (RSINJ Asm.PC). rewrite H. 
    inversion 1; subst.
    exploit (agree_inj_instrs j MATCHINJ b b2 f ofs delta i); eauto.
    intros FIND.
    exploit (exec_instr_step j rs rs'0 m m'0 rs' m' i); eauto.
    intros (rs2' & m2' & FEXEC & MS1).
    exists (State rs2' m2'). split; auto.
    eapply exec_step_internal; eauto.
    eapply (agree_inj_int_funct j MATCHINJ); eauto.
        
  - (* Builtin *)
    unfold regset_inject in RSINJ. generalize (RSINJ Asm.PC). rewrite H.
    inversion 1; subst.
    exploit (agree_inj_instrs j MATCHINJ b b2 f ofs delta (Asm.Pbuiltin ef args res)); auto.
    intros FIND.
    exploit (eval_builtin_args_inject j m m'0 rs rs'0 (rs Asm.RSP) (rs'0 Asm.RSP) args vargs); auto.
    intros (vargs' & EBARGS & ARGSINJ).
    assert (Globalenvs.Genv.to_senv ge = (Genv.genv_senv tge)) as SENVEQ. 
    { eapply transf_prog_pres_senv; eauto. }
    generalize (external_call_inject ge j vargs vargs' m m'0 m' vres t ef ARGSINJ MINJ H3).
    rewrite SENVEQ.
    intros (j' & vres2 & m2' & EXTCALL & RESINJ & MINJ' & INJINCR & INJSEP).
    set (rs' := nextinstr_nf (set_res res vres2 (undef_regs (map preg_of (Machregs.destroyed_by_builtin ef)) rs'0)) 
                             (Ptrofs.repr (instr_size (Pbuiltin ef args res)))).
    exploit (fun b ofs => exec_step_builtin tge b ofs
                                         ef args res rs'0  m'0 vargs' t vres2 rs' m2'); eauto. 
    eapply (agree_inj_int_funct j MATCHINJ); eauto.
    intros FSTEP. eexists; split; eauto.
    eapply match_states_intro with (j:=j'); eauto.
    (* Supposely the following propreties can proved by separation property of injections *)
    + eapply (inject_pres_match_sminj j); eauto.
    + subst rs'. intros. 
      assert (regset_inject j' rs rs'0) by 
          (eapply regset_inject_incr; eauto).
      set (dregs := (map Asm.preg_of (Machregs.destroyed_by_builtin ef))) in *.
      generalize (undef_regs_pres_inject j' rs rs'0 dregs H5). intros.
      set (rs1 := (Asm.undef_regs dregs rs)) in *.
      set (rs2 := (Asm.undef_regs dregs rs'0)) in *.
      generalize (fun h => set_res_pres_inject res j' 
                  rs1 rs2 h vres vres2 RESINJ).
      set (rs3 := (Asm.set_res res vres rs1)) in *.
      set (rs4 := (Asm.set_res res vres2 rs2)) in *.
      intros.
      admit. (* eauto with inject_db. *)
    + (* eapply extcall_pres_glob_block_valid; eauto. *)
      admit.

  - (* External call *)
    unfold regset_inject in RSINJ. generalize (RSINJ Asm.PC). rewrite H. 
    inversion 1; subst. rewrite Ptrofs.add_zero_l in H6.
    exploit Mem.loadv_inject. apply MINJ. apply LOADRA. eauto. intros (v2 & LRA & VI).
    edestruct (extcall_arguments_inject) as (args2 & ARGSINJ & EXTCALLARGS); eauto.
    apply regset_inject_expand. eauto.
    apply Val.offset_ptr_inject. eauto.
    assert (Globalenvs.Genv.to_senv ge = (Genv.genv_senv tge)) as SENVEQ. 
    { eapply transf_prog_pres_senv; eauto. }
    exploit (external_call_inject ge j args args2 ); eauto.
    rewrite SENVEQ.
    
    intros (j' & res' & m2'' & EXTCALL & RESINJ & MINJ' & INJINCR & INJSEP).
    exploit (fun ofs => exec_step_external tge b2 ofs ef args2 res'); eauto.
    eapply agree_inj_ext_funct; eauto.
    + intro; subst. inv VI. congruence.
    + intros FSTEP. eexists. split. apply FSTEP.
      eapply match_states_intro with (j := j'); eauto.
      * eapply (inject_pres_match_sminj j); eauto.
      * assert (regset_inject j' rs rs'0) by 
            (eapply regset_inject_incr; eauto).
        set (dregs := (map Asm.preg_of Conventions1.destroyed_at_call)) in *.
        generalize (undef_regs_pres_inject j' rs rs'0 dregs H4). intros.
        set (rs1 := (Asm.undef_regs dregs rs)) in *.
        set (rs2 := (Asm.undef_regs dregs rs'0)) in *.
        set (cdregs := (CR Asm.ZF :: CR Asm.CF :: CR Asm.PF :: CR Asm.SF :: CR Asm.OF :: nil)) in *.
        generalize (undef_regs_pres_inject j' rs1 rs2 cdregs). intros.
        set (rs3 := (Asm.undef_regs cdregs rs1)) in *.
        set (rs4 := (Asm.undef_regs cdregs rs2)) in *.
        generalize (set_pair_pres_inject j' rs3 rs4 res res' 
                                         (Asm.loc_external_result (ef_sig ef))).
        intros.
        apply regset_inject_expand; auto.
        apply regset_inject_expand; auto.
        apply regset_inject_expand; auto. eapply val_inject_incr; eauto.
        apply Val.offset_ptr_inject; eauto.
      * admit. (* eapply extcall_pres_glob_block_valid; eauto. *)
Admitted.


(** ** Matching of the Final States*)
Lemma transf_final_states:
  forall st1 st2 r,
  match_states st1 st2 -> Asm.final_state st1 r -> final_state st2 r.
Proof.
  intros st1 st2 r MATCH FINAL.
  inv FINAL. inv MATCH. constructor. 
  - red in RSINJ. generalize (RSINJ PC). rewrite H. 
    unfold Vnullptr. destruct Archi.ptr64; inversion 1; auto.
  - red in RSINJ. generalize (RSINJ RAX). rewrite H0.
    inversion 1. auto.
Qed.


(** ** The Main Correctness Theorem *)


Lemma transf_program_correct:
  forward_simulation (RealAsm.semantics prog (Pregmap.init Vundef)) 
                     (semantics tprog (Pregmap.init Vundef)).
Proof.
  intros. apply forward_simulation_step with match_states.
  - simpl. intros. 
    unfold match_prog in TRANSF. unfold transf_program in TRANSF.
    repeat destr_in TRANSF. cbn.
    rewrite add_external_globals_pres_senv. cbn. auto.
  - simpl. intros s1 IS. 
    exploit transf_initial_states; eauto.
    intros.
    rewrite Pregmap.gi. auto.
  - simpl. intros s1 s2 r MS FS. eapply transf_final_states; eauto.
  - simpl. intros s1 t s1' STEP s2 MS. 
    edestruct step_simulation as (STEP' & MS'); eauto.
Qed.


End PRESERVATION.
