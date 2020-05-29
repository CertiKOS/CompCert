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

Lemma fold_left_acc_symb_acc:
  forall defs stbl dofs cofs stbl' dofs' cofs',
    fold_left (acc_symb sec_data_id sec_code_id) defs (stbl, dofs, cofs) = (stbl', dofs', cofs') ->
    forall se,
      In se stbl -> In se stbl'.
Proof.
  induction defs; simpl; intros; eauto. inv H; auto.
  repeat destr_in H.
  eapply IHdefs. eauto. right. auto.
Qed.

Lemma gen_symb_table_ok:
  forall id d defs defs1 defs2 stbl dofs cofs stbl' dofs' cofs',
    defs = defs1 ++ (id, d) :: defs2 ->
    list_norepet (map fst defs) ->
    fold_left (acc_symb sec_data_id sec_code_id) defs (stbl, dofs, cofs) = (stbl', dofs', cofs') ->
    exists dofs1 cofs1 stbl1,
      fold_left (acc_symb sec_data_id sec_code_id) defs1 (stbl, dofs, cofs) = (stbl1, dofs1, cofs1) /\
      In (get_symbentry sec_data_id sec_code_id dofs1 cofs1 id d) stbl'.
Proof.
  induction defs; simpl; intros defs1 defs2 stbl dofs cofs stbl' dofs' cofs' SPLIT NR FL; eauto.
  - apply (f_equal (@length _)) in SPLIT.
    rewrite app_length in SPLIT. simpl in SPLIT. omega.
  - repeat destr_in FL.
    destruct (ident_eq i id).
    + subst.
      assert (defs1 = []). destruct defs1. auto. simpl in SPLIT. inv SPLIT.
      simpl in NR.
      inv NR.
      exfalso; apply H2. rewrite map_app. rewrite in_app. right. simpl. auto. subst.
      simpl in *. inv SPLIT.
      (do 3 eexists); split; eauto.
      eapply fold_left_acc_symb_acc. eauto. left; auto.
    + destruct defs1. simpl in SPLIT. inv SPLIT. congruence.
      simpl in SPLIT. inv SPLIT.
      edestruct IHdefs as (dofs1 & cofs1 & stbl1 & FL1 & IN1). eauto.
      inv NR. auto. eauto.
      simpl. rewrite Heqp0.
      setoid_rewrite FL1.
      (do 3 eexists); split; eauto.
Qed.

Lemma symb_table_ok:
  forall id d defs dofs cofs stbl defs1 defs2,
    defs = defs1 ++ (id, d) :: defs2 ->
    list_norepet (map fst defs) ->
    gen_symb_table sec_data_id sec_code_id defs = (stbl, dofs, cofs) ->
    exists stbl1 dofs1 cofs1,
      gen_symb_table sec_data_id sec_code_id defs1 = (stbl1, dofs1, cofs1) /\
      In (get_symbentry sec_data_id sec_code_id dofs1 cofs1 id d) stbl.
Proof.
  intros.
  unfold gen_symb_table in H1. repeat destr_in H1.
  setoid_rewrite <- in_rev.
  eapply gen_symb_table_ok in Heqp; eauto.
  destruct Heqp as (dofs1 & cofs1 & stbl1 & FL1 & IN1).
  unfold gen_symb_table. setoid_rewrite FL1.
  (do 3 eexists); split; eauto.
Qed.

Lemma symb_table_ok':
  forall id d defs dofs cofs stbl,
    list_norepet (map fst defs) ->
    In (id, d) defs ->
    gen_symb_table sec_data_id sec_code_id defs = (stbl, dofs, cofs) ->
    exists dofs1 cofs1,
      In (get_symbentry sec_data_id sec_code_id dofs1 cofs1 id d) stbl.
Proof.
  intros.
  edestruct in_split as (defs1 & defs2 & SPLIT); eauto.
  edestruct symb_table_ok as (stbl1 & cofs1 & dofs1 & DST & IN); eauto.
Qed.

Section PRESERVATION.

Context `{external_calls_prf: ExternalCalls}.
Existing Instance inject_perm_all.

Local Existing Instance mem_accessors_default.


Variable prog: Asm.program.
Variable tprog: program.

Let ge := Genv.globalenv prog.
Let tge := globalenv tprog.

Definition match_prog (p: Asm.program) (tp: program) :=
  transf_program p = OK tp.

Hypothesis TRANSF: match_prog prog tprog.


(** ** Definitions for matching  states *)

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
        Genv.find_instr tge (Vptr b' (Ptrofs.add (Ptrofs.repr ofs') ofs)) = Some i;

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
      forall b f ofs b',
        Globalenvs.Genv.find_funct_ptr ge b = Some (Internal f) ->
        j b = Some (b', ofs) ->
        Genv.find_ext_funct tge (Vptr b' (Ptrofs.repr ofs)) = None;
  }.

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

(** The internal step preserves the invariant *)
Lemma exec_instr_step : forall j rs1 rs2 m1 m2 rs1' m1' i id ofs f b
                        (MINJ: Mem.inject j (def_frame_inj m1) m1 m2)
                        (MATCHSMINJ: match_inj j)
                        (RSINJ: regset_inject j rs1 rs2)
                        (GBVALID: glob_block_valid m1),
    rs1 PC = Vptr b ofs ->
    Globalenvs.Genv.find_symbol ge id = Some b ->
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
Admitted.

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
