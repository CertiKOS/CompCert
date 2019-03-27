(* ******************* *)
(* Author: Pierre Wilke *)
(* Date:   Jul 5, 2018 *)
(* ******************* *)

(** Correctness proof for the FlatAsm generation **)

Require Import Coqlib Integers Values Maps AST.
Require Import Memtype Memory.
Require Import Smallstep.
Require Import Asm MC MCgen.
Require Import FlatAsm FlatAsmBuiltin FlatAsmProgram.
Require Import Segment.
Require Import Events.
Require Import StackADT.
Require Import Linking Errors.
Require Import Globalenvs FlatAsmGlobenv.
Require Import AsmFacts.
Require Import Num.

Open Scope Z_scope.


Section WITHMEMORYMODEL.

  Context `{external_calls_ops : ExternalCalls }.
  Existing Instance Asm.mem_accessors_default.
  Existing Instance FlatAsm.mem_accessors_default.
  Existing Instance inject_perm_all.

Definition match_prog (p: FlatAsm.program) (tp: MC.program) :=
  transf_program p = OK tp.

Section PRESERVATION.

Variable prog: FlatAsm.program.
Variable tprog: MC.program.
Hypothesis TRANSF: match_prog prog tprog.

Let ge := globalenv prog.
Let tge := globalenv tprog.

  Inductive match_states : Asm.state -> Asm.state -> Prop :=
  | match_states_intro m rs:
      match_states (State m rs) (State m rs).


  Lemma alloc_global_transl:
    forall lmap d d' m m',
      transl_globdef lmap d = OK d' ->
      alloc_global m d = Some m' ->
      alloc_global m d' = Some m'.
  Proof.
    intros lmap d d' m m' TG AG.
    destruct d as ((i & od) & sg).
    unfold transl_globdef in TG.
    repeat destr_in TG; auto.
    monadInv H0. simpl in *; auto.
  Qed.

  Lemma alloc_globals_transl:
    forall lmap d d' m m',
      transl_globdefs lmap d = OK d' ->
      alloc_globals m d = Some m' ->
      alloc_globals m d' = Some m'.
  Proof.
    induction d; simpl; intros d' m m' TG AG.
    - inv TG; inv AG. reflexivity.
    - destr_in AG. monadInv TG. simpl.
      erewrite alloc_global_transl; eauto.
  Qed.

  Lemma add_global_symb:
    forall ge1 ge2
      (SSYMB : forall i : ident, Genv.genv_symb ge1 i = Genv.genv_symb ge2 i)
      (NB : Genv.genv_next ge1 = Genv.genv_next ge2)
      lmap a x (EQ : transl_globdef lmap a = OK x),
    forall i0 : ident, Genv.genv_symb (add_global ge1 a) i0 = Genv.genv_symb (add_global ge2 x) i0.
  Proof.
    unfold add_global; simpl; intros.
    repeat (destr; simpl in *; auto).
    monadInv EQ. monadInv EQ.
  Qed.

  Lemma add_global_next:
    forall ge1 ge2
      (NB : Genv.genv_next ge1 = Genv.genv_next ge2)
      lmap a x (EQ : transl_globdef lmap a = OK x),
      Genv.genv_next (add_global ge1 a) = Genv.genv_next (add_global ge2 x).
  Proof.
    unfold add_global; simpl; intros.
    repeat (destr; simpl in *; auto).
    repeat destr_in EQ.
  Qed.

  Lemma add_globals_symb:
    forall lmap d d' (TG: transl_globdefs lmap d = OK d')
      ge1 ge2 (SSYMB: forall i, Genv.genv_symb ge1 i = Genv.genv_symb ge2 i)
      (NB: Genv.genv_next ge1 = Genv.genv_next ge2)
    ,
    forall i, Genv.genv_symb (add_globals ge1 d) i = Genv.genv_symb (add_globals ge2 d') i.
  Proof.
    induction d; simpl; intros; eauto. inv TG. simpl. auto.
    monadInv TG.
    simpl.
    apply IHd. eauto.
    eapply add_global_symb; eauto.
    eapply add_global_next; eauto.
  Qed.

  Lemma symbol_address_same:
    forall i o,
      Genv.symbol_address ge i o = Genv.symbol_address tge i o.
  Proof.
    unfold Genv.symbol_address, Genv.find_symbol.
    unfold ge, tge. unfold globalenv. simpl.
    unfold match_prog, transform_program in TRANSF. monadInv TRANSF.
    intros. erewrite add_globals_symb; eauto.
  Qed.

  Lemma store_init_data_transl:
    forall ld m b o m',
      store_init_data ge m b o ld = Some m' ->
      store_init_data tge m b o ld = Some m'.
  Proof.
    destruct ld; simpl; intros; eauto.
    erewrite <- symbol_address_same; eauto.
  Qed.

  Lemma store_init_data_list_transl:
    forall ld m b o m',
      store_init_data_list ge m b o ld = Some m' ->
      store_init_data_list tge m b o ld = Some m'.
  Proof.
    induction ld; simpl; intros; eauto.
    destr_in H.
    erewrite store_init_data_transl; eauto.
  Qed.

  Lemma store_global_transl:
    forall lmap n sb d d' m m',
      transl_globdef lmap d = OK d' ->
      store_global ge n sb m d = Some m' ->
      store_global tge n sb m d' = Some m'.
  Proof.
    intros lmap n sb d d' m m' TG SG.
    destruct d as ((i & od) & sg).
    unfold transl_globdef in TG.
    repeat destr_in TG; auto.
    - monadInv H0. simpl in *; auto.
    - simpl in *.
      repeat destr_in SG.
      erewrite store_init_data_list_transl; eauto.
  Qed.

  Lemma store_globals_iter_transl:
    forall lmap sb d d' n m m',
      transl_globdefs lmap d = OK d' ->
      store_globals_iter ge n sb m d = Some m' ->
      store_globals_iter tge n sb m d' = Some m'.
  Proof.
    induction d; simpl; intros d' n m m' TG SG.
    - inv TG; inv SG. reflexivity.
    - destr_in SG. monadInv TG. simpl.
      erewrite store_global_transl; eauto.
  Qed.

  Lemma store_globals_transl:
    forall lmap sb d d' m m',
      transl_globdefs lmap d = OK d' ->
      store_globals ge sb m d = Some m' ->
      store_globals tge sb m d' = Some m'.
  Proof.
    unfold store_globals. intros.
    eapply store_globals_iter_transl; eauto.
  Qed.


Lemma transf_initial_states :
  forall rs st1,
    FlatAsm.initial_state prog rs st1  ->
    exists st2, MC.initial_state tprog rs st2 /\ match_states st1 st2.
Proof.
  intros rs st1 INIT.
  generalize TRANSF. intros TRANSF'.
  generalize store_globals_transl. intro SGT.
  generalize symbol_address_same. intro SAS.
  unfold match_prog in TRANSF'. unfold transform_program in TRANSF'.
  monadInv TRANSF'.
  exists st1; split.
  inv INIT. econstructor.
  - unfold init_mem in H |- *.
    simpl in *. repeat destr_in H.
    erewrite alloc_globals_transl; eauto.
  - inv H0.
    unfold rs0. erewrite SAS.
    econstructor; eauto.
  - destruct st1; constructor.
Qed.




Lemma eval_addrmode32_same:
  forall am rs,
    eval_addrmode32 ge am rs = eval_addrmode32 tge am rs.
Proof.
  unfold eval_addrmode, eval_addrmode64, eval_addrmode32.
  intros.
  repeat (destr; rewrite ? symbol_address_same; auto).
Qed.

Lemma eval_addrmode64_same:
  forall am rs,
    eval_addrmode64 ge am rs = eval_addrmode64 tge am rs.
Proof.
  unfold eval_addrmode, eval_addrmode64, eval_addrmode32.
  intros.
  repeat (destr; rewrite ? symbol_address_same; auto).
Qed.

Lemma eval_addrmode_same:
  forall am rs,
    eval_addrmode ge am rs = eval_addrmode tge am rs.
Proof.
  unfold eval_addrmode; destr; intros.
  eapply eval_addrmode64_same.
  eapply eval_addrmode32_same.
Qed.

Lemma exec_load_step:
  forall ch m am rs pr o,
    exec_load ge ch m am rs pr o = exec_load tge ch m am rs pr o.
Proof.
  unfold exec_load.
  intros; erewrite eval_addrmode_same; eauto.
Qed.

Lemma exec_store_step:
  forall ch m am rs pr lpr o,
    exec_store ge ch m am rs pr lpr o = exec_store tge ch m am rs pr lpr o.
Proof.
  unfold exec_store.
  intros; erewrite eval_addrmode_same; eauto.
Qed.

Lemma acc_instrs_map_codeblock:
  forall I smap b ofs i sb id code acc
    (SMAP:   smap code_segid = code_block)
    (INIT: forall i sb id, acc b ofs = Some (i, sb, id) -> b = code_block /\ segblock_id sb = code_segid /\ segblock_start sb = ofs)
    (CODE: Forall (fun '(i,sb,id) => segblock_id sb = code_segid) code)
    (AIM : @acc_instrs_map I smap code acc b ofs = Some (i, sb, id)),
    b = code_block /\ segblock_id sb = code_segid /\ segblock_start sb = ofs.
Proof.
  induction code; simpl; intros; eauto.
  unfold acc_instr_map in AIM. destr_in AIM.
  - inv AIM. unfold get_instr_ptr in e.
    unfold Genv.label_to_ptr in e. simpl in e. inv e. 
    inv CODE. rewrite H1. auto.
  - eapply IHcode; eauto. inv CODE; auto.
Qed.

Lemma code_segid_segid_code_seg:
  code_segid = segid (code_seg prog).
Proof.
  unfold match_prog, transf_program in TRANSF.
  monadInv TRANSF. auto.
Qed.

Lemma code_segid_not_segid_data_seg:
  code_segid <> segid (data_seg prog).
Proof.
  unfold match_prog, transf_program in TRANSF.
  monadInv TRANSF. auto.
Qed.

Hypothesis lmap_code_seg:
  forall id l s0 i,
    lbl_map prog id l = Some (s0, i) -> s0 = code_segid.

Lemma check_faprog_true: check_faprog prog = true.
Proof.
  unfold match_prog, transf_program in TRANSF.
  monadInv TRANSF. auto.
Qed.

Lemma wf_faprog:
  Forall
    (fun '(i, d, _) =>
       forall f : function,
         d = Some (Gfun (Internal f)) ->
         Forall (fun '(ins, sb1, ii) => segblock_id sb1 = code_segid /\ i = ii /\ is_valid_label (lbl_map prog) (ins,sb1,ii)) (fn_code f) /\
         list_norepet (map (get_instr_ptr (gen_segblocks prog)) (fn_code f))
    )
    (prog_defs prog).
Proof.
  assert (C := check_faprog_true).
  unfold check_faprog in C.
  rewrite forallb_forall in C.
  rewrite Forall_forall. intros x IN.
  specialize (C _ IN).
  destruct x as [[id og] sb].
  unfold check_fadef in C.
  intros f EQ. subst.
  rewrite andb_true_iff in C. destruct C as [A B].
  rewrite forallb_forall in A.
  unfold proj_sumbool in B. destr_in B. split; auto.
  rewrite Forall_forall. intros xx INN. repeat destr.
  specialize (A _ INN).
  unfold proj_sumbool in A. repeat destr_in A.
Qed.

Lemma prog_in_code_block:
  Forall
    (fun '(_, d, _) =>
       forall f : function,
         d = Some (Gfun (Internal f)) ->
         Forall (fun '(_, sb1, _) => segblock_id sb1 = code_segid) (fn_code f)) 
    (prog_defs prog).
Proof.
  eapply Forall_impl. 2: apply wf_faprog. intros [[ia d] sb] IN H f EQ.
  apply H in EQ.
  eapply Forall_impl. 2: apply EQ. simpl. intros. 
  repeat destr.
Qed.

  
Lemma labels_valid:
  Forall (fun '(_,o,_) =>
            forall f,
              o = Some (Gfun (Internal f)) ->
              Forall (is_valid_label (lbl_map prog)) (fn_code f)
         ) (prog_defs prog).
Proof.
  eapply Forall_impl. 2: apply wf_faprog. intros [[ia d] sb] IN H f EQ.
  apply H in EQ.
  eapply Forall_impl. 2: apply EQ. simpl. intros.
  repeat destr_in H1.
Qed.

Lemma code_lnr:
  Forall (fun '(_,o,_) =>
            forall f,
              o = Some (Gfun (Internal f)) ->
              list_norepet (map (get_instr_ptr (gen_segblocks prog)) (fn_code f))
         ) (prog_defs prog).
Proof.
  eapply Forall_impl. 2: apply wf_faprog. intros [[ia d] sb] IN H f EQ.
  apply H in EQ. destruct EQ; auto.
Qed.

Lemma ident_fun_correct:
  Forall
    (fun '(i,o,sb) =>
       forall f,
         o = Some (Gfun (Internal f)) ->
         Forall
           (fun '(_,ii) => i = ii)
           (fn_code f)
    )
    (prog_defs prog).
Proof.
  eapply Forall_impl. 2: apply wf_faprog. intros [[ia d] sb] IN H f EQ.
  apply H in EQ.
  eapply Forall_impl. 2: apply EQ. simpl. intros.
  repeat destr_in H1.
Qed.

Lemma Forall_app:
  forall {A} (P: A -> Prop) (l1 l2: list A),
    Forall P l1 ->
    Forall P l2 ->
    Forall P (l1 ++ l2).
Proof.
  induction 1; simpl; intros; eauto.
Qed.

Lemma genv_instrs_codeblock:
  forall b ofs i sb id,
    Forall (fun '(_,d,sb) => forall f,
                d = Some (Gfun (Internal f)) ->
                Forall (fun '(_,sb,_) => segblock_id sb = code_segid) (fn_code f)
           ) (prog_defs prog) ->
    Genv.genv_instrs ge b ofs = Some (i, sb, id) ->
    b = code_block /\ segblock_id sb = code_segid /\ segblock_start sb = ofs.
Proof.
  unfold ge. unfold globalenv. simpl. intros b ofs i sb id F GI.
  rewrite add_globals_pres_instrs in GI. simpl in GI.
  unfold gen_segblocks, list_of_segments in GI. simpl in GI.
  unfold gen_instrs_map in GI.
  eapply acc_instrs_map_codeblock. 4: eauto.
  cbv beta. rewrite pred_dec_false. rewrite pred_dec_true. reflexivity.
  apply code_segid_segid_code_seg.
  apply code_segid_not_segid_data_seg.
  simpl. inversion 1.
  unfold get_program_code.
  revert F. clear.
  generalize (prog_defs prog).
  induction l; simpl; intros; eauto.
  apply Forall_app; eauto.
  inv F. unfold get_def_code. repeat destr; try solve [constructor].
  apply H1.  auto.
  apply IHl. inv F; auto.
Qed.

Lemma genv_lbl_map:
  forall b, Genv.genv_lbl ge b =  lblmap_to_symbmap (gen_segblocks prog) (lbl_map prog) b.
Proof.
  unfold ge, globalenv.
  intros.
  rewrite add_globals_pres_lbl.
  simpl. reflexivity.  
Qed.

Lemma label_correct:
  forall (rs2: regset) b ofs i sb id
    (RPC : rs2 PC = Vptr b ofs)
    (FI : Genv.genv_instrs ge b ofs = Some (i, sb, id))
    l p
    (Heqo1 : lbl_map prog id l = Some p),
    Val.offset_ptr (rs2 PC)
                   (Ptrofs.add (Ptrofs.sub (snd p) (Ptrofs.add (segblock_start sb) (segblock_size sb)))
                               (segblock_size sb)) = Genv.label_address ge id l.
Proof.
  intros rs2 b ofs i sb id RPC FI l p Heqo0.
  unfold Genv.label_address. rewrite genv_lbl_map.
  unfold lblmap_to_symbmap. rewrite Heqo0.
  destruct p. simpl.
  exploit genv_instrs_codeblock. apply prog_in_code_block. eauto. intros (A & B & C). subst.
  rewrite RPC. simpl. apply lmap_code_seg in Heqo0. subst.
  unfold gen_segblocks. f_equal.
  Arguments ident_eq: simpl nomatch.
  simpl.
  rewrite pred_dec_false by apply code_segid_not_segid_data_seg.
  rewrite pred_dec_true by apply code_segid_segid_code_seg.
  reflexivity.

  rewrite Ptrofs.sub_add_opp.
  rewrite Ptrofs.neg_add_distr.
  rewrite ! Ptrofs.add_assoc.
  rewrite (Ptrofs.add_commut i0).
  rewrite <- ! (Ptrofs.add_assoc).
  rewrite Ptrofs.add_neg_zero.
  rewrite Ptrofs.add_zero_l.
  rewrite (Ptrofs.add_commut (Ptrofs.neg _)).
  rewrite Ptrofs.add_neg_zero.
  rewrite Ptrofs.add_zero_l. reflexivity.
Qed.

Lemma get_lbl_list_offset_ok:
  forall lmap id tbl sb tbl' o l,
    get_lbl_list_offset lmap id tbl sb = OK tbl' ->
    list_nth_z tbl o = Some l ->
    exists ofs,
      list_nth_z tbl' o = Some ofs /\ get_lbl_offset lmap id l sb = OK ofs.
Proof.
  induction tbl; simpl; intros; eauto.
  inv H0.
  monadInv H.
  destr_in H0. inv H0.
  simpl. eexists; split; eauto.
  simpl. rewrite pred_dec_false by auto. apply IHtbl. auto. auto.
Qed.

Lemma exec_instr_step : forall rs1 m1 rs2 m2
                          (MINJ: match_states (State rs1 m1) (State rs2 m2))
                          b ofs i i' rs1' m1',
    rs1 PC = Vptr b ofs ->
    Genv.find_instr ge (Vptr b ofs) = Some i ->
    FlatAsm.exec_instr ge i rs1 m1 = Next rs1' m1' ->
    transl_instr (lbl_map prog) (snd i) i = OK i' ->
    exists rs2' m2',
      MC.exec_instr tge i' rs2 m2 = Next rs2' m2' /\
      match_states (State rs1' m1') (State rs2' m2').
Proof.
  intros rs1 m1 rs2 m2 MINJ b ofs i i' rs1' m1' RPC FI EI TI.
  simpl in FI.
  destruct i as ((i & sb) & id). inv MINJ.
  destruct i; simpl in TI; inv TI; simpl in *; try (exists rs1', m1'; split; [auto|constructor]);
    try destr;
    rewrite <- ? symbol_address_same,
    <- ? exec_load_step,
    <- ? exec_store_step,
    <- ? eval_addrmode_same,
    <- ? eval_addrmode32_same,
    <- ? eval_addrmode64_same; eauto.
  - monadInv H0. monadInv EQ. simpl.
    unfold MC.goto_label. unfold goto_label in EI. inv EI. f_equal. f_equal.
    unfold get_lbl_offset in EQ0. destr_in EQ0. inv EQ0.
    eapply label_correct; eauto.
  - monadInv H0. monadInv EQ. simpl.
    repeat destr_in EI.
    unfold MC.goto_label. f_equal. f_equal.
    unfold get_lbl_offset in EQ0. destr_in EQ0. inv EQ0.
    eapply label_correct; eauto.
  - monadInv H0. monadInv EQ. simpl.
    repeat destr_in EI.
    unfold MC.goto_label. f_equal. f_equal.
    unfold get_lbl_offset in EQ0. destr_in EQ0. inv EQ0.
    eapply label_correct; eauto.
  - monadInv H0. monadInv EQ. simpl.
    repeat destr_in EI.
    unfold MC.goto_label. f_equal. f_equal.
    edestruct get_lbl_list_offset_ok as (ofs' & EQ & GLO). eauto. eauto.
    rewrite EQ.
    f_equal. f_equal.
    rewrite Pregmap.gso. rewrite Pregmap.gso.
    unfold get_lbl_offset in GLO. destr_in GLO. inv GLO.
    eapply label_correct; eauto.
    congruence. congruence.
  - inv EI. f_equal. f_equal. f_equal. destruct ros; simpl; auto.
    symmetry; apply symbol_address_same.
Qed.      

Lemma acc_instrs_map_app:
  forall {I} sbs l1 l2 acc b o,
    acc_instrs_map (I:=I) sbs (l1 ++ l2) acc b o =
    acc_instrs_map sbs l1 (acc_instrs_map sbs l2 acc) b o.
Proof.
  induction l1; simpl; intros; eauto.
  unfold acc_instr_map. destr.
Qed.

Lemma segblock_dec:
  forall s1 s2: segblock,
    { s1 = s2 } + { s1 <> s2 }.
Proof.
  destruct s1, s2; simpl.
  destruct (peq segblock_id segblock_id0).
  2: right; intro A; inv A; congruence.
  destruct (Ptrofs.eq_dec segblock_start segblock_start0).
  2: right; intro A; inv A; congruence.
  destruct (Ptrofs.eq_dec segblock_size segblock_size0).
  2: right; intro A; inv A; congruence.
  subst; left; reflexivity.
Qed.

Lemma instr_with_info_dec:
  forall {I} (Idec: forall i1 i2 : I, {i1 = i2} + {i1 <> i2}) (i1 i2 : instr_with_info (I:= I)),
    { i1 = i2 } + { i1 <> i2 }.
Proof.
  intros I Idec. destruct i1, i2.
  destruct p, p0.
  destruct (segblock_dec s s0). 2: right; intro A; inv A; congruence.
  destruct (peq i i0). 2: right; intro A; inv A; congruence.
  destruct (Idec i1 i2). 2: right; intro A; inv A; congruence.
  subst; left; reflexivity.
Qed.


Axiom asm_instruction_dec:
  forall i1 i2: Asm.instruction, {i1 = i2} + {i1 <> i2}.

Lemma testcond_dec:
  forall t1 t2: testcond, {t1 = t2} + {t1 <> t2}.
Proof.
  destruct t1, t2; first [right; intro A; inv A; congruence | left; auto ].
Qed.

Lemma instruction_dec:
  forall i1 i2: instruction, {i1 = i2} + {i1 <> i2}.
Proof.
  destruct i1, i2; try now (right; intro A; inv A).
  - destruct (Ptrofs.eq_dec ofs ofs0). 2: right; intro A; inv A; congruence.
    subst; left; auto.
  - destruct (Ptrofs.eq_dec ofs ofs0). 2: right; intro A; inv A; congruence.
    destruct (testcond_dec c c0). 2: right; intro A; inv A; congruence.
    subst; left; auto.
  - destruct (Ptrofs.eq_dec ofs ofs0). 2: right; intro A; inv A; congruence.
    destruct (testcond_dec c1 c0). 2: right; intro A; inv A; congruence.
    destruct (testcond_dec c2 c3). 2: right; intro A; inv A; congruence.
    subst; left; auto.
  - destruct (list_eq_dec Ptrofs.eq_dec tbl tbl0). 2: right; intro A; inv A; congruence.
    destruct (ireg_eq r r0). 2: right; intro A; inv A; congruence.
    subst; left; auto.
  - destruct (asm_instruction_dec i i0); [left; subst; auto | right; congruence].
Defined.

Lemma acc_instrs_map_not_in:
  forall {I} sbs l acc b o i,
    acc_instrs_map (I:=I) sbs l acc b o = Some i ->
    ~ In i l ->
    acc b o = Some i.
Proof.
  induction l; simpl; intros; eauto.
  unfold acc_instr_map in H. destr_in H. eauto.
Qed.

Lemma in_instrs_in_code:
  forall b o i,
    Genv.genv_instrs ge b o = Some i ->
    exists f id sb,
      In (id, Some (Gfun (Internal f)), sb) (prog_defs prog) /\ In i (fn_code f).
Proof.
  unfold ge. unfold globalenv. rewrite add_globals_pres_instrs. simpl.
  unfold gen_instrs_map. unfold get_program_code.
  generalize (gen_segblocks prog) as sbs.
  generalize (prog_defs prog). clear.
  induction l; simpl; intros; eauto. inv H.
  rewrite acc_instrs_map_app in H.
  destruct a. simpl in *.
  destruct p. destruct o0; simpl in *; eauto.
  destruct g; simpl in *.
  destruct f; simpl in *.
  - edestruct (in_dec (instr_with_info_dec asm_instruction_dec) i (fn_code f) ).
    + exists f, i0, s; split. left; auto. auto.
    + eapply acc_instrs_map_not_in in H; eauto.
      edestruct IHl as (ff & id & sb & IN & IN'). eauto.
      do 3 eexists; split; eauto.
  - edestruct IHl as (ff & id & sb & IN & IN'). eauto.
    do 3 eexists; split; eauto.
  - edestruct IHl as (ff & id & sb & IN & IN'). eauto.
    do 3 eexists; split; eauto.
  - edestruct IHl as (ff & id & sb & IN & IN'). eauto.
    do 3 eexists; split; eauto.
Qed.

Lemma find_instr_has_transl:
  forall p i,
    Genv.find_instr ge p = Some i ->
    exists i',
      transl_instr (lbl_map prog) (snd i) i = OK i'.
Proof.
  intros p i FI. destruct p; simpl in FI; try solve [inv FI].
  edestruct (in_instrs_in_code _ _ _ FI) as (f & id & sb & INdefs & INcode).
  assert (labels_valid:=labels_valid).
  rewrite Forall_forall in labels_valid. apply labels_valid in INdefs.
  specialize (INdefs _ eq_refl).
  rewrite Forall_forall in INdefs. apply INdefs in INcode.
  destruct i as ((ii & sbb) & idd). simpl in *.
  destruct ii; simpl; eauto.
  - unfold get_lbl_offset.
    destruct (lbl_map prog idd l) as [[? ?]|] eqn:LBL; try congruence.
    simpl. eauto.
  - unfold get_lbl_offset.
    destruct (lbl_map prog idd l) as [[? ?]|] eqn:LBL; try congruence.
    simpl. eauto.
  - unfold get_lbl_offset.
    destruct (lbl_map prog idd l) as [[? ?]|] eqn:LBL; try congruence.
    simpl. eauto.
  - revert INcode. generalize tbl. clear.
    induction 1; simpl; intros; eauto.
    unfold get_lbl_offset. destruct (lbl_map prog idd x) as [[? ?]|] eqn:LBL; try congruence.
    simpl.
    destruct IHINcode as (i' & TR).
    monadInv TR. monadInv EQ.
    rewrite EQ0. simpl. eauto.
Qed.

Lemma gen_segblocks_same:
  gen_segblocks tprog = gen_segblocks prog.
Proof.
  unfold match_prog, transf_program in TRANSF.
  monadInv TRANSF. unfold gen_segblocks. simpl. auto.
Qed.

Lemma code_segid_same:
  code_seg tprog = code_seg prog.
Proof.
  unfold match_prog, transf_program in TRANSF.
  monadInv TRANSF. simpl. auto.
Qed.


Lemma data_segid_same:
  data_seg tprog = data_seg prog.
Proof.
  unfold match_prog, transf_program in TRANSF.
  monadInv TRANSF. simpl. auto.
Qed.

Lemma acc_instrs_map_in:
  forall {I} (Idec: forall i1 i2: I, {i1 = i2} + {i1 <> i2}) (a: @instr_with_info I) sbs l acc b o,
    In a l ->
    (forall b o a, acc b o = Some a -> ~ In a l) ->
    acc_instrs_map sbs l acc b o = Some a ->
    get_instr_ptr sbs a = Vptr b o (* \/ acc b o = Some a *).
Proof.
  induction l; simpl; intros; eauto. easy.
  unfold acc_instr_map in H1. destr_in H1.
  destruct (in_dec (instr_with_info_dec Idec) a l).
  - eapply IHl; eauto. intros. intro IN. edestruct H0; eauto.
  - destruct H; try congruence. subst.
    apply acc_instrs_map_not_in in H1; eauto.
    apply H0 in H1. tauto.
Qed.

Lemma acc_instrs_map_in':
  forall {I} (Idec: forall i1 i2: I, {i1 = i2} + {i1 <> i2}) (a: @instr_with_info I) sbs l acc b o
    (IN: In a l)
    (LNR: list_norepet (map (get_instr_ptr sbs) l))
    (GIP: get_instr_ptr sbs a = Vptr b o),
    acc_instrs_map sbs l acc b o = Some a.
Proof.
  induction l; simpl; intros; eauto. easy.
  unfold acc_instr_map.
  destruct (in_dec (instr_with_info_dec Idec) a l).
  - erewrite IHl; eauto. destr.
    rewrite <- e in LNR. inv LNR.
    exfalso; apply H1. apply in_map_iff.
    eexists; split; eauto. inv LNR; auto.
  - destruct IN; try congruence. subst.
    rewrite GIP. destr.
Qed.


Lemma acc_instrs_map_not_in':
  forall {I} sbs l acc b o,
    ~ In (Vptr b o) (map (get_instr_ptr sbs) l) ->
    acc_instrs_map (I:=I) sbs l acc b o = acc b o.
Proof.
  induction l; simpl; intros; eauto.
  unfold acc_instr_map. destr; eauto. 
Qed.

Lemma acc_instrs_map_get_instr_ptr:
  forall {I} sbs b o (a: @instr_with_info I) l acc,
    (forall b o, acc b o = Some a -> get_instr_ptr sbs a = Vptr b o) ->
    acc_instrs_map sbs l acc b o = Some a ->
    get_instr_ptr sbs a = Vptr b o.
Proof.
  induction l; simpl; intros; eauto.
  unfold acc_instr_map in H0. destr_in H0; eauto.
Qed.

Lemma acc_instrs_map_in_list:
  forall {I} (Idec: forall i1 i2: I, {i1 = i2} + {i1 <> i2})
    sbs l acc b o (a x: @instr_with_info I)
    (LNRCODE: list_norepet (map (get_instr_ptr sbs) l))
    (AIM: acc_instrs_map sbs l acc b o = Some a)
    (IN: In x l)
    (GIP: get_instr_ptr sbs x = Vptr b o),
    a = x.
Proof.
  induction l; simpl; intros; eauto.
  easy.
  inv LNRCODE.
  unfold acc_instr_map in AIM.
  destr_in AIM. inv AIM.
  destruct IN; auto.
  exfalso; apply H1.  rewrite <- e. rewrite in_map_iff.
  eexists; split; eauto.
  destruct IN. subst; congruence.
  eapply IHl; eauto.
Qed.

Lemma relate_instrs:
  forall {I1 I2} (Idec1: forall i1 i2: I1, {i1 = i2} + {i1 <> i2})
    (Idec1: forall i1 i2: I2, {i1 = i2} + {i1 <> i2}) sbs R d1 d2
    (LF: list_forall2 (fun '(_,o1,_) '(_,o2,_) =>
                         match o1 with
                         | Some (Gfun (Internal f1)) =>
                           match o2 with
                           | Some (Gfun (Internal f2)) =>
                             list_forall2 R (fn_code f1) (fn_code f2)
                           | _ => False
                           end
                         | _ =>  match o2 with
                           | Some (Gfun (Internal f2)) => False
                           | _ => True
                           end
                         end
                      ) d1 d2)
    (LNRCODE: Forall (fun '(_,o1,_) =>
                         match o1 with
                         | Some (Gfun (Internal f1)) =>
                           list_norepet (map (get_instr_ptr sbs) (fn_code f1))
                         | _ => True
                         end) d1)
     (LNRCODE': Forall (fun '(_,o1,_) =>
                         match o1 with
                         | Some (Gfun (Internal f1)) =>
                           list_norepet (map (get_instr_ptr sbs) (fn_code f1))
                         | _ => True
                         end) d2)
    a1 a2 acc1 acc2 b o
    (REC: forall a1 a2 b o, acc1 b o = Some a1 -> R a1 a2 -> acc2 b o = Some a2)
    (ACC_OK:   forall a0 (b2 : block) (o2 : ptrofs), acc1 b2 o2 = Some a0 -> get_instr_ptr sbs a0 = Vptr b2 o2
)
    (DET: forall a b1 b2, R a b1 -> R a b2 -> b1 = b2)
    (RGIP: forall a b, R a b -> get_instr_ptr sbs a = get_instr_ptr sbs b)
    (REL: R a1 a2)
    (AIM: acc_instrs_map (I:= I1) sbs (get_defs_code d1) acc1 b o = Some a1),
    acc_instrs_map (I:= I2) sbs (get_defs_code d2) acc2 b o = Some a2.
Proof.
  assert (code_lnr:=code_lnr).
  clear - code_lnr.

  induction 3; simpl; intros; eauto.
  rewrite acc_instrs_map_app in AIM.
  destruct a1 as ((ida1 & od1) & sb1). simpl in *.
  destruct od1; simpl in *; eauto.
  destruct g; simpl in *; eauto.
  destruct f; simpl in *; eauto.
  repeat (destr_in H; try easy; [idtac]). simpl.
  -
    assert (SAMEMAP: map (get_instr_ptr sbs) (fn_code f) = map (get_instr_ptr sbs) (fn_code f1)).
    {
      clear - H RGIP.
      revert H.
      generalize (fn_code f) (fn_code f1).
      induction 1; simpl; intros; eauto. f_equal; eauto.
    }
    rewrite acc_instrs_map_app.
    exploit @acc_instrs_map_get_instr_ptr. 2: eauto.
    intros; eapply acc_instrs_map_get_instr_ptr. 2: eauto. eauto. intro GIP.
    inv LNRCODE. inv LNRCODE'.
    edestruct (in_dec Val.eq (Vptr b o) (map (get_instr_ptr sbs) (fn_code f)) ).
    + rewrite in_map_iff in i0.
      destruct i0 as (x & GIP' & IN).
      exploit @acc_instrs_map_in_list. auto. apply H2. eauto. eauto. auto. intro; subst.
      edestruct list_forall2_in_left as (a22 & INN & PP). apply H. apply IN.
      exploit DET. apply REL. apply PP. intro A; subst.
      apply acc_instrs_map_in'; auto.
      erewrite <- RGIP. eauto. eauto.
    + eapply acc_instrs_map_not_in in AIM; eauto.
      rewrite acc_instrs_map_not_in'; eauto.
      rewrite <- SAMEMAP. auto.
      intro IN. apply n. clear n. rewrite in_map_iff.
      eexists; split; eauto.
  - inv LNRCODE. inv LNRCODE'. repeat destr_in H; simpl; eauto.
  - inv LNRCODE. inv LNRCODE'. repeat destr_in H; simpl; eauto.
  - inv LNRCODE. inv LNRCODE'. repeat destr_in H; simpl; eauto.
Qed.

Lemma same_instr_ptr_transl_instr:
  forall lmap sbs i c x,
    transl_instr lmap i c = OK x ->
    get_instr_ptr sbs c = get_instr_ptr sbs x.
Proof.
  intros. destruct c. destruct p.
  destruct i; simpl in H; monadInv H; simpl; try reflexivity.
Qed.

Lemma same_instr_ptr_transl_instrs:
  forall lmap sbs i c x,
    transl_instrs lmap i c = OK x ->
    map (get_instr_ptr sbs) c = map (get_instr_ptr sbs) x.
Proof.
  induction c; simpl; intros; eauto; monadInv H; simpl; auto.
  f_equal; eauto.
  destruct a. destruct p.
  destruct i1; simpl in EQ; monadInv EQ; simpl; try reflexivity.
Qed.

Lemma lnr_transl_instrs:
  forall lmap sbs i c x,
    list_norepet (map (get_instr_ptr sbs) c) ->
    transl_instrs lmap i c = OK x ->
    list_norepet (map (get_instr_ptr sbs) x).
Proof.
  intros. erewrite <- same_instr_ptr_transl_instrs; eauto.
Qed.

Lemma lnr_code_transl:
  forall lmap d x,
    Forall
      (fun '(_, o, _) =>
         forall f : function,
           o = Some (Gfun (Internal f)) ->
           list_norepet (map (get_instr_ptr (gen_segblocks prog)) (fn_code f)))
      d ->
    transl_globdefs lmap d = OK x ->
    Forall
      (fun '(_, o, _) =>
         forall f : function,
           o = Some (Gfun (Internal f)) ->
           list_norepet (map (get_instr_ptr (gen_segblocks prog)) (fn_code f)))
      x.
Proof.
  induction d; simpl; intros; eauto.
  - inv H0. constructor.
  - monadInv H0. inv H. repeat destr_in H2.
    constructor; eauto. repeat destr.
    intros; subst.
    unfold transl_globdef in EQ.
    repeat destr_in EQ.
    specialize (H2 _ eq_refl). monadInv H0.
    unfold transl_fun in EQ. monadInv EQ. simpl.
    eapply lnr_transl_instrs; eauto.
Qed.


Lemma find_instr_transl_find_instr:
  forall p i i',
    Genv.find_instr ge p = Some i ->
    transl_instr (lbl_map prog) (snd i) i = OK i' ->
    Genv.find_instr tge p = Some i'.
Proof.
  intros p i i' FI TR.
  unfold Genv.find_instr in FI |-*. destr.
  revert FI.
  unfold ge, tge, globalenv.
  rewrite ! add_globals_pres_instrs. simpl.
  rewrite gen_segblocks_same.
  unfold gen_instrs_map.
  unfold get_program_code.
  unfold match_prog, transf_program in TRANSF.
  eapply relate_instrs with (R := fun i1 i2 => transl_instr (lbl_map prog) (snd i1) i1 = OK i2); eauto.
  - apply asm_instruction_dec.
  - apply instruction_dec.
  - assert (ident_fun_correct := ident_fun_correct).
    monadInv TRANSF. simpl.
    revert EQ ident_fun_correct.
    generalize (prog_defs prog) x.
    clear.
    induction l; simpl; intros; eauto.
    inv EQ. constructor.
    monadInv EQ. inv ident_fun_correct0. constructor; eauto.
    repeat (destr; simpl in *; auto).
    subst.
    monadInv EQ0. specialize (H1 _ eq_refl).
    {
      clear - EQ1 H1.
      unfold transl_fun in EQ1. monadInv EQ1.
      revert EQ H1. simpl.
      generalize (fn_code f0) x.
      induction c; simpl; intros; eauto; monadInv EQ; constructor; inv H1; eauto.
      destr_in H2. subst. eauto.
    }
    monadInv EQ0.
    monadInv EQ0.
    monadInv EQ0.
  - generalize code_lnr. apply Forall_impl. intros a IN. repeat destr.
    intro A; apply A. auto.
  - eapply Forall_impl. 2: eapply lnr_code_transl.
    intros a IN. repeat destr.
    intro A; apply A. auto.
    eapply code_lnr. monadInv TRANSF. eauto.
  - congruence.
  - congruence.
  - congruence.
  - intros; eapply same_instr_ptr_transl_instr; eauto.
Qed.

Lemma codeblock_same:
  forall b,
    Genv.genv_internal_codeblock tge b = Genv.genv_internal_codeblock ge b.
Proof.
  intros; unfold ge, tge, globalenv.
  rewrite ! genv_internal_codeblock_add_globals. simpl.
  unfold gen_segblocks. unfold gen_internal_codeblock.
  unfold list_of_segments. simpl.
  rewrite code_segid_same.
  rewrite data_segid_same. reflexivity.
Qed.

Lemma add_global_genv_senv:
  forall {I} (ge: genv) l,
    Genv.genv_senv (add_global (I:=I) ge l) = Genv.genv_senv ge.
Proof.
  intros.
  destruct l. destruct p. simpl. auto.
Qed.

Lemma add_globals_genv_senv:
  forall {I} l (ge: genv),
    Genv.genv_senv (add_globals (I:=I) ge l) = Genv.genv_senv ge.
Proof.
  induction l; simpl; intros; eauto.
  rewrite IHl. apply add_global_genv_senv.
Qed.

Lemma senv_equiv:
  Senv.equiv (Genv.genv_senv ge) (Genv.genv_senv tge).
Proof.
  unfold ge, tge, globalenv. rewrite ! add_globals_genv_senv. simpl.
  unfold match_prog in TRANSF. monadInv TRANSF. simpl.
  repeat apply conj; auto.
Qed.

Lemma eval_builtin_arg_preserved:
  forall {I1 I2 A} (ge : genv (I:= I1)) (tge: genv (I:=I2)) (e: A -> val) sp m al vl (EQ: forall i o, Genv.symbol_address tge i o = Genv.symbol_address ge i o),
    FlatAsmBuiltin.eval_builtin_arg _ _ _ _ ge e sp m al vl ->
    FlatAsmBuiltin.eval_builtin_arg _ _ _ _ tge e sp m al vl.
Proof.
  induction 2; simpl; intros; try econstructor; rewrite ?EQ; eauto.
  rewrite <- EQ. econstructor.
Qed.

Lemma eval_builtin_args_preserved:
  forall {I1 I2 A} (ge : genv (I:= I1)) (tge: genv (I:=I2)) (e: A -> val) sp m al vl (EQ: forall i o, Genv.symbol_address tge i o = Genv.symbol_address ge i o),
    FlatAsmBuiltin.eval_builtin_args _ _ _ _ ge e sp m al vl ->
    FlatAsmBuiltin.eval_builtin_args _ _ _ _ tge e sp m al vl.
Proof.
  induction 2; constructor; eauto using eval_builtin_arg_preserved.
Qed.


Lemma genv_defs_add_globals_rel:
  forall lmap f b o defs tdefs (ge: genv (I:= Asm.instruction)) (tge : genv (I := instruction))
    (REC: Genv.genv_defs ge b o = Some (Gfun (External f)) ->
          Genv.genv_defs tge b o = Some (Gfun (External f)))
    (NB: Genv.genv_next ge = Genv.genv_next tge),
    Genv.genv_defs (add_globals ge defs) b o = Some (Gfun (External f)) ->
    transl_globdefs lmap defs = OK tdefs ->
    Genv.genv_defs (add_globals tge tdefs) b o = Some (Gfun (External f)).
Proof.
  induction defs; simpl; intros; eauto.
  - inv H0. simpl. auto.
  - monadInv H0.
    simpl. eapply IHdefs. 3: apply H.
    + unfold add_global. destruct a as [[a bb] c].
      destruct x as [[x y] z]. simpl.
      simpl in EQ. repeat destr_in EQ.
      monadInv H1. auto. rewrite NB. destr. auto.
      rewrite NB. destr.
    + unfold add_global. repeat destr; simpl; try congruence.
    + auto.
Qed.

Lemma find_funct_ptr_transf:
  forall b ofs f,
    Genv.find_funct_ptr ge b ofs = Some (External f) ->
    Genv.find_funct_ptr tge b ofs = Some (External f).
Proof.
  unfold Genv.find_funct_ptr. intros b ofs f FD.
  repeat destr_in FD.
  unfold ge, tge, globalenv in Heqo |- *.
  unfold Genv.find_def in *.
  unfold match_prog, transf_program in TRANSF.
  monadInv TRANSF. simpl in *. clear - Heqo EQ.
  eapply genv_defs_add_globals_rel in Heqo; eauto.
  rewrite Heqo. auto. simpl. congruence.
  simpl. auto.
Qed.


Theorem step_simulation:
  forall S1 t S2,
    FlatAsm.step ge S1 t S2 ->
    forall S1' (MS: match_states S1 S1'),
    exists S2',
      MC.step tge S1' t S2' /\
      match_states S2 S2'.
Proof.
  destruct 1; intros; inv MS.

  - (* Internal step *)
    edestruct find_instr_has_transl as (i' & TRANSL). eauto.
    edestruct exec_instr_step as (rs2' & m2' & EI' & MS); eauto. constructor.
    
    eexists; split; [| econstructor; eauto].
    eapply MC.exec_step_internal; eauto.
    erewrite codeblock_same; eauto.
    eapply find_instr_transl_find_instr; eauto. inv MS. auto.
        
  - (* Builtin *)
    edestruct find_instr_has_transl as (i' & TRANSL). eauto.
    exploit find_instr_transl_find_instr; eauto. intro FI'.
    simpl in TRANSL. inv TRANSL.
    
    eexists; split; [| econstructor; eauto].
    eapply MC.exec_step_builtin; eauto.
    erewrite codeblock_same; eauto.
    eauto.
    eapply eval_builtin_args_preserved.
    intros. symmetry.
    apply symbol_address_same. eauto.
    eapply external_call_symbols_preserved. apply senv_equiv. eauto.
  - (* External call *)
    simpl in H1.
    exploit find_funct_ptr_transf. eauto. intro FFP.
    eexists; split; [|econstructor; eauto].
    eapply MC.exec_step_external; eauto.
    erewrite codeblock_same; eauto.
    eapply external_call_symbols_preserved. apply senv_equiv. eauto.
Qed.

Lemma transf_final_states:
  forall st1 st2 r,
  match_states st1 st2 -> FlatAsm.final_state st1 r -> MC.final_state st2 r.
Proof.
  intros st1 st2 r MATCH FINAL.
  inv FINAL. inv MATCH. constructor; auto.
Qed.
  
Theorem transf_program_correct:
  forward_simulation (FlatAsm.semantics prog (Pregmap.init Vundef)) (MC.semantics tprog (Pregmap.init Vundef)).
Proof.
  eapply forward_simulation_step with match_states.
  - simpl. intros. 
    unfold match_prog in TRANSF. unfold transf_program in TRANSF.
    apply senv_equiv.
  - simpl. intros s1 IS. 
    exploit transf_initial_states; eauto.
  - simpl. intros s1 s2 r MS FS. eapply transf_final_states; eauto.
  - simpl. intros s1 t s1' STEP s2 MS. 
    edestruct step_simulation as (STEP' & MS'); eauto.
Qed.

End PRESERVATION.


End WITHMEMORYMODEL.