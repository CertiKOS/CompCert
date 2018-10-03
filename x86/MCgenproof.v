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
  
Context `{memory_model: Mem.MemoryModel }.
Existing Instance inject_perm_all.


Definition match_prog (p: FlatAsm.program) (tp: MC.program) :=
  transl_prog p = OK tp.

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

  Lemma store_global_transl:
    forall lmap sb d d' m m',
      transl_globdef lmap d = OK d' ->
      store_global ge sb m d = Some m' ->
      store_global tge sb m d' = Some m'.
  Proof.
    intros lmap sb d d' m m' TG SG.
    destruct d as ((i & od) & sg).
    unfold transl_globdef in TG.
    repeat destr_in TG; auto.
    - monadInv H0. simpl in *; auto.
    - simpl in *.
      repeat destr_in SG.
  Admitted.

  Lemma store_globals_transl:
    forall lmap sb d d' m m',
      transl_globdefs lmap d = OK d' ->
      store_globals ge sb m d = Some m' ->
      store_globals tge sb m d' = Some m'.
  Proof.
    induction d; simpl; intros d' m m' TG SG.
    - inv TG; inv SG. reflexivity.
    - destr_in SG. monadInv TG. simpl.
      erewrite store_global_transl; eauto.
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
    unfold match_prog, transl_prog in TRANSF. monadInv TRANSF.
    intros. erewrite add_globals_symb; eauto.
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
  unfold match_prog in TRANSF'. unfold transl_prog in TRANSF'.
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


Context `{external_calls_ops : !ExternalCallsOps mem }.
Context `{!EnableBuiltins mem}.
Existing Instance Asm.mem_accessors_default.
Existing Instance FlatAsm.mem_accessors_default.


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

Hypothesis code_segid_segid_code_seg:
  code_segid = segid (code_seg prog).

Hypothesis code_segid_not_segid_data_seg:
  code_segid <> segid (data_seg prog).

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

Hypothesis prog_in_code_block:
  Forall
    (fun '(_, d, _) =>
       forall f : function,
         d = Some (Gfun (Internal f)) ->
         Forall (fun '(_, sb1, _) => segblock_id sb1 = code_segid) (fn_code f)) 
    (prog_defs prog).

Hypothesis lmap_code_seg:
  forall id l s0 i,
    lbl_map prog id l = Some (s0, i) -> s0 = code_segid.

Lemma label_correct:
  forall (rs2: regset) b ofs i sb id
    (RPC : rs2 PC = Vptr b ofs)
    (FI : Genv.genv_instrs ge b ofs = Some (i, sb, id))
    l p
    (Heqo1 : Genv.genv_lbl ge id l = Some p),
    Val.offset_ptr (rs2 PC)
                   (Ptrofs.add (Ptrofs.sub (snd p) (Ptrofs.add (segblock_start sb) (segblock_size sb)))
                               (segblock_size sb)) = Genv.label_address ge id l.
Proof.
  intros rs2 b ofs i sb id RPC FI l p Heqo0.
  unfold Genv.label_address. rewrite Heqo0.
  destruct p. simpl.
  unfold ge, globalenv in Heqo0.  rewrite add_globals_pres_lbl in Heqo0.
  simpl in Heqo0. unfold gen_segblocks in Heqo0. simpl in Heqo0.
  unfold lblmap_to_symbmap in Heqo0. repeat (destr_in Heqo0;[idtac]). inv Heqo0.
  rewrite RPC.
  simpl.
  exploit genv_instrs_codeblock. apply prog_in_code_block. eauto. intros (A & B & C). subst.
  f_equal.
  rewrite pred_dec_false.
  rewrite pred_dec_true. reflexivity.
  rewrite <- code_segid_segid_code_seg.
  eapply lmap_code_seg; eauto.
  erewrite (lmap_code_seg _ _ _ _ Heqo); eauto.
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
    transl_instr (Genv.genv_lbl ge) (snd i) i = OK i' ->
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
    <- ? eval_addrmode32_same; eauto.
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

Hypothesis labels_valid:
  Forall (fun '(_,o,_) =>
            forall f,
              o = Some (Gfun (Internal f)) ->
              Forall 
                (fun '(i,_,id) =>
                   match i with
                     Pjcc _ l
                   | Pjcc2 _ _ l
                   | Pjmp_l l => lbl_map prog l id <> None
                   | Pjmptbl _ ll =>
                     Forall (fun l => lbl_map prog l id <> None) ll
                   | _ => True
                   end)
                (fn_code f)
         ) (prog_defs prog).

Lemma find_instr_has_transl:
  forall p i,
    Genv.find_instr ge p = Some i ->
    exists i',
      transl_instr (Genv.genv_lbl ge) (snd i) i = OK i'.
Proof.
  intros p i FI. destruct p; simpl in FI; try solve [inv FI].
  destruct i as ((ii & sb) & id). simpl.
  destruct ii; simpl; eauto.


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
    edestruct exec_instr_step as (rs2' & m2' & EI' & MS); eauto. constructor.
    
    eexists; split; [| econstructor; eauto].
    eapply MC.exec_step_internal; eauto.
    unfold regset_inject in RSINJ. generalize (RSINJ Asm.PC). rewrite H. 
    inversion 1; subst.
    exploit (agree_inj_instr j MATCHSMINJ b b2 f ofs delta i); eauto.
    intros (id & i' & sid & ofs1 & FITARG & FSYMB & TRANSL).
    exploit (exec_instr_step j rs rs'0 m m'0 rs' m' i i' id); eauto.
    intros (rs2' & m2' & FEXEC & MS1).
    exists (State rs2' m2'). split; auto.
    eapply FlatAsm.exec_step_internal; eauto.
        
  - (* Builtin *)
    unfold regset_inject in RSINJ. generalize (RSINJ Asm.PC). rewrite H.
    inversion 1; subst.
    exploit (agree_inj_instr j MATCHSMINJ b b2 f ofs delta (Asm.Pbuiltin ef args res)); auto.
    intros (id & i' & sid & ofs1 & FITARG & FSYMB & TRANSL).
    (* exploit (globs_to_funs_inj_into_flatmem j); eauto. inversion 1; subst. *)
    monadInv TRANSL. (* monadInv EQ. *)
    set (pbseg := {| segblock_id := sid; segblock_start := Ptrofs.repr ofs1; segblock_size := Ptrofs.repr (instr_size (Pbuiltin ef args res)) |}) in *.
    exploit (eval_builtin_args_inject j m m'0 rs rs'0 (rs Asm.RSP) (rs'0 Asm.RSP) args vargs); auto.
    intros (vargs' & EBARGS & ARGSINJ).
    assert (Globalenvs.Genv.to_senv ge = (Genv.genv_senv tge)) as SENVEQ. 
    { 
      unfold match_prog in TRANSF. unfold transf_program in TRANSF.
      repeat destr_in TRANSF. 
      symmetry. eapply transl_prog_pres_senv; eauto.
    }
    generalize (external_call_inject ge j vargs vargs' m m'0 m' vres t ef ARGSINJ MINJ H3).
    rewrite SENVEQ.
    intros (j' & vres2 & m2' & EXTCALL & RESINJ & MINJ' & INJINCR & INJSEP).
    set (rs' := nextinstr_nf (set_res res vres2 (undef_regs (map preg_of (Machregs.destroyed_by_builtin ef)) rs'0)) (segblock_size pbseg)).
    exploit (fun b ofs => FlatAsm.exec_step_builtin tge id b ofs
                                       ef args res rs'0  m'0 vargs' t vres2 rs' m2' pbseg); eauto. 
    (* unfold valid_instr_offset_is_internal in INSTRINTERNAL. *)
    (* eapply INSTRINTERNAL; eauto. *)
    intros FSTEP. eexists; split; eauto.
    eapply match_states_intro with (j:=j'); eauto.
    (* Supposely the following propreties can proved by separation property of injections *)
    + eapply (inject_pres_match_sminj j); eauto.
    (* + eapply (inject_pres_globs_inj_into_flatmem j); eauto. *)
    + eapply (inject_pres_valid_instr_offset_is_internal j); eauto.
    + eapply (inject_pres_extfun_entry_is_external j); eauto.
    + eapply (inject_pres_match_find_funct j); eauto.
    + subst rs'. intros. subst pbseg; simpl.
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
      eauto with inject_db.
    + eapply extcall_pres_glob_block_valid; eauto.

  - (* External call *)
    unfold regset_inject in RSINJ. generalize (RSINJ Asm.PC). rewrite H. 
    inversion 1; subst. rewrite Ptrofs.add_zero_l in H6.
    (* exploit (globs_to_funs_inj_into_flatmem j); eauto. inversion 1; subst. *)
    (* edestruct storev_mapped_inject' as (m2' & SV & INJ2); eauto. *)
    (* apply Val.offset_ptr_inject. eauto. *)
    exploit Mem.loadv_inject. apply MINJ. apply LOADRA. eauto. intros (v2 & LRA & VI).
    edestruct (extcall_arguments_inject) as (args2 & ARGSINJ & EXTCALLARGS); eauto.
    apply regset_inject_expand. eauto.
    apply Val.offset_ptr_inject. eauto.
    assert (Globalenvs.Genv.to_senv ge = (Genv.genv_senv tge)) as SENVEQ. 
    { 
      unfold match_prog in TRANSF. unfold transf_program in TRANSF.
      repeat destr_in TRANSF. 
      symmetry. eapply transl_prog_pres_senv; eauto.
    }
    exploit (external_call_inject ge j args args2 ); eauto.
    rewrite SENVEQ.
    
    intros (j' & res' & m2'' & EXTCALL & RESINJ & MINJ' & INJINCR & INJSEP).
    exploit (fun ofs => FlatAsm.exec_step_external tge b2 ofs ef args2 res'); eauto.
    + intro; subst. inv VI. congruence.
    + intros FSTEP. eexists. split. apply FSTEP.
      eapply match_states_intro with (j := j'); eauto.
      * eapply (inject_pres_match_sminj j); eauto.
      * eapply (inject_pres_valid_instr_offset_is_internal j); eauto.
      * eapply (inject_pres_extfun_entry_is_external j); eauto.
      * eapply (inject_pres_match_find_funct j); eauto.
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
      * eapply extcall_pres_glob_block_valid; eauto.
Qed.        



Lemma weak_valid_ptr_inj: forall j m m',
  Mem.inject j (def_frame_inj m) m m' ->
  forall b1 ofs b2 delta,
  j b1 = Some(b2, delta) ->
  Mem.weak_valid_pointer m b1 (Ptrofs.unsigned ofs) = true ->
  Mem.weak_valid_pointer m' b2 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true.
Proof.
  intros. eapply Mem.weak_valid_pointer_inject'; eauto.
Qed.

Lemma weak_valid_ptr_no_overflow: forall j m m',
  Mem.inject j (def_frame_inj m) m m' ->
  forall b1 ofs b2 delta,
  j b1 = Some(b2, delta) ->
  Mem.weak_valid_pointer m b1 (Ptrofs.unsigned ofs) = true ->
  0 <= Ptrofs.unsigned ofs + Ptrofs.unsigned (Ptrofs.repr delta) <= Ptrofs.max_unsigned.
Proof.
  intros. eapply Mem.weak_valid_pointer_inject_no_overflow; eauto.
Qed.

Lemma valid_different_ptrs_inj: forall j m m',
  Mem.inject j (def_frame_inj m) m m' ->
  forall b1 ofs1 b2 ofs2 b1' delta1 b2' delta2,
  b1 <> b2 ->
  Mem.valid_pointer m b1 (Ptrofs.unsigned ofs1) = true ->
  Mem.valid_pointer m b2 (Ptrofs.unsigned ofs2) = true ->
  j b1 = Some (b1', delta1) ->
  j b2 = Some (b2', delta2) ->
  b1' <> b2' \/
  Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta1)) <> Ptrofs.unsigned (Ptrofs.add ofs2 (Ptrofs.repr delta2)).
Proof.
  intros. eapply Mem.different_pointers_inject; eauto.
Qed.

Definition cmpu_bool_inject := fun j m m' (MINJ: Mem.inject j (def_frame_inj m) m m') =>
                     Val.cmpu_bool_inject j (Mem.valid_pointer m) (Mem.valid_pointer m')
                                          (valid_ptr_inj j m m' MINJ)
                                          (weak_valid_ptr_inj j m m' MINJ)
                                          (weak_valid_ptr_no_overflow j m m' MINJ)
                                          (valid_different_ptrs_inj j m m' MINJ).

Lemma cmpu_bool_lessdef : forall j v1 v2 v1' v2' m m' c,
    Val.inject j v1 v1' -> Val.inject j v2 v2' ->
    Mem.inject j (def_frame_inj m) m m' ->
    Val.opt_lessdef (Val.cmpu_bool (Mem.valid_pointer m) c v1 v2)
                (Val.cmpu_bool (Mem.valid_pointer m') c v1' v2').
Proof.
  intros. destruct (Val.cmpu_bool (Mem.valid_pointer m) c v1 v2) eqn:EQ.
  - exploit (cmpu_bool_inject j m m' H1 c v1 v2); eauto.
    intros. rewrite H2. constructor.
  - constructor.
Qed.

Definition cmplu_bool_inject := fun j m m' (MINJ: Mem.inject j (def_frame_inj m) m m') =>
                     Val.cmplu_bool_inject j (Mem.valid_pointer m) (Mem.valid_pointer m')
                                           (valid_ptr_inj j m m' MINJ)
                                           (weak_valid_ptr_inj j m m' MINJ)
                                           (weak_valid_ptr_no_overflow j m m' MINJ)
                                           (valid_different_ptrs_inj j m m' MINJ).


Lemma cmplu_bool_lessdef : forall j v1 v2 v1' v2' m m' c,
    Val.inject j v1 v1' -> Val.inject j v2 v2' ->
    Mem.inject j (def_frame_inj m) m m' ->
    Val.opt_lessdef (Val.cmplu_bool (Mem.valid_pointer m) c v1 v2)
                (Val.cmplu_bool (Mem.valid_pointer m') c v1' v2').
Proof.
  intros. destruct (Val.cmplu_bool (Mem.valid_pointer m) c v1 v2) eqn:EQ.
  - exploit (cmplu_bool_inject j m m' H1 c v1 v2); eauto.
    intros. rewrite H2. constructor.
  - constructor.
Qed.

Lemma val_of_optbool_lessdef : forall j v1 v2,
    Val.opt_lessdef v1 v2 -> Val.inject j (Val.of_optbool v1) (Val.of_optbool v2).
Proof.
  intros. destruct v1; auto.
  simpl. inv H. destruct b; constructor.
Qed.

Lemma cmpu_inject : forall j v1 v2 v1' v2' m m' c,
    Val.inject j v1 v1' -> Val.inject j v2 v2' ->
    Mem.inject j (def_frame_inj m) m m' ->
    Val.inject j (Val.cmpu (Mem.valid_pointer m) c v1 v2)
               (Val.cmpu (Mem.valid_pointer m') c v1' v2').
Proof.
  intros. unfold Val.cmpu.
  exploit (cmpu_bool_lessdef j v1 v2); eauto. intros. 
  exploit val_of_optbool_lessdef; eauto.
Qed.

Lemma val_negative_inject: forall j v1 v2,
  Val.inject j v1 v2 -> Val.inject j (Val.negative v1) (Val.negative v2).
Proof.
  intros. unfold Val.negative. destruct v1; auto.
  inv H. auto.
Qed.

Lemma val_negativel_inject: forall j v1 v2,
  Val.inject j v1 v2 -> Val.inject j (Val.negativel v1) (Val.negativel v2).
Proof.
  intros. unfold Val.negativel. destruct v1; auto.
  inv H. auto.
Qed.

Lemma sub_overflow_inject : forall v1 v2 v1' v2' j,
    Val.inject j v1 v2 -> Val.inject j v1' v2' -> 
    Val.inject j (Val.sub_overflow v1 v1') (Val.sub_overflow v2 v2').
Proof.
  intros. unfold Val.sub_overflow. 
  destruct v1; auto. inv H. 
  destruct v1'; auto. inv H0. auto.
Qed.

Lemma subl_overflow_inject : forall v1 v2 v1' v2' j,
    Val.inject j v1 v2 -> Val.inject j v1' v2' -> 
    Val.inject j (Val.subl_overflow v1 v1') (Val.subl_overflow v2 v2').
Proof.
  intros. unfold Val.subl_overflow. 
  destruct v1; auto. inv H. 
  destruct v1'; auto. inv H0. auto.
Qed.

Lemma compare_ints_inject: forall j v1 v2 v1' v2' rs rs' m m',
    Val.inject j v1 v1' -> Val.inject j v2 v2' ->
    Mem.inject j (def_frame_inj m) m m' ->
    regset_inject j rs rs' -> 
    regset_inject j (compare_ints v1 v2 rs m) (compare_ints v1' v2' rs' m').
Proof.
  intros. unfold compare_ints, Asm.compare_ints.
  repeat apply regset_inject_expand; auto.
  - apply cmpu_inject; auto.
  - apply cmpu_inject; auto.
  - apply val_negative_inject. apply Val.sub_inject; auto.
  - apply sub_overflow_inject; auto.
Qed.

Lemma cmplu_lessdef : forall j v1 v2 v1' v2' m m' c,
    Val.inject j v1 v1' -> Val.inject j v2 v2' ->
    Mem.inject j (def_frame_inj m) m m' ->
    Val.opt_val_inject j (Val.cmplu (Mem.valid_pointer m) c v1 v2)
                     (Val.cmplu (Mem.valid_pointer m') c v1' v2').
Proof.
  intros. unfold Val.cmplu.
  exploit (cmplu_bool_lessdef j v1 v2 v1' v2' m m' c); eauto. intros.
  inversion H2; subst; simpl; constructor.
  apply Val.vofbool_inject.
Qed.

Lemma compare_longs_inject: forall j v1 v2 v1' v2' rs rs' m m',
    Val.inject j v1 v1' -> Val.inject j v2 v2' ->
    Mem.inject j (def_frame_inj m) m m' ->
    regset_inject j rs rs' -> 
    regset_inject j (compare_longs v1 v2 rs m) (compare_longs v1' v2' rs' m').
Proof.
  intros. unfold compare_longs, Asm.compare_longs.
  repeat apply regset_inject_expand; auto.
  - unfold Val.cmplu.
    exploit (cmplu_bool_lessdef j v1 v2 v1' v2' m m' Ceq); eauto. intros.
    inversion H3; subst.
    + simpl. auto. 
    + simpl. apply Val.vofbool_inject.
  - unfold Val.cmplu.
    exploit (cmplu_bool_lessdef j v1 v2 v1' v2' m m' Clt); eauto. intros.
    inversion H3; subst.
    + simpl. auto. 
    + simpl. apply Val.vofbool_inject.
  - apply val_negativel_inject. apply Val.subl_inject; auto.
  - apply subl_overflow_inject; auto.
Qed.

Ltac solve_val_inject :=
  match goal with
  (* | [ H : Val.inject _ (Vint _) (Vlong _) |- _] => inversion H *)
  (* | [ H : Val.inject _ (Vint _) (Vfloat _) |- _] => inversion H *)
  (* | [ H : Val.inject _ (Vint _) (Vsingle _) |- _] => inversion H *)
  (* | [ H : Val.inject _ (Vint _) (Vptr _ _) |- _] => inversion H *)
  (* | [ H : Val.inject _ (Vptr _ _) (Vlong _) |- _] => inversion H *)
  (* | [ H : Val.inject _ (Vptr _ _) (Vfloat _) |- _] => inversion H *)
  (* | [ H : Val.inject _ (Vptr _ _) (Vsingle _) |- _] => inversion H *)
  | [ H : Val.inject _ (Vfloat _) Vundef |- _] => inversion H
  | [ H : Val.inject _ (Vfloat _) (Vint _) |- _] => inversion H
  | [ H : Val.inject _ (Vfloat _) (Vlong _) |- _] => inversion H
  | [ H : Val.inject _ (Vfloat _) (Vsingle _) |- _] => inversion H
  | [ H : Val.inject _ (Vfloat _) (Vptr _ _) |- _] => inversion H
  | [ H : Val.inject _ (Vfloat _) (Vfloat _) |- _] => inv H; solve_val_inject
  | [ H : Val.inject _ (Vsingle _) Vundef |- _] => inversion H
  | [ H : Val.inject _ (Vsingle _) (Vint _) |- _] => inversion H
  | [ H : Val.inject _ (Vsingle _) (Vlong _) |- _] => inversion H
  | [ H : Val.inject _ (Vsingle _) (Vsingle _) |- _] => inv H; solve_val_inject
  | [ H : Val.inject _ (Vsingle _) (Vptr _ _) |- _] => inversion H
  | [ H : Val.inject _ (Vsingle _) (Vfloat _) |- _] => inversion H
  | [ |- Val.inject _ (Val.of_bool ?v) (Val.of_bool ?v) ] => apply Val.vofbool_inject
  | [ |- Val.inject _ Vundef _ ] => auto
  end.

Ltac solve_regset_inject :=
  match goal with
  | [ H: regset_inject ?j ?rs1 ?rs2 |- regset_inject ?j (Asm.undef_regs ?uregs ?rs1) (Asm.undef_regs ?uregs ?rs2)] =>
    apply undef_regs_pres_inject; auto
  | [ |- regset_inject _ (Asm.undef_regs _ _) _ ] =>
    unfold Asm.undef_regs; solve_regset_inject
  | [ |- regset_inject _ _ (Asm.undef_regs _ _) ] =>
    unfold Asm.undef_regs; simpl; solve_regset_inject
  | [ |- regset_inject _ (?rs1 # ?r <- ?v1) (?rs2 # ?r <- ?v2) ] =>
    apply regset_inject_expand; [solve_regset_inject | solve_val_inject]
  | [ H: regset_inject ?j ?rs1 ?rs2 |- regset_inject ?j ?rs1 ?rs2 ] =>
    auto
  end.

Lemma compare_floats_inject: forall j v1 v2 v1' v2' rs rs',
    Val.inject j v1 v1' -> Val.inject j v2 v2' ->
    regset_inject j rs rs' -> 
    regset_inject j (compare_floats v1 v2 rs) (compare_floats v1' v2' rs').
Proof.
  intros. unfold compare_floats, Asm.compare_floats.
  destruct v1, v2, v1', v2'; try solve_regset_inject. 
Qed.

Lemma compare_floats32_inject: forall j v1 v2 v1' v2' rs rs',
    Val.inject j v1 v1' -> Val.inject j v2 v2' ->
    regset_inject j rs rs' -> 
    regset_inject j (compare_floats32 v1 v2 rs) (compare_floats32 v1' v2' rs').
Proof.
  intros. unfold compare_floats32, Asm.compare_floats32.
  destruct v1, v2, v1', v2'; try solve_regset_inject. 
Qed.

  
Ltac solve_store_load :=
  match goal with
  | [ H : Asm.exec_instr _ _ _ _ _ _ = Next _ _ |- _ ] =>
    unfold Asm.exec_instr in H; simpl in H; solve_store_load
  | [ H : Asm.exec_store _ _ _ _ _ _ _ _ = Next _ _ |- _ ] =>
    exploit exec_store_step; eauto
  | [ H : Asm.exec_load _ _ _ _ _ _ _ = Next _ _ |- _ ] =>
    exploit exec_load_step; eauto
  end.

Ltac solve_opt_lessdef := 
  match goal with
  | [ |- Val.opt_lessdef (match ?rs1 ?r with
                     | _ => _
                     end) _ ] =>
    let EQ := fresh "EQ" in (destruct (rs1 r) eqn:EQ; solve_opt_lessdef)
  | [ |- Val.opt_lessdef None _ ] => constructor
  | [ |- Val.opt_lessdef (Some _) (match ?rs2 ?r with
                              | _ => _
                              end) ] =>
    let EQ := fresh "EQ" in (destruct (rs2 r) eqn:EQ; solve_opt_lessdef)
  | [ H1: regset_inject _ ?rs1 ?rs2, H2: ?rs1 ?r = _, H3: ?rs2 ?r = _ |- _ ] =>
    generalize (H1 r); rewrite H2, H3; clear H2 H3; inversion 1; subst; solve_opt_lessdef
  | [ |- Val.opt_lessdef (Some ?v) (Some ?v) ] => constructor
  end.

Lemma eval_testcond_inject: forall j c rs1 rs2,
    regset_inject j rs1 rs2 ->
    Val.opt_lessdef (Asm.eval_testcond c rs1) (Asm.eval_testcond c rs2).
Proof.
  intros. destruct c; simpl; try solve_opt_lessdef.
Qed.

Hint Resolve nextinstr_nf_pres_inject nextinstr_pres_inject regset_inject_expand
  regset_inject_expand_vundef_left undef_regs_pres_inject
  Val.zero_ext_inject Val.sign_ext_inject Val.longofintu_inject Val.longofint_inject
  Val.singleoffloat_inject Val.loword_inject Val.floatofsingle_inject Val.intoffloat_inject Val.maketotal_inject
  Val.intoffloat_inject Val.floatofint_inject Val.intofsingle_inject Val.singleofint_inject
  Val.longoffloat_inject Val.floatoflong_inject Val.longofsingle_inject Val.singleoflong_inject
  eval_addrmode32_inject eval_addrmode64_inject eval_addrmode_inject
  Val.neg_inject Val.negl_inject Val.add_inject Val.addl_inject
  Val.sub_inject Val.subl_inject Val.mul_inject Val.mull_inject Val.mulhs_inject Val.mulhu_inject
  Val.mullhs_inject Val.mullhu_inject Val.shr_inject Val.shrl_inject Val.or_inject Val.orl_inject
  Val.xor_inject Val.xorl_inject Val.and_inject Val.andl_inject Val.notl_inject
  Val.shl_inject Val.shll_inject Val.vzero_inject Val.notint_inject
  Val.shru_inject Val.shrlu_inject Val.ror_inject Val.rorl_inject
  compare_ints_inject compare_longs_inject compare_floats_inject compare_floats32_inject
  Val.addf_inject Val.subf_inject Val.mulf_inject Val.divf_inject Val.negf_inject Val.absf_inject
  Val.addfs_inject Val.subfs_inject Val.mulfs_inject Val.divfs_inject Val.negfs_inject Val.absfs_inject
  val_of_optbool_lessdef eval_testcond_inject Val.offset_ptr_inject: inject_db.

Ltac solve_exec_instr :=
  match goal with
  | [ |- Next _ _ = Next _ _ ] =>
    reflexivity
  | [ |- context [eval_testcond _ _] ]=>
    unfold eval_testcond; solve_exec_instr
  | [ H: Asm.eval_testcond ?c ?r = _ |- context [Asm.eval_testcond ?c ?r] ] =>
    rewrite H; solve_exec_instr
  | [ H: _ = Asm.eval_testcond ?c ?r |- context [Asm.eval_testcond ?c ?r] ] =>
    rewrite <- H; solve_exec_instr
  end.

Ltac solve_match_states :=
  match goal with
  | [ H: Asm.Stuck = Next _ _ |- _ ] => inv H
  | [ |- exists _, _ ] => eexists; solve_match_states
  | [ |- (FlatAsm.exec_instr _ _ _ _ = Next _ _) /\ match_states _ _ ] =>
    split; [simpl; solve_exec_instr | econstructor; eauto; solve_match_states]
  | [ |- regset_inject _ _ _ ] =>
    eauto 10 with inject_db
  end.

Ltac destr_eval_testcond :=
  match goal with
  | [ H : match Asm.eval_testcond ?c ?rs with | _ => _ end = Next _ _ |- _ ] =>
    let ETEQ := fresh "ETEQ" in (
      destruct (Asm.eval_testcond c rs) eqn:ETEQ); destr_eval_testcond
  | [ H : Some ?b = Asm.eval_testcond _ _ |- _ ] =>
    match b with
    | true => fail 1
    | false => fail 1
    | _ => destruct b; destr_eval_testcond
    end
  | [ H : Asm.eval_testcond _ _ = Some ?b |- _] =>
    match b with
    | true => fail 1
    | false => fail 1
    | _ => destruct b; destr_eval_testcond
    end
  | [ H : Asm.Next _ _ = Next _ _ |- _ ] =>
    inv H; destr_eval_testcond
  | [ H: Val.opt_lessdef (Some true) (Asm.eval_testcond _ _) |- _ ] =>
    inv H; destr_eval_testcond
  | [ H: Val.opt_lessdef (Some false) (Asm.eval_testcond _ _) |- _ ] =>
    inv H; destr_eval_testcond
  | _ => idtac
  end.

Ltac destr_match_outcome :=
  match goal with
  | [ H: Asm.Stuck = Next _ _ |- _ ] => inv H
  | [ H: Asm.Next _ _ = Next _ _ |- _ ] => inv H; destr_match_outcome
  | [ H: match ?a with _ => _ end = Next _ _ |- _] =>
    let EQ := fresh "EQ" in (destruct a eqn:EQ; destr_match_outcome)
  | _ => idtac
  end.


Lemma goto_label_pres_mem : forall f l rs1 m1 rs1' m1',
    Asm.goto_label ge f l rs1 m1 = Next rs1' m1' -> m1 = m1'.
Proof.
  unfold Asm.goto_label. intros.
  destruct (label_pos l 0 (Asm.fn_code f)); try inv H. 
  destruct (rs1 Asm.PC); try inv H1.
  destruct (Globalenvs.Genv.find_funct_ptr ge b); try inv H0. auto.
Qed.

Lemma goto_label_inject : forall rs1 rs2 id b f l j m1 m2 rs1' m1' ofs
                            (MATCHSMINJ: match_inj j)
                            (RINJ: regset_inject j rs1 rs2)
                            (MINJ:Mem.inject j (def_frame_inj m1) m1 m2),
    rs1 PC = Vptr b ofs ->
    Globalenvs.Genv.find_symbol ge id = Some b ->
    Globalenvs.Genv.find_funct_ptr ge b = Some (Internal f) ->
    Asm.goto_label ge f l rs1 m1 = Next rs1' m1' ->
    exists rs2', goto_label tge id l rs2 m2 = Next rs2' m2 /\
            regset_inject j rs1' rs2' /\ Mem.inject j (def_frame_inj m1') m1' m2.
Proof.
  intros. unfold Asm.goto_label in H2.
  destruct (label_pos l 0 (Asm.fn_code f)) eqn:EQLBL; try inv H2.
  setoid_rewrite H in H4. rewrite H1 in H4. inv H4.
  exploit agree_inj_lbl; eauto. intros.
  eexists. split.
  unfold goto_label. auto. split; auto.
  repeat apply regset_inject_expand; auto.
Qed.

Lemma goto_tbl_label_inject : forall id tbl l b f j rs1 rs2 m1 m2 rs1' m1' i ofs
                                (MATCHSMINJ: match_inj j)
                                (RINJ: regset_inject j rs1 rs2)
                                (MINJ:Mem.inject j (def_frame_inj m1) m1 m2),
    rs1 PC = Vptr b ofs ->
    Globalenvs.Genv.find_symbol ge id = Some b ->
    Globalenvs.Genv.find_funct_ptr ge b = Some (Internal f) ->
    list_nth_z tbl i = Some l ->
    Asm.goto_label ge f l ((rs1 # RAX <- Vundef) # RDX <- Vundef) m1 = Next rs1' m1' ->
    exists rs2',
      FlatAsm.goto_label tge id l ((rs2 # RAX <- Vundef) # RDX <- Vundef) m2 = Next rs2' m2 /\
      regset_inject j rs1' rs2' /\ Mem.inject j (def_frame_inj m1') m1' m2.
Proof.
  induction tbl; simpl; intros.
  - congruence.
  - destruct (zeq i 0).
    + inv H2. 
      exploit (goto_label_inject ((rs1 # RAX <- Vundef) # RDX <- Vundef) ((rs2 # RAX <- Vundef) # RDX <- Vundef)); eauto with inject_db.
    + exploit IHtbl; eauto.
Qed.

Lemma add_globals_pres_senv :
  forall (defs : list (ident * option gdef * segblock)) (ge : FlatAsm.genv),
  Genv.genv_senv (add_globals ge defs) = Genv.genv_senv ge.
Proof.
  induction defs; intros.
  - simpl. auto.
  - simpl. erewrite IHdefs; eauto.
    unfold add_global. destruct a. destruct p. 
    destruct (Genv.genv_symb ge0 i) eqn:GENVSYM.
    + destruct p. simpl. auto.
    + auto.
Qed.

Lemma transl_prog_pres_senv : forall gmap lmap dsize csize tprog prog,
    transl_prog_with_map gmap lmap prog dsize csize = OK tprog ->
    (Genv.genv_senv (globalenv tprog)) = (Globalenvs.Genv.globalenv prog).
Proof.
  intros gmap lmap dsize csize tprog0 prog0 H.
  monadInv H. unfold globalenv. simpl.
  rewrite add_globals_pres_senv; eauto.
Qed.


Hypothesis no_pseudo_instrs:
  forall id b f ofs i
    (FS: Globalenvs.Genv.find_symbol ge id = Some b)
    (FFP: Globalenvs.Genv.find_funct_ptr ge b = Some (Internal f))
    (FI : find_instr (Ptrofs.unsigned ofs) (Asm.fn_code f) = Some i),
    match i with
      Pallocframe _ _ _
    | Pfreeframe _ _
    | Pload_parent_pointer _ _ => False
    | _ => True
    end.

(** The internal step preserves the invariant *)
Lemma exec_instr_step : forall j rs1 rs2 m1 m2 rs1' m1' i i' id sid ofs ofs' f b
                        (MINJ: Mem.inject j (def_frame_inj m1) m1 m2)
                        (MATCHSMINJ: match_inj j)
                        (* (GINJFLATMEM: globs_inj_into_flatmem j) *)
                        (INSTRINTERNAL: valid_instr_offset_is_internal j)
                        (EXTEXTERNAL: extfun_entry_is_external j)
                        (MATCHFINDFUNCT: match_find_funct j)
                        (RSINJ: regset_inject j rs1 rs2)
                        (GBVALID: glob_block_valid m1),
    rs1 PC = Vptr b ofs ->
    Globalenvs.Genv.find_symbol ge id = Some b ->
    Globalenvs.Genv.find_funct_ptr ge b = Some (Internal f) ->
    Asm.find_instr (Ptrofs.unsigned ofs) (Asm.fn_code f) = Some i ->
    RealAsm.exec_instr ge f i rs1 m1 = Next rs1' m1' ->
    transl_instr ofs' id sid i = OK i' ->
    exists rs2' m2',
      FlatAsm.exec_instr tge i' rs2 m2 = Next rs2' m2' /\
      match_states (State rs1' m1') (State rs2' m2').
Proof.
  intros.
  destruct i; inv H3; simpl in *; monadInvX H4;
                        try first [solve_store_load |
                                   solve_match_states].

  - (* Pmov_rs *)
    apply nextinstr_nf_pres_inject.
    apply regset_inject_expand; auto.
    inv MATCHSMINJ.
    unfold Globalenvs.Genv.symbol_address.
    destruct (Globalenvs.Genv.find_symbol ge id0) eqn:FINDSYM; auto.
    exploit agree_inj_glob0; eauto.
    intros (b1 & ofs1 & GLBL & JB).
    erewrite Genv.find_sym_to_addr with (ofs:=ofs1); eauto.
    rewrite <- (Ptrofs.add_zero_l ofs1).
    eapply Val.inject_ptr; eauto.
    rewrite Ptrofs.repr_unsigned. auto.

  (* Divisions *)
  - unfold Asm.exec_instr in H6; simpl in H6.
    destr_match_outcome. 
    generalize (RSINJ Asm.RDX). generalize (RSINJ Asm.RAX). generalize (RSINJ r1).
    rewrite EQ, EQ0, EQ1. inversion 1; subst. inversion 1; subst. inversion 1; subst.
    eexists; eexists. split. simpl. setoid_rewrite <- H10. setoid_rewrite <- H8.
    setoid_rewrite <- H6. rewrite EQ2. auto.
    eapply match_states_intro; eauto with inject_db.

  - unfold Asm.exec_instr in H6; simpl in H6.
    destr_match_outcome. 
    generalize (RSINJ Asm.RDX). generalize (RSINJ Asm.RAX). generalize (RSINJ r1).
    rewrite EQ, EQ0, EQ1. inversion 1; subst. inversion 1; subst. inversion 1; subst.
    eexists; eexists. split. simpl. setoid_rewrite <- H10. setoid_rewrite <- H8.
    setoid_rewrite <- H6. rewrite EQ2. auto.
    eapply match_states_intro; eauto with inject_db.

  - unfold Asm.exec_instr in H6; simpl in H6.
    destr_match_outcome. 
    generalize (RSINJ Asm.RDX). generalize (RSINJ Asm.RAX). generalize (RSINJ r1).
    rewrite EQ, EQ0, EQ1. inversion 1; subst. inversion 1; subst. inversion 1; subst.
    eexists; eexists. split. simpl. setoid_rewrite <- H10. setoid_rewrite <- H8.
    setoid_rewrite <- H6. rewrite EQ2. auto.
    eapply match_states_intro; eauto with inject_db.

  - unfold Asm.exec_instr in H6; simpl in H6.
    destr_match_outcome. 
    generalize (RSINJ Asm.RDX). generalize (RSINJ Asm.RAX). generalize (RSINJ r1).
    rewrite EQ, EQ0, EQ1. inversion 1; subst. inversion 1; subst. inversion 1; subst.
    eexists; eexists. split. simpl. setoid_rewrite <- H10. setoid_rewrite <- H8.
    setoid_rewrite <- H6. rewrite EQ2. auto.
    eapply match_states_intro; eauto with inject_db.
     
  - (* Pcmov *)
    unfold Asm.exec_instr in H6; simpl in H6.
    exploit (eval_testcond_inject j c rs1 rs2); eauto.
    intros. 
    destr_eval_testcond; try solve_match_states.
    destruct (Asm.eval_testcond c rs2) eqn:EQ'. destruct b0; solve_match_states.
    solve_match_states.

  - (* Pjmp_l *)
    unfold Asm.exec_instr in H6; simpl in H6.
    unfold Asm.goto_label in H6. destruct (label_pos l 0 (Asm.fn_code f)) eqn:LBLPOS; inv H6.
    destruct (rs1 Asm.PC) eqn:PC1; inv H4. 
    destruct (Globalenvs.Genv.find_funct_ptr ge b0); inv H5.
    eexists; eexists. split. simpl.
    unfold goto_label. eauto.
    eapply match_states_intro; eauto.
    apply regset_inject_expand; auto. 
    rewrite H in *. inv PC1. inv H.
    eapply agree_inj_lbl; eauto.

  - (* Pjmp_s *)
    repeat destr_in H6.
    destruct ros; simpl in *.
    do 2 eexists; split; eauto.
    econstructor; eauto.
    apply regset_inject_expand; auto.
    do 2 eexists; split; eauto.
    econstructor; eauto.
    apply regset_inject_expand; auto.
    inversion MATCHSMINJ.
    unfold Globalenvs.Genv.symbol_address. destr_match; auto.
    exploit (agree_inj_glob0 i b0); eauto.
    intros (b1 & ofs1 & LBLOFS & JB).
    erewrite Genv.find_sym_to_addr with (ofs:=ofs1); eauto.
    rewrite <- (Ptrofs.add_zero_l ofs1).
    eapply Val.inject_ptr; eauto.
    rewrite Ptrofs.repr_unsigned. auto.

  - (* Pjcc *)
    unfold Asm.exec_instr in H6; simpl in H6.
    exploit (eval_testcond_inject j c rs1 rs2); eauto.
    intros.
    destr_eval_testcond; try solve_match_states.
    exploit goto_label_inject; eauto. intros (rs2' & GOTO & RINJ' & MINJ').
    exists rs2', m2. split. simpl. rewrite <- H7. auto.
    eapply match_states_intro; eauto.
    assert (m1 = m1') by (eapply goto_label_pres_mem; eauto). subst. auto.

  - (* Pjcc2 *)
    unfold Asm.exec_instr in H6; simpl in H6.
    exploit (eval_testcond_inject j c1 rs1 rs2); eauto.
    exploit (eval_testcond_inject j c2 rs1 rs2); eauto.
    intros ELF1 ELF2.
    destr_eval_testcond; try solve_match_states.
    exploit goto_label_inject; eauto. intros (rs2' & GOTO & RINJ' & MINJ').
    exists rs2', m2. split. simpl. setoid_rewrite <- H5. setoid_rewrite <- H7. auto.
    eapply match_states_intro; eauto.
    assert (m1 = m1') by (eapply goto_label_pres_mem; eauto). subst. auto.

  - (* Pjmptbl *)
    unfold Asm.exec_instr in H6; simpl in H6.
    destruct (rs1 r) eqn:REQ; inv H6.
    destruct (list_nth_z tbl (Int.unsigned i)) eqn:LEQ; inv H4.
    assert (rs2 r = Vint i) by
        (generalize (RSINJ r); rewrite REQ; inversion 1; auto).
    exploit (goto_tbl_label_inject id tbl l); eauto. 
    intros (rs2' & GLBL & RSINJ' & MINJ').
    exists rs2', m2. split. simpl. setoid_rewrite H3. setoid_rewrite LEQ. auto. 
    eapply match_states_intro; eauto.
    assert (m1 = m1') by (eapply goto_label_pres_mem; eauto). subst. auto.
    
  - (* Pcall_s *)
    repeat destr_in H6.
    generalize (RSINJ PC).
    edestruct storev_mapped_inject' as (m2' & ST & MINJ'). apply MINJ. eauto.
    apply Val.offset_ptr_inject. eauto.
    apply Val.offset_ptr_inject. eauto.
    do 2 eexists; split; eauto. simpl.
    rewrite ST. eauto.
    econstructor; eauto.
    repeat apply regset_inject_expand; auto.
    apply Val.offset_ptr_inject. eauto.
    destruct ros; simpl; repeat apply regset_inject_expand; auto.
    exploit (inject_symbol_address j i Ptrofs.zero); eauto.
    apply Val.offset_ptr_inject. eauto.
    eapply storev_pres_glob_block_valid; eauto.      
  (* - (* Pallocframe *) *)
  (*   generalize (RSINJ RSP). intros RSPINJ. *)
  (*   destruct (Mem.storev Mptr m1 *)
  (*                        (Val.offset_ptr *)
  (*                           (Val.offset_ptr (rs1 RSP) *)
  (*                                           (Ptrofs.neg (Ptrofs.repr (align (frame_size frame) 8)))) *)
  (*                           ofs_ra) (rs1 RA)) eqn:STORERA; try inv H6. *)
  (*   exploit (fun a1 a2 => *)
  (*              storev_mapped_inject' j Mptr m1 a1 (rs1 RA) m1' m2 a2 (rs2 RA)); eauto with inject_db. *)
  (*   intros (m2' & STORERA' & MINJ2). *)
  (*   destruct (rs1 RSP) eqn:RSP1; simpl in *; try congruence. *)
  (*   inv RSPINJ. *)
  (*   eexists; eexists. *)
  (*   (* Find the resulting state *) *)
  (*   rewrite <- H5 in STORERA'. rewrite STORERA'. split. eauto. *)
  (*   (* Solve match states *) *)
  (*   eapply match_states_intro; eauto. *)
  (*   eapply nextinstr_pres_inject; eauto. *)
  (*   repeat eapply regset_inject_expand; eauto. *)
  (*   eapply Val.inject_ptr; eauto. *)
  (*   repeat rewrite (Ptrofs.add_assoc i). *)
  (*   rewrite (Ptrofs.add_commut (Ptrofs.repr delta)). auto. *)
  (*   eapply store_pres_glob_block_valid; eauto. *)

  (* - (* Pfreeframe *) *)
  (*   generalize (RSINJ RSP). intros. *)
  (*   destruct (Mem.loadv Mptr m1 (Val.offset_ptr (rs1 RSP) ofs_ra)) eqn:EQRA; try inv H6. *)
  (*   exploit (fun g a2 => Mem.loadv_inject j g m1' m2 Mptr (Val.offset_ptr (rs1 Asm.RSP) ofs_ra) a2 v); eauto. *)
  (*   apply Val.offset_ptr_inject. auto. *)
  (*   intros (v2 & MLOAD2 & VINJ2). *)
  (*   eexists; eexists. split. simpl. *)
  (*   setoid_rewrite MLOAD2. auto. *)
  (*   eapply match_states_intro; eauto with inject_db. *)

  - repeat destr_in H6. simpl.
    exploit Mem.loadv_inject; eauto. intros (v2 & LD & VI). rewrite LD.
    eexists _, _; split; eauto. econstructor; eauto.
    repeat apply regset_inject_expand; auto.
    apply Val.offset_ptr_inject. eauto.
  - exploit no_pseudo_instrs; eauto. simpl. destruct 1.
  - exploit no_pseudo_instrs; eauto. simpl. destruct 1.
  - exploit no_pseudo_instrs; eauto. simpl. destruct 1.
Qed.

Theorem step_simulation:
  forall S1 t S2,
    RealAsm.step ge S1 t S2 ->
    forall S1' (MS: match_states S1 S1'),
    exists S2',
      FlatAsm.step tge S1' t S2' /\
      match_states S2 S2'.
Proof.
  destruct 1; intros; inv MS.

  - (* Internal step *)
    unfold regset_inject in RSINJ. generalize (RSINJ Asm.PC). rewrite H. 
    inversion 1; subst.
    exploit (agree_inj_instr j MATCHSMINJ b b2 f ofs delta i); eauto.
    intros (id & i' & sid & ofs1 & FITARG & FSYMB & TRANSL).
    exploit (exec_instr_step j rs rs'0 m m'0 rs' m' i i' id); eauto.
    intros (rs2' & m2' & FEXEC & MS1).
    exists (State rs2' m2'). split; auto.
    eapply FlatAsm.exec_step_internal; eauto.
        
  - (* Builtin *)
    unfold regset_inject in RSINJ. generalize (RSINJ Asm.PC). rewrite H.
    inversion 1; subst.
    exploit (agree_inj_instr j MATCHSMINJ b b2 f ofs delta (Asm.Pbuiltin ef args res)); auto.
    intros (id & i' & sid & ofs1 & FITARG & FSYMB & TRANSL).
    (* exploit (globs_to_funs_inj_into_flatmem j); eauto. inversion 1; subst. *)
    monadInv TRANSL. (* monadInv EQ. *)
    set (pbseg := {| segblock_id := sid; segblock_start := Ptrofs.repr ofs1; segblock_size := Ptrofs.repr (instr_size (Pbuiltin ef args res)) |}) in *.
    exploit (eval_builtin_args_inject j m m'0 rs rs'0 (rs Asm.RSP) (rs'0 Asm.RSP) args vargs); auto.
    intros (vargs' & EBARGS & ARGSINJ).
    assert (Globalenvs.Genv.to_senv ge = (Genv.genv_senv tge)) as SENVEQ. 
    { 
      unfold match_prog in TRANSF. unfold transf_program in TRANSF.
      repeat destr_in TRANSF. 
      symmetry. eapply transl_prog_pres_senv; eauto.
    }
    generalize (external_call_inject ge j vargs vargs' m m'0 m' vres t ef ARGSINJ MINJ H3).
    rewrite SENVEQ.
    intros (j' & vres2 & m2' & EXTCALL & RESINJ & MINJ' & INJINCR & INJSEP).
    set (rs' := nextinstr_nf (set_res res vres2 (undef_regs (map preg_of (Machregs.destroyed_by_builtin ef)) rs'0)) (segblock_size pbseg)).
    exploit (fun b ofs => FlatAsm.exec_step_builtin tge id b ofs
                                       ef args res rs'0  m'0 vargs' t vres2 rs' m2' pbseg); eauto. 
    (* unfold valid_instr_offset_is_internal in INSTRINTERNAL. *)
    (* eapply INSTRINTERNAL; eauto. *)
    intros FSTEP. eexists; split; eauto.
    eapply match_states_intro with (j:=j'); eauto.
    (* Supposely the following propreties can proved by separation property of injections *)
    + eapply (inject_pres_match_sminj j); eauto.
    (* + eapply (inject_pres_globs_inj_into_flatmem j); eauto. *)
    + eapply (inject_pres_valid_instr_offset_is_internal j); eauto.
    + eapply (inject_pres_extfun_entry_is_external j); eauto.
    + eapply (inject_pres_match_find_funct j); eauto.
    + subst rs'. intros. subst pbseg; simpl.
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
      eauto with inject_db.
    + eapply extcall_pres_glob_block_valid; eauto.

  - (* External call *)
    unfold regset_inject in RSINJ. generalize (RSINJ Asm.PC). rewrite H. 
    inversion 1; subst. rewrite Ptrofs.add_zero_l in H6.
    (* exploit (globs_to_funs_inj_into_flatmem j); eauto. inversion 1; subst. *)
    (* edestruct storev_mapped_inject' as (m2' & SV & INJ2); eauto. *)
    (* apply Val.offset_ptr_inject. eauto. *)
    exploit Mem.loadv_inject. apply MINJ. apply LOADRA. eauto. intros (v2 & LRA & VI).
    edestruct (extcall_arguments_inject) as (args2 & ARGSINJ & EXTCALLARGS); eauto.
    apply regset_inject_expand. eauto.
    apply Val.offset_ptr_inject. eauto.
    assert (Globalenvs.Genv.to_senv ge = (Genv.genv_senv tge)) as SENVEQ. 
    { 
      unfold match_prog in TRANSF. unfold transf_program in TRANSF.
      repeat destr_in TRANSF. 
      symmetry. eapply transl_prog_pres_senv; eauto.
    }
    exploit (external_call_inject ge j args args2 ); eauto.
    rewrite SENVEQ.
    
    intros (j' & res' & m2'' & EXTCALL & RESINJ & MINJ' & INJINCR & INJSEP).
    exploit (fun ofs => FlatAsm.exec_step_external tge b2 ofs ef args2 res'); eauto.
    + intro; subst. inv VI. congruence.
    + intros FSTEP. eexists. split. apply FSTEP.
      eapply match_states_intro with (j := j'); eauto.
      * eapply (inject_pres_match_sminj j); eauto.
      * eapply (inject_pres_valid_instr_offset_is_internal j); eauto.
      * eapply (inject_pres_extfun_entry_is_external j); eauto.
      * eapply (inject_pres_match_find_funct j); eauto.
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
      * eapply extcall_pres_glob_block_valid; eauto.
Qed.        

Lemma transf_final_states:
  forall st1 st2 r,
  match_states st1 st2 -> Asm.final_state st1 r -> FlatAsm.final_state st2 r.
Proof.
  intros st1 st2 r MATCH FINAL.
  inv FINAL. inv MATCH. constructor. 
  - red in RSINJ. generalize (RSINJ PC). rewrite H. 
    unfold Vnullptr. destruct Archi.ptr64; inversion 1; auto.
  - red in RSINJ. generalize (RSINJ RAX). rewrite H0.
    inversion 1. auto.
Qed.
  
Theorem transf_program_correct:
  forward_simulation (RealAsm.semantics prog (Pregmap.init Vundef)) (FlatAsm.semantics tprog (Pregmap.init Vundef)).
Proof.
  eapply forward_simulation_step with match_states.
  - simpl. intros. 
    unfold match_prog in TRANSF. unfold transf_program in TRANSF.
    repeat destr_in TRANSF.    
    erewrite transl_prog_pres_senv; eauto. auto.
  - simpl. intros s1 IS. 
    exploit transf_initial_states; eauto.
    intros.
    rewrite Pregmap.gi. auto.
  - simpl. intros s1 s2 r MS FS. eapply transf_final_states; eauto.
  - simpl. intros s1 t s1' STEP s2 MS. 
    edestruct step_simulation as (STEP' & MS'); eauto.
Qed.

End PRESERVATION.


End WITHMEMORYMODEL.