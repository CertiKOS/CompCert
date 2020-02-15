(* *******************  *)
(* Author: Pierre Wilke *)
(* Author: Xiangzhe Xu  *)
(* Date:   Feb 4, 2020  *)
(* *******************  *)

Require Import Coqlib Errors.
Require Import Integers Floats AST Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Op Locations Mach Conventions Asm RealAsm.
Require Import RelocBingen.
Require Import RelocProgram RelocProgSemantics1 RelocProgSemantics2.
Import ListNotations.
Require AsmFacts.

Definition match_prog p tp :=
  transf_program p = OK tp.

Lemma transf_program_match:
  forall p tp, transf_program p = OK tp -> match_prog p tp.
Proof.
  intros. subst. red.
  auto.
Qed.






Lemma decode_encode_refl: forall prog z code l,
        fold_left (acc_instrs (gen_reloc_ofs_map (reloctable_code (prog_reloctables prog)))) code (OK (0, [])) = OK (z, l)
        -> (exists c', (decode_instrs (gen_reloc_ofs_map (reloctable_code (prog_reloctables prog)))(prog_symbtable prog) (length (rev l)) 0 (rev l) []) = OK c' /\ forall i ins ins',
            (i<length c')%nat
            -> nth_error  c' i = Some ins'
            /\ nth_error code i = Some ins                                       
            /\ RelocBinDecode.instr_eq ins ins').
Proof.
Admitted.



Section PRESERVATION.
  Existing Instance inject_perm_all.
Context `{external_calls_prf: ExternalCalls}.

Local Existing Instance mem_accessors_default.


Variables prog tprog: program.

Let ge := RelocProgSemantics1.globalenv prog.
Let tge := RelocProgSemantics1.globalenv tprog.

Hypothesis TRANSF: match_prog prog tprog.

Lemma reverse_decode_prog_code_section: decode_prog_code_section tprog = OK prog.
Proof.
  unfold match_prog, transf_program in TRANSF. monadInv TRANSF.
  unfold decode_prog_code_section. simpl.
  unfold transl_sectable in EQ. repeat destr_in EQ.
  monadInv H0. simpl.
Admitted.

Lemma transf_initial_states:
  forall st1 rs, RelocProgSemantics1.initial_state prog rs st1 ->
         exists st2, initial_state tprog rs st2 /\  st1 = st2.
Proof.
  intros st1 rs HInit.
  exists st1.
  inv HInit.
  split.
  +
    unfold match_prog in TRANSF.
    unfold transf_program in TRANSF.
    monadInv TRANSF.
    unfold transl_sectable in EQ.
    destruct (prog_sectable prog);inversion EQ.
    repeat (destruct s; inversion EQ;
            destruct s0; inversion EQ).
    monadInv EQ.
    simpl.
    unfold transl_code in EQ0.
    monadInv  EQ0.
    destruct x. monadInv EQ2.    
    generalize (decode_encode_refl prog _ _ _  EQ1).
    intros [c' HEncodeDecode].
    destruct HEncodeDecode as [HDecode HDecodeSpec].
    econstructor.

    (* decode_prog_code_section *)
    unfold decode_prog_code_section.
    simpl. unfold sec_code_id.
    unfold decode_instrs'.
    rewrite HDecode. simpl. eauto.

    (* init_mem *)
    admit.
    (* initial_state_gen *)
    admit.
  + reflexivity.
Admitted.


Lemma transf_final_states:
  forall st1 st2 r,
    st1 = st2 -> RelocProgSemantics1.final_state st1 r -> final_state st2 r.
Proof.
  intros st1 st2 r MS HFinal.
  rewrite <-  MS.
  auto.
Qed.

Lemma not_find_ext_funct_refl: forall b ofs,
    Genv.find_ext_funct ge (Vptr b ofs) = None
    -> Genv.find_ext_funct (globalenv tprog) (Vptr b ofs) = None.
Admitted.

Lemma find_instr_refl: forall b ofs i,
    Genv.find_instr ge (Vptr b ofs) = Some i ->
    exists i', Genv.find_instr tge (Vptr b ofs) = Some i' /\ RelocBinDecode.instr_eq i i'.
Admitted.


Lemma symbol_address_refl: forall RELOC_CODE z,
    Genv.symbol_address (globalenv tprog) RELOC_CODE z Ptrofs.zero =
    Genv.symbol_address ge RELOC_CODE z Ptrofs.zero.
Proof.
  intros RELOC_CODE z.
  unfold Genv.symbol_address. unfold Genv.find_symbol.
  unfold Genv.genv_reloc_ofs_symb.
  unfold match_prog in TRANSF. monadInv TRANSF. simpl.
  unfold gen_reloc_ofs_symbs. simpl. 
  destruct ( Maps.ZTree.get z
                            (add_reloc_ofs_symb (prog_symbtable prog) RELOC_CODE 
                                                (prog_reloctables prog)
                                                (add_reloc_ofs_symb (prog_symbtable prog) RELOC_DATA 
                                                                    (prog_reloctables prog) (fun _ : reloctable_id => Maps.ZTree.empty ident))
                                                RELOC_CODE)); auto.
  unfold RelocProgSemantics.Genv.find_symbol.
  unfold RelocProgSemantics.globalenv.
  unfold RelocProgSemantics.Genv.genv_symb.
  simpl.
  unfold  RelocProgSemantics.add_external_globals.
  simpl.
  induction  (prog_symbtable prog).
  auto.
  simpl.
Admitted.

    
Lemma eval_addrmode32_refl: forall idofs a rs,
    eval_addrmode32 ge idofs a rs = eval_addrmode32 tge idofs a rs.
Admitted.

Lemma eval_addrmode_refl: forall idofs a rs,
    eval_addrmode ge idofs a rs = eval_addrmode tge idofs a rs.
Admitted.


Theorem step_simulation:
  forall s1 t s2, step ge s1 t s2 ->
                  forall s1' (MS: s1=s1'),
                    (exists s2', step tge s1' t s2' /\ s2 = s2').
Proof.
  intros s1 t s2 HStep s1' MS.
  exists s2.
  split;auto.
  induction HStep.
  + rewrite <- MS.
    unfold tge.
    (* not find def *)
    generalize (not_find_ext_funct_refl _ _ H0). auto.

    (* find instr *)
    generalize (find_instr_refl _ _ _ H1). intros [i' [HInsEx  HInsEQ]].
    unfold tge in HInsEx.
    econstructor.
    eauto. auto. eauto.

    (* "step simulation" *)
    rename H2 into HExec.
    rewrite <- HExec.
    destruct i;
    try(unfold RelocBinDecode.instr_eq in HInsEQ;
    rewrite HInsEQ;
    unfold exec_instr; simpl;
    destruct (get_pc_offset rs); [rewrite <- HInsEQ|auto]);auto. 
    unfold RelocBinDecode.instr_eq in HInsEQ.
    rewrite <- HInsEQ. admit.
    

    
    1:unfold exec_load.
    2:unfold exec_store.
    1-2: rewrite HInsEQ.
    1-2: generalize (eval_addrmode_refl (id_reloc_offset z i') a rs).
    1-2: intros HAddrmode; rewrite HAddrmode; auto.
    
    (* lea *)
    rewrite HInsEQ.
    generalize (eval_addrmode32_refl (id_reloc_offset z i') a rs).
    intros HAddrmode. rewrite HAddrmode. auto.

    (* sall *)
    destruct i';unfold RelocBinDecode.instr_eq in HInsEQ; try(exfalso; apply HInsEQ).
    destruct HInsEQ as [Hrd Hn].
    rewrite Hrd. admit.

    (* test *)
    destruct i';unfold RelocBinDecode.instr_eq in HInsEQ; try(exfalso; apply HInsEQ).
    destruct HInsEQ as [[H10 H23] | [H13 H20]].
    rewrite H10. rewrite H23. auto.
    rewrite H13. rewrite H20.
    unfold exec_instr.
    rewrite Val.and_commut. auto.

    (* jmp *)
    destruct ros; auto.
    rewrite HInsEQ.
    destruct (id_reloc_offset z i').
    f_equal. f_equal.


    generalize (symbol_address_refl RELOC_CODE z0).
    auto. auto.
    
    (* Pcall *)
    destruct i';unfold RelocBinDecode.instr_eq in HInsEQ; try(exfalso; apply HInsEQ).
    unfold exec_instr.
    destruct (get_pc_offset rs);auto.    
    rewrite HInsEQ.
    destruct ros0.
    replace (instr_size (Pcall (inl i) sg0)) with 1.
    replace (instr_size (Pcall (inl i) sg)) with 1.
    destruct (Mem.storev Mptr m
      (Val.offset_ptr (rs RSP) (Ptrofs.neg (Ptrofs.repr (size_chunk Mptr))))
      (Val.offset_ptr (rs PC) (Ptrofs.repr 1))); auto.
    admit. admit.
    replace (instr_size (Pcall (inr i) sg0)) with 5.
    replace (instr_size (Pcall (inr i) sg)) with 5.
    destruct (Mem.storev Mptr m
      (Val.offset_ptr (rs RSP) (Ptrofs.neg (Ptrofs.repr (size_chunk Mptr))))
      (Val.offset_ptr (rs PC) (Ptrofs.repr 5))); auto.
    unfold eval_ros.
    unfold id_reloc_offset. unfold Reloctablesgen.instr_reloc_offset.
    generalize (symbol_address_refl RELOC_CODE (z+1)).
    intros HAddr.
    rewrite HAddr. auto.
    admit. admit.

    (* Pmov_rm_a *)
    destruct i';unfold RelocBinDecode.instr_eq in HInsEQ; try(exfalso; apply HInsEQ).
    destruct HInsEQ as [Hrd Ha].
    rewrite Hrd. rewrite Ha.
    unfold exec_instr.
    destruct (get_pc_offset rs);auto.
    unfold exec_load.
    destruct Archi.ptr64 eqn:EQW; inversion EQW.
    generalize (eval_addrmode_refl  (id_reloc_offset z (Pmov_rm_a rd a0)) a0 rs).
    intros HAddrmode.
    rewrite HAddrmode.
    unfold id_reloc_offset.
    unfold Reloctablesgen.instr_reloc_offset.
    unfold tge. 
    (* int32 and any32 *)
    replace Mint32 with Many32.
    admit.
    admit.

    (* Pmov_mr_a , will have the same problem *)
    admit.
    destruct i';unfold RelocBinDecode.instr_eq in HInsEQ; try(exfalso; apply HInsEQ).
    unfold exec_instr.
    destruct (get_pc_offset rs); auto.
    unfold exec_instr. admit.

    destruct i';unfold RelocBinDecode.instr_eq in HInsEQ; try(exfalso; apply HInsEQ).
    admit.
    unfold exec_instr. auto.

  +
    rewrite <- MS.
    econstructor.
    eauto.
    generalize (not_find_ext_funct_refl _ _ H0).
    auto.
    admit.
    eauto.
    admit.    
    admit.
    auto.
    eauto.

  + rewrite <- MS.
    admit.
    
Admitted.


    
    
    

  
  


Lemma transf_program_correct:
  forall rs, forward_simulation (RelocProgSemantics1.semantics prog rs) (RelocProgSemantics2.semantics tprog rs).
Proof.
  intro rs.
  apply forward_simulation_step with (match_states := fun x y : Asm.state => x = y).
  + simpl.
    unfold match_prog, transf_program in TRANSF. monadInv TRANSF.
    unfold globalenv, genv_senv. simpl.
    unfold RelocProgSemantics.globalenv. simpl. intro id.
    rewrite ! RelocProgSemantics.genv_senv_add_external_globals. simpl. auto.
  + simpl. intros s1 IS.
    inversion IS.
    generalize (transf_initial_states _ _ IS).
    auto.
  +  (* final state *)
    intros s1 s2 r HState HFinal.
    eapply transf_final_states; eauto.
  + simpl. intros s1 t s1' HStep s2 HState.
    exists s1'.
    split;auto.
    

    


    
Admitted.

End PRESERVATION.

Require Import RelocLinking1.
Definition link_reloc_bingen (p1 p2: RelocProgram.program) : option RelocProgram.program :=
  match RelocProgSemantics2.decode_prog_code_section p1, RelocProgSemantics2.decode_prog_code_section p2 with
    | OK pp1, OK pp2 =>
      match RelocLinking1.link_reloc_prog pp1 pp2 with
        Some pp =>
        match RelocBingen.transf_program pp with
        | OK tp => Some tp
        | _ => None
        end
      | _ => None
      end
    | _, _ => None
  end.

Instance linker2 : Linker RelocProgram.program.
Proof.
  eapply Build_Linker with (link := link_reloc_bingen) (linkorder := fun _ _ => True).
  auto. auto. auto.
Defined.

Instance tl : @TransfLink _ _ RelocLinking1.Linker_reloc_prog
                          linker2
                          match_prog.
Proof.
  red. simpl. unfold link_reloc_bingen.
  intros.
  erewrite reverse_decode_prog_code_section. 2: exact H0.
  erewrite reverse_decode_prog_code_section. 2: exact H1.
  rewrite H.
Admitted.
