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



Lemma list_has_tail: forall {A:Type} (l:list A) n,
    (length l = 1 + n)%nat
    ->exists tail prefix, l = prefix++[tail].
Proof.
  intros A l n.
  revert l.
  induction n.
  intros l H.
  destruct l; simpl in H; inversion H.
  exists a. exists [].
  simpl.
  generalize (length_zero_iff_nil l).
  intros H0. destruct H0.
  rewrite(H0 H1). auto.
  intros l H.
  replace (1 + Datatypes.S n)%nat with (Datatypes.S (1+n)%nat)%nat in H by omega.
  destruct l; simpl in H; inversion H.
  generalize (IHn l H1).
  intros [tail [prefix HHasTail]].
  exists tail. exists (a::prefix).
  rewrite HHasTail. simpl. auto.
Qed.


Definition match_prog p tp :=
  transf_program p = OK tp.

Lemma transf_program_match:
  forall p tp, transf_program p = OK tp -> match_prog p tp.
Proof.
  intros. subst. red.
  auto.
Qed.

Fixpoint instr_size_acc code: Z :=
  match code with
  |nil => 0
  |i::tail => instr_size i + instr_size_acc tail
  end.

Lemma instr_size_app: forall n a b,
    length a = n
    -> instr_size_acc (a++b) = instr_size_acc a + instr_size_acc b.
Proof.
  induction n.
  (* base case *)
  admit.
  intros a b HLa.
  generalize (list_has_tail _ _ HLa).
  intros [tail [prefix Ha]].
  rewrite Ha.
  cut(length prefix = n).
  intros HLPrefix.
  generalize(IHn prefix ([tail]++b) HLPrefix).
  intros HApp.
  rewrite <- app_assoc.
  rewrite HApp.
  generalize(IHn prefix [tail] HLPrefix).
  intros HPrefixTail.
  rewrite HPrefixTail.
  assert(HTailB: instr_size_acc ([tail]++b) = instr_size_acc [tail] + instr_size_acc b). {
    unfold instr_size_acc.
    simpl. omega.
  }
  rewrite HTailB. omega.
  admit.    
Admitted.

Fixpoint transl_code_spec code bytes ofs rtbl_ofs_map symbt: Prop :=
  match code, bytes  with
  |nil, nil => True 
  |h::t, _ =>
   exists h' t', RelocBinDecode.fmc_instr_decode rtbl_ofs_map symbt ofs bytes = OK (h',t')
                 /\  RelocBinDecode.instr_eq h h'
                 /\ transl_code_spec t t' (ofs+instr_size h) rtbl_ofs_map  symbt
  |_, _ => False
  end.


Lemma prefix_success: forall rtbl a b ofs r z l,
    fold_left (acc_instrs rtbl) (a ++ [b]) (OK (ofs, r)) = OK (z, l)
    ->exists z' l', fold_left (acc_instrs rtbl) a  (OK (ofs, r)) = OK (z', l').
Proof.
  intros rtbl a b ofs r z l HFoldPrefix.
  rewrite fold_left_app in HFoldPrefix.
  inversion HFoldPrefix.
  monadInv H0.
  destruct x.
  exists z0. exists l0.
  unfold acc_instrs.
  auto.
Qed.  

Lemma fold_spec_length: forall n rtbl code ofs r z l,
    length code = n ->
    fold_left (acc_instrs rtbl) (code) (OK (ofs, r)) = OK (z, l)
    -> z = ofs + instr_size_acc code.
Proof.
  induction n.
  (* base case *)
  admit.
  intros rtbl code ofs r z l HLCode HFoldAll.
  generalize (list_has_tail code n HLCode).
  intros [tail [prefix HCode]].
  rewrite HCode in HFoldAll.
  generalize (prefix_success _ _ _ _ _ _ _ HFoldAll).
  intros [z' [l' HFoldPrefix]].
  assert(HLPrefix: length prefix = n) by admit. 
  generalize(IHn rtbl prefix _ _ _ _ HLPrefix HFoldPrefix).
  intros Hz'.
  rewrite fold_left_app in HFoldAll.
  rewrite HFoldPrefix in HFoldAll.
  simpl in HFoldAll.
  monadInv HFoldAll.
  rewrite (instr_size_app (length prefix)).
  simpl.
  omega.
  auto.
Admitted.


Lemma decode_app:forall x rtbl_ofs_map symbt ofs bytes h t,
    RelocBinDecode.fmc_instr_decode rtbl_ofs_map symbt ofs bytes =OK (h, t)                 
    -> RelocBinDecode.fmc_instr_decode rtbl_ofs_map symbt ofs (bytes++x) = OK (h, t++x).
Proof.
  intros x rtbl_ofs_map symbt ofs bytes h t HDecode.
  unfold RelocBinDecode.fmc_instr_decode in HDecode.
  inversion HDecode.
  destruct bytes;inversion H0.
  unfold RelocBinDecode.fmc_instr_decode.
  simpl.
  (* nop *)
  destruct Byte.eq_dec; inversion HDecode; auto.
  (* jmp *)
  destruct Byte.eq_dec.
  unfold  RelocBinDecode.decode_jmp_l_rel.
  unfold  RelocBinDecode.decode_jmp_l_rel in H2.
  destruct bytes. simpl in H2. inversion H2.
  unfold RelocBinDecode.decode_int_n in H2.
  unfold RelocBinDecode.sublist in H2.
  unfold decode_int in H2.
  unfold int_of_bytes in H2. simpl.
  (** *Something is wrong *)
Admitted.



Lemma transl_code_spec_inc: forall code ofs rtbl_ofs_map symbt bytes instr x,
    (* length code = n -> *)
    transl_code_spec code bytes ofs rtbl_ofs_map symbt
    -> encode_instr rtbl_ofs_map (ofs+(instr_size_acc code)) instr = OK x
    -> transl_code_spec (code++[instr]) (bytes++x) ofs rtbl_ofs_map symbt.
Proof.
  induction code as [|i code].
  - intros ofs rtbl_ofs_map symbt bytes instr x TL EN.
    cbn.
    unfold instr_size_acc in EN. rewrite Z.add_0_r in EN.
    cbn in TL. destruct bytes; try contradiction. cbn.
    generalize (RelocBinDecode.encode_decode_instr_refl _ symbt _ _ _ nil EN).
    rewrite app_nil_r.
    intros (i' & DE & EQ).
    exists i', nil. split; auto.
  - intros ofs rtbl_ofs_map symbt bytes instr x TL EN.
    cbn in TL.
    destruct TL as (h' & t' & DE & EQ & TL).
    cbn in EN. rewrite Z.add_assoc in EN.
    cbn.
    generalize (IHcode _ _ _ _ _ _ TL EN).
    intros TL'.
    exists h', (t' ++ x).
    split; auto.
    generalize(decode_app x _ _ _ _ _ _ DE).
    auto.
Qed.



(* This lemma means the transl_code could preserve the spec 
 * Specifically, if there're two list, code code', having the relation `transl_code_spec` ,
 * where code is list asm, code' is list byte.
 * Then after translation code2 starting from code', we'll get the result 
 * that has `transl_code_spce` relation with (code++code2) 
 *)
Lemma transl_code_spec_prsv: forall code code' code2 l ofs rtbl_ofs_map symbt z n,
    transl_code_spec code (rev code') ofs rtbl_ofs_map symbt
    -> length code2 = n
    -> fold_left (acc_instrs rtbl_ofs_map) code2 (OK (ofs + (instr_size_acc code), code')) = OK (z, l)
    -> transl_code_spec (code ++ code2) (rev l) ofs rtbl_ofs_map symbt.
Proof.
  intros code code' code2 l ofs rtbl_ofs_map symbt z n HTransCode.
  revert dependent l.
  revert dependent z.
  revert dependent code2.
  revert dependent n.
  induction n.
  (* base case *)
  admit.
  intros code2 z l HLCode2 HFoldCode2.
  generalize (list_has_tail code2 n HLCode2).
  intros [tail [prefix HCode2]].
  rewrite HCode2.
  assert(HLPrefix: length prefix = n) by admit.
  rewrite HCode2 in HFoldCode2.
  generalize (prefix_success _ _ _ _ _ _ _ HFoldCode2).
  intros [z' [l' HFoldPrefix]].
  
  generalize (IHn prefix _ _ HLPrefix HFoldPrefix).
  rewrite fold_left_app in HFoldCode2.
  rewrite HFoldPrefix in HFoldCode2.
  generalize (fold_spec_length (length prefix) _ _ _ _ _ _ eq_refl HFoldPrefix).
  intros Hz'.
  rewrite Hz' in HFoldCode2.
  simpl in HFoldCode2.
  monadInv HFoldCode2.
  intros HSpecPrefix.
  assert(HInstrSize: instr_size_acc (code ++ prefix) = instr_size_acc code + instr_size_acc prefix) by admit.
  rewrite <- Zplus_assoc in EQ.
  rewrite <- HInstrSize in EQ.
  generalize (transl_code_spec_inc _ _ _ _ _ _ _ HSpecPrefix EQ).
  rewrite app_assoc.
  intros HResult.
  rewrite rev_app_distr.
  rewrite rev_involutive.
  auto.  
Admitted.


Lemma decode_encode_refl: forall n prog z code l,
    length code = n ->
    fold_left (acc_instrs (gen_reloc_ofs_map (reloctable_code (prog_reloctables prog)))) code (OK (0, [])) = OK (z, l)
    -> transl_code_spec code (rev l) 0 (gen_reloc_ofs_map (reloctable_code (prog_reloctables prog))) (prog_symbtable prog).
Proof.
  intros n.
  induction n.
  (* n is O *)
  admit.
  (* n is S n *)
  intros prog z code l HLength HEncode.
  generalize (list_has_tail code _ HLength).
  intros [lastInstr [prefix HTail]].

  rewrite HTail in HEncode.
  generalize (prefix_success _ _ _ _ _ _ _ HEncode).
  intros [z' [l' HEncodePrefix]].

  cut(length prefix = n).
  intros HLengthN.
  generalize (IHn prog z' prefix l' HLengthN HEncodePrefix).
  intros HPrefix.
  rewrite fold_left_app in HEncode.
  rewrite HEncodePrefix in HEncode.
  (* generalize (suffix_success _ _ _ 0 [] z l z' l'  HEncode HEncodePrefix). *)
  (* intros HEncodeSuffix. *)
  (* simpl in Hz'. *)
  (* rewrite Hz' in HEncodeSuffix. *)
  generalize (fold_spec_length (length prefix) _ _ _ _ _ _ eq_refl HEncodePrefix).
  intros Hz'.
  rewrite Hz' in HEncode.
  generalize (transl_code_spec_prsv prefix l' [lastInstr] _ _ _ _ _ 1 HPrefix eq_refl HEncode).
  rewrite HTail.
  auto.
  admit.
Admitted.


Fixpoint instr_eq_list code1 code2:=
  match code1, code2 with
  |nil, nil => True
  |h::t, h'::t' => RelocBinDecode.instr_eq h h' /\ instr_eq_list t t'
  |_, _ => False
  end.

Lemma decode_instrs_append': forall rtbl symtbl fuel ofs t l1 l2 code,
    decode_instrs rtbl symtbl fuel ofs t l1 = OK code ->
    decode_instrs rtbl symtbl fuel ofs t (l1 ++ l2) = OK (rev l2 ++ code).
Proof.
  induction fuel as [|fuel].
  - (* base case *)
    intros ofs t l1 l2 code DI.
    cbn in DI. destruct t; try congruence. inv DI.
    cbn. rewrite rev_app_distr. auto.
  - 
    intros ofs t l1 l2 code DI.
    cbn in DI. destruct t.
    + inv DI. cbn. rewrite rev_app_distr. auto.
    + monadInv DI. destruct x as (instr, bytes').
      apply (IHfuel _ _ _ l2) in EQ0.
      cbn ["++"] in EQ0.
      unfold decode_instrs. rewrite EQ. cbn.
      exact EQ0.
Qed.

Lemma decode_instrs_append: forall rtbl symtbl fuel ofs t l code,
    decode_instrs rtbl symtbl fuel ofs t [] = OK code ->
    decode_instrs rtbl symtbl fuel ofs t l = OK (rev l ++ code).
Proof.
  intros rtbl symtbl fuel ofs t l code DI.
  apply (decode_instrs_append' _ _ _ _ _ _ l) in DI.
  cbn in DI. auto.
Qed.


Lemma spec_decode_ex: forall code ofs l rtbl symtbl,
    transl_code_spec code l ofs rtbl symtbl ->
    exists fuel code', decode_instrs rtbl symtbl fuel ofs l nil = OK code'
             /\ instr_eq_list code code'.
Proof.
  induction code as [|i code].
  - (* base case *)
    intros ofs l rtbl symtbl TL.
    cbn in TL. destruct l; try contradiction.
    cbn. exists O, nil. split; auto.
  - intros ofs l rtbl symtbl TL.
    cbn in TL.
    destruct TL as (h' & t' & DE & EQ & TL).
    generalize (IHcode _ _ _ _ TL).
    intros (fuel & code' & DE' & EQ').
    exists (Datatypes.S fuel), (h'::code').
    split.
    cbn. destruct l. cbn in DE. congruence.
    rewrite DE. cbn.
    assert (instr_size i = instr_size h') as IEQ. {
      destruct i;
        simpl in EQ;
        try(rewrite EQ;
            auto);
        try(destruct h';inversion EQ; auto).

      1-2: rewrite H; rewrite H0; auto.
    }
      
      
    rewrite <- IEQ.
    generalize (decode_instrs_append _ _ _ _ _ [h'] _ DE').
    intros HAppend.
    simpl in HAppend.
    auto.
    simpl. auto.
Qed.

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
    repeat (destruct v; inversion EQ;
            destruct s; inversion EQ).
    monadInv EQ.
    simpl.
    unfold transl_code in EQ0.
    monadInv  EQ0.
    destruct x. monadInv EQ2.    
    generalize (decode_encode_refl (length code) prog _ _ _  eq_refl EQ1).
    intros HTranslSpec.
    generalize (spec_decode_ex code 0 (rev l) _ _  HTranslSpec).
    intros (fuel & c' & HEncodeDecode).
    destruct HEncodeDecode as [HDecode HDecodeEQ].
    econstructor.
    unfold decode_prog_code_section.
    simpl. unfold sec_code_id.
    (* rewrite HDecode. simpl. eauto. *)

    (* init_mem *)
    admit.
    (* initial_state_gen *)
    admit.
  (* + reflexivity. *)
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
Proof.
  inversion TRANSF. unfold ge.
  unfold transf_program in H0.
  monadInv H0. simpl.
  intros b ofs Hge.

  (** *TODO Help3 *)
  (* unfold RelocProgSemantics.Genv.genv_ext_funs. *)
  (* unfold RelocProgSemantics.globalenv. simpl. *)
  (* unfold RelocProgSemantics.Genv.genv_ext_funs in Hge. *)
  (* unfold RelocProgSemantics.globalenv in Hge. simpl in Hge. *)
  (* unfold RelocProgSemantics.gen_extfuns. *)
  (* unfold RelocProgSemantics.add_external_globals. *)
  (* inversion Hge. *)  
Admitted.

Definition ge_eq (ge1 ge2: RelocProgSemantics.Genv.t) : Prop :=
  ge1.(RelocProgSemantics.Genv.genv_symb) = ge2.(RelocProgSemantics.Genv.genv_symb) /\
  ge1.(RelocProgSemantics.Genv.genv_ext_funs) = ge2.(RelocProgSemantics.Genv.genv_ext_funs) /\
  ge1.(RelocProgSemantics.Genv.genv_next) = ge2.(RelocProgSemantics.Genv.genv_next) /\ 
  ge1.(RelocProgSemantics.Genv.genv_senv) = ge2.(RelocProgSemantics.Genv.genv_senv) /\
  forall ofs i, ge1.(RelocProgSemantics.Genv.genv_instrs) ofs = Some i -> 
           exists i', ge2.(RelocProgSemantics.Genv.genv_instrs) ofs = Some i' /\ RelocBinDecode.instr_eq i i'.

Definition ge_eq1 (ge1 ge2: RelocProgSemantics1.Genv.t) : Prop :=
  ge1.(Genv.genv_reloc_ofs_symb) = ge2.(Genv.genv_reloc_ofs_symb) /\
  ge_eq (ge1.(Genv.genv_genv)) (ge2.(Genv.genv_genv)).

Lemma transf_program_pres_genv: forall p1 p2,
    transf_program p1 = OK p2 ->
    ge_eq1 (globalenv p1) (globalenv p2).
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
  unfold RelocProgSemantics.add_external_globals.
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
    fold ge in HStep.
    generalize(step_simulation _ _ _ HStep s2 HState).
    auto.
Qed.
    

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
