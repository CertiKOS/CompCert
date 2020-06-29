Require Import Coqlib Errors.
Require Import Integers Floats AST Linking OrderedLinking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import RelocProgram.
Require Import RemoveAddend.
Require Import RelocProgSemantics2.
Require Import RelocBingenproof.

Import ListNotations.

Definition match_prog (p tp:RelocProgram.program) :=
  transf_program p = tp.

Lemma transf_program_match:
  forall p tp, transf_program p = tp -> match_prog p tp.
Proof.
  intros. red. auto.
Qed.

(** Preservation of semantics under permutation *)
Section PRESERVATION.

Context `{external_calls_prf: ExternalCalls}.

Variables prog tprog: RelocProgram.program.

Hypothesis transf_encode: RemoveAddend.transf_program prog = tprog.

Lemma gen_reloc_ofs_map_ext:
  forall rtbl k,
    Maps.PTree.get k (Maps.PTree.map (fun _ => remove_addend_relocentry) (gen_reloc_ofs_map rtbl)) =
    Maps.PTree.get k (gen_reloc_ofs_map (map remove_addend_relocentry rtbl)).
Proof.
  unfold gen_reloc_ofs_map.
  induction rtbl; simpl; intros; eauto.
  rewrite Maps.PTree.gmap.
  unfold acc_reloc_ofs_map at 1 3.
  unfold Maps.ZTree.set.
  rewrite ! Maps.PTree.gsspec.
  unfold remove_addend_relocentry at 2. simpl.
  destr.
  rewrite <- IHrtbl. rewrite Maps.PTree.gmap. reflexivity.
Qed.

Section EXT.
  Variables rtbl1 rtbl2: Maps.ZTree.t relocentry.
  Hypothesis EXT:
    forall k, option_map remove_addend_relocentry (Maps.PTree.get k rtbl1) = Maps.PTree.get k rtbl2.
  
Lemma decode_call_ext:
  forall symt ofs bytes,
    RelocBinDecode.decode_call rtbl1 symt ofs bytes = RelocBinDecode.decode_call rtbl2 symt ofs bytes.
Proof.
  intros. unfold RelocBinDecode.decode_call.
  unfold bind. destr. unfold RelocBinDecode.find_ofs_in_rtbl.
  unfold Maps.ZTree.get. rewrite <- EXT. destr.
Qed.

Lemma addrmode_parse_SIB_ext:
  forall ofs bytes modrm sib,
    RelocBinDecode.addrmode_parse_SIB rtbl1 ofs modrm sib bytes =
    RelocBinDecode.addrmode_parse_SIB rtbl2 ofs modrm sib bytes.
Proof.
  unfold RelocBinDecode.addrmode_parse_SIB.
  intros.
  unfold RelocBinDecode.find_ofs_in_rtbl. unfold Maps.ZTree.get. rewrite <- EXT.
  repeat destr.
Qed.

Lemma decode_addrmode_ext:
  forall ofs bytes,
    RelocBinDecode.decode_addrmode rtbl1 ofs bytes = RelocBinDecode.decode_addrmode rtbl2 ofs bytes.
Proof.
  intros.
  unfold RelocBinDecode.decode_addrmode.
  destruct bytes. auto.
  unfold bind. repeat (destr; [idtac]).
  destr.
  - destr. destr.
    + destr. destr. erewrite addrmode_parse_SIB_ext; eauto.
    + destr. destr. unfold RelocBinDecode.find_ofs_in_rtbl; unfold Maps.ZTree.get; rewrite <- EXT; eauto.
      destr.
  - destruct (Byte.eq_dec).
    + destr. destr. destr. destr. erewrite addrmode_parse_SIB_ext; eauto.
    + destr. destr. destr. destr. destr. erewrite addrmode_parse_SIB_ext; eauto.
      destr. unfold RelocBinDecode.find_ofs_in_rtbl; unfold Maps.ZTree.get; rewrite <- EXT; eauto.
      destr.
Qed.

Lemma decode_leal_ext:
  forall ofs bytes,
    RelocBinDecode.decode_leal rtbl1 ofs bytes = RelocBinDecode.decode_leal rtbl2 ofs bytes.
Proof.
  intros. unfold RelocBinDecode.decode_leal.
  unfold bind. destr.
  erewrite decode_addrmode_ext; eauto.
Qed.

Lemma decode_movl_rm_ext:
  forall ofs bytes,
    RelocBinDecode.decode_movl_rm rtbl1 ofs bytes = RelocBinDecode.decode_movl_rm rtbl2 ofs bytes.
Proof.
  unfold RelocBinDecode.decode_movl_rm.
  intros. unfold bind. destr. erewrite decode_addrmode_ext; eauto.
Qed.

Lemma decode_movl_mr_ext:
  forall ofs bytes,
    RelocBinDecode.decode_movl_mr rtbl1 ofs bytes = RelocBinDecode.decode_movl_mr rtbl2 ofs bytes.
Proof.
  unfold RelocBinDecode.decode_movl_mr.
  intros. unfold bind. destr. erewrite decode_addrmode_ext; eauto.
Qed.

Lemma decode_8b_ext:
  forall ofs bytes,
    RelocBinDecode.decode_8b rtbl1 ofs bytes = RelocBinDecode.decode_8b rtbl2 ofs bytes.
Proof.
  unfold RelocBinDecode.decode_8b. intros. unfold bind. destr. destr.
  eapply decode_movl_rm_ext; eauto.
Qed.


Lemma fmc_instr_decode_ext:
  forall symt ofs bytes,
    RelocBinDecode.fmc_instr_decode rtbl1 symt ofs bytes  =
    RelocBinDecode.fmc_instr_decode rtbl2 symt ofs bytes.
Proof.
  unfold RelocBinDecode.fmc_instr_decode. intros.
  destruct bytes. auto.
  repeat (destruct Byte.eq_dec; [auto; fail|]).
  destruct Byte.eq_dec. apply decode_call_ext; auto.
  destruct Byte.eq_dec. apply decode_leal_ext; auto.
  destruct Byte.eq_dec. auto.
  destruct Byte.eq_dec. auto.
  destruct Byte.eq_dec. auto.
  destruct Byte.eq_dec. auto.
  destruct Byte.eq_dec. eapply decode_8b_ext; eauto.
  destruct Byte.eq_dec. eapply decode_movl_mr_ext; eauto.
  destruct Byte.eq_dec. auto.
  destruct Byte.eq_dec. auto.
  destruct Byte.eq_dec. auto.
  destruct Byte.eq_dec. auto.
  destruct Byte.eq_dec. auto.
  destruct Byte.eq_dec. auto.
  destruct Byte.eq_dec. auto.
  auto.
Qed.

Lemma decode_instrs_ext:
  forall symt fuel ofs bytes instrs,
    decode_instrs rtbl1 symt fuel ofs bytes instrs  =
    decode_instrs rtbl2 symt fuel ofs bytes instrs.
Proof.
  induction fuel. simpl. auto.
  simpl. intros. destruct bytes. auto.
  erewrite (fmc_instr_decode_ext symt ofs (i::bytes)). unfold bind.
  destruct (RelocBinDecode.fmc_instr_decode). 2: auto.
  destruct p. apply IHfuel.
Qed.

Lemma decode_instrs'_ext:
  forall symt s,
    decode_instrs' rtbl1 symt s = decode_instrs' rtbl2 symt s.
Proof.
  intros.
  unfold decode_instrs'.
  erewrite decode_instrs_ext. auto.
Qed.

Lemma decode_code_section_ext:
  forall symt s,
    decode_code_section rtbl1 symt s = decode_code_section rtbl2 symt s.
Proof.
  unfold decode_code_section. intros.
  destruct s. auto. auto.
  erewrite decode_instrs'_ext. auto.
Qed.

End EXT.

Lemma decode_prog_section_correct:
  forall prog',
    decode_prog_code_section prog = OK prog' ->
    exists tprog',
      decode_prog_code_section (transf_program prog) = OK tprog' /\
      match_prog prog' tprog'.
Proof.
  intros.
  unfold transf_program.
  unfold decode_prog_code_section in *. simpl. autoinv.
  erewrite <- decode_code_section_ext. rewrite ! EQ. simpl. rewrite Heqo0.
  eexists; split; eauto.
  red. unfold transf_program. simpl. eauto.
  intros. rewrite <- gen_reloc_ofs_map_ext.
  rewrite Maps.PTree.gmap. auto.
Qed.

Lemma match_prog_init_mem:
  forall p m,
    init_mem p = Some m ->
    init_mem (transf_program p) = Some m.
Proof.
  unfold init_mem. intros.
  unfold transf_program. simpl. auto.
Qed.

Lemma gen_reloc_ofs_symb_ext:
  forall stbl rtbl,
    RelocProgSemantics1.gen_reloc_ofs_symb stbl (remove_addend_reloctable rtbl) =
    RelocProgSemantics1.gen_reloc_ofs_symb stbl rtbl.
Proof.
  unfold RelocProgSemantics1.gen_reloc_ofs_symb.
  induction rtbl; simpl; intros; eauto.
  rewrite IHrtbl.
  unfold RelocProgSemantics1.acc_reloc_ofs_symb at 1 3. simpl. destr.
Qed.

Lemma add_reloc_ofs_symb_ext:
  forall stbl id rtblmap t,
    RelocProgSemantics1.add_reloc_ofs_symb stbl id (remove_addend_reloctable_map rtblmap) t =
    RelocProgSemantics1.add_reloc_ofs_symb stbl id rtblmap t.
Proof.
  unfold RelocProgSemantics1.add_reloc_ofs_symb. intros.
  apply Axioms.extensionality. intros. destr. subst. unfold get_reloctable. unfold remove_addend_reloctable_map. simpl.
  destruct x; simpl; apply gen_reloc_ofs_symb_ext.
Qed.

Lemma genv_eq:
  forall p,
    RelocProgSemantics1.globalenv p = RelocProgSemantics1.globalenv (transf_program p).
Proof.
  intros.
  unfold transf_program.
  unfold RelocProgSemantics1.globalenv.
  f_equal.
  unfold RelocProgSemantics1.gen_reloc_ofs_symbs. simpl.
  rewrite ! add_reloc_ofs_symb_ext. auto.
Qed.

Theorem transf_program_correct rs:
  forward_simulation (RelocProgSemantics2.semantics prog rs)
                     (RelocProgSemantics2.semantics tprog rs).
Proof.
  unfold semantics.
  eapply forward_simulation_step with (match_states := fun (e1 e2: Asm.state) => e1 = e2); simpl; intuition try congruence; subst; eauto.
  - inv H.
    exploit decode_prog_section_correct. eauto. intros (tprog' & DEC & MP).
    eexists; split; eauto. econstructor. eauto.
    red in MP. subst.
    eapply match_prog_init_mem; eauto.
    inv H2.
    unfold rs0.
    replace ge with (RelocProgSemantics1.globalenv tprog').
    replace (prog_main prog') with (prog_main tprog').
    econstructor; eauto.
    red in MP; subst; unfold transf_program. reflexivity.
    unfold ge.
    red in MP; subst. symmetry. apply genv_eq.
  - rewrite <- genv_eq. eexists; split; eauto.
Qed.

End PRESERVATION.

Lemma update_reloc_symb_remove_addend:
  forall sym sim rtbl r,
    RelocLinking1.update_reloc_symb sym sim rtbl = Some r ->
    RelocLinking1.update_reloc_symb sym sim (remove_addend_relocentry rtbl) = Some (remove_addend_relocentry r).
Proof.
  unfold RelocLinking1.update_reloc_symb. intros. simpl. autoinv. reflexivity.
Qed.

Lemma update_reloctable_symb_remove_addend:
  forall sym sim rtbl r,
    RelocLinking1.update_reloctable_symb sym sim rtbl = Some r ->
    RelocLinking1.update_reloctable_symb sym sim (remove_addend_reloctable rtbl) = Some (remove_addend_reloctable r).
Proof.
  unfold RelocLinking1.update_reloctable_symb.
  induction rtbl; simpl; intros; eauto. inv H. auto.
  unfold RelocLinking1.acc_update_reloc_symb in H at 1.
  unfold RelocLinking1.acc_update_reloc_symb at 1.
  autoinv.
  erewrite IHrtbl. 2: eauto. simpl.
  erewrite update_reloc_symb_remove_addend; eauto.
Qed.

Lemma remove_addend_reloctable_app:
  forall l1 l2,
    remove_addend_reloctable (l1 ++ l2) = remove_addend_reloctable l1 ++ remove_addend_reloctable l2.
Proof.
  unfold remove_addend_reloctable.
  intros. rewrite map_app. auto.
Qed.

Lemma link_reloctable_remove_addend:
  forall z sym1 sym2 sim rtbl1 rtbl2 rtbl,
    RelocLinking1.link_reloctable z sym1 sym2 sim rtbl1 rtbl2 = Some rtbl ->
    RelocLinking1.link_reloctable z sym1 sym2 sim (remove_addend_reloctable rtbl1) (remove_addend_reloctable rtbl2) = Some (remove_addend_reloctable rtbl).
Proof.
  unfold RelocLinking1.link_reloctable.
  intros. autoinv.
  erewrite update_reloctable_symb_remove_addend; eauto.
  erewrite update_reloctable_symb_remove_addend; eauto.
  rewrite remove_addend_reloctable_app.
  f_equal. f_equal. unfold remove_addend_reloctable. rewrite ! map_map.
  apply list_map_exten. intros.
  unfold remove_addend_relocentry. simpl. unfold RelocLinking1.shift_relocentry_offset. simpl. reflexivity.
Qed.


Instance tl' : @TransfLink _ _ RelocLinking1.Linker_reloc_prog RelocLinking1.Linker_reloc_prog match_prog.
Proof.
  red. unfold link. simpl.
  unfold RelocLinking1.link_reloc_prog. unfold match_prog. intros. autoinv.
  unfold transf_program. simpl.
  unfold RelocLinking.link_reloc_prog in *. simpl in *. autoinv. simpl in *.
  unfold RelocLinking1.link_data_reloctable in *. autoinv. simpl in *.
  rewrite Heqo.
  erewrite link_reloctable_remove_addend; eauto.
  unfold RelocLinking1.link_code_reloctable in *. autoinv. simpl in *.
  rewrite Heqo0.
  erewrite link_reloctable_remove_addend; eauto.
  eexists; split; eauto.
Defined.

(*
  
  exploit tl. apply Heqo. eauto. eauto. intros (tp & LINK & MP).
  simpl in LINK. rewrite LINK.

  Lemma match_prog_relocbingen:
    forall p tp p',
      RelocBingen.transf_program p = OK tp ->
      match_prog p p' ->
    exists tp',
      RelocBingen.transf_program p' = OK tp' /\
      match_prog tp tp'.
  Proof.
    unfold RelocBingen.transf_program. unfold match_prog, transf_program.
    intros. subst. simpl in *. autoinv. simpl in *.

    Lemma transl_sectable_remove_addend:
      forall sect rtblmap,
        RelocBingen.transl_sectable sect (remove_addend_reloctable_map rtblmap) =
        RelocBingen.transl_sectable sect rtblmap.
    Proof.
      unfold RelocBingen.transl_sectable.
      intros. repeat destr.
      simpl.


      Lemma encode_addrmode_remove_addend:
        forall rtbl1 rtbl2,
          (forall k, option_map remove_addend_relocentry (Maps.PTree.get k rtbl1) = Maps.PTree.get k rtbl2) ->
          forall z i a r,
            RelocBingen.encode_addrmode rtbl2 z i a r =
            RelocBingen.encode_addrmode rtbl1 z i a r.
      Proof.
        unfold RelocBingen.encode_addrmode. intros. destr.
        unfold bind. destr. repeat destr. autoinv.
        unfold RelocBingen.get_instr_reloc_addend' in *.
        unfold RelocBingen.get_reloc_addend in *.
        
      Lemma encode_instr_remove_addend:
        forall rtbl1 rtbl2,
          (forall k, option_map remove_addend_relocentry (Maps.PTree.get k rtbl1) = Maps.PTree.get k rtbl2) ->
          forall z i,
            RelocBingen.encode_instr rtbl2 z i =
            RelocBingen.encode_instr rtbl1 z i.
      Proof.
        unfold RelocBingen.encode_instr. intros.
        destr.

        induction code; simpl; intros; eauto.
        
      Qed.

      Lemma acc_instrs_remove_addend:
        forall rtbl1 rtbl2,
          (forall k, option_map remove_addend_relocentry (Maps.PTree.get k rtbl1) = Maps.PTree.get k rtbl2) ->
          forall code z l,
            fold_left (RelocBingen.acc_instrs rtbl2) code (OK (z, l)) =
            fold_left (RelocBingen.acc_instrs rtbl1) code (OK (z, l)).
      Proof.
        induction code; simpl; intros; eauto.

      Qed.
      
    Lemma transl_code_remove_addend:
      forall rtbl1 rtbl2,
        (forall k, option_map remove_addend_relocentry (Maps.PTree.get k rtbl1) = Maps.PTree.get k rtbl2) ->
        forall code,
          RelocBingen.transl_code rtbl2 code = RelocBingen.transl_code rtbl1 code.
    Proof.
      unfold RelocBingen.transl_code.
      intros.

      induction code; simpl; auto.
    Qed.

  Qed.
  
  unfold transf_program. intros. subst. intros.
  unfold decode_prog_code_section in *. simpl in *.
  autoinv.
  erewrite <- decode_code_section_ext. rewrite EQ. simpl.
  erewrite <- decode_code_section_ext. rewrite EQ0. simpl.
  rewrite Heqo2, Heqo3.
  eexists; split; eauto.
  2: 
Defined.

Require Import RelocLinking.


Instance tl : TransfLink match_prog.
Proof.
  red.
  unfold link. simpl.
  unfold match_prog.
  unfold link_reloc_prog.
  intros. unfold transf_program. autoinv. simpl.
  rewrite Heqo. rewrite Heqo0, Heqo1, Heqo2, Heqo3, Heqo4. eauto.
Defined.
*)
