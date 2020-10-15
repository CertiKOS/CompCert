Require Import Coqlib Errors.
Require Import Integers Floats AST Linking OrderedLinking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import RelocProgram.
Require Import StrtableEncode StrtableDecode.
Require Import SymbtableEncode SymbtableDecode.
Require Import ShstrtableEncode ShstrtableDecode.
Require Import ReloctablesEncode ReloctablesDecode.
Require Import RelocProgSemantics2 RelocProgSemantics3.
Require Import RelocBingenproof.
Require Import TablesEncode.

Import ListNotations.

Definition match_prog (p tp:RelocProgram.program) :=
  transf_program p = OK tp.

Lemma transf_program_match:
  forall p tp, transf_program p = OK tp -> match_prog p tp.
Proof.
  intros. red. auto.
Qed.

(** Preservation of semantics under permutation *)
Section PRESERVATION.

Context `{external_calls_prf: ExternalCalls}.

Variables prog tprog: RelocProgram.program.

Hypothesis transf_encode: TablesEncode.transf_program prog = OK tprog.

Lemma valid_reloctables:
  forall id, Forall valid_relocentry (get_reloctable id (prog_reloctables prog)).
Proof.
  unfold transf_program in transf_encode.
  monadInv transf_encode. repeat destr_in EQ0.
  rewrite dump_reloctables_error in H0. congruence.
Qed.

Lemma valid_symbentries_p:
  forall strmap sbytes idbytes,
    get_strings_map_bytes (fold_right acc_symbols nil (prog_symbtable prog)) = OK (idbytes, strmap, sbytes) ->
    Forall (valid_symbentry strmap) (RelocProgram.prog_symbtable prog).
Proof.
  unfold transf_program in transf_encode.
  monadInv transf_encode. repeat destr_in EQ0.
Qed.

Lemma empty_strtable:
  prog_strtable prog = Maps.PTree.empty Z.
Proof.
  unfold transf_program in transf_encode.
  monadInv transf_encode. repeat destr_in EQ0.
Qed.

Lemma symbentries_no_repet:
  list_norepet (map symbentry_id (prog_symbtable prog)).
Proof.
  unfold transf_program in transf_encode.
  monadInv transf_encode. repeat destr_in EQ0.
Qed.

Lemma prog_strings_eq:
  forall l idbytes strmap sbytes,
    get_strings_map_bytes l = OK (idbytes, strmap, sbytes) ->
    Forall (fun '(_, lb) => lb <> []) idbytes.
Proof.
  intros.
  unfold get_strings_map_bytes in H. monadInv H. repeat destr_in EQ0.
  clear Heqp. revert l idbytes EQ. induction l; simpl; intros; eauto.
  inv EQ; auto.
  unfold acc_symbol_strings in EQ at 1. monadInv EQ. repeat destr_in EQ1.
  constructor; eauto. intro EQm; apply (f_equal (@length _)) in EQm.
  rewrite app_length in EQm; simpl in EQm. omega.
Qed.


Lemma acc_symbols_in_in_symbols:
  forall s x0 l,
    fold_right acc_symbol_strings (OK l) (fold_right acc_symbols [] s) = OK x0 ->
    forall i,
      In i (map fst x0) ->
      In i (map fst l) \/ exists a, In a s /\ symbentry_id a = i.
Proof.
  induction s; simpl; intros x0 l FOLD i IN.
  - inv FOLD. auto.
  - unfold acc_symbols at 1 in FOLD.
    + simpl in FOLD.
      unfold acc_symbol_strings at 1 in FOLD. monadInv FOLD.
      repeat destr_in EQ0.
      simpl in IN. destruct IN as [eq | IN]; subst.
      right; eexists; split; eauto.
      exploit IHs. eauto. eauto. intros [A | [a0 [INs EQs]]]; eauto.
Qed.

Lemma gsmb_valid_strtable:
  forall pi strmap sbytes idbytes,
         let symbols := fold_right acc_symbols [] (prog_symbtable pi) in
         get_strings_map_bytes symbols = OK (idbytes, strmap, sbytes) ->
         forall
         x (EQ0 : fold_right acc_symbol_strings (OK []) (fold_right acc_symbols [] (prog_symbtable pi)) = OK x)
         (LNR: list_norepet (map symbentry_id (prog_symbtable pi)))
,
    valid_strtable x strmap.
Proof.
  intros pi strmap sbytes idbytes symbols GSMB x EQ0 LNR.
  unfold valid_strtable.

  assert (LNR': list_norepet (map fst x)).
  {
    revert x EQ0 LNR.
    generalize (prog_symbtable pi). clear.
    induction s; simpl; intros; eauto.
    - inv EQ0. constructor.
    - unfold acc_symbols at 1 in EQ0.
      simpl in EQ0.
      unfold acc_symbol_strings at 1 in EQ0. monadInv EQ0.
      exploit IHs. apply EQ. inv LNR; auto.
      repeat destr_in EQ1. simpl. intros; constructor; auto.
      intro INi.
      eapply acc_symbols_in_in_symbols in INi; eauto. simpl in INi. destruct INi as [[]|(aa & IN & EQa)].
      inv LNR. apply H2.
      rewrite in_map_iff. eexists; split; eauto.
  }
  unfold get_strings_map_bytes in GSMB.
  unfold symbols in GSMB. rewrite EQ0 in GSMB. simpl in GSMB. repeat destr_in GSMB.
  exists z; split; auto.
  revert z Heqp l.
  assert (valid_strtable_thr idbytes (Maps.PTree.empty Z) 1 /\ 0 < 1).
  {
    split.
    constructor; setoid_rewrite Maps.PTree.gempty; congruence.
    omega.
  }
  generalize strmap.
  destruct H as (VALID & POS).
  revert VALID POS.
  generalize (Maps.PTree.empty Z) 1.
  clear -LNR'.
  assert (forall elt, In elt idbytes -> In elt idbytes) by auto. revert H.
  generalize idbytes at 1 4.
  induction idbytes0; simpl.
  - intros; eauto. inv Heqp. auto.
  - intros IN t z VALID POS t0 z1 FOLD LT.
    destr_in FOLD.
    eapply IHidbytes0 in FOLD. auto. eauto.
    constructor; repeat setoid_rewrite Maps.PTree.gsspec.
    + intros i0 j x1 y bytesx bytesy ox oy. repeat destr.
      * intros Tx Ty Bx By Diff Ox Oy. inv Tx. inv VALID.
        specialize (thr _ _ _ _ Ty By Oy). omega.
      * intros Tx Ty Bx By Diff Ox Oy. inv Ty. inv VALID.
        specialize (thr _ _ _ _ Tx Bx Ox). omega.
      * inv VALID; eauto.
    + intros i0 x1 bytesx ox Tx Bx Ox. destr_in Tx.
      * inv Tx. erewrite Assoc.in_lnr_get_assoc in Bx. 3: apply IN; left; reflexivity. inv Bx; omega.
        auto.
      * inv VALID.
        eapply thr in Bx; eauto. omega.
    + intros i0 x1 EQ. destr_in EQ.
      * inv EQ. erewrite Assoc.in_lnr_get_assoc; eauto.
      * inv VALID; eauto.
    + intros i0 x1 EQ. destr_in EQ.
      * inv EQ.
        apply acc_strmap_fold_lt in FOLD. change (two_p 32) with (Int.max_unsigned + 1).
        omega.
      * inv VALID; eauto.
    + intros i0 EQ. destr_in EQ. inv EQ.
      omega. inv VALID; eauto.
    + omega.
    + auto.
Qed.

Lemma valid_strtable_p:
  forall strmap sbytes idbytes,
    get_strings_map_bytes (fold_right acc_symbols nil (prog_symbtable prog)) = OK (idbytes, strmap, sbytes) ->
    valid_strtable idbytes strmap.
Proof.
  intros. eapply gsmb_valid_strtable; eauto.
  unfold get_strings_map_bytes in H. monadInv H.
  repeat destr_in EQ0.
  eapply symbentries_no_repet.
Qed.

Lemma tables_encode_spec:
  forall prog tprog,
    TablesEncode.transf_program prog = OK tprog ->
    prog_defs prog = prog_defs tprog /\
    prog_public prog = prog_public tprog /\
    prog_main prog = prog_main tprog /\
    prog_symbtable prog = prog_symbtable tprog /\
    prog_reloctables prog = prog_reloctables tprog /\
    prog_senv prog = prog_senv tprog /\
    length (prog_sectable prog) = 3%nat /\
    exists (strmap : Maps.PTree.t Z) (sbytes : list byte) idbytes symt,
      get_strings_map_bytes (fold_right acc_symbols nil (prog_symbtable prog)) =
      OK (idbytes, strmap, sbytes) /\
      create_symbtable_section strmap (prog_symbtable prog) = OK symt /\
      prog_strtable tprog = strmap /\
      prog_sectable tprog =
      prog_sectable prog ++
                    [create_strtab_section sbytes;
                       symt;
                       create_reloctable_section (reloctable_rodata (prog_reloctables prog));
                       create_reloctable_section (reloctable_data (prog_reloctables prog));
                       create_reloctable_section (reloctable_code (prog_reloctables prog));
                       create_shstrtab_section].
Proof.
  clear. intros.
  unfold transf_program in H.
  monadInv H.
  repeat destr_in EQ0.
  monadInv H0.
  repeat destr_in EQ1. simpl. repeat split; auto.
  {
    apply beq_nat_true in Heqb. rewrite app_length in Heqb.
    simpl in Heqb. omega.
  }
  rewrite EQ. exists t, l, l0, x. auto.
  rewrite dump_reloctables_error in H0. congruence.
Qed.

Lemma genv_senv_same:
  RelocProgSemantics1.genv_senv (RelocProgSemantics1.globalenv tprog) =
  RelocProgSemantics1.genv_senv (RelocProgSemantics1.globalenv prog).
Proof.
  unfold RelocProgSemantics1.globalenv. simpl.
  unfold RelocProgSemantics1.genv_senv. simpl.
  unfold RelocProgSemantics.globalenv.
  rewrite ! RelocProgSemantics.genv_senv_add_external_globals. simpl.
  exploit tables_encode_spec; eauto.
  intuition congruence.
Qed.

Lemma genv_genv_same:
  RelocProgSemantics1.Genv.genv_genv (RelocProgSemantics1.globalenv tprog) =
  RelocProgSemantics1.Genv.genv_genv (RelocProgSemantics1.globalenv prog).
Proof.
  unfold RelocProgSemantics1.globalenv. simpl.
  unfold RelocProgSemantics.globalenv.
  exploit tables_encode_spec; eauto.
  intros (EQdefs & EQpublic & EQmain & EQsymt & EQreloct & EQsenv & LEN
          & strmap & sbytes & idbytes & symt
          & GSMB & CSS & EQstrt & EQsect).
  f_equal; try intuition congruence.
  f_equal; try intuition congruence.
  rewrite EQsect.
  f_equal. unfold SecTable.get. unfold sec_code_id.
  destruct (prog_sectable prog) eqn:?; simpl in LEN; try congruence.
  destruct s eqn:?; simpl in LEN; try congruence.
  destruct l eqn:?; simpl in LEN; try congruence. simpl.
  auto.
Qed.

Lemma genv_reloc_same:
  RelocProgSemantics1.Genv.genv_reloc_ofs_symb (RelocProgSemantics1.globalenv tprog) =
  RelocProgSemantics1.Genv.genv_reloc_ofs_symb (RelocProgSemantics1.globalenv prog).
Proof.
  unfold RelocProgSemantics1.globalenv. simpl.
  unfold RelocProgSemantics1.gen_reloc_ofs_symbs.
  exploit tables_encode_spec; eauto.
  intros (EQdefs & EQpublic & EQmain & EQsymt & EQreloct & EQsenv & strmap & sbytes & idbytes & symt
          & GSMB & CSS & EQstrt & EQsect).
  f_equal; try intuition congruence.
Qed.

Lemma genv_same:
  RelocProgSemantics1.globalenv tprog =
  RelocProgSemantics1.globalenv prog.
Proof.
  unfold RelocProgSemantics1.globalenv. f_equal.
  apply genv_reloc_same.
  apply genv_genv_same.
Qed.

Lemma decode_tables_correct:
  decode_tables tprog = OK prog.
Proof.
  exploit tables_encode_spec; eauto.
  intros (EQdefs & EQpublic & EQmain & EQsymt & EQreloct & EQsenv & LEN
          & strmap & sbytes & idbytes & symt
          & GSMB & CSS & EQstrt & EQsect).
  generalize empty_strtable. intro EMP.
  unfold decode_tables.
  rewrite EQsect.
  destruct (prog_sectable prog) eqn:?; simpl in LEN; try omega.
  destruct s eqn:?; simpl in LEN; try omega.
  destruct l eqn:?; simpl in LEN; try omega.
  destruct l0 eqn:?; simpl in LEN; try omega.
  simpl.
  rewrite decode_encode_reloctable. simpl.
  rewrite decode_encode_reloctable. simpl.
  rewrite decode_encode_reloctable. simpl.
  erewrite decode_string_map_correct'. 2: eauto. simpl.
  rewrite GSMB. simpl.
  erewrite decode_create_symtable_section. 5: eauto. simpl.
  destruct prog; simpl in *. simpl. subst. f_equal. f_equal.
  destruct (prog_reloctables tprog). simpl. auto.
  eapply valid_strtable_p; eauto.
  eapply prog_strings_eq; eauto.
  eapply valid_symbentries_p; eauto.
  apply valid_reloctables with (id := RELOC_CODE).
  apply valid_reloctables with (id := RELOC_DATA).
  apply valid_reloctables with (id := RELOC_RODATA).
Qed.

(* Require RemoveAddendproof. *)

Theorem semantics2_id_correct p rs:
  forward_simulation (RelocProgSemantics2.semantics p rs)
                     (RelocProgSemantics2.semantics p rs).
Proof.
  apply forward_simulation_step with (match_states:= eq); simpl; intros; subst; eauto.
Qed.

Theorem transf_program_correct rs:
  forward_simulation (RelocProgSemantics2.semantics prog rs)
                     (RelocProgSemantics3.semantics tprog rs).
Proof.
  unfold semantics. rewrite decode_tables_correct.
  apply semantics2_id_correct.
Qed.

End PRESERVATION.

Definition link_reloc_decode_tables (p1 p2: RelocProgram.program) : option RelocProgram.program :=
  match RelocProgSemantics3.decode_tables p1, RelocProgSemantics3.decode_tables p2 with
    | OK pp1, OK pp2 =>
      match RelocLinking1.link_reloc_prog pp1 pp2 with
        Some pp =>
        match TablesEncode.transf_program pp with
        | OK tp => Some tp
        | _ => None
        end
      | _ => None
      end
    | _, _ => None
  end.

Instance linker2 : Linker RelocProgram.program.
Proof.
  eapply Build_Linker with (link := link_reloc_decode_tables) (linkorder := fun _ _ => True).
  auto. auto. auto.
Defined.

Require Import Lia.

(* Lemma SecTable_gsspec': *)
(*   forall (i j : nat) (tbl : SecTable.t) (tbl' : list SecTblParams.V) (v : SecTblParams.V), *)
(*     SecTable.set_nat i v tbl = Some tbl' -> *)
(*     nth_error tbl' j = if Nat.eq_dec i j then Some v else nth_error tbl j. *)
(* Proof. *)
(*   induction i; simpl; intros; eauto. *)
(*   - repeat destr_in H. destr. *)
(*     + subst; reflexivity. *)
(*     + destruct j; simpl; auto. congruence. *)
(*   - repeat destr_in H. *)
(*     generalize (IHi i _ _ _ Heqo). intro EQ1. *)
(*     destr. subst; simpl. rewrite EQ1. destr. *)
(*     destruct j. reflexivity. simpl. *)
(*     erewrite IHi. destr. eauto. *)
(* Qed. *)

(* Lemma SecTable_gsspec: *)
(*   forall i j tbl tbl' v, *)
(*     (j >= SecTblParams.ofs)%N -> *)
(*     (i >= SecTblParams.ofs)%N -> *)
(*     SecTable.set i v tbl = Some tbl' -> *)
(*     SecTable.get j tbl' = if N.eq_dec i j then Some v else SecTable.get j tbl. *)
(* Proof. *)
(*   unfold SecTable.set, SecTable.get. *)
(*   intros. *)
(*   erewrite SecTable_gsspec'. 2: eauto. *)
(*   destr. *)
(*   - apply Nnat.N2Nat.inj in e. *)
(*     unfold SecTable.idx in e. *)
(*     destr. *)
(*     apply f_equal with (f:= fun x => N.add x SecTblParams.ofs) in e. *)
(*     rewrite <- ! N.add_sub_swap in e by lia. *)
(*     rewrite !N.add_sub in e. congruence. *)
(*   - destr. *)
(* Qed. *)

(* Lemma remove_first_n_length: *)
(*   forall {A} n (l l': list A), *)
(*     RelocBinDecode.remove_first_n l n = OK l' -> *)
(*     length l = (length l' + n)%nat. *)
(* Proof. *)
(*   induction n; simpl; intros; eauto. inv H. lia. *)
(*   repeat destr_in H. simpl. apply IHn in H1. lia. *)
(* Qed. *)

(* Ltac autoinv := *)
(*   repeat match goal with *)
(*          | H: context [match ?a with _ => _ end] |- _ => *)
(*            repeat destr_in H *)
(*          | H: bind _ _ = OK _ |- _ => *)
(*            monadInv H *)
(*          end. *)

Opaque Z.of_nat Z.add.
(* Transparent Asm.addrmode_size. *)

(* Lemma decode_addrmode_SIB_size: *)
(*   forall rom ofs sib mod_b mc am mc', *)
(*     RelocBinDecode.addrmode_parse_SIB rom ofs sib mod_b mc = OK (am, mc') -> *)
(*     let idx := ( Byte.shru (Byte.and sib (Byte.repr 56)) (Byte.repr 3)) in *)
(*     let ss :=  (Byte.shru sib (Byte.repr 6)) in *)
(*     let bs := (Byte.and sib (Byte.repr 7)) in *)
(*     idx <> Byte.repr 4 -> (* RSP can not be the index of SIB *) *)
(*     (if Byte.eq_dec bs (Byte.repr 5) *)
(*      then *)
(*        if Byte.eq_dec mod_b (Byte.zero) *)
(*        then 2 else 6 *)
(*      else 6 *)
(*     ) *)
(*     + Z.of_nat (length mc) = Asm.addrmode_size am + Z.of_nat (length mc'). *)
(* Proof. *)
(*   intros rom ofs sib mod_b mc am mc' APSIB idx ss bs NORSP. *)
(*   unfold RelocBinDecode.addrmode_parse_SIB in APSIB. *)
(*   unfold Asm.addrmode_size. *)
(*   fold bs ss idx in APSIB. *)
(*   autoinv. *)
(*   - simpl. *)
(*     unfold RelocBinDecode.addrmode_SIB_parse_index. *)
(*     simpl. rewrite ! Z.add_0_l. *)
(*     rewrite pred_dec_true. 2: rewrite e0. 2: reflexivity. *)
(*     rewrite (@ pred_dec_true (Byte.repr 0 = Byte.zero)). 2: reflexivity. *)
(*     rewrite (@ pred_dec_false (idx = _)). 2: auto. *)
(*     lia. *)
(*   - simpl. *)
(*     rewrite pred_dec_false by auto. *)
(*     unfold RelocBinDecode.addrmode_SIB_parse_index. *)
(*     rewrite pred_dec_false by auto. lia. *)
(*   - simpl. *)
(*     unfold RelocBinDecode.addrmode_SIB_parse_base in EQ2. simpl in EQ2. *)
(*     rewrite !Z.add_0_l in *. *)
(*     rewrite (@pred_dec_false (mod_b = Byte.zero)) in * by auto. *)
(*     rewrite (@pred_dec_false (mod_b = Byte.repr 0)) in * by auto. *)
(*     unfold RelocBinDecode.addrmode_SIB_parse_index. *)
(*     rewrite (@pred_dec_false (idx = _)) by auto. destr. *)
(*   - rewrite pred_dec_true. 2: rewrite e0; reflexivity. *)
(*     rewrite pred_dec_true by reflexivity. simpl. *)
(*     unfold RelocBinDecode.addrmode_SIB_parse_index. *)
(*     rewrite (@pred_dec_false (idx = _)) by auto. lia. *)
(*   - rewrite pred_dec_false. 2: auto. *)
(*     simpl. *)
(*     unfold RelocBinDecode.addrmode_SIB_parse_index. *)
(*     rewrite (@pred_dec_false (idx = _)) by auto. lia. *)
(*   - simpl. *)
(*     unfold RelocBinDecode.addrmode_SIB_parse_index. *)
(*     rewrite (@pred_dec_false (idx = _)) by auto. *)
(*     rewrite (@pred_dec_false (mod_b = Byte.zero)) in * by auto. destr. *)
(* Qed. *)

(* Lemma decode_addrmode_size: *)
(*   forall rom ofs l x0, *)
(*     RelocBinDecode.decode_addrmode rom ofs l = OK x0 -> *)
(*     Z.of_nat (length l) = Asm.addrmode_size (snd (fst x0)) + Z.of_nat (length (snd x0)). *)
(* Proof. *)
(*   unfold RelocBinDecode.decode_addrmode. intros. *)
(*   unfold Asm.addrmode_size. *)
(*   autoinv; simpl. *)
(*   - destruct x2. exploit decode_addrmode_SIB_size. eauto. admit. *)
(*     rewrite e. rewrite (@pred_dec_true ( _ = Byte.zero)) by reflexivity. simpl; intros. *)
(*     unfold Asm.addrmode_size in H. rewrite <- H. *)
(*     unfold RelocBinDecode.addrmode_parse_SIB in EQ0. *)
(*     monadInv EQ0. *)
(*     repeat destr_in EQ6. *)
(*     rewrite e2. rewrite pred_dec_true; auto. lia. *)
(*     simpl in H. *)
(*     admit. admit. admit. *)
(*   - lia. *)
(*   - lia. *)
(*   - admit. *)
(*   - destruct x2. exploit decode_addrmode_SIB_size. eauto. admit. simpl in *. subst. *)
(*     rewrite e. rewrite (@pred_dec_false ( _ = Byte.zero)). 2: intro A; inv A. simpl; intros. *)
(*     unfold Asm.addrmode_size in H. admit. *)
(*   - admit. *)
(*   - *)
(* Admitted. *)

(* Lemma decode_instr_size: *)
(*   forall rom symt ofs bs ins bs', *)
(*     RelocBinDecode.fmc_instr_decode rom symt ofs bs = OK (ins, bs') -> *)
(*     Z.of_nat (length bs) = Asm.instr_size ins + Z.of_nat (length bs'). *)
(* Proof. *)
(*   Transparent Asm.instr_size. *)
(*   unfold RelocBinDecode.fmc_instr_decode, Asm.instr_size. *)
(*   intros rom symt ofs bs ins bs' DEC. *)
(*   Ltac helper := *)
(*     repeat match goal with *)
(*            | H: RelocBinDecode.remove_first_n ?l ?n = OK ?l' |- _ => *)
(*              rewrite (remove_first_n_length _ _ _ H) *)
(*            | H: context [match ?a with _ => _ end] |- _ => *)
(*              repeat destr_in H *)
(*            | H: bind _ _ = OK _ |- _ => *)
(*              monadInv H *)
(*            | H: ?f ?l = OK (?ins: Asm.instruction, ?bs': list byte) |- _ => *)
(*              unfold f in H *)
(*            | H: ?f _ _ = OK (?ins: Asm.instruction, ?bs': list byte) |- _ => *)
(*              unfold f in H *)
(*            | H: ?f _ _ _ = OK (?ins: Asm.instruction, ?bs': list byte) |- _ => *)
(*              unfold f in H *)
(*            | H: ?f _ _ _ _ = OK (?ins: Asm.instruction, ?bs': list byte) |- _ => *)
(*              unfold f in H *)
(*            | H: ?f _ _ _ _ _ = OK (?ins: Asm.instruction, ?bs': list byte) |- _ => *)
(*              unfold f in H *)
(*            | |- _ => simpl; try lia *)
(*            end. *)
  Transparent Z.of_nat.
(*   repeat destr_in DEC. *)
(*   - helper. *)
(*   - helper. *)
(*   - helper. *)
(*   - helper. *)
(*   - helper. *)
(*     exploit decode_addrmode_size. eauto. lia. *)
(*   - helper. *)
(*   - helper. *)
(*   - helper. *)
(*   - helper. *)
(*   - helper. *)
(*     exploit decode_addrmode_size. eauto. lia. *)
(*   - helper. *)
(*     exploit decode_addrmode_size. eauto. lia. *)
(*   - helper. *)
(*   - helper. *)
(*   - helper. *)
(*     admit. *)
(*   - helper. *)
(*   - helper. *)
(*   - helper. *)
(*   - helper. *)
(* Admitted. *)

(* Lemma decode_instrs_size: *)
(*   forall rom symt fuel bs ofs insns x1, *)
(*     decode_instrs rom symt fuel ofs bs insns = OK x1 -> *)
(*     Z.of_nat (length bs) + Asm.code_size (rev insns) = Asm.code_size x1. *)
(* Proof. *)
(*   induction fuel;  intros; eauto. *)
(*   - simpl in H. repeat destr_in H. simpl. auto. *)
(*   - simpl in H. destr_in H. inv H; simpl; auto. *)
(*     monadInv H. *)
(*     destruct x. erewrite decode_instr_size; eauto. *)
(*     erewrite <- IHfuel with (x1 := x1); eauto. *)
(*     simpl. rewrite AsmFacts.code_size_app. simpl. lia. *)
(* Qed. *)

(* Lemma decode_instrs'_size: *)
(*   forall rom symt bs x1, *)
(*     decode_instrs' rom symt bs = OK x1 -> *)
(*     Z.of_nat (length bs) = Asm.code_size x1. *)
(* Proof. *)
(*   unfold decode_instrs'. intros rom symt bs x1 DEC. *)
(*   monadInv DEC. *)
(*   eapply decode_instrs_size in EQ. simpl in EQ. lia. *)
(* Qed. *)


Lemma fold_acc_strmap_size:
  forall l idbytes t0 o0 t1 o1 z,
    fold_left acc_strmap idbytes (t0, o0) = (t1, o1) ->
    fold_right acc_symbol_strings (OK []) l = OK idbytes ->
    fold_right (fun id acc =>
                  match acc with
                    OK z =>
                    match SymbolString.find_symbol_pos id with
                    | Some pos => OK (z + 2 + Z.of_nat (length pos))
                    | None => Error (msg "cannot find string")
                    end
                  | _ => acc
                  end
               ) (OK 0) l = OK z ->
    o1 + Z.of_nat (length idbytes) = o0 + z.
Proof.
  induction l; simpl; intros; eauto.
  inv H0. inv H1. simpl in H. inv H. simpl. lia.
  destr_in H1. unfold acc_symbol_strings in H0 at 1.
  monadInv H0. destr_in H1. inv EQ0. inv H1.
  simpl in H.
  exploit IHl. eauto. eauto. eauto. simpl.
  rewrite app_length. rewrite map_length. simpl. lia.
Qed.

Lemma get_strings_map_bytes_exists':
  forall l z,
    fold_right (fun id acc =>
                  match acc with
                    OK z =>
                    match SymbolString.find_symbol_pos id with
                    | Some pos => OK (z + 2 + Z.of_nat (length pos))
                    | None => Error (msg "cannot find string")
                    end
                  | _ => acc
                  end
               ) (OK 0) l = OK z ->
    z < Int.max_unsigned ->
    exists idbytes strmap sbytes,
      get_strings_map_bytes l = OK (idbytes, strmap, sbytes).
Proof.
  unfold get_strings_map_bytes.
  induction l; simpl; intros; eauto.
  repeat destr_in H.
  edestruct IHl as (idbytes & strmap & sbytes & EQ). eauto. lia.
  monadInv EQ. repeat destr_in EQ1.
  rewrite EQ0. simpl. rewrite Heqo. simpl.
  destr.
  exploit fold_acc_strmap_size. eauto. eauto. eauto. intro EQ. rewrite pred_dec_true.
  (do 3 eexists); eauto.
  revert EQ.
  rewrite app_length.
  rewrite map_length. simpl. revert H0. clear.
  intros.
  eapply Z.le_lt_trans. 2: apply H0. lia.
Qed.

Lemma get_strings_map_bytes_exists:
  forall syms z,
    fold_right (fun id acc =>
                  match acc with
                    OK z =>
                    match SymbolString.find_symbol_pos id with
                    | Some pos => OK (z + 2 + Z.of_nat (length pos))
                    | None => Error (msg "cannot find string")
                    end
                  | _ => acc
                  end
               ) (OK 0) (fold_right acc_symbols [] syms) = OK z ->
    z < Int.max_unsigned ->
    exists idbytes strmap sbytes,
      get_strings_map_bytes (fold_right acc_symbols [] syms) = OK (idbytes, strmap, sbytes).
Proof.
  intros.
  eapply get_strings_map_bytes_exists'; eauto.
Qed.

Lemma create_symbtable_section_succeeds:
  forall strmap symt,
    Forall (fun s => exists si, Maps.PTree.get (symbentry_id s) strmap = Some si) symt ->
    exists symsec,
      create_symbtable_section strmap symt = OK symsec.
Proof.
  unfold create_symbtable_section.
  unfold encode_symbtable.
  induction symt; simpl; intros. eauto.
  destruct IHsymt. inv H; auto. monadInv H0. rewrite EQ. simpl.
  unfold encode_symbentry.
  inv H. destruct H2. rewrite H. simpl. eauto.
Qed.

Lemma link_reloc_bingen_sectable:
  forall p1 p2 p,
    RelocLinking1.link_reloc_prog p1 p2 = Some p ->
    length (prog_sectable p) = 3%nat.
Proof.
  unfold RelocLinking1.link_reloc_prog, RelocLinking.link_reloc_prog.
  intros. autoinv. simpl. clear - Heqo7.
  unfold RelocLinking.link_sectable in Heqo7. autoinv. reflexivity.
Qed.

Lemma get_symbtable_to_tree:
  forall stbl,
    (symbtable_to_tree stbl) =
    (Maps.PTree_Properties.of_list (map (fun s =>(symbentry_id s, s)) stbl)).
Proof.
  reflexivity.
Qed.

Lemma symbtable_to_tree_get_id:
  forall stbl x se,
    Maps.PTree.get x (symbtable_to_tree stbl) = Some se ->
    x = symbentry_id se /\ In se stbl.
Proof.
  intros. rewrite get_symbtable_to_tree in H.
  apply Maps.PTree_Properties.in_of_list in H.
  rewrite in_map_iff in H.
  decompose [ex and] H; clear H. inv H1. auto.
Qed.

(* Lemma get_strings_map_bytes_in: *)
(*   forall l idbytes strmap sbytes, *)
(*     get_strings_map_bytes l = OK (idbytes, strmap, sbytes) -> *)
(*     forall i si, *)
(*       Maps.PTree.get i strmap = Some si -> *)
(*       In i l. *)
(* Proof. *)
(*   unfold get_strings_map_bytes. intros. autoinv. *)

(*   assert ( *)
(*       forall idbytes t0 o0 t1 o1 i si, *)
(*         fold_left acc_strmap idbytes (t0, o0) = (t1, o1) -> *)
(*         Maps.PTree.get i t1 = Some si -> *)
(*         Maps.PTree.get i t0 <> None \/ In i (map fst idbytes) *)
(*     ). *)
(*   { *)
(*     clear. *)
(*     induction idbytes; simpl; intros; eauto. *)
(*     inv H. left ; congruence. *)
(*     destr_in H. eapply IHidbytes in H; eauto. *)
(*     rewrite Maps.PTree.gsspec in H. destr_in H. destruct H. subst; simpl; auto. eauto. *)
(*   } *)
(*   edestruct H. eauto. eauto. rewrite Maps.PTree.gempty in H1. congruence. *)

(*   assert (forall l b0 b1, *)
(*              fold_right acc_symbol_strings (OK b0) l = OK b1 -> *)
(*              forall i, *)
(*                In i (map fst b1) -> *)
(*                In i (map fst b0) \/ In i l *)
(*          ). *)
(*   { *)
(*     clear. *)
(*     induction l; simpl; intros; eauto. *)
(*     inv H. auto. *)
(*     unfold acc_symbol_strings in H at 1. autoinv. simpl in H0. destruct H0; auto. *)
(*     eapply IHl in EQ; eauto. intuition. *)
(*   } *)
(*   edestruct H2; eauto. easy. *)
(* Qed. *)

Lemma acc_strmap_acc:
  forall l t0 i0 t1 i1,
    fold_left acc_strmap l (t0, i0) = (t1, i1) ->
    forall i,
      Maps.PTree.get i t0 <> None -> Maps.PTree.get i t1 <> None.
Proof.
  induction l; simpl; intros; eauto. inv H; eauto.
  destr_in H.
  eapply IHl in H. eauto. rewrite Maps.PTree.gsspec. destr.
Qed.

Lemma acc_strmap_exists:
  forall l t0 i0 t1 i1 i,
    In i (map fst l) ->
    fold_left acc_strmap l (t0, i0) = (t1, i1) ->
    Maps.PTree.get i t1 <> None.
Proof.
  induction l; simpl; intros; eauto.
  destr_in H0. simpl in *.
  destruct H.
  eapply acc_strmap_acc; eauto. subst. rewrite Maps.PTree.gss. congruence.
  eauto.
Qed.

Lemma acc_symbol_strings_in:
  forall l idbytes i,
    fold_right (acc_symbol_strings) (OK []) l = OK idbytes ->
    In i l ->
    In i (map fst idbytes).
Proof.
  induction l; simpl; intros; eauto. easy.
  unfold acc_symbol_strings in H at 1. autoinv. simpl. intuition eauto.
Qed.

Lemma get_strings_map_bytes_has_mapping:
  forall l idbytes strmap sbytes,
    get_strings_map_bytes l = OK (idbytes, strmap, sbytes) ->
    forall i,
      In i l ->
      exists si, Maps.PTree.get i strmap = Some si.
Proof.
  unfold get_strings_map_bytes. intros.
  autoinv.
  eapply acc_symbol_strings_in in EQ; eauto.
  eapply acc_strmap_exists in EQ; eauto. destruct (Maps.PTree.get i strmap) eqn:?; try congruence.
  eauto.
Qed.

Lemma link_symbtable_in:
  forall s1 s2 s,
    RelocLinking.link_symbtable s1 s2 = Some s ->
    forall x,
      In x s ->
      RelocLinking.link_symb_merge (Maps.PTree.get (symbentry_id x) (symbtable_to_tree s1))
                                   (Maps.PTree.get (symbentry_id x) (symbtable_to_tree s2)) = Some x.
Proof.
  intros.
  unfold RelocLinking.link_symbtable in H. autoinv.
  rewrite ! andb_true_iff in Heqb. intuition.
  rewrite in_map_iff in H0.
  destruct H0 as ((id & se) & EQ & IN). subst. simpl in *.
  apply  Maps.PTree.elements_complete in IN.
  rewrite Maps.PTree.gcombine in IN. 2: reflexivity.

  assert (id = symbentry_id se). {
    unfold RelocLinking.link_symb_merge in *. autoinv.
    exploit symbtable_to_tree_get_id. apply Heqo.
    exploit symbtable_to_tree_get_id. apply Heqo0. intuition subst.
    unfold RelocLinking.link_symb in H0. autoinv.
    simpl; auto. simpl; auto.
    exploit symbtable_to_tree_get_id. apply Heqo. intuition.
    exploit symbtable_to_tree_get_id. apply H0. intuition.
  }
  subst. auto.
Qed.

Lemma update_reloctable_valid:
  forall symt sim rtbl rtbl',
    Forall valid_relocentry rtbl ->
    (forall i n, Maps.PTree.get i sim = Some n -> Z.of_N n < two_p 24) ->
    RelocLinking1.update_reloctable_symb symt sim rtbl = Some rtbl' ->
    Forall valid_relocentry rtbl'.
Proof.
  intros symt sim rtbl rtbl' F LT URS.
  unfold RelocLinking1.update_reloctable_symb in URS.
  revert F rtbl' URS.
  induction 1; simpl; intros; eauto. inv URS. constructor.
  unfold RelocLinking1.acc_update_reloc_symb in URS at 1. autoinv.
  constructor; eauto.
  unfold RelocLinking1.update_reloc_symb in Heqo0. autoinv.
  inv H. constructor; eauto.
Qed.

Lemma link_reloctable_valid:
  forall sz symt1 symt2 sim rtbl1 rtbl2 rtbl,
    Forall valid_relocentry rtbl1 ->
    Forall valid_relocentry rtbl2 ->
    (forall i n, Maps.PTree.get i sim = Some n -> Z.of_N n < two_p 24) ->
    RelocLinking1.link_reloctable sz symt1 symt2 sim rtbl1 rtbl2 = Some rtbl ->
    Forall valid_relocentry rtbl.
Proof.
  intros sz symt1 symt2 sim rtbl1 rtbl2 rtbl F1 F2 LT LR.
  unfold RelocLinking1.link_reloctable in LR. autoinv.
  rewrite Forall_forall. intros.
  rewrite in_app in H. destruct H.
  revert x H. rewrite <- Forall_forall. eapply update_reloctable_valid. 3: eauto. auto. auto.
  rewrite in_map_iff in H.
  destruct H as (x0 & SHIFT & IN).
  exploit update_reloctable_valid. apply F2. eauto. eauto. rewrite Forall_forall.
  intro A; specialize (A _ IN). subst.
  inv A; constructor; simpl; auto.
  admit.                    (* reloc offset could overflow *)
Admitted.

Instance tl : @TransfLink _ _ RelocLinking1.Linker_reloc_prog
                          linker2
                          match_prog.
Proof.
  red. simpl. unfold link_reloc_decode_tables.
  unfold match_prog.
  intros.
  erewrite decode_tables_correct; eauto.
  erewrite decode_tables_correct; eauto.
  simpl. rewrite H.
  cut (exists tp, transf_program p = OK tp).
  intros (tp & TP); rewrite TP; eauto.
  unfold transf_program in *. autoinv. simpl in *.

  assert (
      exists s0 v v0 v1,
        SecTable.get sec_rodata_id (prog_sectable p1) = Some v /\
        SecTable.get sec_data_id (prog_sectable p1) = Some v0 /\
        SecTable.get sec_code_id (prog_sectable p1) = Some v1 /\
        RelocLinking.reloc_symbtable (RelocLinking.reloc_offset_fun (sec_size v) (sec_size v0) (sec_size v1))
            (prog_symbtable p2) = Some s0 /\
      Some (prog_symbtable p) = RelocLinking.link_symbtable (prog_symbtable p1) s0).
  {
    clear - H.
    unfold RelocLinking1.link_reloc_prog in H. autoinv.
    simpl.
    unfold RelocLinking.link_reloc_prog in Heqo. autoinv. simpl.
    exists s0, v, v0, v1; repeat split; eauto.
  }

  exploit (get_strings_map_bytes_exists (prog_symbtable p)); eauto. admit. admit.
  intros (idbytes & strmap & sbytes & smb). rewrite smb. simpl.
  destruct H0 as (s0 & v & v0 & v1 & GETrodata & GETdata & GETcode & RELOCsym & EQsym).

  assert (NRsymb_id:   list_norepet (map symbentry_id (prog_symbtable p))).
  {
    clear - EQsym. symmetry in EQsym.
    unfold RelocLinking.link_symbtable in EQsym.
    repeat destr_in EQsym.
    rewrite map_map.
    rewrite list_map_exten with (f:= fst).
    apply Maps.PTree.elements_keys_norepet.
    intros.
    destruct x.
    apply Maps.PTree.elements_complete in H.
    rewrite Maps.PTree.gcombine in H by reflexivity. simpl.
    unfold RelocLinking.link_symb_merge in H.
      assert (LinkSymbId:
                forall s1 s2 s3,
                       RelocLinking.link_symb s1 s2 = Some s3 ->
                       symbentry_id s1 = symbentry_id s3 /\
                       symbentry_id s2 = symbentry_id s3
             ).
      {
        unfold RelocLinking.link_symb. clear. intros. autoinv; simpl; intuition.
      }
      autoinv; repeat
                 match goal with
                   H: Maps.PTree.get _ (symbtable_to_tree _) = _ |- _ =>
                   apply symbtable_to_tree_get_id in H
                 | H: RelocLinking.link_symb _ _ = Some _ |- _ =>
                   apply LinkSymbId in H
                 end; intuition congruence.
  }

  assert (valid_strtable idbytes strmap).
  {
    generalize smb; intro smb'.
    unfold get_strings_map_bytes in smb. monadInv smb.
    exploit gsmb_valid_strtable. apply smb'. eauto. eauto.
    repeat destr_in EQ4.
  }

  assert (Valids: Forall (valid_symbentry strmap) (prog_symbtable p)).
  {
    rewrite Forall_forall. intros.

    exploit link_symbtable_in. 2: eauto. eauto.

    assert (ValidRelocSymbentries: Forall (valid_symbentry t0) s0).
    {
      clear - f2 RELOCsym.
      unfold RelocLinking.reloc_symbtable in RELOCsym.
      revert f2 RELOCsym.
      generalize (prog_symbtable p2) (RelocLinking.reloc_offset_fun (sec_size v) (sec_size v0)) s0. clear.
      induction s; simpl; intros; eauto. inv RELOCsym; auto.
      inv f2.
      unfold RelocLinking.reloc_iter at 1 in RELOCsym.
      autoinv.
      constructor; eauto.
      unfold RelocLinking.reloc_symbol in Heqo1. autoinv.
      inv H1. rewrite Heqs0 in *. constructor; simpl in *; auto.
      admit.                    (* symbentry_value relocated could overflow... *)
    }
    unfold RelocLinking.link_symb_merge. destr.

    destr.
    Lemma acc_symbols_map:
      forall l,
        fold_right acc_symbols [] l = map symbentry_id l.
    Proof.
      induction l; simpl; intros; eauto.
    Qed.
    - exploit symbtable_to_tree_get_id. apply Heqo.
      exploit symbtable_to_tree_get_id. apply Heqo0.
      intros (EQid1 & IN1) (EQid2 & IN2) LS.
      rewrite Forall_forall in f1. generalize (f1 _ IN2).
      rewrite Forall_forall in ValidRelocSymbentries. generalize (ValidRelocSymbentries _ IN1).
      unfold RelocLinking.link_symb in LS.
      inversion 1; inversion 1; constructor; simpl; eauto.
      + autoinv; simpl; auto.
        rewrite Zmax_spec; destr; vm_compute; intuition congruence.
        vm_compute; intuition congruence.
      + autoinv; simpl; auto.
        vm_compute; intuition congruence.
        vm_compute; intuition congruence.
      + edestruct get_strings_map_bytes_has_mapping as (si & MAP1).
        3: rewrite MAP1. eauto.
        rewrite acc_symbols_map. rewrite in_map_iff.
        eexists; split; eauto. eexists; split; eauto.
        destruct H0 as (o & V & LT'). destruct V. eapply table_range; eauto.
      + autoinv; simpl; auto.
    - intro A; inv A.
      exploit symbtable_to_tree_get_id. apply Heqo.
      intros (EQid1 & IN1).
      rewrite Forall_forall in f1. generalize (f1 _ IN1).
      inversion 1; constructor; simpl; eauto.
      edestruct get_strings_map_bytes_has_mapping as (si & MAP1).
      3: rewrite MAP1. eauto.
      rewrite acc_symbols_map. rewrite in_map_iff.
      eauto. eexists; split; eauto.
      destruct H0 as (o & V & LT'). destruct V. eapply table_range; eauto.
    - intro A.
      exploit symbtable_to_tree_get_id. apply A.
      intros (EQid1 & IN1).
      rewrite Forall_forall in ValidRelocSymbentries. generalize (ValidRelocSymbentries _ IN1).
      inversion 1; constructor; simpl; eauto.
      edestruct get_strings_map_bytes_has_mapping as (si & MAP1).
      3: rewrite MAP1. eauto.
      rewrite acc_symbols_map. rewrite in_map_iff.
      eauto. eexists; split; eauto.
      destruct H0 as (o & V & LT'). destruct V. eapply table_range; eauto.
  }
  rewrite pred_dec_true by auto.
  assert (prog_strtable p = Maps.PTree.empty Z).
  {
    clear - e e0 H.
    unfold RelocLinking1.link_reloc_prog in H. autoinv. simpl.
    unfold RelocLinking.link_reloc_prog in Heqo. autoinv. simpl. auto.
  }
  rewrite pred_dec_true by auto.
  rewrite pred_dec_true by auto.
  assert ((forall id : reloctable_id, Forall valid_relocentry (get_reloctable id (prog_reloctables p)))).
  {
    clear - f0 f H.
    unfold RelocLinking1.link_reloc_prog in H. autoinv. simpl.
    unfold RelocLinking1.link_rodata_reloctable in Heqo0. autoinv.
    unfold RelocLinking1.link_data_reloctable in Heqo1. autoinv.
    unfold RelocLinking1.link_code_reloctable in Heqo2. autoinv.
    simpl in *.
    clear - H0 H1 f f0.
    intros.
    specialize (f id). specialize (f0 id).
    destruct id; simpl in *; eapply link_reloctable_valid. 4,8: eauto. all: eauto.
    admit.
    admit.                      (* sim gives values < 2 ^ 24 *)
    admit.
    admit.
    admit.
  }
  rewrite pred_dec_true by auto.

  exploit create_symbtable_section_succeeds.
  2: intros (symsec & CSS); rewrite CSS.
  {
    rewrite Forall_forall. intros xx IN.
    exploit link_symbtable_in. eauto. eauto.
    intros.
    eapply get_strings_map_bytes_has_mapping. eauto.
    rewrite acc_symbols_map.
    apply in_map. auto.
  }
  simpl. rewrite app_length. simpl.
  
  erewrite link_reloc_bingen_sectable; eauto. simpl. eauto.
  rewrite dump_reloctables_error in H1. congruence.
  rewrite dump_reloctables_error in H1. congruence.
  rewrite dump_reloctables_error in H1. congruence.
Admitted.
