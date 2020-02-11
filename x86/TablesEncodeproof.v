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

Hypothesis valid_reloctables:
  forall id, Forall valid_relocentry (get_reloctable id (prog_reloctables prog)).

Hypothesis valid_symbentries_p:
  forall strmap sbytes,
    get_strings_map_bytes (fold_right acc_symbols nil (prog_symbtable prog)) = OK (strmap, sbytes) ->
    Forall (valid_symbentry strmap) (RelocProgram.prog_symbtable prog).

Hypothesis empty_strtable:
  prog_strtable prog = Maps.PTree.empty Z.

Hypothesis symbentries_no_repet:
  list_norepet
    (filter
       (fun o : option ident =>
        match o with
        | Some _ => true
        | None => false
        end) (map symbentry_id (prog_symbtable prog))).

Parameter prog_strings : list (ident * list byte).
Hypothesis prog_strings_eq:
  fold_right acc_symbol_strings (OK [])
             (fold_right acc_symbols [] (prog_symbtable prog)) =
  OK prog_strings.

Hypothesis prog_strings_not_empty:
  Forall (fun '(_, lb) => lb <> []) prog_strings.


Lemma acc_symbols_in_in_symbols:
  forall s x0 l,
    fold_right acc_symbol_strings (OK l) (fold_right acc_symbols [] s) = OK x0 ->
    forall i,
      In i (map fst x0) ->
      In i (map fst l) \/ exists a, In a s /\ symbentry_id a = Some i.
Proof.
  induction s; simpl; intros x0 l FOLD i IN.
  - inv FOLD. auto.
  - unfold acc_symbols at 1 in FOLD.
    destr_in FOLD; eauto.
    + simpl in FOLD.
      unfold acc_symbol_strings at 1 in FOLD. monadInv FOLD.
      repeat destr_in EQ0.
      simpl in IN. destruct IN as [eq | IN]; subst.
      right; eexists; split; eauto.
      exploit IHs. eauto. eauto. intros [A | [a0 [INs EQs]]]; eauto.
    + exploit IHs; eauto. intros [A | [a0 [INs EQs]]]; eauto.
Qed.

Lemma gsmb_valid_strtable:
  forall pi strmap sbytes,
         let symbols := fold_right acc_symbols [] (prog_symbtable pi) in
         get_strings_map_bytes symbols = OK (strmap, sbytes) ->
         forall
         x (EQ0 : fold_right acc_symbol_strings (OK []) (fold_right acc_symbols [] (prog_symbtable pi)) = OK x)
         (LNR: list_norepet (filter (fun o => match o with None => false | _ => true end)
                                    (map symbentry_id (prog_symbtable pi))))
,
    valid_strtable x strmap.
Proof.
  intros pi strmap sbytes symbols GSMB x EQ0 LNR.
  unfold valid_strtable.

  assert (LNR': list_norepet (map fst x)).
  {
    revert x EQ0 LNR.
    generalize (prog_symbtable pi). clear.
    induction s; simpl; intros; eauto.
    - inv EQ0. constructor.
    - unfold acc_symbols at 1 in EQ0.
      destr_in EQ0; eauto. simpl in EQ0.
      unfold acc_symbol_strings at 1 in EQ0. monadInv EQ0.
      exploit IHs. apply EQ. inv LNR; auto.
      repeat destr_in EQ1. simpl. intros; constructor; auto.
      intro INi.
      eapply acc_symbols_in_in_symbols in INi; eauto. simpl in INi. destruct INi as [[]|(aa & IN & EQa)].
      inv LNR. apply H2.
      apply filter_In. split; auto.
      rewrite in_map_iff. eexists; split; eauto.
  }
  unfold get_strings_map_bytes in GSMB.
  unfold symbols in GSMB. rewrite EQ0 in GSMB. simpl in GSMB. repeat destr_in GSMB.
  exists z; split; auto.
  revert z Heqp l.
  assert (valid_strtable_thr x (Maps.PTree.empty Z) 1 /\ 0 < 1).
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
  assert (forall elt, In elt x -> In elt x) by auto. revert H.
  generalize x at 1 4.
  induction x0; simpl.
  - intros; eauto. inv Heqp. auto.
  - intros IN t z VALID POS t0 z1 FOLD LT.
    destr_in FOLD.
    eapply IHx0 in FOLD. auto. eauto.
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
  forall strmap sbytes,
    get_strings_map_bytes (fold_right acc_symbols nil (prog_symbtable prog)) = OK (strmap, sbytes) ->
    valid_strtable prog_strings strmap.
Proof.
  intros. eapply gsmb_valid_strtable; eauto.
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
    exists (strmap : Maps.PTree.t Z) (sbytes : list byte) symt,
      get_strings_map_bytes (fold_right acc_symbols nil (prog_symbtable prog)) =
      OK (strmap, sbytes) /\
      create_symbtable_section strmap (prog_symbtable prog) = OK symt /\
      prog_strtable tprog = strmap /\
      prog_sectable tprog =
      prog_sectable prog ++
                    [create_strtab_section sbytes;
                       symt;
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
  rewrite EQ. exists t, l, x. auto.
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
  intros (EQdefs & EQpublic & EQmain & EQsymt & EQreloct & EQsenv & LEN & strmap & sbytes & symt
          & GSMB & CSS & EQstrt & EQsect).
  f_equal; try intuition congruence.
  f_equal; try intuition congruence.
  rewrite EQsect.
  f_equal. unfold SeqTable.SeqTable.get. unfold sec_code_id.
  destruct (prog_sectable prog) eqn:?; simpl in LEN; try congruence.
  destruct s0 eqn:?; simpl in LEN; try congruence.
  destruct l eqn:?; simpl in LEN; try congruence. simpl.
  destruct l0 eqn:?; simpl in LEN; try congruence.
Qed.

Lemma genv_reloc_same:
  RelocProgSemantics1.Genv.genv_reloc_ofs_symb (RelocProgSemantics1.globalenv tprog) =
  RelocProgSemantics1.Genv.genv_reloc_ofs_symb (RelocProgSemantics1.globalenv prog).
Proof.
  unfold RelocProgSemantics1.globalenv. simpl.
  unfold RelocProgSemantics1.gen_reloc_ofs_symbs.
  exploit tables_encode_spec; eauto.
  intros (EQdefs & EQpublic & EQmain & EQsymt & EQreloct & EQsenv & strmap & sbytes & symt
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
  intros (EQdefs & EQpublic & EQmain & EQsymt & EQreloct & EQsenv & LEN & strmap & sbytes & symt
          & GSMB & CSS & EQstrt & EQsect).
  unfold decode_tables.
  rewrite EQsect.
  destruct (prog_sectable prog) eqn:?; simpl in LEN; try omega.
  destruct s0 eqn:?; simpl in LEN; try omega.
  destruct l eqn:?; simpl in LEN; try omega.
  destruct l0 eqn:?; simpl in LEN; try omega. simpl.
  rewrite decode_encode_reloctable. simpl.
  rewrite decode_encode_reloctable. simpl.
  erewrite decode_string_map_correct'. 2: eauto. simpl.
  rewrite GSMB. simpl.
  erewrite decode_create_symtable_section. 5: eauto. simpl.
  destruct prog; simpl in *. subst. f_equal. f_equal; intuition try congruence.
  destruct tprog; simpl. destruct prog_reloctables; simpl; auto.
  all: eauto.
  eapply valid_strtable_p; eauto.
  apply valid_reloctables with (id := RELOC_CODE).
  apply valid_reloctables with (id := RELOC_DATA).
Qed.

Theorem transf_program_correct rs:
  forward_simulation (RelocProgSemantics2.semantics prog rs)
                     (RelocProgSemantics3.semantics tprog rs).
Proof.
  unfold semantics. rewrite decode_tables_correct.
  eapply forward_simulation_step with (match_states := fun (e1 e2: Asm.state) => e1 = e2); simpl; intuition try congruence; subst; eauto.
Qed.

End PRESERVATION.

Definition link_reloc_decode_tables (p1 p2: RelocProgram.program) : option RelocProgram.program :=
  match RelocProgSemantics3.decode_tables p1, RelocProgSemantics3.decode_tables p2 with
    | OK pp1, OK pp2 =>
      match RelocBingenproof.link_reloc_bingen pp1 pp2 with
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

Instance tl : @TransfLink _ _ RelocBingenproof.linker2
                          linker2
                          match_prog.
Proof.
  red. simpl. unfold link_reloc_decode_tables.
  unfold match_prog.
  intros.
  erewrite decode_tables_correct; eauto.
  erewrite decode_tables_correct; eauto.
  simpl. rewrite H.
Admitted.
