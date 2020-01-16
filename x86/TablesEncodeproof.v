Require Import Coqlib Errors.
Require Import Integers Floats AST Linking OrderedLinking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import RelocProgram.
Require Import StrtableEncode StrtableDecode.
Require Import SymbtableEncode SymbtableDecode.
Require Import ShstrtableEncode ShstrtableDecode.
Require Import ReloctablesEncode ReloctablesDecode.
Require Import RelocProgSemantics2 RelocProgSemantics3.

Import ListNotations.
(** Preservation of semantics under permutation *)
Section PRESERVATION.

Context `{external_calls_prf: ExternalCalls}.

Variables prog prog1 prog2 prog3 tprog: RelocProgram.program.

Hypothesis transf_str_encode: StrtableEncode.transf_program prog = OK prog1.
Hypothesis transf_symb_encode: SymbtableEncode.transf_program prog1 = OK prog2.
Hypothesis transf_reloc_encode: ReloctablesEncode.transf_program prog2 = OK prog3.
Hypothesis transf_shstr_encode: ShstrtableEncode.transf_program prog3 = OK tprog.

Hypothesis valid_reloctables:
  forall id, Forall valid_relocentry (get_reloctable id (prog_reloctables prog)).

Hypothesis valid_symbentries_p:
  Forall (valid_symbentry (RelocProgram.prog_strtable prog1)) (RelocProgram.prog_symbtable prog1).

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

Lemma strtable_encode_spec:
  forall prog prog1,
    StrtableEncode.transf_program prog = OK prog1 ->
    prog_defs prog = prog_defs prog1 /\
    prog_public prog = prog_public prog1 /\
    prog_main prog = prog_main prog1 /\
    prog_symbtable prog = prog_symbtable prog1 /\
    prog_reloctables prog = prog_reloctables prog1 /\
    prog_senv prog = prog_senv prog1 /\
    (exists strmap sbytes,
      get_strings_map_bytes (fold_right acc_symbols nil (prog_symbtable prog)) = OK (strmap, sbytes) /\
      prog_strtable prog1 = strmap /\
      prog_sectable prog1 = prog_sectable prog ++ create_strtab_section sbytes :: nil
    ).
Proof.
  clear.
  unfold StrtableEncode.transf_program. intros prog prog1 TF.
  monadInv TF. repeat destr_in EQ0. simpl; auto.
  repeat split.
  rewrite EQ. eauto.
Qed.

Lemma symbtable_encode_spec:
  forall prog prog1,
    SymbtableEncode.transf_program prog = OK prog1 ->
    prog_defs prog = prog_defs prog1 /\
    prog_public prog = prog_public prog1 /\
    prog_main prog = prog_main prog1 /\
    prog_symbtable prog = prog_symbtable prog1 /\
    prog_strtable prog = prog_strtable prog1 /\
    prog_reloctables prog = prog_reloctables prog1 /\
    prog_senv prog = prog_senv prog1 /\
    (exists s,
        create_symbtable_section (prog_strtable prog) (prog_symbtable prog) = OK s /\
        prog_sectable prog1 = prog_sectable prog ++ s :: nil
    ).
Proof.
  clear.
  unfold SymbtableEncode.transf_program. intros prog prog1 TF.
  monadInv TF. repeat destr_in EQ0. simpl; auto.
  repeat split.
  rewrite EQ. eauto.
Qed.

Lemma reloctables_encode_spec:
  forall prog prog1,
    ReloctablesEncode.transf_program prog = OK prog1 ->
    prog_defs prog = prog_defs prog1 /\
    prog_public prog = prog_public prog1 /\
    prog_main prog = prog_main prog1 /\
    prog_symbtable prog = prog_symbtable prog1 /\
    prog_strtable prog = prog_strtable prog1 /\
    prog_reloctables prog = prog_reloctables prog1 /\
    prog_senv prog = prog_senv prog1 /\
    prog_sectable prog1 = prog_sectable prog ++ create_reloctables_sections prog.
Proof.
  clear.
  unfold ReloctablesEncode.transf_program. intros prog prog1 TF.
  repeat destr_in TF. simpl; auto.
  repeat split.
Qed.

Lemma shstrtable_encode_spec:
  forall prog prog1,
    ShstrtableEncode.transf_program prog = OK prog1 ->
    prog_defs prog = prog_defs prog1 /\
    prog_public prog = prog_public prog1 /\
    prog_main prog = prog_main prog1 /\
    prog_symbtable prog = prog_symbtable prog1 /\
    prog_strtable prog = prog_strtable prog1 /\
    prog_reloctables prog = prog_reloctables prog1 /\
    prog_senv prog = prog_senv prog1 /\
    prog_sectable prog1 = prog_sectable prog ++ create_shstrtab_section :: nil.
Proof.
  clear.
  unfold ShstrtableEncode.transf_program. intros prog prog1 TF.
  repeat destr_in TF. simpl; auto.
  repeat split.
Qed.


Lemma valid_strtable_p: valid_strtable prog_strings (RelocProgram.prog_strtable prog1).
Proof.
  generalize transf_str_encode. unfold StrtableEncode.transf_program. intro H. monadInv H.
  repeat destr_in EQ0. simpl in *.
  unfold get_strings_map_bytes in EQ. rewrite prog_strings_eq in EQ. simpl in EQ. repeat destr_in EQ.
  exploit StrtableEncode.transf_program_valid_strtable. eauto. eauto. eauto. simpl. auto.
Qed.


Lemma genv_senv_add_external_global:
  forall exts ge a,
    RelocProgSemantics.Genv.genv_senv (RelocProgSemantics.add_external_global exts ge a) =
    RelocProgSemantics.Genv.genv_senv ge.
Proof.
  unfold RelocProgSemantics.add_external_global. intros.
  destr.
Qed.

Lemma genv_senv_add_external_globals:
  forall st exts ge,
    RelocProgSemantics.Genv.genv_senv (RelocProgSemantics.add_external_globals exts ge st) =
    RelocProgSemantics.Genv.genv_senv ge.
Proof.
  induction st; simpl; intros; eauto.
  rewrite IHst.
  apply genv_senv_add_external_global.
Qed.

Lemma genv_senv_same:
  RelocProgSemantics1.genv_senv (RelocProgSemantics1.globalenv tprog) =
  RelocProgSemantics1.genv_senv (RelocProgSemantics1.globalenv prog).
Proof.
  unfold RelocProgSemantics1.globalenv. simpl.
  unfold RelocProgSemantics1.genv_senv. simpl.
  unfold RelocProgSemantics.globalenv.
  rewrite ! genv_senv_add_external_globals. simpl.
  exploit strtable_encode_spec; eauto. exploit symbtable_encode_spec; eauto.
  exploit reloctables_encode_spec; eauto. exploit shstrtable_encode_spec; eauto.
  intuition congruence.
Qed.


Lemma tables_encode_spec:
  forall prog prog1 prog2 prog3 tprog,
    StrtableEncode.transf_program prog = OK prog1 ->
    SymbtableEncode.transf_program prog1 = OK prog2 ->
    ReloctablesEncode.transf_program prog2 = OK prog3 ->
    ShstrtableEncode.transf_program prog3 = OK tprog ->
    prog_defs prog = prog_defs tprog /\
    prog_public prog = prog_public tprog /\
    prog_main prog = prog_main tprog /\
    prog_symbtable prog = prog_symbtable tprog /\
    prog_reloctables prog = prog_reloctables tprog /\
    prog_senv prog = prog_senv tprog /\
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
  exploit strtable_encode_spec; eauto.
  exploit symbtable_encode_spec; eauto.
  exploit reloctables_encode_spec; eauto.
  exploit shstrtable_encode_spec; eauto. intuition try congruence.
  destruct H31 as (strmap & sbytes & GSM & STR & SEC).
  destruct H34 as (symt & CSS & EQ).
  exists strmap, sbytes, symt; intuition try congruence.
  rewrite H32, H33, EQ, SEC. simpl.
  rewrite <- app_assoc. simpl.
  rewrite <- ! app_assoc. simpl.
  intuition congruence.
Qed.

Lemma genv_genv_same:
  RelocProgSemantics1.Genv.genv_genv (RelocProgSemantics1.globalenv tprog) =
  RelocProgSemantics1.Genv.genv_genv (RelocProgSemantics1.globalenv prog).
Proof.
  unfold RelocProgSemantics1.globalenv. simpl.
  unfold RelocProgSemantics.globalenv.
  exploit tables_encode_spec; eauto.
  intros (EQdefs & EQpublic & EQmain & EQsymt & EQreloct & EQsenv & strmap & sbytes & symt
          & GSMB & CSS & EQstrt & EQsect).
  f_equal; try intuition congruence.
  f_equal; try intuition congruence.
  rewrite EQsect.
  cut (length (prog_sectable prog) = 3%nat). intro LEN.
  destruct (prog_sectable prog) eqn:?; simpl in LEN; try congruence.
  destruct s0 eqn:?; simpl in LEN; try congruence.
  destruct l eqn:?; simpl in LEN; try congruence.
  destruct l0 eqn:?; simpl in LEN; try congruence. simpl. auto.
  unfold StrtableEncode.transf_program in transf_str_encode.
  monadInv transf_str_encode. repeat destr_in EQ0. simpl in *.
  apply beq_nat_true in Heqb. rewrite app_length in Heqb.
  simpl in Heqb. omega.
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

Theorem transf_program_correct rs:
  forward_simulation (RelocProgSemantics2.semantics prog rs)
                     (RelocProgSemantics3.semantics tprog rs).
Proof.
  generalize(ShstrtableDecode.transf_program_inv_correct _ transf_shstr_encode). intro shstr_decode.
  generalize (fun v1 v2 => ReloctablesDecode.transf_program_inv_correct
                _ v1 v2 transf_reloc_encode).
  replace (prog_reloctables prog2) with (prog_reloctables prog).
  intro reloc_decode.
  trim reloc_decode. apply valid_reloctables with (id := RELOC_CODE).
  trim reloc_decode. apply valid_reloctables with (id := RELOC_DATA).
  Focus 2.
  exploit strtable_encode_spec; eauto. exploit symbtable_encode_spec; eauto. intuition congruence.
  exploit SymbtableDecode.transf_program_inv_correct. 3: apply valid_strtable_p.
  all: eauto.
  replace (prog_symbtable prog1) with (prog_symbtable prog). auto.
  {
    exploit strtable_encode_spec. eauto. intuition congruence.
  }
  intro symb_decode.
  generalize (StrtableDecode.transf_program_inv_correct _ empty_strtable transf_str_encode). intro str_decode.
  eapply forward_simulation_step with (match_states := fun (e1 e2: Asm.state) => e1 = e2).
  - simpl. intro id. f_equal.
    unfold RelocProgSemantics1.globalenv. simpl.
    unfold RelocProgSemantics1.genv_senv. simpl.
    unfold RelocProgSemantics.globalenv.
    rewrite ! genv_senv_add_external_globals. simpl.
    exploit strtable_encode_spec; eauto. exploit symbtable_encode_spec; eauto.
    exploit reloctables_encode_spec; eauto. exploit shstrtable_encode_spec; eauto.
    intuition congruence.
  - intros s1 IS.
    eexists; split; eauto.
    econstructor.
    unfold decode_tables.
    rewrite shstr_decode. simpl.
    rewrite reloc_decode. simpl.
    rewrite symb_decode. simpl.
    rewrite str_decode. simpl. eauto. apply IS.
  - simpl. intuition congruence.
  - simpl. intros.
    rewrite genv_same. subst. eauto.
Qed.

End PRESERVATION.
