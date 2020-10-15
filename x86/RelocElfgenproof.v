(* *******************  *)
(* Author: Pierre Wilke *)
(* Date:   Jan 29, 2020 *)
(* *******************  *)

Require Import Coqlib Errors.
Require Import Integers Floats AST Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Op Locations Mach Conventions Asm RealAsm.
Require Import RelocProgram RelocProgSemantics3.
Require Import RelocElf RelocElfSemantics.
Require Import TablesEncodeproof.
Require Import RelocElfgen.
Import ListNotations.

Definition match_prog p tp :=
  gen_reloc_elf p = OK tp.

Lemma transf_program_match:
  forall p tp, gen_reloc_elf p = OK tp -> match_prog p tp.
Proof.
  unfold match_prog; intuition.
Qed.

Section PRESERVATION.
  Existing Instance inject_perm_all.
Context `{external_calls_prf: ExternalCalls}.

Local Existing Instance mem_accessors_default.


Variable prog: RelocProgram.program.
Variable tprog: elf_file.

Hypothesis TRANSF: match_prog prog tprog.

(* Hypothesis first_section_is_null: *)
(*   hd_error (prog_sectable prog) = Some sec_null. *)

Lemma decodable:
  exists pp, decode_tables prog = OK pp.
Proof.
  unfold match_prog in TRANSF. unfold gen_reloc_elf in TRANSF.
  monadInv TRANSF. repeat destr_in EQ2. eauto.
Qed.

Lemma decode_tables_same:
  decode_tables prog = decode_tables (reloc_program_of_elf_program tprog).
Proof.
  unfold match_prog in TRANSF. unfold gen_reloc_elf in TRANSF.
  monadInv TRANSF. repeat destr_in EQ2.
  unfold decode_tables.
  unfold gen_sections in EQ. 
  assert (map sec_bytes x = (prog_sectable prog)).
  {
    revert EQ. clear. revert x.
    generalize (prog_sectable prog).
    induction s; simpl; intros; eauto. inv EQ. reflexivity.
    destruct (fold_right acc_sections (OK []) s) eqn:?.
    unfold acc_sections in EQ. simpl in EQ. monadInv EQ. simpl. f_equal.
    unfold transl_section in EQ0. destr_in EQ0. eauto.
    simpl in EQ. inv EQ.
  } 
  unfold reloc_program_of_elf_program. simpl.
  apply Nat.eqb_eq in Heqb.
  destruct x; simpl in Heqb; try omega.
  destruct x; simpl in Heqb; try omega.
  destruct x; simpl in Heqb; try omega.
  destruct x; simpl in Heqb; try omega.
  destruct x; simpl in Heqb; try omega.
  destruct x; simpl in Heqb; try omega.
  destruct x; simpl in Heqb; try omega.
  rewrite <- H.
  subst. simpl.
  auto.
Qed.

Lemma decode_tables_eq: forall p1 p2,
    RelocProgram.prog_defs p1 = RelocProgram.prog_defs p2 ->
    RelocProgram.prog_public p1 = RelocProgram.prog_public p2 ->
    RelocProgram.prog_main p1 = RelocProgram.prog_main p2 ->
    RelocProgram.prog_sectable p1 = RelocProgram.prog_sectable p2 ->
    RelocProgram.prog_senv p1 = RelocProgram.prog_senv p2 ->
    decode_tables p1 = decode_tables p2.
Proof.
  intros p1 p2 eq_defs eq_public eq_main eq_sectable eq_senv.
  unfold decode_tables.
  rewrite eq_sectable, eq_senv. unfold bind, bind2.
  repeat (destr; [idtac]).  destr.
Qed.

Lemma semantics3same: forall p1 p2 rs,
    RelocProgram.prog_defs p1 = RelocProgram.prog_defs p2 ->
    RelocProgram.prog_public p1 = RelocProgram.prog_public p2 ->
    RelocProgram.prog_main p1 = RelocProgram.prog_main p2 ->
    RelocProgram.prog_sectable p1 = RelocProgram.prog_sectable p2 ->
    RelocProgram.prog_senv p1 = RelocProgram.prog_senv p2 ->
    (exists p, decode_tables p1 = OK p) ->
    RelocProgSemantics3.semantics p1 rs = RelocProgSemantics3.semantics p2 rs.
Proof.
  intros p1 p2 rs eq_defs eq_public eq_main eq_sectable eq_senv (pp & DT).
  unfold RelocProgSemantics3.semantics.
  erewrite <- (decode_tables_eq p1 p2); eauto.
  rewrite DT. auto.
Qed.

Lemma fr_acc_sections_map s0 x:
  fold_right acc_sections (OK []) s0 = OK x -> s0 = sec_bytes ## x.
Proof.
  revert x; induction s0; simpl; intros; eauto. inv H; auto.
  unfold acc_sections in H at 1. monadInv H. apply IHs0 in EQ. subst.
  unfold transl_section in EQ1. destr_in EQ1. inv EQ1. auto.
Qed.

Lemma transf_program_correct:
  forall rs, forward_simulation (RelocProgSemantics3.semantics prog rs)
                                (RelocElfSemantics.semantics tprog rs).
Proof.
  unfold semantics. intro rs.
  assert (EQ: RelocProgSemantics3.semantics prog rs =
              RelocProgSemantics3.semantics (reloc_program_of_elf_program tprog) rs).
  {
    unfold match_prog, gen_reloc_elf in TRANSF.
    monadInv TRANSF. repeat destr_in EQ2.
    unfold reloc_program_of_elf_program. simpl.
    apply semantics3same; simpl; auto.
    unfold gen_sections in EQ.
    apply Nat.eqb_eq in Heqb.
    destruct x; simpl in Heqb; try omega.
    destruct x; simpl in Heqb; try omega.
    destruct x; simpl in Heqb; try omega.
    destruct x; simpl in Heqb; try omega.
    destruct x; simpl in Heqb; try omega.
    destruct x; simpl in Heqb; try omega.
    destruct x; simpl in Heqb; try omega.
    apply fr_acc_sections_map in EQ. subst. auto.
    eauto.
  }
  rewrite EQ.
  eapply forward_simulation_step with (match_states := fun (e1 e2: Asm.state) => e1 = e2);
    simpl; intros; subst; eauto.
Qed.

End PRESERVATION.

Definition link_reloc_elf_gen (p1 p2: RelocElf.elf_file) : option RelocElf.elf_file :=
  match link_reloc_decode_tables (reloc_program_of_elf_program p1) (reloc_program_of_elf_program p2) with
    Some pp =>
    match gen_reloc_elf pp with
    | OK tp => Some tp
    | _ => None
    end
  | _ => None
  end.

Instance linker2 : Linker RelocElf.elf_file.
Proof.
  eapply Build_Linker with (link := link_reloc_elf_gen) (linkorder := fun _ _ => True).
  auto. auto. auto.
Defined.

Lemma gen_sections_succeeds:
  forall st,
    Forall (fun s => exists b, s = sec_bytes b) st
    <->
    (exists x, gen_sections st = OK x).
Proof.
  split.
  - unfold gen_sections. induction 1; simpl; intros; eauto.
    destruct H. subst.
    destruct IHForall. rewrite H. simpl. eauto.
  - unfold gen_sections. intros (x & EQ). revert x EQ.
    induction st; simpl; intros; eauto.
    unfold acc_sections in EQ at 1. repeat destr_in EQ. monadInv H0.
    eapply IHst in EQ. constructor; auto.
    unfold transl_section in EQ1. repeat destr_in EQ1. eauto.
Qed.

Lemma Forall_app:
  forall {A} P (l1 l2: list A),
    Forall P l1 ->
    Forall P l2 ->
    Forall P (l1 ++ l2).
Proof.
  intros. rewrite Forall_forall in *.
  intros x IN. rewrite in_app in IN. intuition eauto.
Qed.

Instance tl : @TransfLink _ _ TablesEncodeproof.linker2
                          linker2
                          match_prog.
Proof.
  red. simpl. unfold link_reloc_elf_gen.
  intros.
  unfold link_reloc_decode_tables.
  erewrite <- decode_tables_same. 2: eauto.
  erewrite <- decode_tables_same. 2: eauto.
  unfold link_reloc_decode_tables in H.
  repeat destr_in H.
  cut (exists tp, gen_reloc_elf p = OK tp). intros (tp & EQ); rewrite EQ; eauto.
  unfold match_prog in *.
  unfold gen_reloc_elf in *. autoinv.
  edestruct (proj1 (gen_sections_succeeds (prog_sectable p))) as (secs & GS).
  unfold TablesEncode.transf_program in Heqr1. autoinv. simpl in *.
  apply Forall_app.
  {
    unfold RelocLinking1.link_reloc_prog in Heqo. autoinv. simpl in *.
    unfold RelocLinking.link_reloc_prog in Heqo0. autoinv. simpl in *.
    unfold RelocLinking.link_sectable in Heqo7. autoinv. simpl in *.
    unfold RelocLinking1.link_code_reloctable, RelocLinking1.link_data_reloctable, RelocLinking1.link_rodata_reloctable in *.
    rewrite Heqo0 in Heqo1.
    rewrite Heqo10 in Heqo2.
    rewrite Heqo11 in Heqo3. simpl in *.
    rewrite EQ1 in Heqr; inv Heqr.
    rewrite EQ3 in Heqr0; inv Heqr0.
    unfold decode_tables in EQ1, EQ3. autoinv.
    unfold gen_sections in EQ0, EQ. simpl in *. unfold acc_sections in *. autoinv.
    unfold transl_section in *. autoinv. simpl in *.
    vm_compute in Heqo0, Heqo10, Heqo11, Heqo12, Heqo13, Heqo14.
    inv Heqo0; inv Heqo4; inv Heqo5; inv Heqo6; inv Heqo10; inv Heqo11; inv Heqo12; inv Heqo13; inv Heqo14. 
    simpl in Heqo15. inv Heqo15. repeat constructor; eauto.
    simpl in Heqo17. inv Heqo17. repeat constructor; eauto.
    simpl in Heqo16. inv Heqo16. repeat constructor; eauto.
  }
  {
    constructor. eauto.
    constructor. unfold SymbtableEncode.create_symbtable_section in EQ4. autoinv. eauto.
    constructor. unfold ReloctablesEncode.create_reloctable_section. eauto.
    constructor. unfold ReloctablesEncode.create_reloctable_section. eauto.
    constructor. unfold ReloctablesEncode.create_reloctable_section. eauto.
    constructor. unfold ShstrtableEncode.create_shstrtab_section. eauto.
    constructor.
  }
  rewrite TablesEncode.dump_reloctables_error in H0. congruence.
  rewrite GS. simpl.
  unfold decode_tables.
  generalize (valid_strtable_p _ _ Heqr1). intro VALID_STR.
  unfold TablesEncode.transf_program in Heqr1. autoinv. simpl in *.
  unfold gen_sections in GS. simpl in *.
  unfold RelocLinking1.link_reloc_prog in Heqo. autoinv. simpl in *.
  unfold RelocLinking.link_reloc_prog in Heqo0. autoinv. simpl in *.
  unfold RelocLinking.link_sectable in Heqo7. autoinv. simpl in *.
  rewrite ReloctablesDecode.decode_encode_reloctable.
  rewrite ReloctablesDecode.decode_encode_reloctable. simpl.
  erewrite StrtableDecode.decode_string_map_correct'. 2: eauto; fail. simpl.
  rewrite EQ2. simpl. erewrite SymbtableDecode.decode_create_symtable_section.
  4-5: eauto. simpl.
  unfold acc_sections in GS. autoinv. simpl.
  rewrite pred_dec_true. eauto.
  admit.                        (* get_elf_shoff < 2 ^ 32 *)
  admit.
  eapply VALID_STR. eauto.
  eapply prog_strings_eq; eauto.
  generalize (f RELOC_CODE). simpl. auto.
  generalize (f RELOC_DATA). simpl. auto.
  generalize (f RELOC_RODATA). simpl. auto.
  rewrite TablesEncode.dump_reloctables_error in H0; congruence.
Admitted.
