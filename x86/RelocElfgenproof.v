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

Hypothesis first_section_is_null:
  hd_error (prog_sectable prog) = Some sec_null.

Hypothesis decodable:
  exists pp, decode_tables prog = OK pp.

Lemma decode_tables_same:
  decode_tables prog = decode_tables (reloc_program_of_elf_program tprog).
Proof.
  unfold match_prog in TRANSF. unfold gen_reloc_elf in TRANSF.
  monadInv TRANSF. repeat destr_in EQ0.
  unfold decode_tables.
  unfold gen_sections in EQ. destr_in EQ.
  assert (map sec_bytes x = s0).
  {
    revert EQ. clear. revert x.
    induction s0; simpl; intros; eauto. inv EQ. reflexivity.
    destruct (fold_right acc_sections (OK []) s0) eqn:?.
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
  destruct x; simpl in Heqb; try omega.
  simpl in first_section_is_null. inv first_section_is_null. subst. simpl.
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
    monadInv TRANSF. repeat destr_in EQ0.
    unfold reloc_program_of_elf_program. simpl.
    apply semantics3same; simpl; auto.
    destruct (prog_sectable prog); simpl in *; try congruence.
    apply Nat.eqb_eq in Heqb.
    destruct x; simpl in Heqb; try omega.
    destruct x; simpl in Heqb; try omega.
    destruct x; simpl in Heqb; try omega.
    destruct x; simpl in Heqb; try omega.
    destruct x; simpl in Heqb; try omega.
    destruct x; simpl in Heqb; try omega.
    destruct x; simpl in Heqb; try omega.
    destruct x; simpl in Heqb; try omega.
    inv first_section_is_null.
    apply fr_acc_sections_map in EQ. subst. auto.
  }
  rewrite EQ.
  eapply forward_simulation_step with (match_states := fun (e1 e2: Asm.state) => e1 = e2);
    simpl; intros; subst; eauto.
Qed.

End PRESERVATION.
