Require Import Coqlib Integers AST Maps.
Require Import Asm.
Require Import Errors.
Require Import Memtype.
Require Import Asm RelocProgram.
Require Import Symbtablegen.
Require Import Linking RelocLinking.
Require Import SeqTable.
Import ListNotations.

Set Implicit Arguments.

Definition match_prog (p: Asm.program) (tp: program) :=
  transf_program p = OK tp.

Lemma link_prog_inv: forall (F V: Type) (fi:F -> bool) (LF: Linker F) (LV: Linker V) (p1 p2 p: AST.program F V), 
    link_prog fi p1 p2 = Some p ->
    (AST.prog_main p1 = AST.prog_main p2)
    /\ list_norepet (map fst (AST.prog_defs p1))
    /\ list_norepet (map fst (AST.prog_defs p2))
    /\ exists defs, 
        p = {| AST.prog_defs := defs; 
               AST.prog_public := AST.prog_public p1 ++ AST.prog_public p2; 
               AST.prog_main := AST.prog_main p1 |}
        /\ link_defs fi (AST.prog_defs p1) (AST.prog_defs p2) = Some defs.
Proof.
  intros F V fi LF LV p1 p2 p LINK.
  unfold link_prog in LINK.
  destruct ident_eq; simpl in LINK.
  unfold prog_unique_idents in LINK.
  repeat (destruct list_norepet_dec; simpl in LINK).
  destr_in LINK; inv LINK. 
  repeat split; auto. eauto.
  congruence.
  congruence.
  congruence.
Qed.


Lemma match_prog_pres_prog_defs : forall p tp,
  match_prog p tp -> AST.prog_defs p = prog_defs tp.
Proof.
  intros p tp MATCH. red in MATCH.
  unfold transf_program in MATCH.
  destruct check_wellformedness; try monadInv MATCH.
  destruct (gen_symb_table sec_data_id sec_code_id (AST.prog_defs p)) eqn:EQ.
  destruct p0. 
  destruct zle; try monadInv MATCH. simpl. auto.
Qed.

Lemma match_prog_pres_prog_main : forall p tp,
  match_prog p tp -> AST.prog_main p = prog_main tp.
Proof.
  intros p tp MATCH. red in MATCH.
  unfold transf_program in MATCH.
  destruct check_wellformedness; try monadInv MATCH.
  destruct (gen_symb_table sec_data_id sec_code_id (AST.prog_defs p)) eqn:EQ.
  destruct p0. 
  destruct zle; try monadInv MATCH. simpl. auto.
Qed.

Lemma match_prog_pres_prog_public : forall p tp,
  match_prog p tp -> AST.prog_public p = prog_public tp.
Proof.
  intros p tp MATCH. red in MATCH.
  unfold transf_program in MATCH.
  destruct check_wellformedness; try monadInv MATCH.
  destruct (gen_symb_table sec_data_id sec_code_id (AST.prog_defs p)) eqn:EQ.
  destruct p0. 
  destruct zle; try monadInv MATCH. simpl. auto.
Qed.

Lemma link_transf_symbtablegen : forall (p1 p2 : Asm.program) (tp1 tp2 : program) (p : Asm.program),
    link p1 p2 = Some p -> match_prog p1 tp1 -> match_prog p2 tp2 -> 
    exists tp : program, link tp1 tp2 = Some tp /\ match_prog p tp.
Proof.
  intros p1 p2 tp1 tp2 p LINK MATCH1 MATCH2.
  unfold link. unfold Linker_reloc_prog. unfold link_reloc_prog.
  rewrite <- (match_prog_pres_prog_defs MATCH1).
  rewrite <- (match_prog_pres_prog_defs MATCH2).
  rewrite <- (match_prog_pres_prog_main MATCH1).
  rewrite <- (match_prog_pres_prog_main MATCH2).
  rewrite <- (match_prog_pres_prog_public MATCH1).
  rewrite <- (match_prog_pres_prog_public MATCH2).
  setoid_rewrite LINK.
  apply link_prog_inv in LINK.
  destruct LINK as (MAINEQ & NRPT1 & NRPT2 & defs & PEQ & LINKDEFS). subst. simpl.
  unfold link_defs in LINKDEFS.
  unfold match_prog in *.

  unfold transf_program in MATCH1.
  destruct check_wellformedness; try monadInv MATCH1.
  destruct (gen_symb_table sec_data_id sec_code_id (AST.prog_defs p1)) as (p & csz1) eqn:GSEQ1 .
  destruct p as (stbl1 & dsz1).
  destruct zle; try monadInv MATCH1; simpl.
  
  unfold transf_program in MATCH2.
  destruct check_wellformedness; try monadInv MATCH2.
  destruct (gen_symb_table sec_data_id sec_code_id (AST.prog_defs p2)) as (p & csz2) eqn:GSEQ2 .
  destruct p as (stbl2 & dsz2).
  destruct zle; try monadInv MATCH2; simpl.

  unfold link_symbtable.

  Admitted.


Instance TransfLinkSymbtablegen : TransfLink match_prog :=
  link_transf_symbtablegen.

