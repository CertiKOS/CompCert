(* *******************  *)
(* Author: Pierre Wilke *)
(* Date:   Feb 4, 2020 *)
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

Lemma transf_program_correct:
  forall rs, forward_simulation (RelocProgSemantics1.semantics prog rs) (RelocProgSemantics2.semantics tprog rs).
Proof.
  intro rs.
  apply forward_simulation_step with (match_states := fun x y : Asm.state => x = y).
  - simpl.
    unfold match_prog, transf_program in TRANSF. monadInv TRANSF.
    unfold globalenv, genv_senv. simpl.
    unfold RelocProgSemantics.globalenv. simpl. intro id.
    rewrite ! RelocProgSemantics.genv_senv_add_external_globals. simpl. auto.
  - simpl; intros s1 IS.
    inv IS.
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
