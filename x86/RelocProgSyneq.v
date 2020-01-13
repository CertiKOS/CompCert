(* ********************* *)
(* Author: Yuting Wang   *)
(* Date:   Oct 31, 2019  *)
(* ********************* *)

(** * Syntactic equality bewteen relocatble programs *)

Require Import Coqlib Maps Integers Values AST.
Require Import Globalenvs SeqTable Asm.
Require Import RelocProgram.
Require Import Permutation.

Definition symbtable_syneq (s1 s2: symbtable) : Prop :=
  Permutation (PTree.elements (symbtable_to_tree s1))
              (PTree.elements (symbtable_to_tree s2)).

Lemma symbtable_syneq_symm: forall t1 t2,
    symbtable_syneq t1 t2 -> symbtable_syneq t2 t1.
Proof.
  unfold symbtable_syneq.
  intros. 
  apply Permutation_sym; eauto.
Qed.

Lemma symbtable_syneq_trans: forall t1 t2 t3,
    symbtable_syneq t1 t2 -> symbtable_syneq t2 t3 ->
    symbtable_syneq t1 t3.
Proof.
  unfold symbtable_syneq.
  intros. 
  eapply Permutation_trans; eauto.
Qed.


Definition reloc_prog_syneq (p tp: program) : Prop :=
  Permutation (prog_defs p) (prog_defs tp) 
  /\ prog_main p = prog_main tp
  /\ prog_public p = prog_public tp
  /\ prog_sectable p = prog_sectable tp
  /\ symbtable_syneq (prog_symbtable p) (prog_symbtable tp)
  /\ prog_strtable p = prog_strtable tp
  /\ prog_reloctables p = prog_reloctables tp.
  
