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
              (PTree.elements (symbtable_to_tree s1)).

Definition reloc_prog_syneq (p tp: program) : Prop :=
  Permutation (prog_defs p) (prog_defs tp) 
  /\ prog_main p = prog_main tp
  /\ prog_public p = prog_public tp
  /\ prog_sectable p = prog_sectable tp
  /\ symbtable_syneq (prog_symbtable p) (prog_symbtable tp).
  