(* *******************  *)
(* Author: Author C  *)
(* Date:   Jan 14, 2020 *)
(* *******************  *)

(** * Decoding of the section header string table *)
Require Import Coqlib Integers AST Maps.
Require Import Asm.
Require Import Errors.
Require Import RelocProgram Encode.
Require Import SeqTable Memdata.
Require Import Hex Bits.
Import Hex Bits.
Import ListNotations.
Require Import ShstrtableEncode.
Set Implicit Arguments.

Local Open Scope error_monad_scope.
Local Open Scope hex_scope.
Local Open Scope bits_scope.


Definition transf_program_inv p :=
  do (sectable, _) <- take_drop 7 (prog_sectable p);
    OK {|
        prog_defs := prog_defs p;
        prog_public := prog_public p;
        prog_main := prog_main p;
        prog_sectable := sectable;
        prog_symbtable := prog_symbtable p;
        prog_strtable := prog_strtable p;
        prog_reloctables := prog_reloctables p;
        prog_senv := prog_senv p |}.


Theorem transf_program_inv_correct p p'
        (TP: transf_program p = OK p'):
  transf_program_inv p' = OK p.
Proof.
  unfold transf_program in TP.
  repeat destr_in TP.
  unfold transf_program_inv. simpl.
  apply beq_nat_true in Heqb.
  destruct (prog_sectable p) eqn:?; simpl in *; try congruence.
  destruct s0; simpl in *; try congruence.
  destruct s1; simpl in *; try congruence.
  destruct s2; simpl in *; try congruence.
  destruct s3; simpl in *; try congruence.
  destruct s4; simpl in *; try congruence.
  destruct s5; simpl in *; try congruence.
  destruct s6; simpl in *; try congruence.
  f_equal. destruct p; simpl in *. f_equal; simpl in *; auto.
Qed.
