(* ******************** *)
(* Author: Zhenguo Yin  *)
(* Date:   Sep 21, 2020 *)
(* ******************** *)

Require Import Coqlib Errors.
Require Import Integers Floats AST Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Op Locations Mach Conventions Asm RealAsm.
Require Import AsmFloatLiteral AsmFloatLiteralproof.
Import ListNotations.

Instance TransfPermuteOrderedLink2 
  : TransfLink AsmFloatLiteralproof.match_prog.
Proof.
  red. unfold match_prog.
Admitted.
