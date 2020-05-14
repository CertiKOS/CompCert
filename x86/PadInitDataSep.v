(* *******************  *)
(* Author: Yuting Wang  *)
(* Date:   Dec 2, 2019 *)
(* *******************  *)

Require Import Coqlib Errors.
Require Import Integers Floats AST Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Op Locations Mach Conventions Asm RealAsm.
Require Import PadInitData PadInitDataproof.
Import ListNotations.

Axiom TransfPermuteOrderedLink2 
  : TransfLink PadInitDataproof.match_prog.

