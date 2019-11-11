(* *******************  *)
(* Author: PLDI-authors  *)
(* Date:   Sep 19, 2019 *)
(* *******************  *)

Require Import Coqlib Integers AST Maps.
Require Import Events.
Require Import Asm.
Require Import Errors.
Require Import Memtype.
Require Import Globalenvs .
Import ListNotations.

Set Implicit Arguments.

Local Open Scope error_monad_scope.

(** *Padding Nops in functions *)

(** This pass is necessary to make the sizes of functions correctly
aligned for memory injections *)

Definition gen_nops (n:nat) :=
  map (fun _ => Pnop) (seq 1 n).

Compute (gen_nops 0).
Compute (gen_nops 3).

Definition compute_padding_nops (sz:Z) :=
  let n := Z.to_nat ((align sz alignw) - sz) in
  gen_nops n.

Compute (compute_padding_nops 16).
Compute (compute_padding_nops 13).

(** Pad nops *)
Definition transl_function (f:function) : function :=
  let nops := compute_padding_nops (code_size (fn_code f)) in
  mkfunction (fn_sig f) ((fn_code f) ++ nops) (fn_stacksize f) (fn_pubrange f).

Definition transf_fundef (f:fundef) :=
  transf_fundef transl_function f.

Definition transf_program (p: program) : program :=
  transform_program transf_fundef p.
