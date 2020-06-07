(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*                 Xavier Leroy, INRIA Paris                           *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Machine- and ABI-dependent layout information for activation records. *)

Require Import Coqlib.
Require Import AST Memory Separation.
Require Import Bounds.

Local Open Scope sep_scope.

(** The general shape of activation records is as follows,
  from bottom (lowest offsets) to top:
- Space for outgoing arguments to function calls.
- Back link to parent frame
- Saved values of integer callee-save registers used by the function.
- Saved values of float callee-save registers used by the function.
- Local stack slots.
- Space for the stack-allocated data declared in Cminor
- Return address.
*)

Definition fe_ofs_arg := 0.

Definition make_env (b: bounds) : frame_env :=
  let w := if Archi.ptr64 then 8 else 4 in
(*  let olink := align (4 * b.(bound_outgoing)) w in  (* back link *) *)
  let ocs := align (4 * b.(bound_outgoing)) w (*SACC:comments this*)(*+ w*) in  (* callee-saves *)
  let ol :=  align (size_callee_save_area b ocs) 8 in (* locals *)
  let ostkdata := align (ol + 4 * b.(bound_local)) 8 in (* stack data *)
  let preretaddr := align (ostkdata + b.(bound_stack_data)) w in
  let sz := align (preretaddr + w) 8 in (* total size *)
  let oretaddr := sz - w in (* return address *)
  {| fe_size := sz;
(*SACC: comments this*)(*fe_ofs_link := olink;*)
     fe_ofs_retaddr := oretaddr;
     fe_ofs_local := ol;
     fe_ofs_callee_save := ocs;
     fe_stack_data := ostkdata;
     fe_used_callee_save := b.(used_callee_save) |}.

(*SACC:*)
Lemma retaddr_le: forall preretaddr w,
  preretaddr <= (align (preretaddr + w) 8) - w.
Proof.
  intros.
  assert (preretaddr + w <= (align (preretaddr + w) 8)).
  apply align_le; omega.
  omega.
Qed.

Lemma frame_env_separated:
  forall b sp m P,
  let fe := make_env b in
  m |= range sp 0 (fe_stack_data fe) ** range sp (fe_stack_data fe + bound_stack_data b) (fe_size fe) ** P ->
  m |= range sp (fe_ofs_local fe) (fe_ofs_local fe + 4 * bound_local b)
       ** range sp fe_ofs_arg (fe_ofs_arg + 4 * bound_outgoing b)
      (*SACC:comments this*)(* ** range sp (fe_ofs_link fe) (fe_ofs_link fe + size_chunk Mptr) *)
       ** range sp (fe_ofs_retaddr fe) (fe_ofs_retaddr fe + size_chunk Mptr)
       ** range sp (fe_ofs_callee_save fe) (size_callee_save_area b (fe_ofs_callee_save fe))
       ** P.
Proof.
Local Opaque Z.add Z.mul sepconj range.
  intros; simpl.
  set (w := if Archi.ptr64 then 8 else 4).
  (*SACC: comments this*)(*set (olink := align (4 * b.(bound_outgoing)) w).*)
  (*SACC: comments this*)(*set (ocs := olink + w).*)
  set (ocs := align (4 * b.(bound_outgoing)) w).
  set (ol :=  align (size_callee_save_area b ocs) 8).
  set (ostkdata := align (ol + 4 * b.(bound_local)) 8).
  (*SACC:*)set (preretaddr := align (ostkdata + b.(bound_stack_data)) w).
  (*SACC:*)set (sz := align (preretaddr + w) 8).
  (*SACC:comments this*)(*set (oretaddr := align (ostkdata + b.(bound_stack_data)) w).*)
  (*SACC:*)set (oretaddr := sz - w).
  replace (size_chunk Mptr) with w by (rewrite size_chunk_Mptr; auto).
  assert (0 < w) by (unfold w; destruct Archi.ptr64; omega).
  generalize b.(bound_local_pos) b.(bound_outgoing_pos) b.(bound_stack_data_pos); intros.
  assert (0 <= 4 * b.(bound_outgoing)) by omega.
  assert (4 * b.(bound_outgoing) <= (*SACC:*)(*olink*)ocs) by (apply align_le; omega).
  (*SACC:comments this*)(*assert (olink + w <= ocs) by (unfold ocs; omega).*)
  assert (preretaddr <= oretaddr) as RET by apply retaddr_le.
  assert (ocs <= size_callee_save_area b ocs) by (apply size_callee_save_area_incr). 
  assert (size_callee_save_area b ocs <= ol) by (apply align_le; omega).
  assert (ol + 4 * b.(bound_local) <= ostkdata) by (apply align_le; omega).
  assert (ostkdata + bound_stack_data b <= oretaddr).
  {
    apply Z.le_trans with (align (ostkdata + bound_stack_data b) w).
    apply align_le. omega.
    subst preretaddr. omega.
  }
  (*SACC:*)assert (oretaddr + w = fe_size fe) as SZEQ. 
  { 
    subst fe. subst w ocs ol ostkdata preretaddr oretaddr sz. 
    unfold make_env. simpl. omega.
  }
(* Reorder as:
     outgoing
     back link
     callee-save
     local
     retaddr *)
  rewrite sep_swap12.
  rewrite sep_swap23.
  rewrite sep_swap34.
  rewrite sep_swap23.
  rewrite sep_swap34.
(* Apply range_split and range_split2 repeatedly *)
  unfold fe_ofs_arg.
  apply range_split_2. fold ocs. omega. omega. 
  (*apply range_split. omega.*)
  apply range_split_2. fold ol. omega. omega.
  apply range_drop_right with ostkdata. omega.
  rewrite sep_swap.
  apply range_drop_left with (ostkdata + bound_stack_data b). omega.
  rewrite sep_swap.
  rewrite SZEQ. exact H.
Qed.

Lemma frame_env_range:
  forall b,
  let fe := make_env b in
  0 <= fe_stack_data fe /\ fe_stack_data fe + bound_stack_data b <= fe_size fe.
Proof.
  intros; simpl.
  set (w := if Archi.ptr64 then 8 else 4).
  (*SACC:comments this*)(*set (olink := align (4 * b.(bound_outgoing)) w).*)
  (*SACC:comments this*)(*set (ocs := olink + w).*)
  (*SACC:*)set (ocs := align (4 * b.(bound_outgoing)) w).
  set (ol :=  align (size_callee_save_area b ocs) 8).
  set (ostkdata := align (ol + 4 * b.(bound_local)) 8).
  (*SACC:*)set (preretaddr := align (ostkdata + b.(bound_stack_data)) w).
  (*SACC:comments this*)(*set (oretaddr := align (ostkdata + b.(bound_stack_data)) w).*)
  (*SACC:*)set (sz := align (preretaddr + w) 8).
  (*SACC:*)set (oretaddr := sz - w).
  assert (0 < w) by (unfold w; destruct Archi.ptr64; omega).
  generalize b.(bound_local_pos) b.(bound_outgoing_pos) b.(bound_stack_data_pos); intros.
  assert (0 <= 4 * b.(bound_outgoing)) by omega.
  assert (4 * b.(bound_outgoing) <= (*SACC:*)(*olink*)ocs) by (apply align_le; omega).
  (*SACC:*)(*assert (olink + w <= ocs) by (unfold ocs; omega).*)
  assert (ocs <= size_callee_save_area b ocs) by (apply size_callee_save_area_incr). 
  assert (size_callee_save_area b ocs <= ol) by (apply align_le; omega).
  assert (ol + 4 * b.(bound_local) <= ostkdata) by (apply align_le; omega).
  (*SACC:*)assert (preretaddr <= oretaddr) as RET by apply retaddr_le.
  assert (ostkdata + bound_stack_data b <= oretaddr). 
  {
    apply Z.le_trans with (align (ostkdata + bound_stack_data b) w).
    apply align_le. omega.
    subst preretaddr. omega.
  }
  split. omega. subst oretaddr. omega. 
Qed.

Lemma frame_env_aligned:
  forall b,
  let fe := make_env b in
     (8 | fe_ofs_arg)
  /\ (8 | fe_ofs_local fe)
  /\ (8 | fe_stack_data fe)
(*  /\ (align_chunk Mptr | fe_ofs_link fe) *)
  /\ (align_chunk Mptr | fe_ofs_retaddr fe).
Proof.
  intros; simpl.
  set (w := if Archi.ptr64 then 8 else 4).
  (*SACC: comments this*)
  (*set (olink := align (4 * b.(bound_outgoing)) w).
  set (ocs := olink + w).*)
  (*SACC:*)set (ocs := align (4 * b.(bound_outgoing)) w).
  set (ol :=  align (size_callee_save_area b ocs) 8).
  set (ostkdata := align (ol + 4 * b.(bound_local)) 8).
  (*SACC:*)set (preretaddr := align (ostkdata + b.(bound_stack_data)) w).
  (*SACC:*)set (sz := align (preretaddr + w) 8).
  (*SACC:comments this*)(*
  set (oretaddr := align (ostkdata + b.(bound_stack_data)) w).*)
  set (oretaddr := sz - w).
  assert (0 < w) by (unfold w; destruct Archi.ptr64; omega).
  assert (w_divides8: (w | 8)).
  {
    simpl. unfold w. destr. apply Z.divide_refl.
    apply Zdivide_intro with 2. omega.
  }
  (*SACC:*)assert (preretaddr <= oretaddr) as RET by apply retaddr_le.
  replace (align_chunk Mptr) with w by (rewrite align_chunk_Mptr; auto).
  split. apply Zdivide_0.
  split. apply align_divides; omega.
  split. apply align_divides; omega.
  subst oretaddr. apply Z.divide_sub_r. 
  subst sz. apply Z.divide_trans with 8. apply w_divides8.
  apply align_divides; omega.
  apply Z.divide_refl.
Qed.


(*========================SACC:========================*)

Lemma frame_env_separated':
  (* forall `{memory_model_prf: Mem.MemoryModel} *)
  forall b ,
    let w := if Archi.ptr64 then 8 else 4 in
    let fe := make_env b in
     let ocs := align (4 * bound_outgoing b) w in
     (* let ocs := olink + w in *)
     let ol := align (size_callee_save_area b ocs) 8 in
     let ostkdata := align (ol + 4 * bound_local b) 8 in
     let oretaddr := align (ostkdata + bound_stack_data b) w in
     0 <= ocs
  (* /\ olink + w <= ocs *)
  /\ ocs <= size_callee_save_area b ocs
  /\ size_callee_save_area b ocs <= ol
  /\ ol + 4 * bound_local b <= ostkdata
  /\ ostkdata + bound_stack_data b <= oretaddr
  /\ ocs <= fe_stack_data fe.
Proof.
Local Opaque Z.add Z.mul sepconj range fe_stack_data.
intros; simpl.
generalize b.(bound_local_pos) b.(bound_outgoing_pos) b.(bound_stack_data_pos); intros.
replace (size_chunk Mptr) with w by (rewrite size_chunk_Mptr; auto).
assert (0 < w) by (unfold w; destruct Archi.ptr64; omega).
generalize b.(bound_local_pos) b.(bound_outgoing_pos) b.(bound_stack_data_pos); intros.
assert (0 <= 4 * b.(bound_outgoing)) by omega.
assert (4 * b.(bound_outgoing) <= ocs) by (apply align_le; omega).
(* assert (olink + w <= ocs) by (unfold ocs; omega). *)
assert (ocs <= size_callee_save_area b ocs) by (apply size_callee_save_area_incr). 
assert (size_callee_save_area b ocs <= ol) by (apply align_le; omega).
assert (ol + 4 * b.(bound_local) <= ostkdata) by (apply align_le; omega).
assert (ostkdata + bound_stack_data b <= oretaddr) by (apply align_le; omega).
repeat split; auto.
omega.
Local Transparent fe_stack_data.
simpl. fold w. fold ocs. fold ol. fold ostkdata. omega.
Qed.

Lemma zero_lt_align8 : forall x,
  0 < x -> 0 < align x 8.
Proof.
  intros.
  eapply Z.lt_le_trans. 
  Focus 2. apply align_le. omega.
  auto.
Qed.

Lemma fe_size_pos (b: bounds) :
  let fe := make_env b in
  0 < fe_size fe.
Proof.
  simpl. apply zero_lt_align8.
  replace 0 with (0 + 0) by omega.
  eapply Z.add_le_lt_mono. 2: destr; omega.
  etransitivity. 2: apply align_le. 2: destr; omega.
  etransitivity. 2: apply le_add_pos. 2: generalize (bound_stack_data_pos b); omega.
  etransitivity. 2: apply align_le. 2: omega.
  etransitivity. 2: apply le_add_pos. 2: generalize (bound_local_pos b); omega.
  etransitivity. 2: apply align_le. 2: omega.
  etransitivity. 2: apply size_callee_save_area_incr.
  etransitivity. 2: apply align_le. 2: destr; omega.
  generalize (bound_outgoing_pos b); omega.
Qed.

