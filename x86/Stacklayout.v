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

(* Definition make_env (b: bounds) : frame_env := *)
(*   let w := if Archi.ptr64 then 8 else 4 in *)
(*   let ocs := align (4 * b.(bound_outgoing)) w in  (* back link *) *)
(*   (* let ocs := olink + w in                           (* callee-saves *) *) *)
(*   let ol :=  align (size_callee_save_area b ocs) 8 in (* locals *) *)
(*   let ostkdata := align (ol + 4 * b.(bound_local)) 8 in (* stack data *) *)
(*   let oretaddr := align (ostkdata + b.(bound_stack_data)) w in (* return address *) *)
(*   let sz := oretaddr + w in (* total size *) *)
(*   {| fe_size := sz; *)
(*      (* fe_ofs_link := olink; *) *)
(*      fe_ofs_retaddr := oretaddr; *)
(*      fe_ofs_local := ol; *)
(*      fe_ofs_callee_save := ocs; *)
(*      fe_stack_data := ostkdata; *)
(*      fe_used_callee_save := b.(used_callee_save) |}. *)

Definition make_env (b: bounds) : frame_env :=
  let w := if Archi.ptr64 then 8 else 4 in
  let ocs := align (4 * b.(bound_outgoing)) w in  (* back link *)
  (* let ocs := olink + w in                           (* callee-saves *) *)
  let ol :=  align (size_callee_save_area b ocs) 8 in (* locals *)
  let ostkdata := align (ol + 4 * b.(bound_local)) 8 in (* stack data *)
  let preretaddr := align (ostkdata + b.(bound_stack_data)) w in
  let sz := align (preretaddr + w) 8 in (* total size *)
  let oretaddr := sz - w in (* return address *)
  {| fe_size := sz;
     (* fe_ofs_link := olink; *)
     fe_ofs_retaddr := oretaddr;
     fe_ofs_local := ol;
     fe_ofs_callee_save := ocs;
     fe_stack_data := ostkdata;
     fe_used_callee_save := b.(used_callee_save) |}.

Lemma retaddr_le: forall preretaddr w,
  preretaddr <= (align (preretaddr + w) 8) - w.
Proof.
  intros.
  assert (preretaddr + w <= (align (preretaddr + w) 8)).
  apply align_le; omega.
  omega.
Qed.

Section WITHMEM.
  Context `{memory_model_prf: Mem.MemoryModel}.
  Lemma frame_env_separated:
    forall b sp (m: mem) P,
      let fe := make_env b in
      m |= range sp 0 (fe_stack_data fe) ** range sp (fe_stack_data fe + bound_stack_data b) (fe_size fe) ** P ->
      m |= range sp (fe_ofs_local fe) (fe_ofs_local fe + 4 * bound_local b)
        ** range sp fe_ofs_arg (fe_ofs_arg + 4 * bound_outgoing b)
        (* ** range sp (fe_ofs_link fe) (fe_ofs_link fe + size_chunk Mptr) *)
        ** range sp (fe_ofs_retaddr fe) (fe_ofs_retaddr fe + size_chunk Mptr)
        ** range sp (fe_ofs_callee_save fe) (size_callee_save_area b (fe_ofs_callee_save fe))
        ** P.
  Proof.
    Local Opaque Z.add Z.mul sepconj range.
    intros; simpl.
    set (w := if Archi.ptr64 then 8 else 4).
    set (ocs := align (4 * b.(bound_outgoing)) w).
    (* set (ocs := olink + w). *)
    set (ol :=  align (size_callee_save_area b ocs) 8).
    set (ostkdata := align (ol + 4 * b.(bound_local)) 8).
    set (preretaddr := align (ostkdata + b.(bound_stack_data)) w).
    set (sz := align (preretaddr + w) 8).
    set (oretaddr := sz - w).
    assert (preretaddr <= oretaddr) as RET by apply retaddr_le.
    replace (size_chunk Mptr) with w by (rewrite size_chunk_Mptr; auto).
    assert (0 < w) by (unfold w; destruct Archi.ptr64; omega).
    generalize b.(bound_local_pos) b.(bound_outgoing_pos) b.(bound_stack_data_pos); intros.
    assert (0 <= 4 * b.(bound_outgoing)) by omega.
    assert (4 * b.(bound_outgoing) <= ocs) by (apply align_le; omega).
    (* assert (olink + w <= ocs) by (unfold ocs; omega). *)
    assert (ocs <= size_callee_save_area b ocs) by (apply size_callee_save_area_incr).
    assert (size_callee_save_area b ocs <= ol) by (apply align_le; omega).
    assert (ol + 4 * b.(bound_local) <= ostkdata) by (apply align_le; omega).
    assert (ostkdata + bound_stack_data b <= oretaddr).
    { 
      apply Z.le_trans with (align (ostkdata + bound_stack_data b) w).
      apply align_le. omega.
      subst preretaddr. omega.
    }
    (* Reorder as: *)
  (*    outgoing *)
  (*    callee-save *)
  (*    local *)
  (*    retaddr *)
    rewrite sep_swap12.
    rewrite sep_swap23.
    rewrite sep_swap34.
    rewrite sep_swap23.
    rewrite sep_swap34.
    (* Apply range_split and range_split2 repeatedly *)
    unfold fe_ofs_arg.
    apply range_split_2. fold ocs. omega. omega.
    apply range_split_2. fold ol. omega. omega.
    apply range_drop_right with ostkdata. omega.
    rewrite sep_swap.
    apply range_drop_left with (ostkdata + bound_stack_data b). omega.
    rewrite sep_swap.
    assert (oretaddr + w = fe_size fe) as SZEQ. 
    { 
      subst fe. subst w ocs ol ostkdata preretaddr oretaddr sz. 
      unfold make_env. simpl. omega.
    }
    rewrite SZEQ.
    exact H.
  Qed.


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

Lemma frame_env_range:
  forall b,
  let fe := make_env b in
  0 <= fe_stack_data fe /\ fe_stack_data fe + bound_stack_data b <= fe_size fe.
Proof.
  intros; simpl.
  set (w := if Archi.ptr64 then 8 else 4).
  set (ocs := align (4 * b.(bound_outgoing)) w).
  (* set (ocs := olink + w). *)
  set (ol :=  align (size_callee_save_area b ocs) 8).
  set (ostkdata := align (ol + 4 * b.(bound_local)) 8).
  set (preretaddr := align (ostkdata + b.(bound_stack_data)) w).
  set (sz := align (preretaddr + w) 8).
  set (oretaddr := sz - w).
  assert (preretaddr <= oretaddr) as RET by apply retaddr_le.
  assert (0 < w) by (unfold w; destruct Archi.ptr64; omega).
  generalize b.(bound_local_pos) b.(bound_outgoing_pos) b.(bound_stack_data_pos); intros.
  assert (0 <= 4 * b.(bound_outgoing)) by omega.
  assert (4 * b.(bound_outgoing) <= ocs) by (apply align_le; omega).
  assert (ocs <= size_callee_save_area b ocs) by (apply size_callee_save_area_incr).
  assert (size_callee_save_area b ocs <= ol) by (apply align_le; omega).
  assert (ol + 4 * b.(bound_local) <= ostkdata) by (apply align_le; omega).
  assert (ostkdata + bound_stack_data b <= oretaddr).
  { 
    apply Z.le_trans with (align (ostkdata + bound_stack_data b) w).
    apply align_le. omega.
    subst preretaddr. omega.
  }
  split. omega. subst oretaddr. omega.
Qed.

Lemma w_divides8 :
  let w := if Archi.ptr64 then 8 else 4 in
  (w | 8).
Proof.
  simpl. destr. apply Z.divide_refl.
  apply Zdivide_intro with 2. omega.
Qed.

Lemma frame_env_aligned:
  forall b,
  let fe := make_env b in
     (8 | fe_ofs_arg)
  /\ (8 | fe_ofs_local fe)
  /\ (8 | fe_stack_data fe)
  (* /\ (align_chunk Mptr | fe_ofs_link fe) *)
  /\ (align_chunk Mptr | fe_ofs_retaddr fe).
Proof.
  intros; simpl.
  set (w := if Archi.ptr64 then 8 else 4).
  set (ocs := align (4 * b.(bound_outgoing)) w).
  set (ol :=  align (size_callee_save_area b ocs) 8).
  set (ostkdata := align (ol + 4 * b.(bound_local)) 8).
  set (preretaddr := align (ostkdata + b.(bound_stack_data)) w).
  set (sz := align (preretaddr + w) 8).
  set (oretaddr := sz - w).
  assert (preretaddr <= oretaddr) as RET by apply retaddr_le.
  assert (0 < w) by (unfold w; destruct Archi.ptr64; omega).
  replace (align_chunk Mptr) with w by (rewrite align_chunk_Mptr; auto).
  split. apply Zdivide_0.
  split. apply align_divides; omega.
  split. apply align_divides; omega.
  subst oretaddr. apply Z.divide_sub_r. 
  subst sz. apply Z.divide_trans with 8. apply w_divides8.
  apply align_divides; omega.
  apply Z.divide_refl.
Qed.

Lemma le_add_pos:
  forall a b,
    0 <= b ->
    a <= a + b.
Proof.
  intros; omega.
Qed.

Lemma lt_add_pos:
  forall a b,
    0 < b ->
    a < a + b.
Proof.
  intros; omega.
Qed.


(* fe_ofs_link fe_ofs_retaddr fe_size fe_ofs_local  fe_ofs_arg *)
(*        fe_ofs_callee_save  fe_stack_data. *)
Opaque bound_local bound_outgoing  size_callee_save_area bound_stack_data.

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

Lemma zero_le_align8 : forall x,
  0 <= x -> 0 <= align x 8.
Proof.
  intros.
  eapply Z.le_trans. 
  Focus 2. apply align_le. omega.
  auto.
Qed.

(* Lemma zero_le_alignw : forall x, *)
(*   0 <= x -> 0 <= align x (if Archi.ptr64 then 8 else 4). *)
(* Proof. *)
(*   intros. *)
(*   eapply Z.le_trans.  *)
(*   Focus 2. apply align_le. destr; omega. *)
(*   auto. *)
(* Qed. *)


Program Definition frame_of_frame_env (b: bounds) : frame_info :=
  let fe := make_env b in
  {|
    frame_size := fe_size fe;
    frame_perm := fun o =>
                    if zle (fe_stack_data fe) o && zlt o (fe_stack_data fe + bound_stack_data b)
                    then Public
                    else Private
  |}.
Next Obligation.
  apply zero_le_align8. etransitivity. 2: apply le_add_pos. 2: destr; omega.
  etransitivity. 2: apply align_le. 2: destr; omega.
  etransitivity. 2: apply le_add_pos. 2: generalize (bound_stack_data_pos b); omega.
  etransitivity. 2: apply align_le. 2: omega.
  etransitivity. 2: apply le_add_pos. 2: generalize (bound_local_pos b); omega.
  etransitivity. 2: apply align_le. 2: omega.
  etransitivity. 2: apply size_callee_save_area_incr.
  etransitivity. 2: apply align_le. 2: destr; omega.
  generalize (bound_outgoing_pos b); omega.
Qed.

Lemma stkdata_retaddr_sep:
  forall b,
    let fe := make_env b in
    forall o,
      fe_stack_data fe <= o < fe_stack_data fe + bound_stack_data b ->
      fe_ofs_retaddr fe <= o < fe_ofs_retaddr fe + size_chunk Mptr ->
      False.
Proof.
  clear. intros b fe.
  generalize (frame_env_separated' b).
  intros.
  destruct H. destruct H2. destruct H3. destruct H4. destruct H5.
  set (w := if Archi.ptr64 then 8 else 4) in *.
  set (ocs := align (4 * b.(bound_outgoing)) w) in *.
  set (ol :=  align (size_callee_save_area b ocs) 8) in *.
  set (ostkdata := align (ol + 4 * b.(bound_local)) 8) in *.
  set (preretaddr := align (ostkdata + b.(bound_stack_data)) w) in *.
  set (sz := align (preretaddr + w) 8) in *.
  set (oretaddr := sz - w) in *.
  assert (preretaddr <= oretaddr) as RET by apply retaddr_le.
  subst w ocs ol ostkdata preretaddr sz oretaddr. simpl in *. omega.
Qed.


Lemma arg_retaddr_sep:
  forall b,
    let fe := make_env b in
    forall o,
      fe_ofs_arg <= o < fe_ofs_arg + 4 * bound_outgoing b ->
      fe_ofs_retaddr fe <= o < fe_ofs_retaddr fe + size_chunk Mptr ->
      False.
Proof.
  clear. intros b fe.
  generalize (frame_env_separated' b).
  intros.
  destruct H. destruct H2. destruct H3. destruct H4. destruct H5.
  set (w := if Archi.ptr64 then 8 else 4) in *.
  set (ocs := align (4 * b.(bound_outgoing)) w) in *.
  set (ol :=  align (size_callee_save_area b ocs) 8) in *.
  set (ostkdata := align (ol + 4 * b.(bound_local)) 8) in *.
  set (preretaddr := align (ostkdata + b.(bound_stack_data)) w) in *.
  set (sz := align (preretaddr + w) 8) in *.
  set (oretaddr := sz - w) in *.
  assert (preretaddr <= oretaddr) as RET by apply retaddr_le.
  cut (fe_ofs_arg + 4 * bound_outgoing b <= oretaddr). 
  subst w ocs ol ostkdata preretaddr sz oretaddr. simpl in *. omega.
  eapply Z.le_trans. 2: eauto. 
  unfold preretaddr. 
  unfold fe_ofs_arg. rewrite Z.add_0_l.
  eapply Z.le_trans with ocs. unfold ocs. apply align_le. unfold w; destr; omega.
  eapply Z.le_trans. exact H2. 
  apply Z.le_trans with ol. unfold ol. apply align_le; omega.
  eapply Z.le_trans. apply le_add_pos with (b:= 4* bound_local b).
  generalize (bound_local_pos b); omega.
  apply Z.le_trans with ostkdata; auto.
  eapply Z.le_trans. apply le_add_pos with (b:= bound_stack_data b).
  generalize (bound_stack_data_pos b); omega.
  apply align_le. unfold w; destr; omega.
Qed.

Lemma arg_local_sep:
  forall b,
    let fe := make_env b in
    forall o,
      fe_ofs_arg <= o < fe_ofs_arg + 4 * bound_outgoing b ->
      fe_ofs_local fe <= o < fe_ofs_local fe + 4 * bound_local b ->
      False.
Proof.
  clear. intros b fe.
  generalize (frame_env_separated' b).
  simpl. intuition.
  cut (o<o). omega.
  eapply Z.lt_le_trans. apply H8.
  etransitivity. 2: apply H4.
  etransitivity. 2: apply align_le; try (omega).
  etransitivity. 2: apply size_callee_save_area_incr.
  change fe_ofs_arg with 0.
  rewrite Z.add_0_l.
  apply align_le. destr; omega.
Qed.

Lemma arg_callee_save_sep:
  forall b,
    let fe := make_env b in
    forall o,
      fe_ofs_arg <= o < fe_ofs_arg + 4 * bound_outgoing b ->
      fe_ofs_callee_save fe <= o < size_callee_save_area b (fe_ofs_callee_save fe) ->
      False.
Proof.
  clear. intros b fe.
  generalize (frame_env_separated' b).
  simpl. intuition.
  cut (o<o). omega.
  eapply Z.lt_le_trans. apply H8.
  etransitivity. 2: apply H4.
  change fe_ofs_arg with 0.
  rewrite Z.add_0_l.
  apply align_le. destr; omega.
Qed.

Lemma local_retaddr_sep:
  forall b,
    let fe := make_env b in
    forall o,
      fe_ofs_local fe <= o < fe_ofs_local fe + 4 * bound_local b ->
      fe_ofs_retaddr fe <= o < fe_ofs_retaddr fe + size_chunk Mptr ->
      False.
Proof.
  clear. intros b fe.
  generalize (frame_env_separated' b).
  intros.
  destruct H. destruct H2. destruct H3. destruct H4. destruct H5.
  set (w := if Archi.ptr64 then 8 else 4) in *.
  set (ocs := align (4 * b.(bound_outgoing)) w) in *.
  set (ol :=  align (size_callee_save_area b ocs) 8) in *.
  set (ostkdata := align (ol + 4 * b.(bound_local)) 8) in *.
  set (preretaddr := align (ostkdata + b.(bound_stack_data)) w) in *.
  set (sz := align (preretaddr + w) 8) in *.
  set (oretaddr := sz - w) in *.
  assert (preretaddr <= oretaddr) as RET by apply retaddr_le.
  cut (ol + 4 * bound_local b <= oretaddr). 
  subst w ocs ol ostkdata preretaddr sz oretaddr. simpl in *. omega.
  eapply Z.le_trans. 2: exact RET.
  unfold preretaddr.
  eapply Z.le_trans. eauto.
  eapply Z.le_trans. apply le_add_pos with (b:= bound_stack_data b).
  generalize (bound_stack_data_pos b); omega.
  apply align_le. unfold w; destr; omega.
Qed.

Lemma local_callee_save_sep:
  forall b,
    let fe := make_env b in
    forall o,
      fe_ofs_local fe <= o < fe_ofs_local fe + 4 * bound_local b ->
      fe_ofs_callee_save fe <= o < size_callee_save_area b (fe_ofs_callee_save fe) ->
      False.
Proof.
  clear. intros b fe.
  generalize (frame_env_separated' b).
  simpl. intuition.
Qed.

Lemma stkdata_callee_save_sep:
  forall b,
    let fe := make_env b in
    forall o,
      fe_stack_data fe <= o < fe_stack_data fe + bound_stack_data b ->
      fe_ofs_callee_save fe <= o < size_callee_save_area b (fe_ofs_callee_save fe) ->
      False.
Proof.
  clear. intros b fe.
  generalize (frame_env_separated' b).
  simpl. intuition.
  cut (o < o). omega.
  eapply Z.lt_le_trans.
  apply H9. etransitivity.
  2: apply H7.
  etransitivity. 2: apply align_le ; try omega.
  etransitivity. 2: apply le_add_pos; [ generalize (bound_local_pos b); omega].
  apply align_le. omega.
Qed.

Lemma local_arg_sep:
  forall b,
    let fe := make_env b in
    forall o,
      fe_ofs_local fe <= o < fe_ofs_local fe + 4 * bound_local b ->
      fe_ofs_arg <= o < fe_ofs_arg + 4 * bound_outgoing b ->
      False.
Proof.
  clear. intros b fe.
  generalize (frame_env_separated' b).
  simpl. intuition.
    cut (o < o). omega.
  eapply Z.lt_le_trans.
  apply H9. etransitivity.
  2: apply H7.
  etransitivity. 2: apply align_le ; try omega.
  etransitivity. 2: apply size_callee_save_area_incr.
  change fe_ofs_arg with 0.
  rewrite Z.add_0_l.
  apply align_le. destr; omega.
Qed.

Lemma stkdata_arg_sep:
  forall b,
    let fe := make_env b in
    forall o,
      fe_stack_data fe <= o < fe_stack_data fe + bound_stack_data b ->
      fe_ofs_arg <= o < fe_ofs_arg + 4 * bound_outgoing b ->
      False.
Proof.
  clear. intros b fe.
  generalize (frame_env_separated' b).
  simpl. intuition.
  cut (o < o). omega.
  eapply Z.lt_le_trans.
  apply H9. etransitivity.
  2: apply H7.
  etransitivity. 2: apply align_le ; try omega.
  etransitivity. 2: apply le_add_pos; [ generalize (bound_local_pos b); omega].
  etransitivity. 2: apply align_le ; try omega.
  etransitivity. 2: apply size_callee_save_area_incr.
  change fe_ofs_arg with 0.
  rewrite Z.add_0_l.
  apply align_le. destr; omega.
Qed.

Lemma stkdata_local_sep:
  forall b,
    let fe := make_env b in
    forall o,
      fe_stack_data fe <= o < fe_stack_data fe + bound_stack_data b ->
      fe_ofs_local fe <= o < fe_ofs_local fe + 4 * bound_local b ->
      False.
Proof.
  clear. intros b fe.
  generalize (frame_env_separated' b).
  simpl. intuition.
Qed.

End WITHMEM.
