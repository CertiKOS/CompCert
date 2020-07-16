(* *******************  *)
(* Author: Pierre Wilke  *)
(* Date:   Jan 14, 2020 *)
(* *******************  *)

(** * Decoding of the relocation tables sections *)

Require Import Coqlib Integers AST Maps.
Require Import Asm.
Require Import Errors.
Require Import RelocProgram Encode.
Require Import SeqTable Memdata.
Require Import Hex Bits.
Import Hex Bits.
Import ListNotations.
Require Import TablesEncode.
Require Import ReloctablesEncode.
Require Import Encode ZArith.
Set Implicit Arguments.

Local Open Scope error_monad_scope.
Local Open Scope hex_scope.
Local Open Scope bits_scope.
Local Open Scope Z_scope.

Definition decode_reloctype (z: Z) : res reloctype :=
  match z with
  | 0 => OK reloc_null
  | 1 => OK reloc_abs
  | 2 => OK reloc_rel
  | _ => Error (msg "decode_reloctype: Unexpected value for symbtype")
  end.

Lemma decode_encode_reloctype rt:
  decode_reloctype (encode_reloctype rt) = OK rt.
Proof. destruct rt; reflexivity. Qed.

Definition decode_reloc_info (lb: list byte) : res (reloctype * N) :=
  let z := decode_int32 lb in
  do rt <- decode_reloctype (z mod Z.pow 2 8);
    let symb := z / (Z.pow 2 8) in
    OK (rt, Z.to_N symb).

Lemma encode_reloctype_range:
  forall rt,
    0 <= encode_reloctype rt <= 2.
Proof.
  destruct rt; simpl; omega.
Qed.

Lemma decode_encode_reloc_info rt symb:
  Z.of_N symb < two_p 24 ->
  decode_reloc_info (encode_reloc_info rt symb) = OK (rt, symb).
Proof.
  unfold decode_reloc_info, encode_reloc_info.
  rewrite decode_encode_int32.
  intros.
  rewrite Z.mod_small with (b := two_p (Z.of_nat 32)).
  rewrite Z.add_comm. rewrite Z_mod_plus_full.
  rewrite Z_div_plus_full.
  rewrite Z.div_small. 
  rewrite Z.mod_small.
  rewrite decode_encode_reloctype. simpl.
  f_equal. f_equal.
  apply N2Z.id.
  destruct rt; simpl; vm_compute; intuition congruence.
  destruct rt; simpl; vm_compute; intuition congruence.
  vm_compute; intuition congruence.

  assert (Z.of_N symb * 2 ^ 8 <= two_p 32 - 2 ^ 8).
  {
    transitivity ((two_p 24 - 1) * 2 ^ 8).
    apply Zmult_le_compat_r. omega. apply Z.pow_nonneg. omega.
    rewrite Z.mul_sub_distr_r. simpl. omega.
  }
  generalize (encode_reloctype_range rt). intros.
  split. apply Z.add_nonneg_nonneg. apply Z.mul_nonneg_nonneg. apply N2Z.is_nonneg.
  apply Z.pow_nonneg. omega. omega.
  eapply Z.le_lt_trans.
  apply Z.add_le_mono_r. apply H10.
  simpl Z.of_nat. cut (encode_reloctype rt < 2 ^ 8). omega.
  change (2 ^ 8) with 256. omega.
Qed.

Definition decode_relocentry (l: list byte) : res relocentry :=
  do (ofsbytes, l) <- take_drop 4 l;
    do (infobytes, l) <- take_drop 4 l;
    let ofs := decode_int32 ofsbytes in
    do (rt, sym) <- decode_reloc_info infobytes;
      OK ({| reloc_offset := ofs; reloc_type := rt; reloc_symb := sym; reloc_addend := 0 |}).


(* Record eq_relocentry (e1 e2: relocentry) := *)
(*   { *)
(*     eq_reloc_offset: reloc_offset e1 = reloc_offset e2; *)
(*     eq_reloc_type: reloc_type e1 = reloc_type e2; *)
(*     eq_reloc_symb: reloc_symb e1 = reloc_symb e2; *)
(*   }. *)

Lemma decode_encode_relocentry e (v: valid_relocentry e):
  decode_relocentry (encode_relocentry e) = OK e.
Proof.
  destruct e; simpl.
  unfold decode_relocentry, encode_relocentry.
  Opaque take_drop.
  inv v.
  simpl.
  rewrite take_drop_encode_int. simpl.
  rewrite take_drop_length. simpl.
  rewrite decode_encode_reloc_info. simpl.
  rewrite decode_encode_int32. rewrite Z.mod_small; simpl in *; auto.
  subst. auto. subst. auto. simpl in *; auto.
Qed.

Program Fixpoint decode_reloctable l {measure (length l)} : res (list relocentry) :=
  match l with
    [] => OK []
  | _ => match take_drop 8 l with
         | OK (e, r) =>
           do e <- decode_relocentry e;
             do r <- decode_reloctable r;
             OK (e::r)
         | Error m => Error m
         end
  end.
Next Obligation.
  eapply take_drop_length_2. 2: eauto. omega.
Defined.

Lemma decode_reloctable_eq l:
  decode_reloctable l =
  match l with
    [] => OK []
  | _ => match take_drop 8 l with
         | OK (e, r) =>
           do e <- decode_relocentry e;
             do r <- decode_reloctable r;
             OK (e::r)
         | Error m => Error m
         end
  end.
Proof.
  unfold decode_reloctable. destr. rewrite Wf.fix_sub_eq. simpl. fold decode_reloctable. destr.
  destr.
  intros x f g H.
  destruct x. auto.
  Transparent take_drop.
  destruct x; simpl. auto. 
  destruct x; simpl. auto. 
  destruct x; simpl. auto. 
  destruct x; simpl. auto. 
  destruct x; simpl. auto. 
  destruct x; simpl. auto. 
  destruct x; simpl. auto. 
  unfold bind. destr. rewrite H. auto.
Qed.
Opaque take_drop.

Lemma length_encode_relocentry e:
  length (encode_relocentry e) = 8%nat.
Proof.
  unfold encode_relocentry.
  rewrite app_length. setoid_rewrite encode_int_length.
  reflexivity.
Qed.

Lemma decode_encode_reloctable (t: reloctable) (v: Forall valid_relocentry t):
  decode_reloctable (encode_reloctable t) = OK t.
Proof.
  induction v; simpl.
  - rewrite decode_reloctable_eq. auto.
  - rewrite decode_reloctable_eq.
    rewrite take_drop_length_app.
    destr.
    apply (f_equal (@length _)) in Heql0.
    rewrite app_length in Heql0.
    rewrite length_encode_relocentry in Heql0. simpl in Heql0. omega.
    rewrite decode_encode_relocentry. simpl.
    rewrite IHv. simpl. auto. auto.
    apply length_encode_relocentry.
Qed.

Definition decode_reloctable_section (s: section) : res reloctable :=
  match s with
    sec_bytes bytes => decode_reloctable bytes
  | _ => Error []
  end.

Definition decode_create_reloctable_section t (v: Forall valid_relocentry t):
  decode_reloctable_section (create_reloctable_section t) = OK t.
Proof.
  unfold decode_reloctable_section, create_reloctable_section.
  apply decode_encode_reloctable; auto.
Qed.

Definition decode_reloctables_sections (ls: list section) : res (reloctable * reloctable) :=
  match ls with
    [dsec; csec] =>
    do ds <- decode_reloctable_section dsec;
      do cs <- decode_reloctable_section csec;
      OK (cs, ds)
  | _ => Error nil
  end.

Lemma decode_create_reloctables_sections p:
  Forall valid_relocentry (reloctable_code (prog_reloctables p)) ->
  Forall valid_relocentry (reloctable_data (prog_reloctables p)) ->
  decode_reloctables_sections (create_reloctables_sections p) =
  OK ((reloctable_code (prog_reloctables p)),
      (reloctable_data (prog_reloctables p))).
Proof.
  unfold create_reloctables_sections, decode_reloctables_sections.
  intros.
  repeat rewrite decode_create_reloctable_section; auto.
Qed.

Definition transf_program_inv p : res program :=
  match nth_error (prog_sectable p) (N.to_nat sec_rel_code_id) with
  | Some relcode =>
    match nth_error (prog_sectable p) (N.to_nat sec_rel_data_id) with
    | Some reldata =>
      do rmap <- decode_reloctables_sections [reldata; relcode];
        do (sect, _) <- take_drop 5 (prog_sectable p);
        OK {| prog_defs := prog_defs p;
              prog_public := prog_public p;
              prog_main := prog_main p;
              prog_sectable := sect;
              prog_strtable := (prog_strtable p);
              prog_symbtable := prog_symbtable p;
              prog_reloctables := prog_reloctables p;
              prog_senv := prog_senv p;
           |}
    | None => Error (msg "No reldata section")
    end
  | None => Error (msg "No relcode section")
  end.

Lemma length_create_reloctables_sections m ls:
  create_reloctables_sections m = ls ->
  length ls = 2%nat.
Proof.
  unfold create_reloctables_sections.
  repeat destr. intro A; inv A. reflexivity.
Qed.

(***** Remove Proofs By Chris Start ******)
(* Lemma transf_program_inv_correct p p':
  Forall valid_relocentry (reloctable_code (prog_reloctables p)) ->
  Forall valid_relocentry (reloctable_data (prog_reloctables p)) ->
  transf_program p = OK p' ->
  transf_program_inv p' = OK p.
Proof.
  unfold transf_program, transf_program_inv.
  intros Vdata Vcode TF. repeat destr_in TF. simpl.
  apply beq_nat_true in Heqb.
  rewrite app_length in Heqb. erewrite (length_create_reloctables_sections eq_refl) in Heqb; eauto.
  destruct (prog_sectable p) eqn:?; simpl in *; try congruence.
  destruct s; simpl in *; try congruence.
  destruct s; simpl in *; try congruence.
  destruct s; simpl in *; try congruence.
  destruct s; simpl in *; try congruence.
  destruct s; simpl in *; try congruence.
  2: destruct s; simpl in *; omega.
  rewrite decode_encode_reloctable; auto.
  rewrite decode_encode_reloctable; auto. simpl.
  Transparent take_drop. simpl. f_equal. destruct p; f_equal; simpl in *; auto.
Qed. *)
(***** Remove Proofs By Chris End ******)