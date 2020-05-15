(* *******************  *)


(* *******************  *)

(** * Decoding of the symbol table from a section *)

Require Import Coqlib Integers AST Maps.
Require Import Asm.
Require Import Errors.
Require Import RelocProgram Encode.
Require Import SeqTable Memdata.
Require Import Hex Bits.
Import Hex Bits.
Import ListNotations.
Require Import StrtableEncode.
Require Import SymbtableEncode.

Set Implicit Arguments.

Local Open Scope error_monad_scope.
Local Open Scope hex_scope.
Local Open Scope bits_scope.

Definition decode_symbtype (z: Z) : res symbtype :=
  match z with
  | 0 => OK symb_notype
  | 1 => OK symb_data
  | 2 => OK symb_func
  | _ => Error (msg "decode_symbtype: Unexpected value for symbtype")
  end.

Lemma decode_encode_symbtype st:
  decode_symbtype (encode_symbtype st) = OK st.
Proof.
  destruct st; reflexivity.
Qed.


Definition decode_bindtype (z: Z) : res bindtype :=
  match z with
  | 0 => OK bind_local
  | 1 => OK bind_global
  | _ => Error (msg "decode_bindtype: Unexpected value for bindtype")
  end.

Lemma decode_encode_bindtype bt:
  decode_bindtype (encode_symbbind bt) = OK bt.
Proof.
  destruct bt; reflexivity.
Qed.



Definition decode_glob_symb_info (z: Z) :=
  let st := z mod 16 in
  let bt := z / 16 in
  do st <- decode_symbtype st;
    do bt <- decode_bindtype bt;
    OK (st, bt).

Lemma decode_encode_glob_symb_info st bt :
  decode_glob_symb_info (encode_glob_symb_info bt st) = OK (st, bt).
Proof.
  unfold decode_glob_symb_info, encode_glob_symb_info.
  change (2 ^ 4) with 16.
  rewrite Z.add_comm, Z_mod_plus_full, <- Z.add_comm.
  rewrite Z_div_plus_full_l by omega.
  rewrite Z.div_small, Z.mod_small, Z.add_0_r.
  rewrite decode_encode_symbtype, decode_encode_bindtype. reflexivity.
  destruct st; simpl; omega.
  destruct st; simpl; omega.
Qed.

Definition decode_secindex (lb: list byte) : res secindex :=
  let i := decode_int lb in
  if zeq i (HZ["FFF2"])
  then OK secindex_comm
  else if zeq i 0
       then OK secindex_undef
       else
         OK (secindex_normal (Z.to_N i)).

Definition valid_secindex (i: secindex) :=
  match i with
  | secindex_normal idx => 0 < Z.of_N idx < HZ["FFF2"]
  | secindex_comm => True
  | secindex_undef => True
  end.

Lemma decode_encode_secindex i (V: valid_secindex i):
  decode_secindex (encode_secindex i) = OK i.
Proof.
  unfold decode_secindex, encode_secindex.
  rewrite decode_encode_int.
  destruct i; try reflexivity.
  simpl in V.
  rewrite Z.mod_small. rewrite pred_dec_false. rewrite pred_dec_false.
  rewrite N2Z.id. auto. omega. simpl. omega.
  change (two_p (Z.of_nat 2 * 8)) with 65536. omega.
Qed.
Record valid_symbentry strtab (e: symbentry) : Prop :=
  {
    valid_symbentry_size: 0 <= symbentry_size e < two_p 32;
    valid_symbentry_value: 0 <= symbentry_value e < two_p 32;
    valid_symbentry_id: forall id, symbentry_id e = Some id ->
                                   exists si, strtab ! id  = Some si /\ 0 <= si < two_p 32;
    valid_symbentry_secindex: valid_secindex (symbentry_secindex e);
  }.

(* Record valid_strtable (strtab: strtable) : Prop := *)
(*   { *)
(*     nodupstr: forall i j x y, *)
(*       strtab ! i = Some x -> strtab ! j = Some y -> i <> j -> x <> y; *)
(*     strtab_no_0: *)
(*       forall i : positive, strtab ! i = Some 0 -> False; *)
(*   }. *)


Section WITH_STRTAB.

Variable (strtab: strtable) (strs: list (ident * list byte)).

Hypothesis valid_strtab: StrtableEncode.valid_strtable strs strtab.

Hypothesis no_empty_string: Forall (fun '(_, lb) => lb <> []) strs.

Definition strtab_inv si : option ident :=
  PTree.fold (fun acc id val =>
                match acc with
                | Some _ => acc
                | None =>
                  if zeq val si then Some id else acc
                end
             ) strtab None.

Definition decode_symbentry (lb: list byte) : res symbentry :=
  do (st_name_bytes, lb) <- take_drop 4 lb;
    do (st_value_bytes, lb) <- take_drop 4 lb;
    do (st_size_bytes, lb) <- take_drop 4 lb;
    do (st_info_bytes, lb) <- take_drop 1 lb;
    do (st_other_bytes, lb) <- take_drop 1 lb;
    do (st_shndx_bytes, lb) <- take_drop 2 lb;

    let name_index := decode_int32 st_name_bytes in
    let svalue := decode_int32 st_value_bytes in
    let ssize := decode_int32 st_size_bytes in
    do (st, bt) <- decode_glob_symb_info (decode_int st_info_bytes);
      do secindex <- decode_secindex st_shndx_bytes;
      let sid := strtab_inv name_index in
      OK (
          {|
            symbentry_id := sid;
            symbentry_bind := bt;
            symbentry_type := st;
            symbentry_value := svalue;
            symbentry_secindex := secindex;
            symbentry_size := ssize
          |}
        ).

Lemma fold_left_strtab_inv_stable:
  forall x l i,
  fold_left
    (fun (a : option positive) (p : positive * Z) =>
     match a with
     | Some _ => a
     | None => if zeq (snd p) x then Some (fst p) else a
     end) l (Some i) = Some i.
Proof.
  induction l; simpl; intros; eauto.
Qed.

Lemma length_str_pos:
  forall xx bytesxx,
    Assoc.get_assoc positive (list byte) peq strs xx = Some bytesxx ->
    0 < Z.of_nat (length bytesxx).
Proof.
  intros xx bytesxx GA.
  apply Assoc.get_assoc_in in GA. rewrite Forall_forall in no_empty_string.
  apply no_empty_string in GA. destruct bytesxx. congruence. simpl. 
  reflexivity.
Qed.

Lemma strtab_inv_ok
  : forall i x,
    strtab ! i = Some x ->
    strtab_inv x = Some i.
Proof.
  unfold strtab_inv.
  intros i x EQ.
  apply PTree.elements_correct in EQ.
  rewrite PTree.fold_spec.
  revert EQ.
  assert (list_norepet (map snd (PTree.elements strtab))).
  {

    generalize (PTree.elements_complete strtab).
    generalize (PTree.elements_keys_norepet strtab).
    generalize (PTree.elements strtab).
    induction l; simpl; intros; eauto. constructor.
    constructor.
    - intro IN. rewrite in_map_iff in IN. destruct IN as ((xx & y) & EQ & IN).
      simpl in EQ. subst. inv H.
      destruct a; simpl in *.
      clear IHl.
      generalize (H10 _ _ (or_introl eq_refl)).
      generalize (H10 _ _ (or_intror IN)). intros A B.
      destruct valid_strtab as (o & v & olt).
      edestruct real_string as (bytesxx & Bxx). eauto. apply A.
      edestruct real_string as (bytesp & Bp). eauto. apply B.
      exploit nodupstr. eauto. apply A. apply B. eauto. eauto.
      intro; subst. apply H13. apply in_map_iff. eexists; split; eauto. reflexivity.
      split. 2: eapply length_str_pos; eauto. omega.
      split. 2: eapply length_str_pos; eauto. omega.
      omega. auto.
    - apply IHl. inv H; auto. intros; eauto.
  } revert H.
  generalize (PTree.elements strtab).
  induction l; simpl; intros. easy.
  destruct EQ as [EQ|IN].
  - subst. simpl. rewrite zeq_true.
    apply fold_left_strtab_inv_stable.
  - inv H. rewrite zeq_false. auto. intro; subst. apply H12.
    apply in_map_iff.
    eexists; split. 2: apply IN. reflexivity.
Qed.

Lemma strtab_inv_none
  : forall x,
    (forall i, strtab ! i = Some x -> False) ->
    strtab_inv x = None.
Proof.
  unfold strtab_inv.
  intros x NEQ.
  assert (~ In x (map snd (PTree.elements strtab))).
  {
    intro IN.
    rewrite in_map_iff in IN. destruct IN as (x0 & EQ & IN).
    destruct x0; simpl in *; subst.
    apply PTree.elements_complete in IN. eapply NEQ. eauto.
  } clear NEQ.
  rewrite PTree.fold_spec.
  revert H.
  assert (list_norepet (map snd (PTree.elements strtab))).
  {

    generalize (PTree.elements_complete strtab).
    generalize (PTree.elements_keys_norepet strtab).
    generalize (PTree.elements strtab).
    induction l; simpl; intros; eauto. constructor.
    constructor.
    - intro IN. rewrite in_map_iff in IN. destruct IN as ((xx & y) & EQ & IN).
      simpl in EQ. subst. inv H.
      destruct a; simpl in *.
      clear IHl.
      generalize (H10 _ _ (or_introl eq_refl)).
      generalize (H10 _ _ (or_intror IN)). intros A B.
      destruct valid_strtab as (o & v & olt).
      edestruct real_string as (bytesxx & Bxx). eauto. apply A.
      edestruct real_string as (bytesp & Bp). eauto. apply B.
      exploit nodupstr. eauto. apply A. apply B. eauto. eauto.
      intro; subst. apply H13. apply in_map_iff. eexists; split; eauto. reflexivity.
      split. 2: eapply length_str_pos; eauto. omega.
      split. 2: eapply length_str_pos; eauto. omega.
      omega. auto.
    - apply IHl. inv H; auto. intros; eauto.
  } revert H.
  generalize (PTree.elements strtab).
  induction l; simpl; intros. auto.
  rewrite zeq_false. 2: intuition congruence.
  apply IHl. inv H; auto. intuition.
Qed.

Lemma encode_symbbind_range:
  forall sb,
    0 <= encode_symbbind sb < two_p 4.
Proof.
  unfold encode_symbbind.
  intros; destr; vm_compute; intuition congruence.
Qed.

Lemma encode_symbtype_range:
  forall sb,
    0 <= encode_symbtype sb < two_p 4.
Proof.
  unfold encode_symbtype.
  intros; destr; vm_compute; intuition congruence.
Qed.
Require Import Psatz.
Lemma encode_glob_symb_info_range:
  forall sb st,
    0 <= encode_glob_symb_info sb st < two_p 8.
Proof.
  unfold encode_glob_symb_info.
  intros.
  generalize (encode_symbbind_range sb) (encode_symbtype_range st).
  intros. split. lia.
  change (two_p 8) with (2 ^ 8).
  apply Z.add_nocarry_lt_pow2.
  change (2 ^ 4) with (two_p 4).
  rewrite <- Byte.Zshiftl_mul_two_p.
  apply Byte.equal_same_bits.
  intros. rewrite Byte.Ztestbit_0.
  rewrite Z.land_spec.
  destruct (zlt i 4).
  rewrite Z.shiftl_spec_low. reflexivity. auto.
  apply andb_false_intro2.
  apply Byte.Ztestbit_above with (n:=4%nat).
  change (two_power_nat 4) with (two_p 4); auto. simpl; auto. omega.
  change (2 ^ 8) with (two_p 4 * 2 ^ 4).
  apply Zmult_lt_compat_r. lia. apply H.
  cut (two_p 4 < 2 ^ 8). lia. vm_compute; intuition congruence.
Qed.


Lemma decode_encode_symbentry e (V: valid_symbentry strtab e) lb:
  encode_symbentry strtab e = OK lb ->
  decode_symbentry lb = OK e.
Proof.
  unfold encode_symbentry, decode_symbentry.
  intros A. monadInv A.
  Opaque take_drop.
  rewrite take_drop_encode_int. simpl.
  rewrite take_drop_encode_int. simpl.
  rewrite take_drop_encode_int. simpl.
  rewrite take_drop_cons. simpl.
  rewrite take_drop_cons. simpl.
  rewrite take_drop_length. simpl.
  assert (forall x, [Byte.repr x] = encode_int 1 x).
  {
    clear.
    unfold encode_int. simpl.
    unfold rev_if_be. intros; destr.
  }
  rewrite H.
  rewrite decode_encode_int.
  rewrite Z.mod_small.
  rewrite decode_encode_glob_symb_info. simpl.
  rewrite decode_encode_secindex. simpl.
  rewrite decode_encode_int. rewrite Z.mod_small.
  rewrite decode_encode_int. rewrite Z.mod_small.
  rewrite decode_encode_int. rewrite Z.mod_small.
  f_equal. destruct e; f_equal.
  simpl in *. destr_in EQ. destr_in EQ. inv EQ.
  eapply strtab_inv_ok. auto.
  apply strtab_inv_none. inv EQ. destruct valid_strtab as (o & v & lt).
  eapply strtab_no_0; eauto.
  eapply valid_symbentry_size; eauto.
  eapply valid_symbentry_value; eauto.
  destr_in EQ.
  edestruct valid_symbentry_id as (id & EQid & IN); eauto.
  rewrite EQid in EQ. inv EQ. auto.
  inv EQ.
  split. omega. apply Z.gt_lt. apply two_p_gt_ZERO. omega.
  eapply valid_symbentry_secindex. eauto.
  apply encode_glob_symb_info_range.
  unfold encode_secindex.
  rewrite encode_int_length.
  auto.
Qed.

Program Fixpoint decode_symbentries l {measure (length l)} : res (list symbentry) :=
  match l with
    [] => OK []
  | _ => match take_drop 16 l with
         | OK (e, r) =>
           do e <- decode_symbentry e;
             do r <- decode_symbentries r;
             OK (e::r)
         | Error m => Error m
         end
  end.
Next Obligation.
  eapply take_drop_length_2. 2: eauto. omega.
Defined.

Axiom decode_symbentries_eq: forall l,
  decode_symbentries l =
  match l with
    [] => OK []
  | _ => match take_drop 16 l with
         | OK (e, r) =>
           do e <- decode_symbentry e;
             do r <- decode_symbentries r;
             OK (e::r)
         | Error m => Error m
         end
  end.

Lemma encode_secindex_length i:
  length (encode_secindex i) = 2%nat.
Proof.
  unfold encode_secindex. rewrite encode_int_length. auto.
Qed.

Lemma encode_symbentry_length e l:
  encode_symbentry strtab e = OK l ->
  length l = 16%nat.
Proof.
  unfold encode_symbentry. intro A. monadInv A.
  rewrite ! app_length.
  unfold encode_int32.
  rewrite ! encode_int_length.
  simpl.
  rewrite encode_secindex_length.
  auto.
Qed.

Lemma decode_encode_symtable t (V: Forall (valid_symbentry strtab) t) lb:
  encode_symbtable strtab t = OK lb ->
  decode_symbentries lb = OK t.
Proof.
  unfold encode_symbtable.
  revert lb.
  induction t; simpl; intros; eauto.
  - inv H; auto. 
  - unfold acc_bytes in H. monadInv H.
    rewrite decode_symbentries_eq.
    generalize (encode_symbentry_length _ EQ1). intro L.
    rewrite take_drop_length_app; auto.
    erewrite decode_encode_symbentry. 3: eauto. 2: inv V; auto.
    destr. destruct x0; simpl in *; congruence.
    simpl.
    rewrite IHt. simpl. auto.
    inv V; auto. auto.
Qed.

Definition decode_symtable_section (s: section) : res symbtable :=
  match s with
  | sec_bytes bytes => decode_symbentries bytes
  | _ => Error (msg "decode_symtable_section: should be a bytes section")
  end.

Lemma decode_create_symtable_section t (V: Forall (valid_symbentry strtab) t) s :
  create_symbtable_section strtab t = OK s ->
  decode_symtable_section s = OK t.
Proof.
  intros A. unfold create_symbtable_section in A. monadInv A.
  simpl. eapply decode_encode_symtable; eauto.
Qed.

End WITH_STRTAB.


Definition correct_encoding_symtable_program p : Prop :=
  match nth_error (prog_sectable p) 4 with
  | None => False
  | Some s =>
    match decode_symtable_section (prog_strtable p) s with
    | OK s => prog_symbtable p = s
    | _ => False
    end
  end.

Lemma transf_program_correct p strs
      (STRS : fold_right acc_symbol_strings (OK []) (fold_right acc_symbols [] (prog_symbtable p)) = OK strs)
      (STRS_noempty:   Forall (fun '(_, lb) => lb <> []) strs)
      (V: valid_strtable strs (prog_strtable p))
      (VE: Forall (valid_symbentry (prog_strtable p)) (prog_symbtable p))
      p' (TF: transf_program p = OK p'):
  correct_encoding_symtable_program p'.
Proof.
  unfold transf_program in TF. monadInv TF.
  destr_in EQ0. simpl in *. inv EQ0.
  red. simpl.
  destruct (prog_sectable p); simpl in *; try congruence.
  destruct s0; simpl in *; try congruence.
  destruct s1; simpl in *; try congruence.
  destruct s2; simpl in *; try congruence.
  destruct s3; simpl in *; try congruence.
  erewrite decode_create_symtable_section; eauto.
  apply beq_nat_true in Heqb.
  rewrite app_length in Heqb. simpl in Heqb. omega.
Qed.

Definition transf_program_inv (p: program) : res program :=
  match nth_error (prog_sectable p) 4 with
  | None => Error (msg "Found no section for symtable")
  | Some s =>
    match decode_symtable_section (prog_strtable p) s with
    | OK s =>
      do (sectable,_) <- take_drop 4 (prog_sectable p);
      OK {|
        prog_defs := prog_defs p;
        prog_public := prog_public p;
        prog_main := prog_main p;
        prog_sectable := sectable;
        prog_symbtable := prog_symbtable p;
        prog_strtable := prog_strtable p;
        prog_reloctables := prog_reloctables p;
        prog_senv := prog_senv p |}
    | _ => Error (msg "Unable to decode symtable")
    end
  end.

Theorem transf_program_inv_correct p p' strs
        (STRS : fold_right acc_symbol_strings (OK []) (fold_right acc_symbols [] (prog_symbtable p)) = OK strs)
        (STRS_noempty:   Forall (fun '(_, lb) => lb <> []) strs)
        (V: valid_strtable strs (prog_strtable p))
        (VE: Forall (valid_symbentry (prog_strtable p)) (prog_symbtable p))
        (TP: transf_program p = OK p'):
  transf_program_inv p' = OK p.
Proof.
  unfold transf_program in TP.
  monadInv TP. destr_in EQ0. inv EQ0. simpl in *.
  unfold transf_program_inv. simpl.
  destruct (prog_sectable p) eqn:?; simpl in *; try congruence.
  destruct s0; simpl in *; try congruence.
  destruct s1; simpl in *; try congruence.
  destruct s2; simpl in *; try congruence.
  destruct s3; simpl in *; try congruence.
  erewrite decode_create_symtable_section; eauto.
  f_equal. destruct p; simpl. f_equal; simpl in *. auto.
  apply beq_nat_true in Heqb. rewrite app_length in Heqb; simpl in Heqb. omega.
Qed.

