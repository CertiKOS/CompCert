(* *******************  *)
(* Author: Yuting Wang  *)
(* Date:   Sep 22, 2019 *)
(* *******************  *)

(** * Generation of the relocatable Elf file *)

Require Import Coqlib Integers AST Maps.
Require Import Asm.
Require Import Errors.
Require Import RelocProgram Encode.
Require Import SeqTable Memdata.
Require Import RelocElf.
Require Import ShstrtableEncode.
Require Import Hex Bits.
Require Import SymbtableEncode.
Import Hex Bits.
Import ListNotations.
Require Import RelocProgSemantics3.

Set Implicit Arguments.

Local Open Scope error_monad_scope.
Local Open Scope hex_scope.
Local Open Scope bits_scope.

(* We create a simple ELF file with the following layout
   where every section is aligned at 4 bytes:

   1. ELF Header                                       (52 bytes)
   2. Sections
      -- .data section (global variables)                 
      -- .text section (instructions)                     
      -- .strtab section (string table)
      -- .symtab section (symbol table)                   
      -- .reladata section (relocation of .data)          
      -- .relatext section (relocation of .text)
      -- .shstrtab section (section string table)
   3. Section headers
      -- Null header                      (40 bytes)
      -- header for .data      (40 bytes)
      -- header for .text      (40 bytes)
      -- header for .strtab
      -- header for .symbtab      (40 bytes)
      -- header for .reladata
      -- header for .relatext
      -- header for .shstrtab
 *)


(** ** Generation of ELF header *)

Definition get_sections_size (t: SecTable.t) :=
  fold_left (fun acc sec => sec_size sec + acc) t 0.

Definition get_elf_shoff (p:program) :=
  elf_header_size +
  get_sections_size (prog_sectable p).

  
Definition gen_elf_header (p:program) : elf_header :=
  let sectbl_size := Z.of_nat (SecTable.size (prog_sectable p)) in
  {| e_class        := ELFCLASS32;
     e_encoding     := if Archi.big_endian then ELFDATA2MSB else ELFDATA2LSB;
     e_version      := EV_CURRENT;
     e_type         := ET_REL;
     e_machine      := EM_386;
     e_entry        := 0;
     e_phoff        := 0;
     e_shoff        := get_elf_shoff p;      
     e_flags        := 0;
     e_ehsize       := elf_header_size;
     e_phentsize    := prog_header_size;
     e_phnum        := 0;
     e_shentsize    := sec_header_size;
     e_shnum        := 1 + sectbl_size;      
     e_shstrndx     := Z.of_N sec_shstrtbl_id;
  |}.


Fixpoint list_first_n {A:Type} (n:nat) (l:list A) :=
  match n, l with
  | O, _ => nil
  | S n', (h::t) => h :: (list_first_n n' t)
  | _ , nil =>  nil
  end.

Fixpoint sectable_prefix_size (id:N) t :=
  let l := list_first_n (N.to_nat id) t in
  get_sections_size l.

Lemma unfold_sectable_prefix_size : forall id t,
    sectable_prefix_size id t =   
    get_sections_size (list_first_n (N.to_nat id) t).
Proof.
  induction id. 
  - cbn. auto.
  - cbn. auto.
Qed.

                      
Definition get_sh_offset id (t:sectable) :=
  elf_header_size + (sectable_prefix_size (SecTable.idx id) t).

Definition get_section_size id (t:sectable) :=
  match SecTable.get id t with
  | None => 0
  | Some s => sec_size s
  end.

(** Create section headers *)
Definition gen_rodata_sec_header p :=
  let t := (prog_sectable p) in
  {| sh_name     := rodata_str_ofs;
     sh_type     := SHT_PROGBITS;
     sh_flags    := [SHF_ALLOC];
     sh_addr     := 0;
     sh_offset   := get_sh_offset sec_rodata_id t;
     sh_size     := get_section_size sec_rodata_id t;
     sh_link     := 0;
     sh_info     := 0;
     sh_addralign := 16;
     sh_entsize  := 0;
  |}.

Definition gen_data_sec_header p :=
  let t := (prog_sectable p) in
  {| sh_name     := data_str_ofs;
     sh_type     := SHT_PROGBITS;
     sh_flags    := [SHF_ALLOC; SHF_WRITE];
     sh_addr     := 0;
     sh_offset   := get_sh_offset sec_data_id t;
     sh_size     := get_section_size sec_data_id t;
     sh_link     := 0;
     sh_info     := 0;
     sh_addralign := 1;
     sh_entsize  := 0;
  |}.

Definition gen_text_sec_header p :=
  let t := (prog_sectable p) in
  {| sh_name     := text_str_ofs;
     sh_type     := SHT_PROGBITS;
     sh_flags    := [SHF_ALLOC; SHF_EXECINSTR];
     sh_addr     := 0;
     sh_offset   := get_sh_offset sec_code_id t;
     sh_size     := get_section_size sec_code_id t;
     sh_link     := 0;
     sh_info     := 0;
     sh_addralign := 1;
     sh_entsize  := 0;
  |}.

(** We assume local symbols come before global symbols,
 so one greater than the index of the last local symbol is exactly 
 the size of local symbols*)
Definition one_greater_last_local_symb_index p :=
  let t := (prog_symbtable p) in
  let locals := SymbTable.filter (fun s => match symbentry_bind s with
                                    | bind_local => true
                                    | _ => false
                                    end) t in
  Z.of_nat (1 + length locals).

Definition gen_symtab_sec_header p :=
  let t := (prog_sectable p) in
  {| sh_name     := symtab_str_ofs;
     sh_type     := SHT_SYMTAB;
     sh_flags    := [];
     sh_addr     := 0;
     sh_offset   := get_sh_offset sec_symbtbl_id t;
     sh_size     := get_section_size sec_symbtbl_id t;
     sh_link     := Z.of_N sec_strtbl_id;
     sh_info     := one_greater_last_local_symb_index p;
     sh_addralign := 1;
     sh_entsize  := symb_entry_size;
  |}.

Definition gen_relrodata_sec_header p :=
  let t := (prog_sectable p) in
  {| sh_name     := relarodata_str_ofs;
     sh_type     := SHT_REL;
     sh_flags    := [];
     sh_addr     := 0;
     sh_offset   := get_sh_offset sec_rel_rodata_id t;
     sh_size     := get_section_size sec_rel_rodata_id t;
     sh_link     := Z.of_N sec_symbtbl_id;
     sh_info     := Z.of_N sec_rodata_id;
     sh_addralign := 1;
     sh_entsize  := reloc_entry_size;
  |}.

Definition gen_reldata_sec_header p :=
  let t := (prog_sectable p) in
  {| sh_name     := reladata_str_ofs;
     sh_type     := SHT_REL;
     sh_flags    := [];
     sh_addr     := 0;
     sh_offset   := get_sh_offset sec_rel_data_id t;
     sh_size     := get_section_size sec_rel_data_id t;
     sh_link     := Z.of_N sec_symbtbl_id;
     sh_info     := Z.of_N sec_data_id;
     sh_addralign := 1;
     sh_entsize  := reloc_entry_size;
  |}.

Definition gen_reltext_sec_header p :=
  let t := (prog_sectable p) in
  {| sh_name     := relatext_str_ofs;
     sh_type     := SHT_REL;
     sh_flags    := [];
     sh_addr     := 0;
     sh_offset   := get_sh_offset sec_rel_code_id t;
     sh_size     := get_section_size sec_rel_code_id t;
     sh_link     := Z.of_N sec_symbtbl_id;
     sh_info     := Z.of_N sec_code_id;
     sh_addralign := 1;
     sh_entsize  := reloc_entry_size;
  |}.

Definition gen_shstrtab_sec_header p :=
  let t := (prog_sectable p) in
  {| sh_name     := shstrtab_str_ofs;
     sh_type     := SHT_STRTAB;
     sh_flags    := [];
     sh_addr     := 0;
     sh_offset   := get_sh_offset sec_shstrtbl_id t;
     sh_size     := get_section_size sec_shstrtbl_id t;
     sh_link     := 0;
     sh_info     := 0;
     sh_addralign := 1;
     sh_entsize  := 0;
  |}.

Definition gen_strtab_sec_header p :=
  let t := (prog_sectable p) in
  {| sh_name     := strtab_str_ofs;
     sh_type     := SHT_STRTAB;
     sh_flags    := [];
     sh_addr     := 0;
     sh_offset   := get_sh_offset sec_strtbl_id t;
     sh_size     := get_section_size sec_strtbl_id t;
     sh_link     := 0;
     sh_info     := 0;
     sh_addralign := 1;
     sh_entsize  := 0;
  |}.


(** Generation of the Elf file *)

Definition transl_section (sec: RelocProgram.section) : res section :=
  match sec with
  | sec_bytes bs => OK bs
  | _ => Error (msg "Section has not been encoded into bytes")
  end.

Definition acc_sections sec r :=
  do r' <- r;
  do sec' <- transl_section sec;
  OK (sec' :: r').

Definition gen_sections (t:sectable) : res (list section) :=
  fold_right acc_sections (OK []) t.

Definition gen_reloc_elf (p:program) : res elf_file :=
  do secs <- gen_sections (prog_sectable p);
  do _ <- RelocProgSemantics3.decode_tables p;
    if (beq_nat (length secs) 9) then
      if zlt (get_elf_shoff p) (two_p 32)
      then 
        let headers := [null_section_header;
                       gen_rodata_sec_header p;
                       gen_data_sec_header p;
                       gen_text_sec_header p;
                       gen_strtab_sec_header p;
                       gen_symtab_sec_header p;
                       gen_relrodata_sec_header p;
                       gen_reldata_sec_header p;
                       gen_reltext_sec_header p;
                       gen_shstrtab_sec_header p] in
        OK {| prog_defs     := RelocProgram.prog_defs p;
              prog_public   := RelocProgram.prog_public p;
              prog_main     := RelocProgram.prog_main p;
              prog_senv     := RelocProgram.prog_senv p;
              elf_head      := gen_elf_header p;
              elf_sections  := secs;
              elf_section_headers := headers;
           |}
      else
        Error (msg "Sections too big (get_elf_shoff above bounds)")
    else
      Error [MSG "Number of sections is incorrect (not 9: "; POS (Pos.of_nat (length secs))].

Require Import Lia.

(* Lemma gen_elf_header_valid p:
  0 <= get_elf_shoff p < two_p 32 ->
  length (prog_sectable p) = 7%nat ->
  valid_elf_header (gen_elf_header p).
Proof.
  unfold gen_elf_header. intros.
  constructor; simpl.
  vm_compute; intuition try congruence.
  vm_compute; intuition try congruence.
  auto.
  vm_compute; intuition try congruence.
  vm_compute; intuition try congruence.
  vm_compute; intuition try congruence.
  vm_compute; intuition try congruence.
  vm_compute; intuition try congruence.
  setoid_rewrite H10.
  vm_compute; intuition try congruence.
  vm_compute; intuition try congruence.
Qed.

Lemma sec_size_pos a:
  0 <= sec_size a.
Proof.
  destruct a; simpl. generalize (code_size_non_neg code); omega.
  generalize (init_data_list_size_pos init). omega.
  omega.
Qed.

Lemma fold_sec_size_range: forall l,
    0 <= fold_right (fun (y : RelocProgram.section) (x : Z) => sec_size y + x) 0 l.
Proof.
  induction l; simpl; intros; eauto. omega.
  apply Z.add_nonneg_nonneg. apply sec_size_pos. auto.
Qed.

Lemma get_sections_size_pos t:
  0 <= get_sections_size t.
Proof.
  unfold get_sections_size.
  intros. rewrite <- fold_left_rev_right.
  apply fold_sec_size_range.
Qed.

Lemma sectable_prefix_size_pos: forall id stbl, 
    0 <= sectable_prefix_size id stbl.
Proof.
  intros. rewrite unfold_sectable_prefix_size.
  apply get_sections_size_pos.
Qed.

Lemma get_elf_shoff_pos p:
  0 <= get_elf_shoff p.
Proof.
  unfold get_elf_shoff.
  apply Z.add_nonneg_nonneg. vm_compute; intuition congruence.
  apply get_sections_size_pos.
Qed.

Lemma gen_sections_length t x (G: gen_sections t = OK x):
  (length x) = length t.
Proof.
  unfold gen_sections in G. 
  revert t x G. clear.
  induction t; simpl; intros; eauto.
  inv G. reflexivity.
  unfold acc_sections in G at 1. monadInv G. apply IHt in EQ. simpl in EQ. inv EQ.
  reflexivity.
Qed.

Lemma list_first_n_prefix:
  forall n {A} (l: list A),
  exists l2, l = list_first_n n l ++ l2.
Proof.
  induction n; simpl; intros; eauto.
  destruct l. simpl. eauto. simpl.
  edestruct (IHn A0 l) as (l2 & EQ).
  eexists. f_equal. eauto.
Qed.

Lemma fold_left_size_acc: forall b acc,
    fold_left (fun (acc : Z) (sec : RelocProgram.section) => sec_size sec + acc) b acc =
    acc + fold_left (fun (acc : Z) (sec : RelocProgram.section) => sec_size sec + acc) b 0.
Proof.
  induction b; simpl; intros; eauto.
  omega.
  rewrite (IHb (sec_size a + acc)).
  rewrite (IHb (sec_size a + 0)). omega.
Qed.

Lemma fold_left_le: forall b acc,
    acc <= fold_left (fun (acc : Z) (sec : RelocProgram.section) => sec_size sec + acc) b acc.
Proof.
  induction b; simpl; intros; eauto.
  omega.
  rewrite fold_left_size_acc. specialize (IHb 0).
  generalize (sec_size_pos a). omega.
Qed.

Lemma get_sections_size_app a b:
  get_sections_size (a ++ b) = get_sections_size a + get_sections_size b.
Proof.
  unfold get_sections_size. rewrite fold_left_app.
  rewrite fold_left_size_acc. auto.
Qed.

Lemma get_sh_offset_range p id
      (l : get_elf_shoff p < two_p 32):
  0 <= get_sh_offset id (prog_sectable p) < two_power_pos 32.
Proof.
  unfold get_elf_shoff, get_sh_offset in *.
  set (id' := SecTable.idx id).
  split.
  apply Z.add_nonneg_nonneg. vm_compute; intuition congruence.
  clear. induction id; simpl. vm_compute. congruence.
  apply sectable_prefix_size_pos.
  eapply Z.le_lt_trans. 2: eauto.
  apply Z.add_le_mono_l.
  generalize (prog_sectable p). clear.
  induction id; intros.
  apply get_sections_size_pos.
  rewrite unfold_sectable_prefix_size. 
  destruct (list_first_n_prefix (N.to_nat id') s) as (l2 & EQ).
  rewrite EQ at 2.
  rewrite get_sections_size_app.
  generalize (get_sections_size_pos l2); omega.
Qed.

Lemma get_section_size_range p id
      (l : get_elf_shoff p < two_p 32):
  0 <= get_section_size id (prog_sectable p) < two_power_pos 32.
Proof.
  unfold get_elf_shoff in *.
  split.
  unfold get_section_size. destr. apply sec_size_pos. omega.
  eapply Z.le_lt_trans. 2: eauto.
  cut (get_section_size id (prog_sectable p) <= get_sections_size (prog_sectable p)).
  cut (0 <= elf_header_size). intros; omega. vm_compute; congruence.
  generalize (prog_sectable p). clear. Opaque Z.add.
  unfold get_section_size, SecTable.get. generalize (N.to_nat (SecTable.idx id)). clear.
  unfold get_sections_size.
  induction n; destruct s; simpl; intros; eauto. omega.
  etransitivity. 2: apply fold_left_le. omega. omega.
  etransitivity. apply IHn.
  rewrite fold_left_size_acc with (acc:=sec_size v + 0) .
  generalize (sec_size_pos v). omega.
Qed.

Lemma get_sections_size_in t x:
  In x t ->
  sec_size x <= get_sections_size t.
Proof.
  revert x.
  unfold get_sections_size.
  induction t; simpl; intros; eauto.
  easy.
  destruct H.
  - subst; simpl.
    etransitivity. 2: apply fold_left_le. omega.
  - etransitivity. eapply IHt. auto.
    rewrite (fold_left_size_acc t (sec_size a + 0)).
    generalize (sec_size_pos a); omega.
Qed.

Lemma dummy_symbentry_length: length encode_dummy_symbentry = 16%nat.
Proof.
  unfold encode_dummy_symbentry. cbn.
  repeat rewrite app_length.
  repeat (setoid_rewrite encode_int_length; simpl).
  auto.
Qed.
  
Lemma create_symbtable_section_length p symt
      (EQ : create_symbtable_section (prog_strtable p) (prog_symbtable p) = OK symt):
  sec_size symt = 16 * Z.of_nat (1 + length (prog_symbtable p)).
Proof.
  Opaque Z.mul.
  unfold create_symbtable_section in EQ. monadInv EQ. simpl.
  unfold encode_symbtable in EQ0. 
  rewrite app_length. rewrite dummy_symbentry_length.
  revert x EQ0.
  generalize (prog_strtable p).
  generalize (prog_symbtable p).
  induction s; intros; eauto. inv EQ0. reflexivity.
  simpl in EQ0. unfold acc_bytes at 1 in EQ0. monadInv EQ0.
  eapply IHs in EQ.
  repeat rewrite app_length.
  assert (length x1 = 16%nat).
  {
    clear - EQ0.
    unfold encode_symbentry in EQ0. monadInv EQ0.
    repeat rewrite app_length.
    repeat (setoid_rewrite encode_int_length; simpl).
    auto.
  }
  rewrite H.
  simpl length.
  rewrite Nat2Z.inj_add. rewrite EQ. lia.
Qed.

Lemma length_filter {A} (l: list A) f:
  (length (filter f l) <= length l)%nat.
Proof.
  induction l; simpl; intros; eauto.
  destr; simpl; omega.
Qed.

Lemma one_greater_last_local_symb_range p symt
      (EQ: create_symbtable_section (prog_strtable p) (prog_symbtable p) = OK symt)
      (IN:  In symt (prog_sectable p))
      (l : get_elf_shoff p < two_p 32):
  0 <= one_greater_last_local_symb_index p < two_power_pos 32.
Proof.
  unfold one_greater_last_local_symb_index.
  split. omega.
  eapply Z.le_lt_trans. 2: apply l. clear l.
  unfold get_elf_shoff.
  transitivity (get_sections_size (prog_sectable p)).
  2: change elf_header_size with 52; omega.
  etransitivity. 2: apply get_sections_size_in; eauto.
  erewrite create_symbtable_section_length; eauto.
  change 16 with (Z.of_nat 16).
  rewrite <- Nat2Z.inj_mul.
  apply Nat2Z.inj_le.
  transitivity (S (length (prog_symbtable p))).
  cbn. apply le_n_S.
  apply length_filter.
  lia.
Qed.

Lemma gen_reloc_elf_valid p ef (GRE: gen_reloc_elf p = OK ef)
      symt
      (SYMT: create_symbtable_section (prog_strtable p) (prog_symbtable p) = OK symt)
      (* (HD: hd sec_null (prog_sectable p) = sec_null) *)
      (INSYMT: In symt (prog_sectable p)):
  valid_elf_file ef.
Proof.
  unfold gen_reloc_elf in GRE.
  monadInv GRE.
  repeat destr_in EQ2.
  Opaque Z.add Z.eqb check_sizes.
  constructor; simpl.
  - apply gen_elf_header_valid. split; auto.
    apply get_elf_shoff_pos.
    apply Nat.eqb_eq in Heqb.
    erewrite <- gen_sections_length; eauto.
  - constructor.
    constructor; simpl; vm_compute; try intuition congruence. constructor.
    constructor.
    constructor; simpl.
    vm_compute; try intuition congruence.
    vm_compute; try intuition congruence.
    apply get_sh_offset_range; auto.
    apply get_section_size_range; auto.
    vm_compute; try intuition congruence.
    vm_compute; try intuition congruence.
    vm_compute; try intuition congruence.
    vm_compute; try intuition congruence.
    constructor.
    constructor.
    constructor; simpl.
    vm_compute; try intuition congruence.
    vm_compute; try intuition congruence.
    apply get_sh_offset_range; auto.
    apply get_section_size_range; auto.
    vm_compute; try intuition congruence.
    vm_compute; try intuition congruence.
    vm_compute; try intuition congruence.
    vm_compute; try intuition congruence.
    constructor.
        constructor.
    constructor; simpl.
    vm_compute; try intuition congruence.
    vm_compute; try intuition congruence.
    apply get_sh_offset_range; auto.
    apply get_section_size_range; auto.
    vm_compute; try intuition congruence.
    vm_compute; try intuition congruence.
    vm_compute; try intuition congruence.
    vm_compute; try intuition congruence.
    constructor.
        constructor.
    constructor; simpl.
    vm_compute; try intuition congruence.
    vm_compute; try intuition congruence.
    apply get_sh_offset_range; auto.
    apply get_section_size_range; auto.
    vm_compute; try intuition congruence.
    eapply one_greater_last_local_symb_range; eauto.
    vm_compute; try intuition congruence.
    vm_compute; try intuition congruence.
    constructor.
        constructor.
    constructor; simpl.
    vm_compute; try intuition congruence.
    vm_compute; try intuition congruence.
    apply get_sh_offset_range; auto.
    apply get_section_size_range; auto.
    vm_compute; try intuition congruence.
    vm_compute; try intuition congruence.
    vm_compute; try intuition congruence.
    vm_compute; try intuition congruence.
    constructor.
        constructor.
    constructor; simpl.
    vm_compute; try intuition congruence.
    vm_compute; try intuition congruence.
    apply get_sh_offset_range; auto.
    apply get_section_size_range; auto.
    vm_compute; try intuition congruence.
    vm_compute; try intuition congruence.
    vm_compute; try intuition congruence.
    vm_compute; try intuition congruence.
    constructor.
        constructor.
    constructor; simpl.
    vm_compute; try intuition congruence.
    vm_compute; try intuition congruence.
    apply get_sh_offset_range; auto.
    apply get_section_size_range; auto.
    vm_compute; try intuition congruence.
    vm_compute; try intuition congruence.
    vm_compute; try intuition congruence.
    vm_compute; try intuition congruence.
    constructor.
    constructor.
  - unfold get_elf_shoff.
    f_equal.
    clear -EQ. revert x EQ. generalize (prog_sectable p).
    unfold gen_sections, get_sections_size.
    intro s. intros; subst. simpl. 
    revert s x EQ. clear.
    induction s; simpl; intros; eauto.
    + inv EQ. reflexivity.
    + unfold acc_sections at 1 in EQ. monadInv EQ.
      apply IHs in EQ0.
      simpl.
      rewrite <- EQ0.
      rewrite fold_left_size_acc.
      cut (Z.of_nat (length x1) = sec_size a). omega. clear - EQ.
      unfold transl_section in EQ. destr_in EQ. inv EQ. simpl. auto.
  - apply gen_sections_length in EQ. setoid_rewrite <- EQ.
    apply Nat.eqb_eq in Heqb.
    rewrite Heqb. reflexivity.
  - Transparent check_sizes.
    exploit gen_sections_length; eauto.
    unfold gen_sections in EQ. destr_in EQ.
    apply Nat.eqb_eq in Heqb.
    rewrite Heqb. simpl length. intro A; inv A.
    destruct (prog_sectable p) eqn:Heqs; simpl in H11; try congruence.
    destruct s; simpl in H11; try congruence.
    destruct s; simpl in H11; try congruence.
    destruct s; simpl in H11; try congruence.
    destruct s; simpl in H11; try congruence.
    destruct s; simpl in H11; try congruence.
    destruct s; simpl in H11; try congruence.
    destruct s; simpl in H11; try congruence.
    simpl in H10. monadInv H10.
    monadInv EQ.
    monadInv EQ0.
    monadInv EQ3.
    monadInv EQ4.
    monadInv EQ5.
    monadInv EQ6.
    cbn.
    rewrite Heqs.
    unfold check_sizes.
    unfold get_section_size, get_sh_offset, SecTable.get. simpl. 
    repeat match goal with
             H: transl_section ?s = OK ?x |- _ =>
             unfold transl_section in H; repeat destr_in H
           end. simpl.
    rewrite ! Z.eqb_refl.
    unfold get_sections_size. simpl.
    change elf_header_size with 52.
    rewrite !  (proj2 (Z.eqb_eq _ _)) by omega; auto.
  - reflexivity.
Qed. *)
