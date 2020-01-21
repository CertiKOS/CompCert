(* Decoding of Relocatable Elf Files *)
(* Author        : Pierre Wilke *)
(* Date Created  : Jan 20, 2020 *)

Require Import Coqlib Integers Maps.
Require Import Errors.
Require Import Encode.
Require Import Memdata.
Require Import RelocElf.
Require Import Asm.
Require Import Hex.
Require Import EncodeRelocElf.
Import Hex.
Import ListNotations.
Require Import Encode.

Set Implicit Arguments.
Set Asymmetric Patterns.

Local Open Scope error_monad_scope.
Local Open Scope hex_scope.
Local Open Scope string_byte_scope.

(** * Encoding of the relocatble ELF files into bytes *)

Notation " 'check' A ; B" := (if A then B else Error nil) (at level 100).


Definition decode_elf_file_class (b: byte) : res elf_file_class :=
  match Byte.unsigned b with
  | 0 => OK ELFCLASSNONE
  | 1 => OK ELFCLASS32
  | 2 => OK ELFCLASS64
  | _ => Error (msg "Unexpected elf file class")
  end.

Lemma decode_encode_elf_file_class efc :
  decode_elf_file_class (elf_class_to_byte efc) = OK efc.
Proof.
  destruct efc; reflexivity.
Qed.


Definition decode_elf_data (b: byte) : res elf_data :=
  match Byte.unsigned b with
  | 0 => OK ELFDATANONE
  | 1 => OK ELFDATA2LSB
  | 2 => OK ELFDATA2MSB
  | _ => Error (msg "Unexpected elf data")
  end.

Lemma decode_encode_elf_data ed :
  decode_elf_data (elf_data_to_byte ed) = OK ed.
Proof.
  destruct ed; reflexivity.
Qed.

Definition decode_elf_version (b: byte) : res elf_version :=
  match Byte.unsigned b with
  | 0 => OK EV_NONE
  | 1 => OK EV_CURRENT
  | _ => Error (msg "Unexpected elf version")
  end.

Lemma decode_encode_elf_version v :
  decode_elf_version (elf_version_to_byte v) = OK v.
Proof.
  destruct v; reflexivity.
Qed.


Definition decode_elf_version32 (b: list byte) : res elf_version :=
  match decode_int b with
  | 0 => OK EV_NONE
  | 1 => OK EV_CURRENT
  | _ => Error (msg "Unexpected elf version")
  end.

Lemma decode_encode_elf_version32 v :
  decode_elf_version32 (encode_int32 (elf_version_value v)) = OK v.
Proof.
  destruct v; reflexivity.
Qed.

Definition decode_e_ident (l: list byte) : res (elf_file_class * elf_data * elf_version) :=
  match l with
    b7f::be::bl::bf::bclass::bencoding::bversion::l =>
    check (Byte.eq b7f HB["7F"]);
      check (Byte.eq be CB["E"]);
      check (Byte.eq bl CB["L"]);
      check (Byte.eq bf CB["F"]);
      do cl <- decode_elf_file_class bclass;
      do enc <- decode_elf_data bencoding;
      do v <- decode_elf_version bversion;
      check (Nat.eqb (List.length l) 9);
      check (forallb (Byte.eq Byte.zero) l);
      OK (cl, enc, v)
  | _ => Error nil
  end.

Lemma decode_encode_e_ident eh:
  decode_e_ident (encode_e_ident eh) = OK (e_class eh, e_encoding eh, e_version eh).
Proof.
  simpl.
  repeat rewrite Byte.eq_true.
  rewrite decode_encode_elf_file_class, decode_encode_elf_data, decode_encode_elf_version.
  reflexivity.
Qed.

Definition decode_elf_file_type (l: list byte) : res elf_file_type :=
  check (Nat.eqb (List.length l) 2);
    check (Z.eqb (decode_int l) 1);
    OK ET_REL.
Lemma decode_encode_elf_file_type eft:
  decode_elf_file_type (encode_elf_file_type eft) = OK eft.
Proof.
  unfold encode_elf_file_type, decode_elf_file_type.
  rewrite encode_int_length. simpl.
  rewrite decode_encode_int.
  simpl. destruct eft. simpl. auto.
Qed.


Definition decode_elf_machine (l: list byte) : res elf_machine :=
  check (Nat.eqb (List.length l) 2);
    check (Z.eqb (decode_int l) 3);
    OK EM_386.

Lemma decode_encode_elf_machine em:
  decode_elf_machine (encode_elf_machine em) = OK em.
Proof.
  unfold encode_elf_machine, decode_elf_machine.
  rewrite encode_int_length. simpl.
  rewrite decode_encode_int.
  simpl. destruct em. simpl. auto.
Qed.

Definition decode_elf_header (l: list byte) : res elf_header :=
  do (eident,l) <- take_drop 16 l;
    do (eft,l) <- take_drop 2 l;
    do (em, l) <- take_drop 2 l;
    do (ev, l) <- take_drop 4 l;
    do (entry, l) <- take_drop 4 l;
    do (phoff, l) <- take_drop 4 l;
    do (shoff, l) <- take_drop 4 l;
    do (flags, l) <- take_drop 4 l;
    do (ehsize, l) <- take_drop 2 l;
    do (phentsize, l) <- take_drop 2 l;
    do (phnum, l) <- take_drop 2 l;
    do (shentsize, l) <- take_drop 2 l;
    do (shnum, l) <- take_drop 2 l;
    do (shstrndx, l) <- take_drop 2 l;
    check (Nat.eqb (length l) O);
    do eident <- decode_e_ident eident;
    let '(eclass, eenc, ever) := eident in
    do eft <- decode_elf_file_type eft;
    do em <- decode_elf_machine em;
    do ev <- decode_elf_version32 ev;
    let entry := decode_int entry in
    let phoff := decode_int phoff in
    let shoff := decode_int shoff in
    let flags := decode_int flags in
    let ehsize := decode_int ehsize in
    let phentsize := decode_int phentsize in
    let phnum := decode_int phnum in
    let shentsize := decode_int shentsize in
    let shnum := decode_int shnum in
    let shstrndx := decode_int shstrndx in
    OK {|
        e_class := eclass;
        e_encoding := eenc;
        e_version := ever;
        e_type := eft;
        e_machine := em;
        e_entry := entry;
        e_phoff := phoff;
        e_shoff := shoff;
        e_flags := flags;
        e_ehsize := ehsize;
        e_phentsize := phentsize;
        e_phnum := phnum;
        e_shentsize := shentsize;
        e_shnum := shnum;
        e_shstrndx := shstrndx;
      |}.

Record valid_elf_header (eh: elf_header) :=
  {
    valid_entry: 0 <= e_entry eh < two_p 32;
    valid_phoff: 0 <= e_phoff eh < two_p 32;
    valid_shoff: 0 <= e_shoff eh < two_p 32;
    valid_flags: 0 <= e_flags eh < two_p 32;
    valid_ehsize: 0 <= e_ehsize eh < two_p 16;
    valid_phentsize: 0 <= e_phentsize eh < two_p 16;
    valid_phnum: 0 <= e_phnum eh < two_p 16;
    valid_shentsize: 0 <= e_shentsize eh < two_p 16;
    valid_shnum: 0 <= e_shnum eh < two_p 16;
    valid_shstrndx: 0 <= e_shstrndx eh < two_p 16;
  }.

Lemma decode_encode_int_small:
  forall n x,
    0 <= x < two_p (Z.of_nat n * 8) ->
    decode_int (encode_int n x) = x.
Proof.
  intros.
  rewrite decode_encode_int.
  rewrite Z.mod_small; auto.
Qed.

Lemma decode_encode_elf_header eh (V: valid_elf_header eh):
  decode_elf_header (encode_elf_header eh) = OK eh.
Proof.
  unfold encode_elf_header, decode_elf_header.
  Local Opaque take_drop.
  rewrite take_drop_length_app by reflexivity.
  Local Opaque encode_e_ident decode_e_ident.
  simpl.
  repeat (rewrite take_drop_length_app by reflexivity; simpl).
  rewrite take_drop_length by reflexivity. simpl.
  rewrite decode_encode_e_ident. simpl.
  rewrite decode_encode_elf_file_type.
  rewrite decode_encode_elf_machine.
  rewrite decode_encode_elf_version32. simpl.
  inv V.
  unfold encode_int32, encode_int16.
  repeat (rewrite decode_encode_int_small by auto).
  f_equal. clear. destruct eh; reflexivity.
Qed.

Definition decode_section_type (l: list byte) :=
  let z := decode_int l in
  match z with
  | 0 => OK SHT_NULL
  | 1 => OK SHT_PROGBITS
  | 2 => OK SHT_SYMTAB
  | 3 => OK SHT_STRTAB
  | 4 => OK SHT_RELA
  | 8 => OK SHT_NOBITS
  | 9 => OK SHT_REL
  | _ => Error (msg "Unrecognized section type")
  end.

Lemma decode_encode_section_type t:
  decode_section_type (encode_section_type t) = OK t.
Proof.
  destruct t; reflexivity.
Qed.

Inductive valid_section_flags : list section_flag -> Prop :=
| vsf_nil : valid_section_flags []
| vsf_alloc_write : valid_section_flags [SHF_ALLOC; SHF_WRITE]
| vsf_alloc_exec : valid_section_flags [SHF_ALLOC; SHF_EXECINSTR].

Definition decode_section_flags (l: list byte) : list section_flag :=
  let z := decode_int l in
  (if Z.testbit z 1 then [SHF_ALLOC] else [])
    ++ (if Z.testbit z 0 then [SHF_WRITE] else [])
    ++ (if Z.testbit z 2 then [SHF_EXECINSTR] else []).

Lemma decode_encode_section_flags sf (V: valid_section_flags sf):
  decode_section_flags (encode_section_flags sf) = sf.
Proof.
  inv V; reflexivity.
Qed.

Definition decode_section_header (l: list byte) : res section_header :=
  do (name, l) <- take_drop 4 l;
    do (sect, l) <- take_drop 4 l;
    do (flags, l) <- take_drop 4 l;
    do (addr, l) <- take_drop 4 l;
    do (ofs, l) <- take_drop 4 l;
    do (size, l) <- take_drop 4 l;
    do (link, l) <- take_drop 4 l;
    do (info, l) <- take_drop 4 l;
    do (addralign, l) <- take_drop 4 l;
    do (entsize, l) <- take_drop 4 l;
    do sect <- decode_section_type sect;
    let flags := decode_section_flags flags in
    OK {|
        sh_name := decode_int name;
        sh_type := sect;
        sh_flags := flags;
        sh_addr := decode_int addr;
        sh_offset := decode_int ofs;
        sh_size := decode_int size;
        sh_link := decode_int link;
        sh_info := decode_int info;
        sh_addralign := decode_int addralign;
        sh_entsize := decode_int entsize;
      |}.

Record valid_section_header sh :=
  {
    vsh_name: 0 <= sh_name sh < two_p 32;
    vsh_addr: 0 <= sh_addr sh < two_p 32;
    vsh_offset: 0 <= sh_offset sh < two_p 32;
    vsh_size: 0 <= sh_size sh < two_p 32;
    vsh_link: 0 <= sh_link sh < two_p 32;
    vsh_info: 0 <= sh_info sh < two_p 32;
    vsh_addralign: 0 <= sh_addralign sh < two_p 32;
    vsh_entsize: 0 <= sh_entsize sh < two_p 32;
    vsh_flags: valid_section_flags (sh_flags sh);
  }.

Lemma decode_encode_section_header sh (V: valid_section_header sh) :
  decode_section_header (encode_section_header sh) = OK sh.
Proof.
  unfold decode_section_header, encode_section_header.
  repeat (rewrite take_drop_length_app by reflexivity; simpl).
  rewrite take_drop_length by reflexivity. simpl.
  rewrite decode_encode_section_type. simpl.
  unfold encode_int32.
  inv V.
  repeat rewrite decode_encode_int_small by auto.
  rewrite decode_encode_section_flags by auto.
  destruct sh; reflexivity.
Qed.

Fixpoint decode_section_headers' (n: nat) (l: list byte) : res (list section_header) :=
  match n with
  | O => OK []
  | S n =>
    do (sh, l) <- take_drop 40 l;
      do sh <- decode_section_header sh;
      do shs <- decode_section_headers' n l;
      OK (sh::shs)
  end.

Definition decode_section_headers (eh: elf_header) (whole_file: list byte) : res (list section_header) :=
  do (_,l) <- take_drop (Z.to_nat (e_shoff eh)) whole_file;
    decode_section_headers' (Z.to_nat (e_shnum eh)) l.

Lemma decode_encode_section_headers (shs: list section_header) (V: Forall valid_section_header shs):
  decode_section_headers' (length shs) (encode_section_headers shs) = OK shs.
Proof.
  revert V. induction shs; simpl; intros; eauto.
  rewrite take_drop_length_app by reflexivity.
  simpl.
  rewrite decode_encode_section_header; simpl. 2: inv V; auto.
  rewrite IHshs. 2: inv V; auto.
  reflexivity.
Qed.

Definition encode_sections (ss:list section) :=
  fold_right (fun bytes r => bytes ++ r) [] ss.

Definition encode_section_headers (shs: list section_header) :=
  fold_right (fun sh r => (encode_section_header sh) ++ r) [] shs.

Definition encode_elf_file (ef: elf_file) : (list byte * program) :=
  let bs := 
      (encode_elf_header (elf_head ef)) ++
      (encode_sections (elf_sections ef)) ++
      (encode_section_headers (elf_section_headers ef)) in
  let p := {| AST.prog_defs   := RelocElf.prog_defs ef;
              AST.prog_public := RelocElf.prog_public ef;
              AST.prog_main   := RelocElf.prog_main ef; |} in
  (bs, p).
