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
Require Import Hex Bits.
Import Hex Bits.
Import ListNotations.

Set Implicit Arguments.

Local Open Scope error_monad_scope.
Local Open Scope hex_scope.
Local Open Scope bits_scope.

(* We create a simple ELF file with the following layout
   where every section is aligned at 4 bytes:

   1. ELF Header                                       (52 bytes)
   2. Sections
      a) .data section (global variables)                 
      b) .text section (instructions)                     
      c) .symtab section (symbol table)                   
      d) .reladata section (relocation of .data)          
      e) .relatext section (relocation of .text)
      f) .shstrtab section (section string table)
      g) .strtab section (string table)
   3. Section headers
      a) Null header                      (40 bytes)
      b) header for .data      (40 bytes)
      c) header for .text      (40 bytes)
      d) header for .symbtab      (40 bytes)
      e) header for .reladata
      f) header for .relatext
      g) header for .shstrtab
      h) header for .strtab
 *)


(** ** Generation of ELF header *)

Definition get_sections_size (t: SeqTable.t RelocProgram.section) :=
  match t with
  | nil => 0
  | h :: l => fold_left (fun acc sec => sec_size sec + acc) l 0
  end.

(** THIS IS NOT QUITE RIGHT *)
Definition get_elf_shoff (p:program) :=
  elf_header_size + 
  get_sections_size (prog_sectable p).

  
Definition gen_elf_header (p:program) : elf_header :=
  let sectbl_size := Z.of_nat (SeqTable.size (prog_sectable p)) in
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
     e_shnum        := sectbl_size + 2;      (** with additional sections .strtab and .shstrtab *)
     e_shstrndx     := sectbl_size + 1;
  |}.

(** The default shstrtab is '.data .text .symtab .reladata .relatext .strtab .shstrtab' *)
Local Open Scope string_byte_scope.
Definition data_str := HB["00"] :: SB[".data"].
Definition text_str := HB["00"] :: SB[".text"].
Definition symtab_str := HB["00"] :: SB[".symtab"].
Definition reladata_str := HB["00"] :: SB[".reladata"].
Definition relatext_str := HB["00"] :: SB[".relatext"].
Definition shstrtab_str := HB["00"] :: SB[".shstrtab"].
Definition strtab_str := HB["00"] :: SB[".strtab"].


Definition default_shstrtab := 
  data_str ++ 
  text_str ++
  symtab_str ++
  reladata_str ++
  relatext_str ++
  shstrtab_str ++
  strtab_str.

Definition data_str_ofs := 1.
Definition text_str_ofs := data_str_ofs + (Z.of_nat (length data_str)).
Definition symtab_str_ofs := text_str_ofs + (Z.of_nat (length text_str)).
Definition reladata_str_ofs := symtab_str_ofs + (Z.of_nat (length symtab_str)).
Definition relatext_str_ofs := reladata_str_ofs + (Z.of_nat (length reladata_str)).
Definition shstrtab_str_ofs := relatext_str_ofs + (Z.of_nat (length relatext_str)).
Definition strtab_str_ofs := shstrtab_str_ofs + (Z.of_nat (length shstrtab_str)).

Fixpoint list_first_n {A:Type} (n:nat) (l:list A) :=
  match n, l with
  | O, _ => nil
  | S n', (h::t) => h :: (list_first_n n' t)
  | _ , nil =>  nil
  end.

Fixpoint sectable_prefix_size (id:ident) t :=
  match t with
  | nil => 0
  | h :: t' => 
    let l := list_first_n (pred (Pos.to_nat id)) t' in
    get_sections_size l
  end.
    

Definition get_sh_offset id (t:sectable) :=
  elf_header_size + (sectable_prefix_size id t).

Definition get_section_size id (t:sectable) :=
  match SeqTable.get id t with
  | None => 0
  | Some s => sec_size s
  end.

(** Create section headers *)
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

Definition gen_symtab_sec_header p :=
  let t := (prog_sectable p) in
  {| sh_name     := symtab_str_ofs;
     sh_type     := SHT_SYMTAB;
     sh_flags    := [];
     sh_addr     := 0;
     sh_offset   := get_sh_offset sec_symbtbl_id t;
     sh_size     := get_section_size sec_symbtbl_id t;
     sh_link     := 0;
     sh_info     := 0;
     sh_addralign := 1;
     sh_entsize  := symb_entry_size;
  |}.

Definition gen_reladata_sec_header p :=
  let t := (prog_sectable p) in
  {| sh_name     := reladata_str_ofs;
     sh_type     := SHT_RELA;
     sh_flags    := [];
     sh_addr     := 0;
     sh_offset   := get_sh_offset sec_rel_data_id t;
     sh_size     := get_section_size sec_rel_data_id t;
     sh_link     := Z.pos sec_symbtbl_id;
     sh_info     := Z.pos sec_data_id;
     sh_addralign := 1;
     sh_entsize  := reloc_entry_size;
  |}.

Definition gen_relatext_sec_header p :=
  let t := (prog_sectable p) in
  {| sh_name     := relatext_str_ofs;
     sh_type     := SHT_RELA;
     sh_flags    := [];
     sh_addr     := 0;
     sh_offset   := get_sh_offset sec_rel_code_id t;
     sh_size     := get_section_size sec_rel_code_id t;
     sh_link     := Z.pos sec_symbtbl_id;
     sh_info     := Z.pos sec_code_id;
     sh_addralign := 1;
     sh_entsize  := reloc_entry_size;
  |}.

Definition gen_shstrtab_sec_header p :=
  let t := (prog_sectable p) in
  {| sh_name     := shstrtab_str_ofs;
     sh_type     := SHT_STRTAB;
     sh_flags    := [];
     sh_addr     := 0;
     sh_offset   := get_sh_offset sec_rel_code_id t;
     sh_size     := get_section_size sec_rel_code_id t;
     sh_link     := Z.pos sec_symbtbl_id;
     sh_info     := Z.pos sec_code_id;
     sh_addralign := 1;
     sh_entsize  := reloc_entry_size;
  |}.
