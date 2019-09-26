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

Definition get_sections_size (t: SeqTable.t RelocProgram.section) :=
  match t with
  | nil => 0
  | h :: l => fold_left (fun acc sec => sec_size sec + acc) l 0
  end.

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
     e_shnum        := sectbl_size;      
     e_shstrndx     := Z.of_N (SecIndex.interp sec_shstrtbl_id);
  |}.


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
  match SeqTable.get (SecIndex.interp id) t with
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
     sh_link     := Z.of_N (SecIndex.interp sec_strtbl_id);
     sh_info     := 0;
     sh_addralign := 1;
     sh_entsize  := symb_entry_size;
  |}.

Definition gen_reldata_sec_header p :=
  let t := (prog_sectable p) in
  {| sh_name     := reladata_str_ofs;
     sh_type     := SHT_REL;
     sh_flags    := [];
     sh_addr     := 0;
     sh_offset   := get_sh_offset sec_rel_data_id t;
     sh_size     := get_section_size sec_rel_data_id t;
     sh_link     := Z.of_N (SecIndex.interp sec_symbtbl_id);
     sh_info     := Z.of_N (SecIndex.interp sec_data_id);
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
     sh_link     := Z.of_N (SecIndex.interp sec_symbtbl_id);
     sh_info     := Z.of_N (SecIndex.interp sec_code_id);
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


(** Generation of the Elf file 
    without the actual string table section and its header *)

Definition transl_section (sec: RelocProgram.section) : res section :=
  match sec_info_ty sec as t
        return interp_sec_info_type t -> res section
  with
  | sec_info_byte => fun bytes => OK bytes
  | _ => fun _ => Error (msg "Section has not been encoded into bytes")
  end (sec_info sec).

Definition gen_sections (t:sectable) : res (list section) :=
  match t with
  | nil => Error (msg "No section found")
  | null :: t' =>
    fold_right (fun sec r => 
                  do r' <- r;
                    do sec' <- transl_section sec;
                    OK (sec' :: r'))
               (OK [])
               t'
  end.

Definition gen_reloc_elf (p:program) : res elf_file :=
  do secs <- gen_sections (prog_sectable p);
  if (beq_nat (length secs) 7) then
    let headers := [null_section_header;
                      gen_data_sec_header p;
                      gen_text_sec_header p;
                      gen_strtab_sec_header p;
                      gen_symtab_sec_header p;
                      gen_reldata_sec_header p;
                      gen_reltext_sec_header p;
                      gen_shstrtab_sec_header p] in
    OK {| elf_head      := gen_elf_header p;
          elf_sections  := secs;
          elf_section_headers := headers;
       |}
  else
    Error [MSG "Number of sections is incorrect (not 7): "; POS (Pos.of_nat (length secs))].