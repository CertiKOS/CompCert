open Camlcoq
open Elf
open Errors
open ElfLayout
open RawBinary
open Integers

let get_data_p_offset (code_sz: int) = 
  (Z.to_int elf_header_size) + 
  (Z.to_int num_prog_headers)*(Z.to_int prog_header_size) +
  code_sz

(* Create the program headers from a flat binary program *)
let gen_text_seg (p:program) : program_header =
  let text_size = Z.to_int p.prog_code_size in
  let text_vaddr = Z.to_int p.prog_code_addr in
  {
    p_type     = PT_LOAD;
    p_offset   = Z.to_int get_text_p_offset;
    p_vaddr    = text_vaddr;
    p_paddr    = text_vaddr;
    p_filesz   = text_size;
    p_memsz    = text_size;
    p_flags    = [PF_EXEC; PF_READ];
    p_align    = Z.to_int page_alignment
  }

let gen_data_seg (p:program) : program_header =
  let text_size = Z.to_int p.prog_code_size in
  let data_size = Z.to_int p.prog_data_size in
  let data_vaddr = Z.to_int p.prog_data_addr in
  {
    p_type     = PT_LOAD;
    p_offset   = get_data_p_offset text_size;
    p_vaddr    = data_vaddr;
    p_paddr    = data_vaddr;
    p_filesz   = data_size;
    p_memsz    = data_size;
    p_flags    = [PF_WRITE; PF_READ];
    p_align    = Z.to_int page_alignment
  }

(* Create the section headers from a flat binary program *)
let gen_text_sec (p: program) : section_header =
  let text_size = Z.to_int p.prog_code_size in
  let text_vaddr = Z.to_int p.prog_code_addr in
  {
    sh_name       = 0x0b;
    sh_type       = SHT_PROGBITS;
    sh_flags      = [SHF_ALLOC; SHF_EXECINSTR];
    sh_addr       = text_vaddr;
    sh_offset     = Z.to_int get_text_p_offset;
    sh_size       = text_size;
    sh_addralign  = 1;
  }

let gen_data_sec (p: program) : section_header =
  let text_size = Z.to_int p.prog_code_size in
  let data_size = Z.to_int p.prog_data_size in
  let data_vaddr = Z.to_int p.prog_data_addr in
  {
    sh_name       = 0x11;
    sh_type       = SHT_PROGBITS;
    sh_flags      = [SHF_ALLOC; SHF_WRITE];
    sh_addr       = data_vaddr;
    sh_offset     = (get_data_p_offset text_size);
    sh_size       = data_size;
    sh_addralign  = 1;
  }

let get_strtab_sh_offset (p:program) : int =
  (Z.to_int elf_header_size) + 
  (Z.to_int num_prog_headers)*(Z.to_int prog_header_size) + 
  (Z.to_int p.prog_code_size) + 
  (Z.to_int p.prog_data_size)

let gen_shstrtab_sec (p:program) : section_header =
  {
    sh_name       = 0x01;
    sh_type       = SHT_STRTAB;
    sh_flags      = [];
    sh_addr       = 0;
    sh_offset     = get_strtab_sh_offset p;
    sh_size       = 0x17;
    sh_addralign  = 1;
  }


(* Create the ELF header from a flat binary program *)
let get_e_entry (p:program) : int =
  Z.to_int p.prog_entry

let get_e_phoff (p:program) : int = Z.to_int elf_header_size

let strtab_size = 24

let get_e_shoff (p:program) : int =
  (Z.to_int elf_header_size) + 
  (Z.to_int num_prog_headers)*(Z.to_int prog_header_size) + 
  (Z.to_int p.prog_code_size) + 
  (Z.to_int p.prog_data_size) + 
  strtab_size

let gen_elf_header (p:program) : elf_header =
  create_386_exec_elf_header (get_e_entry p) (get_e_phoff p) (get_e_shoff p)

(* Create the ELF file from a FlatBinary program *)
let gen_elf (p:program) : elf_file =
  (* print_rs_globdefs p; *)
  (* Printf.printf "Length of the text segment: %d\n" (List.length p.machine_code); *)
  let instrs_bytes = List.map (fun b -> Z.to_int (Byte.unsigned b)) p.prog_code in
  let data_bytes   = List.map (fun b -> Z.to_int (Byte.unsigned b)) p.prog_data in
  {
    ef_header        = gen_elf_header p;
    ef_text_sec      = gen_text_sec p;
    ef_data_sec      = gen_data_sec p;
    ef_shstrtab_sec  = gen_shstrtab_sec p;
    ef_text_seg      = gen_text_seg p;
    ef_data_seg      = gen_data_seg p;
    ef_text          = instrs_bytes;
    ef_data          = data_bytes;
  }


