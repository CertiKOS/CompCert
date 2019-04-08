(* Translation from raw binary to ELF files *)
(* Author        : Yuting Wang *)
(* Date Created  : 04-05-2019 *)

open Camlcoq
open Elf
open Errors
open ElfLayout
open RawBinary


(* Create the program headers from a flat binary program *)
let gen_text_seg (p:program) : program_header =
  let text_size = text_seg_size (prog_code_size p) in
  let text_vaddr = (prog_code_addr p) in
  {
    p_type     = PT_LOAD;
    p_offset   = Z.to_int get_text_p_offset;
    p_vaddr    = Z.to_int text_vaddr;
    p_paddr    = Z.to_int text_vaddr;
    p_filesz   = Z.to_int text_size;
    p_memsz    = Z.to_int text_size;
    p_flags    = [PF_EXEC; PF_READ];
    p_align    = Z.to_int page_alignment
  }

let gen_data_seg (p:program) : program_header =
  let data_size = prog_data_size p in
  let data_vaddr = prog_data_addr p in
  {
    p_type     = PT_LOAD;
    p_offset   = Z.to_int (get_data_p_offset (prog_code_size p));
    p_vaddr    = Z.to_int data_vaddr;
    p_paddr    = Z.to_int data_vaddr;
    p_filesz   = Z.to_int data_size;
    p_memsz    = Z.to_int data_size;
    p_flags    = [PF_WRITE; PF_READ];
    p_align    = Z.to_int page_alignment
  }

(* Create the section headers from a flat binary program *)
let gen_text_sec (p: program) : section_header =
  let text_size = text_seg_size (prog_code_size p) in
  let text_vaddr = (prog_code_addr p) in
  {
    sh_name       = 0x0b;
    sh_type       = SHT_PROGBITS;
    sh_flags      = [SHF_ALLOC; SHF_EXECINSTR];
    sh_addr       = Z.to_int text_vaddr;
    sh_offset     = Z.to_int get_text_p_offset;
    sh_size       = Z.to_int text_size;
    sh_addralign  = 1;
  }

let gen_data_sec (p: program) : section_header =
  let data_size = prog_data_size p in
  let data_vaddr = prog_data_addr p in
  {
    sh_name       = 0x11;
    sh_type       = SHT_PROGBITS;
    sh_flags      = [SHF_ALLOC; SHF_WRITE];
    sh_addr       = Z.to_int data_vaddr;
    sh_offset     = Z.to_int (get_data_p_offset (prog_code_size p));
    sh_size       = Z.to_int data_size;
    sh_addralign  = 1;
  }

let get_strtab_sh_offset (p:program) : int =
  (Z.to_int elf_header_size) + 
  (Z.to_int num_prog_headers)*(Z.to_int prog_header_size) + 
  (Z.to_int (text_seg_size (prog_code_size p))) + 
  (Z.to_int (prog_data_size p))

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
  let text_vaddr = prog_code_addr p in
  (Z.to_int text_vaddr) + (Z.to_int (prog_code_size p))

let get_e_phoff (p:program) : int = Z.to_int elf_header_size

let get_e_shoff (p:program) : int =
  (Z.to_int elf_header_size) + 
  (Z.to_int num_prog_headers)*(Z.to_int prog_header_size) + 
  (Z.to_int (text_seg_size (prog_code_size p))) + 
  (Z.to_int (prog_data_size p)) + 
  (Z.to_int strtab_size)

let gen_elf_header (p:program) : elf_header =
  create_386_exec_elf_header (get_e_entry p) (get_e_phoff p) (get_e_shoff p)

(* Create the ELF file from a FlatBinary program *)
let gen_elf (p:program) : elf_file =
  (* print_rs_globdefs p; *)
  (* Printf.printf "Length of the text segment: %d\n" (List.length p.machine_code); *)
  let text_vaddr = prog_code_addr p in
  let data_vaddr = prog_data_addr p in
  let main_ofs   = (prog_main_ofs p) - (prog_code_size p + call_size) in
  let startstub_bytes = create_start_stub main_ofs in
  let instrs_bytes = encode_instr_list (p.text_instrs (Z.of_uint data_vaddr)) in
  {
    ef_header        = gen_elf_header p;
    ef_text_sec      = gen_text_sec p;
    ef_data_sec      = gen_data_sec p;
    ef_shstrtab_sec  = gen_shstrtab_sec p;
    ef_text_seg      = gen_text_seg p;
    ef_data_seg      = gen_data_seg p;
    ef_text          = instrs_bytes @ startstub_bytes;
    ef_data          = List.map (fun d -> Z.to_int d) (p.init_data (Z.of_uint data_vaddr));
  }


