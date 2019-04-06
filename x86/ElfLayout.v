Require Import Coqlib Integers AST Maps.
Require Import Errors.
Require Import Hex Bits Memdata.
Import ListNotations.
Import Hex Bits.

Local Open Scope error_monad_scope.
Local Open Scope hex_scope.
Local Open Scope bits_scope.

(* Create the following start stub *)
  (* call   main *)
  (* mov    %eax,%ebx *)
  (* mov    $0x1,%eax *)
  (* int    $0x80 *)
Definition call_size : Z := 5.

Definition create_start_stub (main_ofs: Z) : list byte := 
  let call_main_bytes := 
      (HB["E8"] :: encode_int 4 main_ofs) in             (* call   main *)
  let startsub := 
    [HB["89"]; HB["C3"];                                 (* mov    %eax,%ebx *)
     HB["B8"]; HB["01"]; HB["00"]; HB["00"]; HB["00"];   (* mov    $0x1,%eax *)
     HB["CD"]; HB["80"]]                                 (* int    $0x80 *)
  in
  call_main_bytes ++ startsub.


(* We create a simple ELF file with the following layout
   where every section is aligned at 4 bytes:

   1. ELF Header                          (52 bytes)
   2. Program Headers       
      a) Header for the text segment      (32 bytes)
      b) Header for the data segment      (32 bytes)
   3. Text section (instructions)         (TSZ bytes)
   4. Data section (global variables)     (DSZ bytes)
   5. String table                        (24 bytes)
   6. Section headers
      a) Null header                      (40 bytes)
      a) Header for the text section      (40 bytes)
      a) Header for the data section      (40 bytes)
      a) Header for the string table      (40 bytes)

 *)

Definition alignw n := align n 8.

Definition elf_header_size  := 52.
Definition prog_header_size := 32.
Definition sec_header_size  := 40.
Definition num_prog_headers := 2.
Definition num_sec_headers  := 4.
Definition strtab_size      := 24.

Definition page_alignment   := HZ["1000"].


(* Calculate the size of text and data segments *)
Definition startstub_size := Z.of_nat (List.length (create_start_stub 0)).

Definition text_seg_size (code_sz:Z) : Z :=
  (** We assume code_sz is aligned to 8 bytes *)
  code_sz + alignw startstub_size.

(* Calcualte the virtual/physical addresses of a segment *)
Definition calculate_seg_vaddr (seg_file_ofs: Z) (seg_size: Z) (start_addr: Z) 
  : (Z * Z) :=
  (* Set the starting address to be aligned at page boundaries *)
  let start_addr := align start_addr page_alignment in
  (* Calculate the offset to the beginning of a page *)
  let ofs_in_page := seg_file_ofs mod page_alignment in
  (* Get the virtual address the segment should begin with *)
  let vaddr := start_addr + ofs_in_page in
  (* Get the virtual address for the first page after the segment *)
  let new_start_addr := align (vaddr + seg_size) page_alignment in
  (vaddr, new_start_addr).


(* Calcualte the virtual/physical addresses of the text and data segments *)
Definition get_text_p_offset := 
  elf_header_size + num_prog_headers*prog_header_size.

Definition get_data_p_offset (code_sz: Z):= 
  elf_header_size + num_prog_headers*prog_header_size +
  (text_seg_size code_sz).

Definition init_addr := HZ["08048000"].

Definition cal_text_data_vaddrs (code_sz data_sz: Z): (Z * Z) :=
  let (text_vaddr, vaddr_data_start) := 
    calculate_seg_vaddr (get_text_p_offset) code_sz init_addr in
  let (data_vaddr, _) :=
    calculate_seg_vaddr (get_data_p_offset code_sz) data_sz vaddr_data_start in
  (text_vaddr, data_vaddr).
