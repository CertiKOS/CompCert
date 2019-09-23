open Integers
open Camlcoq


(* Write bytes into a binary file *)
let write_elf fname (bs:Byte.int list) =
  let bytes = List.map Z.to_int bs in
  let dump_channel = open_out_bin fname in
  List.iter (fun i -> output_byte dump_channel i) bytes;
  close_out dump_channel
