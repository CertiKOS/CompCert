(* *******************  *)
(* Author: Yuting Wang  *)
(* Date:   Sep 23, 2019 *)
(* *******************  *)

(* Finding the string assciated with a symbol *)

open Printf
open Camlcoq
open Errors
open Integers
open BinNums
open extraction.ExtrOcamlIntConv

let string_to_list (s:string) : char list =
  let l = ref [] in
  String.iter (fun c -> l := c::(!l)) s;
  List.rev !l

let find_symbol_string_bytes a : Byte.int res =
  try 
    let s = (Hashtbl.find string_of_atom a) in
    let coq_zs = List.map (fun c -> z_of_int (Char.code c)) (string_to_list s) in
    OK (List.map (fun z -> Byte.repr z) coq_zs)
  with
  | Not_found ->
    Error [MSG(coqstring_of_camlstring "Cannot find the string of the symbol ");
           CTX a]
