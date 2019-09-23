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

let rec int_to_pos (i:int) : positive =
  if i = 1 then
    Coq_xH
  else if i > 1 then      
    let un = int_to_pos (i / 2) in
    let rm = i mod 2 in
    if i = 0 then
      Coq_xO un
    else
      Coq_xI un
  else
    let s = sprintf "%i" i in
    raise (Invalid_argument s)

let int_to_Z (i:int) : coq_Z =
  if i = 0 then
    Z0
  else if i > 0 then
    Zpos (int_to_pos i)
  else
    Zneg (int_to_pos (-i))


let string_to_list (s:string) : char list =
  let l = ref [] in
  String.iter (fun c -> l := c::(!l)) s;
  List.rev !l

let find_symbol_string_bytes a : Byte.int list res =
  try 
    let s = (Hashtbl.find string_of_atom a) in
    let coq_zs = List.map (fun c -> int_to_Z (Char.code c)) (string_to_list s) in
    OK (List.map (fun z -> Byte.repr z) coq_zs)
  with
  | Not_found ->
    Error [MSG(coqstring_of_camlstring "Cannot find the string of the symbol ");
           CTX a]
