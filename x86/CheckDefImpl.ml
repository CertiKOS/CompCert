(** * Check if the definition is a local or global one *)

open Printf
open Camlcoq
open C2C
open AST


let is_def_builtin (id: ident) : bool =
  try
    let name = Hashtbl.find string_of_atom id in
    List.mem_assoc name builtins.Builtins.functions
  with
  | Not_found ->
     false

let is_def_string_literal (id: ident) : bool =
  let lit_sec = [Sections.for_stringlit()] in
  try 
    let a = Hashtbl.find decl_atom id in
    a.a_sections = lit_sec
  with
  | Not_found ->
     false
