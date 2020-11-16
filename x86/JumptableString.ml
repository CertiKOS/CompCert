(* *******************  *)
(* Author: Zhenguo Yin  *)
(* Date:   Aug 04, 2020 *)
(* *******************  *)

(* Generate the string assciated with a jump table symbol *)

open Printf
open Camlcoq
open Integers
open BinNums

let jmptbl_id = ref 0
let label_id = ref 0

let create_jump_table_ident () : positive =
  incr jmptbl_id;
  label_id := 0;
  let name = Printf.sprintf "__jumptable_%d" (!jmptbl_id) in
  let id = intern_string name in
  id

let create_label_ident() : positive =
  incr label_id;
  let name = Printf.sprintf "__jmptbl%d_label_%d" (!jmptbl_id) (!label_id) in
  let id = intern_string name in
  id

