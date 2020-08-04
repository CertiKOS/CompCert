(* *******************  *)
(* Author: Zhenguo Yin  *)
(* Date:   Jul 27, 2020 *)
(* *******************  *)

(* Generate the string assciated with a float literal symbol *)

open Printf
open Camlcoq
open Integers
open BinNums

let litNum = ref 0

let create_float_literal_ident () : positive =
  incr litNum;
  let name = Printf.sprintf "__floatlit_%d" (!litNum) in
  let id = intern_string name in
  id
    
let create_float_mask_ident () : ((positive*positive)*(positive*positive)) =
  let negd_mask_s = "__negd_mask" in
  let negd_mask_id = intern_string negd_mask_s in
  let negs_mask_s = "__negs_mask" in
  let negs_mask_id = intern_string negs_mask_s in
  let absd_mask_s = "__absd_mask" in
  let absd_mask_id = intern_string absd_mask_s in
  let abss_mask_s = "__abss_mask" in
  let abss_mask_id = intern_string abss_mask_s in
  ((negd_mask_id,negs_mask_id),(absd_mask_id,abss_mask_id))
  
