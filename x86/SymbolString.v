(* *******************  *)
(* Author: Yuting Wang  *)
(* Date:   Oct 3, 2019  *)
(* *******************  *)

Require Import Coqlib Integers AST Maps.
Require Import Errors.
Require Import Ascii String.

(** This an external function in ML for 
    finding the strings associated with the global symbols *)
Parameter find_symbol_pos : ident -> option (list positive).

Parameter string_to_ident : list byte -> option ident.


(* Assumptions about the size of symbols *)
Axiom string_to_ident_symbol_to_pos:
  forall s lb, find_symbol_pos s = Some lb ->
               string_to_ident (map (fun p => Byte.repr (Zpos p)) lb) = Some s.

Axiom string_bounds: forall l, exists z, fold_right (fun id acc =>
                                        match acc with
                                          OK z =>
                                          match find_symbol_pos id with
                                          | Some pos => OK (z + 2 + Z.of_nat (List.length pos))
                                          | None => Error (msg "cannot find string")
                                          end
                                        | _ => acc
                                        end
                                     ) (OK 0) l = OK z /\ 
                               z < Int.max_unsigned.
