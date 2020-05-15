(* *******************  *)


(* *******************  *)

(** * Check if the definition is a local or global one *)

Require Import Coqlib Integers AST Maps.


(** Local definitions include string literals and built-in functions *)

Parameter is_def_builtin: ident -> bool.

Parameter is_def_string_literal: ident -> bool.

Definition is_def_local id :=
  is_def_builtin id || is_def_string_literal id.
