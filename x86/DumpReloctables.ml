open Camlcoq
open RelocProgram
open Errors

let dump_reloctype rt =
  match rt with
  | Coq_reloc_abs  -> "abs"
  | Coq_reloc_rel  -> "rel"
  | Coq_reloc_null -> "null"

let dump_relocentry re =
  Format.printf "[ofs = %d, type = %s, symb = %d, addend = %d\n"
    (Z.to_int (reloc_offset re))
    (dump_reloctype (reloc_type re))
    (N.to_int (reloc_symb re))
    (Z.to_int (reloc_addend re))

let dump_reloctable rtbl =
  List.iter dump_relocentry rtbl

let dump_reloctables rmap =
  Format.printf "RELOC CODE:\n"; dump_reloctable (reloctable_code rmap);
  Format.printf "RELOC DATA:\n"; dump_reloctable (reloctable_data rmap);
  Error []
