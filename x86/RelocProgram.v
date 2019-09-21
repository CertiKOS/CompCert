(* *******************  *)
(* Author: Yuting Wang  *)
(* Date:   Sep 13, 2019 *)
(* *******************  *)

(** * Template of languages with information about symbols and relocation *)

Require Import Coqlib Maps Integers Values AST.
Require Import Globalenvs SeqTable Asm.


(** ** Sections *)
Inductive sectype : Type := sec_text | sec_data | sec_symbtbl | sec_rela | sec_null.

Inductive sec_info_type : Type := sec_info_byte | sec_info_instr | sec_info_init_data | sec_info_null.

Definition interp_sec_info_type (I: sec_info_type) :=
  match I with
  | sec_info_byte => list byte
  | sec_info_instr => list instruction
  | sec_info_init_data => list init_data
  | sec_info_null => unit
  end.

Record section : Type :=
{
  sec_type: sectype;
  sec_size: Z;
  sec_info_ty : sec_info_type;
  sec_info: interp_sec_info_type sec_info_ty;
}.

Definition sectable := SeqTable.t section.

Definition sections_size stbl :=
  fold_left (fun sz sec => sz + (sec_size sec)) stbl 0.

Definition seclabel : Type := ident * Z.

(** ** Symbol table *)
Inductive symbtype : Type := symb_func | symb_data | symb_notype.

Inductive secindex : Type :=
| secindex_normal (id:ident)
| secindex_comm
| secindex_undef.

Record symbentry : Type :=
{
  symbentry_type: symbtype;
  symbentry_value: Z;  (** This holds the alignment info if secindex is secindex_comm,
                           otherwise, it holds the offset from the beginning of the section *)
  symbentry_secindex: secindex;
  symbentry_size: Z;
}.

Definition symbtable := SeqTable.t (ident * symbentry).

(** ** Relocation table *)
Inductive reloctype : Type := reloc_abs | reloc_rel | reloc_null.

Record relocentry : Type :=
{
  reloc_offset: Z;
  reloc_type  : reloctype;
  reloc_symb  : ident;    (* Index into the symbol table *)
  reloc_addend : Z;
}.

Definition reloctable := SeqTable.t relocentry.
Definition reloctables := SeqTable.t reloctable.


(** ** Definition of program constructs *)
Definition gdef := AST.globdef fundef unit.

Record program : Type := {
  prog_defs: list (ident * option gdef);
  prog_public: list ident;
  prog_main: ident;
  prog_sectable: sectable;
  prog_symbtable: symbtable;
  prog_reloctables: reloctables; (** Given the index of a section, it returns its relocation table *)
  prog_senv : Globalenvs.Senv.t;
}.

(* Definition prog_to_prog (p: program) : AST.program fundef unit := *)
(*   {| *)
(*     AST.prog_defs := prog_defs p; *)
(*     AST.prog_public := prog_public p; *)
(*     AST.prog_main := prog_main p; *)
(*   |}. *)

(* Coercion prog_to_prog : program >-> AST.program. *)

(** Section table ids *)
Definition sec_data_id := 1%positive.
Definition sec_code_id := 2%positive.
