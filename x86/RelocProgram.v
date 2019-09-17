(* *******************  *)
(* Author: Yuting Wang  *)
(* Date:   Sep 13, 2019 *)
(* *******************  *)

(** * Template of languages with information about symbols and relocation *)

Require Import Coqlib Maps Integers Values AST.
Require Import Globalenvs.

(** ** Sections *)
Inductive sectype : Type := sec_text | sec_data.

Record section : Type :=
{
  sec_type: sectype;
  sec_size: Z;
}.

Definition sectable := PTree.t section.

Definition sections_size (t:sectable) :=
  let l := PTree.elements t in
  fold_left (fun sz '(_,s) => sec_size s + sz) l 0.

Definition seclabel : Type := ident * Z.

Record secblock:Type := 
{
  secblock_id: ident;
  secblock_start : Z;  (**r The begining of the block relative to the starting point of the segment *)
  secblock_size : Z;
}.

Definition segblock_to_label (sb: secblock) : seclabel :=
  (secblock_id sb,  secblock_start sb).


(** ** Symbol table *)
Inductive symbtype : Type := symb_func | symb_data | symb_notype.

Inductive secindex : Type :=
| secindex_normal (id:ident)
| secindex_comm
| secindex_undef.

Record symbentry : Type :=
{
  symbentry_id : ident;  (** This symbol's original id in its source program *)
  symbentry_type: symbtype;
  symbentry_value: Z;  (** This holds the alignment info if secindex is secindex_comm,
                           otherwise, it holds the offset from the beginning of the section *)
  symbentry_secindex: secindex;
}.

Definition symbtable := PTree.t symbentry.


(** ** Relocation table *)
Inductive reloctype : Type := RelocAbs | RelocRel.

Record relocentry : Type :=
{
  reloc_offset: Z;
  reloc_type  : reloctype;
  reloc_symb  : ident;    (* Index into the symbol table *)
  reloc_addend : Z;
}.

Definition reloctable := PTree.t relocentry.


(** ** Definition of program constructs *)
Module Type RelocProgParams.
  Parameter C :Type.  (* Type of code in a function*)
  Parameter D: Type. (* Type of global data *)
End RelocProgParams.


Module RelocProg (P: RelocProgParams).

Import P.

Record function : Type := mkfunction { fn_sig: signature; fn_code: C; fn_stacksize: Z; fn_pubrange: Z * Z}.
Definition fundef := AST.fundef function.
Definition gdef := AST.globdef fundef D.

Record program : Type := {
  prog_defs: list (ident * option gdef);
  prog_public: list ident;
  prog_main: ident;
  prog_sectable: sectable;
  prog_symbtable: symbtable;
  prog_reloctables: PTree.t reloctable; (** Given the index of a section, it returns its relocation table *)
  prog_senv : Globalenvs.Senv.t;
}.

Definition prog_to_prog (p: program) : AST.program fundef D :=
  {|
    AST.prog_defs := prog_defs p;
    AST.prog_public := prog_public p;
    AST.prog_main := prog_main p;
  |}.

Coercion prog_to_prog : program >-> AST.program.

End RelocProg.

(** Section table ids *)
Definition sec_data_id := 1%positive.
Definition sec_code_id := 2%positive.
