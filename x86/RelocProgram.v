(* *******************  *)
(* Author: Yuting Wang  *)
(* Date:   Sep 13, 2019 *)
(* *******************  *)

(** * Template of languages with information about symbols and relocation *)

Require Import Coqlib Maps Integers Values AST.
Require Import Globalenvs SeqTable Asm.

(** In the programs we use postives (ident) for indexing into various
    tables.  However, the indexes of tables are natural numbers.
    Thus, we need to define interpretation of positives into natural
    numbers for different tables. The following sigature is for this
    purpose. *)
Module Type INDEX.
  Parameter interp : ident -> N.
  Parameter deinterp : N -> option ident.

  Axiom interp_round_trip : forall i, deinterp (interp i) = Some i. 
End INDEX.

Module IdIndex <: INDEX.
  Definition interp i := Npos i.
  Definition deinterp i := match i with
                           | N0 => None
                           | Npos p => Some p
                           end.
  Lemma interp_round_trip : forall i, deinterp (interp i) = Some i. 
  Proof.
    intros i. simpl. auto.
  Qed.

End IdIndex.

Module SubOneIndex <: INDEX.
  Definition interp i := Pos.pred_N i.
  Definition deinterp i := Some (N.succ_pos i).

  Lemma interp_round_trip : forall i, deinterp (interp i) = Some i. 
  Proof.
    intros i. unfold deinterp, interp.
    f_equal. unfold N.succ_pos, Pos.pred_N.
    destruct i. simpl. auto.
    rewrite Pos.succ_pred_double. auto.
    auto.
  Qed.

End SubOneIndex.


(** ** Sections *)
Inductive sectype : Type := sec_text | sec_data | sec_symbtbl | sec_strtbl | sec_rela | sec_null.

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

Definition null_section :=
  {| sec_type := sec_null;
     sec_size := 0;
     sec_info_ty := sec_info_null;
     sec_info := tt;
  |}.


(** Positive indexes to sections are mapped by the identity function,
    the 0-th section is a pre-defined null section *)
Module SecIndex := IdIndex.
Definition sectable := @SeqTable.t section.

Definition sections_size stbl :=
  fold_left (fun sz sec => sz + (sec_size sec)) stbl 0.

Definition seclabel : Type := ident * Z.

(** ** Symbol table *)
Inductive symbtype : Type := symb_func | symb_data | symb_notype.

Inductive secindex : Type :=
| secindex_normal (idx:N)
| secindex_comm
| secindex_undef.

Record symbentry : Type :=
{
  symbentry_id: option ident;  (** The original identifier of the symbol *) 
  symbentry_type: symbtype;
  symbentry_value: Z;  (** This holds the alignment info if secindex is secindex_comm,
                           otherwise, it holds the offset from the beginning of the section *)
  symbentry_secindex: secindex;
  symbentry_size: Z;
}.

Definition dummy_symbentry : symbentry :=
  {| symbentry_id := None;
     symbentry_type := symb_notype;
     symbentry_value := 0;
     symbentry_secindex := secindex_undef;
     symbentry_size := 0;
  |}.

(** Positive indexes to symbols are mapped by the identity function,
    the 0-th section is a pre-defined dummy symbol *)
Module SymbIndex := IdIndex.
Definition symbtable := SeqTable.t symbentry.

(** ** Relocation table *)
Inductive reloctype : Type := reloc_abs | reloc_rel | reloc_null.

Record relocentry : Type :=
{
  reloc_offset: Z;
  reloc_type  : reloctype;
  reloc_symb  : N;    (* Index into the symbol table *)
  reloc_addend : Z;
}.

(** Positive indexes to symbols are mapped by subtraction by one *)
Module RelocIndex := SubOneIndex.
Definition reloctable := SeqTable.t relocentry.

(** ** String table *)
Definition strtable := PTree.t Z.

(** ** Definition of program constructs *)
Definition gdef := AST.globdef fundef unit.

Record program : Type := {
  prog_defs: list (ident * option gdef);
  prog_public: list ident;
  prog_main: ident;
  prog_sectable: sectable;
  prog_symbtable: symbtable;
  prog_strtable: strtable;
  prog_reloctables: SeqTable.t (option reloctable); (** Given the index of a section, it returns its relocation table (if exists) *)
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
Definition sec_data_id     := 1%positive.
Definition sec_code_id     := 2%positive.
Definition sec_strtbl_id   := 3%positive.
Definition sec_symbtbl_id  := 4%positive.
Definition sec_rel_data_id := 5%positive.
Definition sec_rel_code_id := 6%positive.
Definition sec_shstrtbl_id := 7%positive.