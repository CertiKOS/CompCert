(* *******************  *)
(* Author: Yuting Wang  *)
(* Date:   Sep 13, 2019 *)
(* *******************  *)

(** * Template of languages with information about symbols and relocation *)

Require Import Coqlib Maps Integers Values AST.
Require Import Globalenvs SeqTable Asm.

(* (** In the programs we use postives (ident) for indexing into various *)
(*     tables.  However, the indexes of tables are natural numbers. *)
(*     Thus, we need to define interpretation of positives into natural *)
(*     numbers for different tables. The following sigature is for this *)
(*     purpose. *) *)
(* Module Type INDEX. *)
(*   Parameter interp : ident -> N. *)
(*   Parameter deinterp : N -> option ident. *)

(*   Axiom interp_round_trip : forall i, deinterp (interp i) = Some i.  *)
(* End INDEX. *)

(* Module IdIndex <: INDEX. *)
(*   Definition interp i := Npos i. *)
(*   Definition deinterp i := match i with *)
(*                            | N0 => None *)
(*                            | Npos p => Some p *)
(*                            end. *)
(*   Lemma interp_round_trip : forall i, deinterp (interp i) = Some i.  *)
(*   Proof. *)
(*     intros i. simpl. auto. *)
(*   Qed. *)

(* End IdIndex. *)

(* Module SubOneIndex <: INDEX. *)
(*   Definition interp i := Pos.pred_N i. *)
(*   Definition deinterp i := Some (N.succ_pos i). *)
(*   Definition deinterp' i := (N.succ_pos i). *)

(*   Lemma interp_round_trip : forall i, deinterp (interp i) = Some i.  *)
(*   Proof. *)
(*     intros i. unfold deinterp, interp. *)
(*     f_equal. unfold N.succ_pos, Pos.pred_N. *)
(*     destruct i. simpl. auto. *)
(*     rewrite Pos.succ_pred_double. auto. *)
(*     auto. *)
(*   Qed. *)

(* End SubOneIndex. *)


(** ** Sections *)

Inductive section : Type :=
| sec_null
| sec_text (code: list instruction)
| sec_data (init: list init_data)
| sec_bytes (bs: list byte).

Definition sec_size (s: section) : Z :=
  match s with
  | sec_null => 0
  | sec_text c => code_size c
  | sec_data d => AST.init_data_list_size d
  | sec_bytes bs => Z.of_nat (length bs)
  end.

(** Positive indexes to sections are mapped by the identity function,
    the 0-th section is a pre-defined null section *)
(* Module SecIndex := IdIndex. *)
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

Inductive bindtype : Type :=
| bind_local
| bind_global.

Record symbentry : Type :=
{
  symbentry_id: option ident;  (** The original identifier of the symbol *) 
  symbentry_bind: bindtype;
  symbentry_type: symbtype;
  symbentry_value: Z;  (** This holds the alignment info if secindex is secindex_comm,
                           otherwise, it holds the offset from the beginning of the section *)
  symbentry_secindex: secindex;
  symbentry_size: Z;
}.

Definition dummy_symbentry : symbentry :=
  {| symbentry_id := None;
     symbentry_bind := bind_local;
     symbentry_type := symb_notype;
     symbentry_value := 0;
     symbentry_secindex := secindex_undef;
     symbentry_size := 0;
  |}.

Definition is_symbol_internal e :=
  match symbentry_secindex e with
  | secindex_normal _ => true
  | _ => false
  end.

(** Positive indexes to symbols are mapped by the identity function,
    the 0-th section is a pre-defined dummy symbol *)
(* Module SymbIndex := IdIndex. *)
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
(* Module RelocIndex := SubOneIndex. *)
Definition reloctable := SeqTable.t relocentry.

(** ** String table *)
Definition strtable := PTree.t Z.

(** ** Definition of program constructs *)
Definition gdef := AST.globdef fundef unit.

Inductive reloctable_id := RELOC_CODE | RELOC_DATA.

Definition reloctable_id_eq: forall (x y: reloctable_id), {x = y} + { x <> y}.
Proof.
  decide equality.
Defined.

Record reloctable_map :=
  {
    reloctable_code: reloctable;
    reloctable_data: reloctable;
  }.

Definition set_reloctable (i: reloctable_id) (rtbl:reloctable) (rmap:reloctable_map) :=
  match i with
  | RELOC_CODE => {| reloctable_code := rtbl; reloctable_data := reloctable_data rmap |}
  | RELOC_DATA => {| reloctable_data := rtbl; reloctable_code := reloctable_code rmap |}
  end.

Definition get_reloctable (i:reloctable_id) (rmap: reloctable_map) :=
  match i with
  | RELOC_CODE => reloctable_code rmap
  | RELOC_DATA => reloctable_data rmap
  end.

Record program : Type := {
  prog_defs: list (ident * option gdef);
  prog_public: list ident;
  prog_main: ident;
  prog_sectable: sectable;
  prog_symbtable: symbtable;
  prog_strtable: strtable;
  prog_reloctables: reloctable_map;
  prog_senv : Globalenvs.Senv.t;
}.

(** Generate the mapping from symbol ids to indexes *)
Definition symb_index_map_type := PTree.t N.

Definition acc_symb_index_map (rs:(N * symb_index_map_type)) (e:symbentry) : N * symb_index_map_type :=
  let '(index, map) := rs in
  let map' := 
      match symbentry_id e with
      | None => map
      | Some id => PTree.set id index map
      end in
  (N.succ index, map').

Definition gen_symb_index_map (stbl: symbtable) : symb_index_map_type :=
  let '(_, map) := fold_left acc_symb_index_map stbl (0%N, PTree.empty N) in
  map.

Definition reloc_ofs_map_type := ZTree.t relocentry.

Definition acc_reloc_ofs_map (e:relocentry) (rs: reloc_ofs_map_type): reloc_ofs_map_type :=
  let ofs := reloc_offset e in
  ZTree.set ofs e rs.

Definition gen_reloc_ofs_map (rtbl: reloctable) :  reloc_ofs_map_type :=
  fold_right acc_reloc_ofs_map (ZTree.empty relocentry) rtbl.

(* Definition prog_to_prog (p: program) : AST.program fundef unit := *)
(*   {| *)
(*     AST.prog_defs := prog_defs p; *)
(*     AST.prog_public := prog_public p; *)
(*     AST.prog_main := prog_main p; *)
(*   |}. *)

(* Coercion prog_to_prog : program >-> AST.program. *)

(** Section table ids *)
Definition sec_data_id     := 1%N.
Definition sec_code_id     := 2%N.
Definition sec_strtbl_id   := 3%N.
Definition sec_symbtbl_id  := 4%N.
Definition sec_rel_data_id := 5%N.
Definition sec_rel_code_id := 6%N.
Definition sec_shstrtbl_id := 7%N.

(** Ultility function s*)
Definition add_symb_to_list (t: list (ident * symbentry)) (s:symbentry) :=
  match symbentry_id s with
  | None => t
  | Some id => (id, s) :: t
  end.

Definition symbtable_to_tree (t:symbtable) : PTree.t symbentry :=
  let l := fold_left add_symb_to_list t nil in
  PTree_Properties.of_list l.

Definition acc_symb_ids (ids: list ident) (s:symbentry) :=
  match symbentry_id s with
  | None => ids
  | Some id => id :: ids
  end.

Definition get_symbentry_ids (t:symbtable) : list ident :=
  fold_left acc_symb_ids t nil.


Definition is_not_dummy_symbentry (e:symbentry) :=
  match symbentry_id e with
  | None => false
  | Some _ => true
  end.

(* Definition symbentry_id_neq (id:ident) (e:symbentry) := *)
(*   match symbentry_id e with *)
(*   | None => true *)
(*   | Some id' => if ident_eq id id' then false else true *)
(*   end. *)

Definition symbentry_id_eq (id:ident) (e:symbentry) :=
  match symbentry_id e with
  | None => false
  | Some id' => if ident_eq id id' then true else false
  end.


Lemma symbtable_to_tree_ignore_dummy: forall stbl, 
    symbtable_to_tree (dummy_symbentry :: stbl) = symbtable_to_tree stbl.
Proof.
  intros. unfold symbtable_to_tree. cbn. auto.
Qed.

Lemma add_symb_to_list_id_eq: forall id e l,
    symbentry_id_eq id e = true -> add_symb_to_list l e = (id,e)::l.
Proof.
  intros id e l EQ.
  unfold symbentry_id_eq in EQ. 
  destr_in EQ. destruct ident_eq; try congruence. subst.
  unfold add_symb_to_list. rewrite Heqo. auto.
Qed.

Lemma acc_to_list_loop: forall idstbl1 idstbl2,
    Forall (fun '(id, e) => symbentry_id_eq id e = true) idstbl1 ->
    (fold_left add_symb_to_list (map snd idstbl1) idstbl2) = (rev idstbl1) ++ idstbl2.
Proof.
  induction idstbl1 as [|ide idstbl1].
  - cbn. auto.
  - cbn. intros idstbl2 IDEQ.
    destruct ide as (id,e). 
    inv IDEQ.
    cbn.
    erewrite add_symb_to_list_id_eq; eauto.
    rewrite <- app_assoc.
    auto.
Qed.

