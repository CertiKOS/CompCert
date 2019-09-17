(* *******************  *)
(* Author: Yuting Wang  *)
(* Date:   Sep 13, 2019 *)
(* *******************  *)

Require Import Coqlib Integers AST Maps.
Require Import Asm.
Require Import Errors.
Require Import Memtype.
Require Import RelocProgram RelocAsm.
Import ListNotations.


Set Implicit Arguments.

Local Open Scope error_monad_scope.

(** * Generation of symbol table *)

(** ** Translate the program using the symbol table *)
Section WITH_SYMB_TABLE.

Variable stbl: symbtable.

Definition transl_instr (ofs:Z) (sid:ident) (i:Asm.instruction) : res instr_with_info :=
  match i with
      Pallocframe _ _ _
    | Pfreeframe _ _
    | Pload_parent_pointer _ _ => Error (msg "Source program contains pseudo instructions")
    | _ =>
      let sz := instr_size i in
      let sblk := 
          {| 
            secblock_id := sid;
            secblock_start := ofs;
            secblock_size := sz
          |} in
      OK (i, sblk)
  end.

(** Translation of a sequence of instructions in a function *)
Fixpoint transl_instrs (sid:ident) (ofs:Z) (instrs: list Asm.instruction) : res (list instr_with_info) :=
  match instrs with
  | nil => OK nil
  | i::instrs' =>
    let sz := instr_size i in
    let nofs := ofs+sz in
    do instr <- transl_instr ofs sid i;
    do tinstrs' <- transl_instrs sid nofs instrs';
    OK (instr :: tinstrs')
  end.

(** Tranlsation of an internal function *)
Definition transl_fun (fid: ident) (f:Asm.function) : res function :=
  match PTree.get fid stbl with
  | None => Error (MSG "Translation of function fails: no symbol entry for this function" :: nil)
  | Some e =>
    (** The entry for internal function must be of type SymbFunc and 
        has a normal index pointing to the code section *)
    match symbentry_type e, symbentry_secindex e with
    | SymbFunc, secindex_normal sid =>
      let ofs := symbentry_value e in
      do code' <- transl_instrs sid ofs (Asm.fn_code f);
      OK (mkfunction (Asm.fn_sig f) code' (Asm.fn_stacksize f) (Asm.fn_pubrange f))
    | _, _ => 
      Error (msg "Translation of internal function fails: invalid symbol entry found")
    end
  end.


Definition transl_globdef (id:ident) (def: option (AST.globdef Asm.fundef unit)) 
  : res (option gdef) :=
  match def with
  | None => OK None
  | Some (AST.Gvar v) => OK (Some (Gvar v))
  | Some (AST.Gfun f) =>
    match f with
    | External f => OK (Some (Gfun (External f)))
    | Internal fd =>
      do fd' <- transl_fun id fd;
      OK (Some (Gfun (Internal fd')))
    end
  end.

Fixpoint transl_globdefs (defs : list (ident * option (AST.globdef Asm.fundef unit))) 
  : res (list (ident * option gdef)) :=
  match defs with
  | nil => OK nil
  | (id, def)::defs' =>
    do tdef <- transl_globdef id def;
    do tdefs' <- transl_globdefs defs';
    OK ((id, tdef) :: tdefs')
  end.
  
(** Translation of a program *)
Definition transl_prog (sectbl:sectable) (p:Asm.program) : res program := 
  do defs <- transl_globdefs (AST.prog_defs p);
  OK (Build_program
        defs
        (AST.prog_public p)
        (AST.prog_main p)
        sectbl
        stbl
        (PTree.empty relocentry)
        (Globalenvs.Genv.to_senv (Globalenvs.Genv.globalenv p)))
      .

End WITH_SYMB_TABLE.


(** ** Compute the symbol table *)

Section WITH_CODE_DATA_SEC.

Variables (dsec csec:ident).

Section WITH_CODE_DATA_SIZE.

Variables (dsize csize: Z).

(** get_symbol_entry takes the ids and the current sizes of data and text sections and 
    a global definition as input, and outputs the corresponding symbol entry *) 
Definition get_symbol_entry (id:ident) (def: option (AST.globdef Asm.fundef unit)) : symbentry :=
  match def with
  | None =>
    (** This is an external symbol with unknown type *)
    {|
      symbentry_id := id;
      symbentry_type := symb_notype;
      symbentry_value := 0;
      symbentry_secindex := secindex_undef 
    |}
  | Some (Gvar gvar) =>
    match AST.gvar_init gvar with
    | nil => 
      (** This is an external data symbol *)
      {|
        symbentry_id := id;
        symbentry_type := symb_data;
        symbentry_value := 0;
        symbentry_secindex := secindex_undef 
      |}
    | [Init_space sz] =>
      (** This is an external data symbol in the COMM section *)
      {|
        symbentry_id := id;
        symbentry_type := symb_data;
        symbentry_value := 8 ; (* 8 is a safe alignment for any data *)
        symbentry_secindex := secindex_comm 
      |}
    | _ =>
      (** This is an internal data symbol *)
      {|
        symbentry_id := id;
        symbentry_type := symb_data;
        symbentry_value := dsize;
        symbentry_secindex := secindex_normal dsec
      |}
    end
  | Some (Gfun (External ef)) =>
    (** This is an external function symbol *)
    {|
      symbentry_id := id;
      symbentry_type := symb_func;
      symbentry_value := 0;
      symbentry_secindex := secindex_undef
    |}
  | Some (Gfun (Internal f)) =>
    {|      
      symbentry_id := id;
      symbentry_type := symb_func;
      symbentry_value := csize;
      symbentry_secindex := secindex_normal csec
    |}
  end.

(** Update the symbol table given a global definition *)
Definition update_symbtable (stbl: symbtable) (i: ident) 
           (def: option (AST.globdef Asm.fundef unit)): symbtable :=
  let se := get_symbol_entry i def in
  PTree.set i se stbl.


(** update_code_data_size takes the current sizes of data and text
    sections and a global definition as input, and updates these sizes
    accordingly *) 
Definition update_code_data_size (def: option (AST.globdef Asm.fundef unit)) : (Z * Z) :=
  match def with
  | None => (dsize, csize)
  | Some (Gvar gvar) =>
    match gvar_init gvar with
    | nil
    | [Init_space _] => (dsize, csize)
    | l =>
      let sz := align (AST.init_data_list_size l) alignw in
      (dsize + sz, csize)
    end
  | Some (Gfun (External ef)) => (dsize, csize)
  | Some (Gfun (Internal f)) =>
    let sz := align (Asm.code_size (Asm.fn_code f)) alignw in
    (dsize, csize+sz)
  end.

End WITH_CODE_DATA_SIZE.

(** Generate the symbol and section table *)
Definition gen_symb_table defs :=
  fold_left (fun '(stbl, dsize, csize) '(id, def) => 
               let stbl' := update_symbtable dsize csize stbl id def in
               let '(dsize', csize') := update_code_data_size dsize csize def in
               (stbl', dsize', csize'))
            defs (PTree.empty symbentry, 0, 0).

End WITH_CODE_DATA_SEC.


(** Check if the source program is well-formed **)

(* Definition def_size (def: AST.globdef Asm.fundef unit) : Z := *)
(*   match def with *)
(*   | AST.Gfun (External e) => 1 *)
(*   | AST.Gfun (Internal f) => Asm.code_size (Asm.fn_code f) *)
(*   | AST.Gvar v => AST.init_data_list_size (AST.gvar_init v) *)
(*   end. *)

(* Definition odef_size (def: option (AST.globdef Asm.fundef unit)) : Z := *)
(*   match def with *)
(*   | Some def => def_size def *)
(*   | _ => 0 *)
(*   end. *)

(* Lemma def_size_pos: *)
(*   forall d, *)
(*     0 <= def_size d. *)
(* Proof. *)
(*   unfold def_size. intros. *)
(*   destr. *)
(*   destr. generalize (code_size_non_neg (Asm.fn_code f0)); omega. *)
(*   omega. *)
(*   generalize (AST.init_data_list_size_pos (AST.gvar_init v)); omega. *)
(* Qed. *)

(* Lemma odef_size_pos: *)
(*   forall d, *)
(*     0 <= odef_size d. *)
(* Proof. *)
(*   unfold odef_size. intros. *)
(*   destr. apply def_size_pos. omega. *)
(* Qed. *)

(* Definition def_not_empty def : Prop := *)
(*   match def with *)
(*   | None => True *)
(*   | Some def' => 0 < def_size def' *)
(*   end. *)


(* Definition defs_not_empty defs := *)
(*   Forall def_not_empty defs. *)

(* Definition defs_not_empty_dec defs : { defs_not_empty defs } + { ~ defs_not_empty defs }. *)
(* Proof. *)
(*   apply Forall_dec. intros. destruct x.  *)
(*   - simpl. apply zlt. *)
(*   - simpl. left. auto. *)
(* Defined. *)

Definition main_exists main (defs: list (ident * option (AST.globdef Asm.fundef unit))) :=
  Exists (fun '(id, def) => 
            main = id 
            /\ match def with
              | None => False
              | Some _ => True
              end) defs.

Definition main_exists_dec main defs : {main_exists main defs } + {~ main_exists main defs}.
Proof.
  apply Exists_dec. intros. destruct x.
  generalize (ident_eq main i). intros.
  destruct o; inv H.
  - left. auto.
  - right. inversion 1. auto.
  - right. inversion 1. auto.
  - right. inversion 1. auto.
Qed.

Record wf_prog (p:Asm.program) : Prop :=
  {
    wf_prog_no_jmp_rel : prog_no_jmp_rel p;
    wf_prog_norepet_defs: list_norepet (map fst (AST.prog_defs p));
    wf_prog_main_exists: main_exists (AST.prog_main p) (AST.prog_defs p);
  }.

Definition check_wellformedness p : { wf_prog p } + { ~ wf_prog p }.
Proof.
  destruct (prog_no_jmp_rel_dec p).
  destruct (list_norepet_dec ident_eq (map fst (AST.prog_defs p))).
  destruct (main_exists_dec (AST.prog_main p) (AST.prog_defs p)).
  left; constructor; auto.
  right. inversion 1. apply n. auto.
  right. inversion 1. apply n. auto.
  right. inversion 1. apply n. auto.
Qed.


Definition sec_data_id := 1%positive.
Definition sec_code_id := 2%positive.

(** Create the section table *)
Definition create_sec_table dsize csize :=
  let empty_tbl := PTree.empty section in
  let data_section := {| sec_type := sec_data; sec_size := dsize |} in
  let code_section := {| sec_type := sec_text; sec_size := csize |} in
  let stbl := PTree.set sec_data_id data_section empty_tbl in
  let stbl1 := PTree.set sec_code_id code_section stbl in
  stbl1.

(** The full translation *)
Definition transf_program (p:Asm.program) : res program :=
  if check_wellformedness p then
    let '(symb_tbl, dsize, csize) := gen_symb_table sec_data_id sec_code_id (AST.prog_defs p) in
    let sec_tbl := create_sec_table dsize csize in
    if zle (sections_size sec_tbl) Ptrofs.max_unsigned then 
      transl_prog symb_tbl sec_tbl p 
    else 
      Error (msg "Size of sections too big")
  else
    Error (msg "Program not well-formed").
