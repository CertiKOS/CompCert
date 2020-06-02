(* *******************  *)
(* Author: Yuting Wang  *)
(* Date:   Sep 13, 2019 *)
(* *******************  *)

Require Import Coqlib Integers AST Maps.
Require Import Asm.
Require Import Errors.
Require Import Memtype.
Require Import RelocProgram.
Require Import CheckDef.
Import ListNotations.


Set Implicit Arguments.

Local Open Scope error_monad_scope.

Definition def_size (def: AST.globdef Asm.fundef unit) : Z :=
  match def with
  | AST.Gfun (External e) => 1
  | AST.Gfun (Internal f) => Asm.code_size (Asm.fn_code f)
  | AST.Gvar v => AST.init_data_list_size (AST.gvar_init v)
  end.

Definition odef_size (def: option (AST.globdef Asm.fundef unit)) : Z :=
  match def with
  | Some def => def_size def
  | _ => 0
  end.

Lemma def_size_pos:
  forall d,
    0 <= def_size d.
Proof.
  unfold def_size. intros.
  destr.
  destr. generalize (code_size_non_neg (Asm.fn_code f0)); omega.
  omega.
  generalize (AST.init_data_list_size_pos (AST.gvar_init v)); omega.
Qed.

Lemma odef_size_pos:
  forall d,
    0 <= odef_size d.
Proof.
  unfold odef_size. intros.
  destr. apply def_size_pos. omega.
Qed.

Definition odefs_size (defs: list (option (AST.globdef Asm.fundef unit))) : Z :=
  fold_right (fun def sz => odef_size def + sz) 0 defs.

Lemma odefs_size_pos:
  forall defs, 0 <= odefs_size defs.
Proof.
  induction defs as [|def defs].
  - cbn. omega.
  - cbn. generalize (odef_size_pos def).
    intros. apply OMEGA2; eauto.
Qed.


(** * Generation of symbol table *)


(** ** Compute the symbol table *)

Section WITH_CODE_DATA_SEC.

Variables (dsec csec:N).

Section WITH_CODE_DATA_SIZE.

Variables (dsize csize: Z).

Definition get_bind_ty id :=
  if is_def_local id then bind_local else bind_global.

(** get_symbol_entry takes the ids and the current sizes of data and text sections and 
    a global definition as input, and outputs the corresponding symbol entry *) 
Definition get_symbentry (id:ident) (def: option (AST.globdef Asm.fundef unit)) : symbentry :=
  let bindty := get_bind_ty id in
  match def with
  | None =>
    (** This is an external symbol with unknown type *)
    {|symbentry_id := id;
      symbentry_bind := bindty;
      symbentry_type := symb_notype;
      symbentry_value := 0;
      symbentry_secindex := secindex_undef;
      symbentry_size := 0;
    |}
  | Some (Gvar gvar) =>
    match AST.gvar_init gvar with
    | nil => 
      (** This is an external data symbol *)
      {|symbentry_id := id;
        symbentry_bind := bindty;
        symbentry_type := symb_data;
        symbentry_value := 0;
        symbentry_secindex := secindex_undef;
        symbentry_size := 0;
      |}
    | [Init_space sz] =>
      (** This is an external data symbol in the COMM section *)
      {|symbentry_id := id;
        symbentry_bind := bindty;
        symbentry_type := symb_data;
        symbentry_value := 8 ; (* 8 is a safe alignment for any data *)
        symbentry_secindex := secindex_comm;
        symbentry_size := Z.max sz 0;
      |}
    | _ =>
      (** This is an internal data symbol *)
      {|symbentry_id := id;
        symbentry_bind := bindty;
        symbentry_type := symb_data;
        symbentry_value := dsize;
        symbentry_secindex := secindex_normal dsec;
        symbentry_size := AST.init_data_list_size (AST.gvar_init gvar);
      |}
    end
  | Some (Gfun (External ef)) =>
    (** This is an external function symbol *)
    {|symbentry_id := id;
      symbentry_bind := bindty;
      symbentry_type := symb_func;
      symbentry_value := 0;
      symbentry_secindex := secindex_undef;
      symbentry_size := 0;
    |}
  | Some (Gfun (Internal f)) =>
    {|symbentry_id := id;
      symbentry_bind := bindty;
      symbentry_type := symb_func;
      symbentry_value := csize;
      symbentry_secindex := secindex_normal csec;
      symbentry_size := code_size (fn_code f);
    |}
  end.

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
      let sz := AST.init_data_list_size l in
      (dsize + sz, csize)
    end
  | Some (Gfun (External ef)) => (dsize, csize)
  | Some (Gfun (Internal f)) =>
    let sz := Asm.code_size (Asm.fn_code f) in
    (dsize, csize+sz)
  end.

End WITH_CODE_DATA_SIZE.

Definition acc_symb (ssize: symbtable * Z * Z) 
           (iddef: ident * option (AST.globdef Asm.fundef unit)) :=
  let '(stbl, dsize, csize) := ssize in
  let (id, def) := iddef in
  let e := get_symbentry dsize csize id def in
  let stbl' := e :: stbl in
  let '(dsize', csize') := update_code_data_size dsize csize def in
  (stbl', dsize', csize').


(** Generate the symbol and section table *)
Definition gen_symb_table defs :=
  let '(rstbl, dsize, csize) := 
      fold_left acc_symb  defs (nil, 0, 0) in
  (rev rstbl, dsize, csize).

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

Local Open Scope Z_scope.

Definition def_aligned (def:option (globdef fundef unit)) :=
  match def with
  | None => True
  | Some (Gvar v) =>
    match gvar_init v with
    | nil
    | [Init_space _] => True
    | _ => (AST.init_data_list_size (gvar_init v)) mod alignw = 0
    end
  | Some (Gfun f) =>
    match f with
    | External _ => True
    | Internal f => (code_size (fn_code f)) mod alignw = 0
    end
  end.

Lemma def_aligned_dec: forall def, {def_aligned def} + {~def_aligned def}.
Proof.
  destruct def. destruct g.
  - destruct f. 
    + simpl. decide equality; decide equality.
    + simpl. auto.
  - simpl. destruct (gvar_init v); simpl. auto.
    destruct i; try (decide equality; decide equality).
    destruct l; auto.
    decide equality; decide equality.
  - simpl. auto.
Qed.
    
Definition instr_invalid (i: instruction) := 
  match i with
  | Pjmp_l _ 
  | Pjcc _ _ 
  | Pjcc2 _ _ _ 
  | Pjmptbl _ _ 
  | Pallocframe _ _ _ 
  | Pfreeframe _ _ 
  | Pload_parent_pointer _ _ => True
  | _ => False
  end.

Definition instr_valid i := ~instr_invalid i.

Lemma instr_invalid_dec: forall i, {instr_invalid i} + {~instr_invalid i}.
Proof.
  destruct i; cbn; auto.
Qed.

Lemma instr_valid_dec: forall i, {instr_valid i} + {~instr_valid i}.
Proof.
  unfold instr_valid.
  destruct i; cbn; auto.
Qed.

Definition def_instrs_valid (def: option (globdef fundef unit)) :=
  match def with
  | None => True
  | Some (Gvar v) => True
  | Some (Gfun f) =>
    match f with
    | External _ => True
    | Internal f =>  Forall instr_valid (fn_code f)
    end
  end.

Lemma def_instrs_valid_dec: 
  forall def, {def_instrs_valid def} + {~def_instrs_valid def}.
Proof.
  destruct def. destruct g.
  - destruct f. 
    + simpl. apply Forall_dec. apply instr_valid_dec.
    + simpl. auto.
  - simpl. auto.
  - simpl. auto.
Qed.

Record wf_prog (p:Asm.program) : Prop :=
  {
    wf_prog_norepet_defs: list_norepet (map fst (AST.prog_defs p));
    wf_prog_main_exists: main_exists (AST.prog_main p) (AST.prog_defs p);
    wf_prog_defs_aligned: Forall def_aligned (map snd (AST.prog_defs p));
    wf_prog_no_local_jmps: Forall def_instrs_valid (map snd (AST.prog_defs p));
  }.

Definition check_wellformedness p : { wf_prog p } + { ~ wf_prog p }.
Proof.
  destruct (list_norepet_dec ident_eq (map fst (AST.prog_defs p))).
  destruct (main_exists_dec (AST.prog_main p) (AST.prog_defs p)).
  destruct (Forall_dec _ def_aligned_dec (map snd (AST.prog_defs p))).
  destruct (Forall_dec _ def_instrs_valid_dec (map snd (AST.prog_defs p))).
  left; constructor; auto.
  right. inversion 1. apply n. auto.
  right. inversion 1. apply n. auto.
  right. inversion 1. apply n. auto.
  right. inversion 1. apply n. auto.
Qed.


(** Create the code section *)
Definition get_def_instrs (def: option (globdef fundef unit)) : code :=
  match def with
  | Some (Gfun (Internal f)) => fn_code f
  | _ => []
  end.

Definition acc_instrs (iddef: ident * option (globdef fundef unit)) instrs :=
  let (id, def) := iddef in
  (get_def_instrs def) ++ instrs.

Definition create_code_section (defs: list (ident * option (globdef fundef unit))) : section :=
  let code := fold_right acc_instrs
                         [] defs in
  sec_text code.

(** Create the data section *)
Definition get_def_init_data (def: option (globdef fundef unit)) : list init_data :=
  match def with
  | Some (Gvar v) => 
    match (gvar_init v) with
    | nil
    | [Init_space _] => []
    | _ => gvar_init v
    end
  | _ => []
  end.

Definition acc_init_data (iddef: ident * option (globdef fundef unit)) dinit :=
  let '(id, def) := iddef in
  (get_def_init_data def) ++ dinit.

Definition create_data_section (defs: list (ident * option (globdef fundef unit))) : section :=
  let data := fold_right acc_init_data
                         [] defs in
  sec_data data.
  
Definition create_sec_table defs : sectable :=
  let data_sec := create_data_section defs in
  let code_sec := create_code_section defs in
  [data_sec; code_sec].

(** The full translation *)
Definition transf_program (p:Asm.program) : res program :=
  if check_wellformedness p then
    let '(symb_tbl, dsize, csize) := gen_symb_table sec_data_id sec_code_id (AST.prog_defs p) in
    let sec_tbl := create_sec_table (AST.prog_defs p) in
    if zle (sections_size sec_tbl) Ptrofs.max_unsigned then
      OK {| prog_defs := AST.prog_defs p;
            prog_public := AST.prog_public p;
            prog_main := AST.prog_main p;
            prog_sectable := sec_tbl;
            prog_strtable := PTree.empty Z;
            prog_symbtable := symb_tbl;
            prog_reloctables := Build_reloctable_map nil nil;
            prog_senv := Globalenvs.Genv.to_senv (Globalenvs.Genv.globalenv p)
         |}
    else 
      Error (msg "Size of sections too big")
  else
    Error (msg "Program not well-formed").
