(* ******************* *)
(* Author: Yuting Wang *)
(* Date:   Jan 9, 2018 *)
(* ******************* *)

Require Import Coqlib Integers AST Maps.
Require Import Asm FlatAsm Segment.
Require Import Errors.
Require Import FlatAsmBuiltin.
Require Import Memtype.
Import ListNotations.


Local Open Scope error_monad_scope.

(** Translation from CompCert Assembly (RawAsm) to FlatAsm *)

Definition alignw:Z := 8.


Definition data_label (ofs:Z) : seglabel := (data_segid, Ptrofs.repr ofs).
Definition code_label (ofs:Z) : seglabel := (code_segid, Ptrofs.repr ofs).
(* Definition extfun_label (ofs:Z) : seglabel := (extfuns_segid, Ptrofs.repr ofs). *)

Definition default_gid_map : GID_MAP_TYPE := fun id => None.
Definition default_label_map : LABEL_MAP_TYPE :=
  fun id l => None.

Definition update_gid_map (id:ident) (l:seglabel) (map:GID_MAP_TYPE) : GID_MAP_TYPE :=
  fun id' => if peq id id' then Some l else (map id').

Definition update_label_map (id:ident) (l:Asm.label) (tl:seglabel) (map:LABEL_MAP_TYPE) : LABEL_MAP_TYPE :=
  fun id' l' => if peq id id' then (if peq l l' then Some tl else (map id' l')) else (map id' l').


Section WITH_GID_MAP.

(** A mapping from global identifiers their locations in sections 
    (i.e. pairs of section ids and offsets) *)
Variable gid_map : GID_MAP_TYPE.

(* (** * Translation of global variables *) *)

(* (** Translation init data *) *)
(* Definition transl_init_data (idata: AST.init_data) : res init_data := *)
(*   match idata with  *)
(*   | AST.Init_int8 x => OK (Init_int8 x) *)
(*   | AST.Init_int16 x => OK (Init_int16 x) *)
(*   | AST.Init_int32 x => OK (Init_int32 x) *)
(*   | AST.Init_int64 x => OK (Init_int64 x) *)
(*   | AST.Init_float32 f => OK (Init_float32 f) *)
(*   | AST.Init_float64 f => OK (Init_float64 f) *)
(*   | AST.Init_space s => OK (Init_space s) *)
(*   | AST.Init_addrof id ofs => *)
(*     match gid_map id with *)
(*     | None => Error (MSG "Transation of init data failed: unknown global id" :: nil) *)
(*     | Some l => OK (Init_addrof l ofs) *)
(*     end *)
(*   end. *)

(* Fixpoint transl_init_data_list (l : list AST.init_data) : res (list init_data) := *)
(*   match l with  *)
(*   | nil => OK nil *)
(*   | (i::l1) => *)
(*     do i' <- transl_init_data i; *)
(*     do l1' <- transl_init_data_list l1; *)
(*     OK (i'::l1') *)
(*   end. *)

(* (** Translation of a global variable *) *)
(* Definition transl_gvar {V:Type} (gvar : AST.globvar V) : res (globvar V) := *)
(*   do idata <- transl_init_data_list (AST.gvar_init gvar); *)
(*   OK ( *)
(*       mkglobvar *)
(*         V *)
(*         (AST.gvar_info gvar) *)
(*         idata *)
(*         (AST.gvar_readonly gvar) *)
(*         (AST.gvar_volatile gvar)). *)

(* (** Translation of global variables *) *)
(* Fixpoint transl_globvars (gdefs : list (ident * option (AST.globdef Asm.fundef unit))) *)
(*                          : res (list (ident * option FlatAsm.gdef * segblock)) := *)
(*   match gdefs with *)
(*   | nil => OK nil *)
(*   | ((id, None) :: gdefs') => *)
(*     transl_globvars gdefs' *)
(*   | ((_, Some (AST.Gfun _)) :: gdefs') => *)
(*     transl_globvars gdefs' *)
(*   | ((id, Some (AST.Gvar v)) :: gdefs') => *)
(*     match gid_map id with *)
(*     | None => Error (MSG "Translation of a global variable fails: no address for the variable" :: nil) *)
(*     | Some (sid,ofs) => *)
(*       let sz := AST.init_data_list_size (AST.gvar_init v) in *)
(*       let sblk := mkSegBlock sid ofs (Ptrofs.repr sz) in *)
(*       do tgdefs' <- transl_globvars gdefs'; *)
(*       do v' <- transl_gvar v; *)
(*       OK ((id, Some (Gvar v'), sblk) :: tgdefs') *)
(*     end *)
(*   end. *)

(* (* Fixpoint transl_globvars (ofs:Z) (gdefs : list (ident * option (AST.globdef Asm.fundef unit))) *) *)
(* (*                          : res (Z * list (ident * option FlatAsm.gdef * segblock)) := *) *)
(* (*   match gdefs with *) *)
(* (*   | nil => OK (ofs, nil) *) *)
(* (*   | ((id, None) :: gdefs') => *) *)
(* (*     transl_globvars ofs gdefs' *) *)
(* (*   | ((_, Some (AST.Gfun _)) :: gdefs') => *) *)
(* (*     transl_globvars ofs gdefs' *) *)
(* (*   | ((id, Some (AST.Gvar v)) :: gdefs') => *) *)
(* (*     let sz := AST.init_data_list_size (AST.gvar_init v) in *) *)
(* (*     let sblk := mkSegBlock data_segid (Ptrofs.repr ofs) (Ptrofs.repr sz) in *) *)
(* (*     let nofs := ofs+sz in *) *)
(* (*     do (fofs, tgdefs') <- transl_globvars nofs gdefs'; *) *)
(* (*     do v' <- transl_gvar v; *) *)
(* (*     OK (fofs, ((id, Some (Gvar v'), sblk) :: tgdefs')) *) *)
(* (*   end. *) *)


(* (** * Translation of instructions *) *)

(* (** Translation of addressing modes *) *)
(* Definition transl_addr_mode (m: Asm.addrmode) : res FlatAsm.addrmode := *)
(*   match m with *)
(*   | Asm.Addrmode b ofs const => *)
(*     do const' <- *)
(*     match const with *)
(*     | inl disp => OK (inl disp) *)
(*     | inr (id, ofs') =>  *)
(*       match gid_map id with *)
(*       | None => Error (MSG "An id in addressing mode is undefined" :: nil) *)
(*       | Some l => OK (inr (l, ofs')) *)
(*       end *)
(*     end; *)
(*     OK (Addrmode b ofs const') *)
(*   end. *)

(* (** Translation of builtin arguments *) *)
(* Fixpoint transl_builtin_arg {A:Type} (arg: AST.builtin_arg A) : res (builtin_arg A) := *)
(*   match arg with *)
(*   | AST.BA x => OK (BA A x) *)
(*   | AST.BA_int n => OK (BA_int A n) *)
(*   | AST.BA_long n => OK (BA_long A n) *)
(*   | AST.BA_float f => OK (BA_float A f) *)
(*   | AST.BA_single f => OK (BA_single A f) *)
(*   | AST.BA_loadstack chunk ofs => OK (BA_loadstack A chunk ofs) *)
(*   | AST.BA_addrstack ofs => OK (BA_addrstack A ofs) *)
(*   | AST.BA_loadglobal chunk id ofs =>  *)
(*     match (gid_map id) with *)
(*     | None => Error (MSG "translation of builtin arg failed" :: nil) *)
(*     | Some l => OK (BA_loadglobal A chunk l ofs) *)
(*     end *)
(*   | AST.BA_addrglobal id ofs =>  *)
(*     match (gid_map id) with *)
(*     | None => Error (MSG "translation of builtin arg failed" :: nil) *)
(*     | Some l => OK (BA_addrglobal A l ofs) *)
(*     end *)
(*   | AST.BA_splitlong hi lo =>  *)
(*     do hi' <- transl_builtin_arg hi; *)
(*     do lo' <- transl_builtin_arg lo; *)
(*     OK (BA_splitlong A hi' lo') *)
(*   end. *)

(* Fixpoint transl_builtin_args {A:Type} (args: list (AST.builtin_arg A)) : res (list (builtin_arg A)) := *)
(*   match args with *)
(*   | nil => OK nil *)
(*   | a::args1 => *)
(*     do a'<- transl_builtin_arg a; *)
(*     do args' <- transl_builtin_args args1; *)
(*     OK (a'::args') *)
(*   end. *)


Section WITH_LABEL_MAP.
(** A mapping from labels in functions to their offsets in the code section *)
Variable label_map : LABEL_MAP_TYPE.

(* Fixpoint transl_tbl (fid:ident) (tbl: list Asm.label) : res (list seglabel) := *)
(*   match tbl with *)
(*   | nil => OK nil *)
(*   | l::tbl' => *)
(*     match (label_map fid l) with *)
(*     | None => Error (MSG "Unknown label in the jump table" :: nil) *)
(*     | Some tl =>  *)
(*       do rtbl <- transl_tbl fid tbl'; *)
(*       OK (tl :: rtbl) *)
(*     end *)
(*   end. *)

(** Translation of an instruction *)



Definition transl_instr (ofs:Z) (fid: ident) (sid:segid_type) (i:Asm.instruction) : res FlatAsm.instr_with_info :=
    let sz := instr_size i in
    let sblk := mkSegBlock sid (Ptrofs.repr ofs) (Ptrofs.repr sz) in
    OK ( i, sblk, fid).

(** Translation of a sequence of instructions in a function *)
Fixpoint transl_instrs (fid:ident) (sid:segid_type) (ofs:Z) (instrs: list Asm.instruction) : res (Z * list instr_with_info) :=
  match instrs with
  | nil => OK (ofs, nil)
  | i::instrs' =>
    let sz := instr_size i in
    let nofs := ofs+sz in
    do instr <- transl_instr ofs fid sid i;
    do (fofs, tinstrs') <- transl_instrs fid sid nofs instrs';
    OK (fofs, instr :: tinstrs')
  end.

(** Tranlsation of a function *)
Definition transl_fun (fid: ident) (f:Asm.function) : res function :=
  match gid_map fid with
  | None => Error (MSG "Translation of function fails: no address for this function" :: nil)
  | Some (sid, ofs) =>
    let ofs' := Ptrofs.unsigned ofs in
    do (fofs, code') <- transl_instrs fid sid ofs' (Asm.fn_code f);
      if zle fofs Ptrofs.max_unsigned then
        (let sz := (Asm.code_size (Asm.fn_code f))  in
         let sblk := mkSegBlock sid ofs (Ptrofs.repr sz) in
         OK (mkfunction (Asm.fn_sig f) code' sblk))
      else
        Error (MSG "The size of the function exceeds limit" ::nil)
  end.


Definition transl_globdef (id:ident) (def: option (AST.globdef Asm.fundef unit)) 
  : res ((ident * option FlatAsm.gdef * segblock) * code) :=
  match def with
  | None => OK ((id, None, (mkSegBlock undef_segid Ptrofs.zero Ptrofs.zero)), nil)
  | Some (AST.Gvar v) =>
    match gid_map id with
    | None => Error (MSG "Translation of a global variable fails: no address for the variable" :: nil)
    | Some (sid,ofs) =>
      let sz := AST.init_data_list_size (AST.gvar_init v) in
      let sblk := mkSegBlock sid ofs (Ptrofs.repr sz) in
      OK ((id, Some (Gvar v), sblk), nil)
    end
  | Some (AST.Gfun f) =>
    match f with
    | External f => 
      let sblk := mkSegBlock undef_segid Ptrofs.zero Ptrofs.zero in
      OK ((id, Some (Gfun (External f)), sblk), nil)
    | Internal fd =>
      do fd' <- transl_fun id fd;
        OK ((id, Some (Gfun (Internal fd')), (fn_range fd')), (fn_code fd'))
    end
  end.

Fixpoint transl_globdefs (defs : list (ident * option (AST.globdef Asm.fundef unit))) 
  : res (list (ident * option gdef * segblock) * code) :=
  match defs with
  | nil => OK (nil, nil)
  | (id, def)::defs' =>
    do tdef_code <- transl_globdef id def;
    do (tdefs', c') <- transl_globdefs defs';
    let (tdef, c) := tdef_code in 
    OK (tdef :: tdefs', c++c')
  end.
  
(** Translation of a program *)
Definition transl_prog_with_map (p:Asm.program) (data_sz code_sz:Z): res program := 
  do (defs, code) <- transl_globdefs (AST.prog_defs p);
  OK (Build_program
        defs
        (AST.prog_public p)
        (AST.prog_main p)
        (mkSegment data_segid (Ptrofs.repr data_sz))
        (mkSegment code_segid (Ptrofs.repr code_sz), code)
        gid_map
        label_map
        (Globalenvs.Genv.to_senv (Globalenvs.Genv.globalenv p)))
      .

(* Definition transl_prog_with_map (p:Asm.program) (data_sz code_sz extfuns_sz:Z): res program :=  *)
(*   do data_defs <- transl_globvars (AST.prog_defs p); *)
(*   do (fun_defs, code) <- transl_funs (AST.prog_defs p); *)
(*   do ext_fun_defs <- transl_ext_funs (AST.prog_defs p); *)
(*   OK (Build_program *)
(*         (data_defs ++ fun_defs ++ ext_fun_defs) *)
(*         (AST.prog_public p) *)
(*         (AST.prog_main p) *)
(*         (* (mkSegment stack_segid (Ptrofs.repr Mem.stack_limit)) *) *)
(*         (mkSegment data_segid (Ptrofs.repr data_sz)) *)
(*         (mkSegment code_segid (Ptrofs.repr code_sz), code) *)
(*         (mkSegment extfuns_segid (Ptrofs.repr extfuns_sz))) *)
(*       . *)

End WITH_LABEL_MAP.

End WITH_GID_MAP.


(** * Compute mappings from global identifiers to section labels *)

(* (** Information accumulated during the translation of global data *) *)
(* Record dinfo : Type := *)
(* mkDinfo{ *)
(*   di_size : Z;           (**r The size of the data section traversed so far *) *)
(*   di_map : GID_MAP_TYPE *)
(*                           (**r The mapping from global identifiers to section labels *) *)
(* }. *)


(* (** Update the gid mapping for a single variable *) *)
(* Definition update_gvar_map {V:Type} (di: dinfo) *)
(*            (id:ident) (gvar: AST.globvar V) : dinfo := *)
(*   let sz:= AST.init_data_list_size (AST.gvar_init gvar) in *)
(*   let ofs := align (di_size di) alignw in *)
(*   mkDinfo (ofs + sz) (update_gid_map id (data_label ofs) (di_map di)). *)


(* (** Update the gid mapping for all global variables *) *)
(* Fixpoint update_gvars_map (di:dinfo) (gdefs : list (ident * option (AST.globdef Asm.fundef unit))) *)
(*                          : dinfo := *)
(*   match gdefs with *)
(*   | nil => di *)
(*   | ((id, None) :: gdefs') => *)
(*     update_gvars_map di gdefs' *)
(*   | ((_, Some (AST.Gfun _)) :: gdefs') => *)
(*     update_gvars_map di gdefs' *)
(*   | ((id, Some (AST.Gvar v)) :: gdefs') => *)
(*     let di' := update_gvar_map di id v in *)
(*     update_gvars_map di' gdefs' *)
(*   end. *)


(* (** Update the gid mapping for a single instruction *) *)
(* Record cinfo : Type := *)
(* mkCinfo{ *)
(*   ci_size : Z;           (**r The size of the code section traversed so far *) *)
(*   ci_map : GID_MAP_TYPE;  (**r The mapping from global identifiers to section labels *) *)
(*   ci_lmap : LABEL_MAP_TYPE; (**r The mapping for labels in functions *) *)
(* }. *)


(* (** Update the gid mapping for a single instruction *) *)
(* Definition update_instr_map (fid:ident) (ci:cinfo) (instr:Asm.instr_with_info) : cinfo := *)
(*   let new_lmap := *)
(*       match (fst instr) with *)
(*       | Asm.Plabel l =>  *)
(*         let ofs := ci_size ci in *)
(*         update_label_map fid l (code_label (ofs + instr_size instr)) (ci_lmap ci) *)
(*       | _ => ci_lmap ci *)
(*       end *)
(*   in *)
(*   let sz := si_size (snd instr) in *)
(*   mkCinfo (ci_size ci + sz) (ci_map ci) new_lmap. *)

(* (** Update the gid mapping for a list of instructions *) *)
(* Fixpoint update_instrs_map (fid:ident) (ci:cinfo) (instrs: list Asm.instr_with_info) : cinfo := *)
(*   match instrs with *)
(*   | nil => ci *)
(*   | i::instrs' => *)
(*     let ci' := update_instr_map fid ci i in *)
(*     update_instrs_map fid ci' instrs' *)
(*   end. *)

(* (** Update the gid mapping for all internal functions *) *)
(* Fixpoint update_funs_map (ci:cinfo) (gdefs : list (ident * option (AST.globdef Asm.fundef unit))) *)
(*                          : cinfo := *)
(*   match gdefs with *)
(*   | nil => ci *)
(*   | ((id, None) :: gdefs') => *)
(*     update_funs_map ci gdefs' *)
(*   | ((id, Some (AST.Gfun f)) :: gdefs') => *)
(*     match f with *)
(*     | External _ => update_funs_map ci gdefs' *)
(*     | Internal f => *)
(*       let ofs := align (ci_size ci) alignw in *)
(*       let ci' := mkCinfo ofs *)
(*                          (update_gid_map id (code_label ofs) (ci_map ci)) *)
(*                          (ci_lmap ci) *)
(*       in *)
(*       let ci'' := update_instrs_map id ci' (Asm.fn_code f) in *)
(*       update_funs_map ci'' gdefs' *)
(*     end *)
(*   | ((id, Some (AST.Gvar v)) :: gdefs') => *)
(*     update_funs_map ci gdefs' *)
(*   end. *)


(* (** Update the gid mapping for all external functions *) *)
(* Fixpoint update_extfuns_map (ei: dinfo) (gdefs : list (ident * option (AST.globdef Asm.fundef unit))) *)
(*   : dinfo := *)
(*   match gdefs with *)
(*   | nil => ei *)
(*   | ((id, None) :: gdefs') => *)
(*     update_extfuns_map ei gdefs' *)
(*   | ((id, Some (AST.Gfun f)) :: gdefs') => *)
(*     match f with *)
(*     | External _ =>  *)
(*       let ofs := align (di_size ei) alignw in *)
(*       let ei' := mkDinfo (ofs + alignw) *)
(*                          (update_gid_map id (extfun_label ofs) (di_map ei)) *)
(*       in *)
(*       update_extfuns_map ei' gdefs' *)
(*     | Internal f => *)
(*       update_extfuns_map ei gdefs' *)
(*     end *)
(*   | ((id, Some (AST.Gvar v)) :: gdefs') => *)
(*     update_extfuns_map ei gdefs' *)
(*   end. *)

Definition is_label (i: Asm.instruction) : option Asm.label :=
  match i with
  | Asm.Plabel l => Some l
  | _ => None
  end.

Definition update_instr (lmap: ident -> Asm.label -> option seglabel) (csize: Z) (fid: ident) (i: Asm.instruction) :=
  let csize' := csize + instr_size i in
  let lmap' :=
      match is_label i with
      | Some l => update_label_map fid l (code_label csize') lmap
      | _ => lmap
      end in
  (lmap', csize').

Definition update_instrs lmap csize fid c : LABEL_MAP_TYPE * Z :=
  fold_left (fun (ls : LABEL_MAP_TYPE * Z) i =>
               let '(lmap, csize) := ls in
               update_instr lmap csize fid i) c (lmap, csize).

Definition update_maps_def
           (gmap: ident -> option seglabel)
           (lmap: ident -> Asm.label -> option seglabel)
           (dsize csize: Z) (i: ident) (def: option (AST.globdef Asm.fundef unit)):
  (GID_MAP_TYPE * LABEL_MAP_TYPE * Z * Z) :=
  match def with
  | None => (gmap, lmap, dsize, csize)
  | Some (AST.Gvar gvar) =>
    let sz:= AST.init_data_list_size (AST.gvar_init gvar) in
    (update_gid_map i (data_label dsize) gmap, lmap, dsize + align sz alignw, csize)
  | Some (AST.Gfun (External ef)) =>  (gmap, lmap, dsize, csize)
  | Some (AST.Gfun (Internal f)) =>
    let (lmap', csize') := update_instrs lmap csize i (Asm.fn_code f) in
    (update_gid_map i (code_label csize) gmap, lmap', dsize, align csize' alignw)
  end.

Definition update_maps gmap lmap dsize csize defs : (GID_MAP_TYPE * LABEL_MAP_TYPE * Z * Z) :=
  fold_left (fun (acc : GID_MAP_TYPE * LABEL_MAP_TYPE * Z * Z)
               (id: ident * option (AST.globdef Asm.fundef unit)) =>
               let '(gmap, lmap, dsize, csize) := acc in
               let '(i,def) := id in
               update_maps_def gmap lmap dsize csize i def)
            defs (gmap, lmap, dsize, csize).

Definition make_maps (p:Asm.program) : (GID_MAP_TYPE * LABEL_MAP_TYPE * Z * Z) :=
  update_maps default_gid_map default_label_map 0 0 (AST.prog_defs p).

(* (** Update the gid and label mappings by traversing an Asm program *) *)
(* Definition update_map (p:Asm.program) : res (GID_MAP_TYPE * LABEL_MAP_TYPE * Z * Z * Z) := *)
(*   let init_di := (mkDinfo 0 default_gid_map) in *)
(*   let di := update_gvars_map init_di (AST.prog_defs p) in *)
(*   let data_seg_size := align (di_size di) alignw in *)
(*   let ei := mkDinfo 0 (di_map di) in *)
(*   let ei' := update_extfuns_map ei (AST.prog_defs p) in *)
(*   let extfuns_seg_size := align (di_size ei') alignw in *)
(*   let init_ci := mkCinfo 0 (di_map ei') default_label_map in *)
(*   let final_ci := update_funs_map init_ci (AST.prog_defs p) in *)
(*   let code_seg_size := align (ci_size final_ci) alignw in *)
(*   OK (ci_map final_ci, ci_lmap final_ci, data_seg_size, code_seg_size, extfuns_seg_size). *)


(** Check if the source program is well-formed **)
Definition no_duplicated_defs {F V: Type} (defs: list (ident * option (AST.globdef F V))) :=
  list_norepet (map fst defs).

Fixpoint labels (c: Asm.code) : list Asm.label :=
  match c with
  | [] => []
  | i :: r =>
    match is_label i with
      Some l => l :: labels r
    | None => labels r
    end
  end.

Definition no_duplicated_labels (c: Asm.code)  :=
  list_norepet (labels c).

Definition globdef_no_duplicated_labels (def: option (AST.globdef Asm.fundef unit)) :=
  match def with
  | Some (AST.Gfun (Internal f)) => no_duplicated_labels (Asm.fn_code f)
  | _ => True
  end.

Definition globdef_no_duplicated_labels_dec def : { globdef_no_duplicated_labels def } + { ~ globdef_no_duplicated_labels def }.
Proof.
  unfold globdef_no_duplicated_labels.
  repeat destr.
  apply list_norepet_dec. apply ident_eq.
Defined.

Definition defs_no_duplicated_labels (defs: list (ident * _)) :=
  Forall globdef_no_duplicated_labels (map snd defs).

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

Definition def_not_empty def : Prop :=
  match def with
  | None => True
  | Some def' => 0 < def_size def'
  end.


Definition defs_not_empty defs :=
  Forall def_not_empty defs.

Definition defs_not_empty_dec defs : { defs_not_empty defs } + { ~ defs_not_empty defs }.
Proof.
  apply Forall_dec. intros. destruct x. 
  - simpl. apply zlt.
  - simpl. left. auto.
Defined.

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
    wf_prog_not_empty: defs_not_empty (map snd (AST.prog_defs p));
    wf_prog_norepet_defs: list_norepet (map fst (AST.prog_defs p));
    wf_prog_norepet_labels: defs_no_duplicated_labels (AST.prog_defs p);
    wf_prog_main_exists: main_exists (AST.prog_main p) (AST.prog_defs p);
  }.

Definition check_wellformedness p : { wf_prog p } + { ~ wf_prog p }.
Proof.
  destruct (defs_not_empty_dec (map snd (AST.prog_defs p))).
  destruct (list_norepet_dec ident_eq (map fst (AST.prog_defs p))).
  destruct (Forall_dec _ globdef_no_duplicated_labels_dec (map snd (AST.prog_defs p))).
  destruct (main_exists_dec (AST.prog_main p) (AST.prog_defs p)).
  left; constructor; auto.
  right. inversion 1. apply n. apply wf_prog_main_exists0.
  right; inversion 1. apply n. apply wf_prog_norepet_labels0.
  right; inversion 1. apply n. apply wf_prog_norepet_defs0.
  right; inversion 1. apply n. apply wf_prog_not_empty0.
Qed.

(** The full translation *)
Definition transf_program (p:Asm.program) : res program :=
  if check_wellformedness p then
    (let r := make_maps p in
     let '(gmap,lmap,dsize,csize) := r in
     if zle (dsize + csize) Ptrofs.max_unsigned then
       transl_prog_with_map gmap lmap p dsize csize
     else
       Error (MSG "Size of segments too big" :: nil))
  else
    Error (MSG "Program not well-formed. There exists duplicated labels or definitions" :: nil). 

