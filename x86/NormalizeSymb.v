(* *******************  *)
(* Author: Yuting Wang  *)
(* Date:   Sep 16, 2019 *)
(* *******************  *)

Require Import Coqlib Integers AST Maps.
Require Import Asm.
Require Import Errors.
Require Import Memtype.
Require Import RelocProgram.
Require Import SeqTable.
Import ListNotations.

Set Implicit Arguments.

Local Open Scope error_monad_scope.

(** * Normalize the indexes of symbols to sequential numbers *)

Section WITH_NORM_ID_MAPPING.

Variable idmap: PTree.t ident.

(** ** Translation of instructions *)

Definition transl_addrmode (a:addrmode) : res addrmode :=
  let '(Addrmode base ofs const) := a in
  do const' <- 
     match const with
     | inl c => OK const
     | inr (id,ofs) =>
       match PTree.get id idmap with
       | None => Error (msg "Translation of addrmode fails: the base id is unmapped")
       | Some id' => OK (inr (id', ofs))
       end
     end;
  OK (Addrmode base ofs const').

Definition transl_instr (i:Asm.instruction) : res instruction :=
  match i with
    Pallocframe _ _ _
  | Pfreeframe _ _
  | Pload_parent_pointer _ _ => Error (msg "Source program contains pseudo instructions")
  | Pjmp_l _
  | Pjcc _ _
  | Pjcc2 _ _ _
  | Pjmptbl _ _ => Error (msg "Source program contains jumps to labels")
  | Pmov_rs rd id =>
    match PTree.get id idmap with
    | None => Error (msg "Translation of Pmov_rs failed: the source id is unmapped")
    | Some id' => OK (Pmov_rs rd id')
    end
  | Pmovl_rm rd a => 
    do a' <- transl_addrmode a;
    OK (Pmovl_rm rd a')
  | Pmovq_rm rd a =>
    do a' <- transl_addrmode a;
    OK (Pmovq_rm rd a')
  | Pmovl_mr a rs =>
    do a' <- transl_addrmode a;
    OK (Pmovl_mr a' rs)
  | Pmovq_mr a rs =>
    do a' <- transl_addrmode a;
    OK (Pmovq_mr a' rs)
  | Pmovsd_fm rd a =>
    do a' <- transl_addrmode a;
    OK (Pmovsd_fm rd a')
  | Pmovsd_mf a r1 =>
    do a' <- transl_addrmode a;
    OK (Pmovsd_mf a' r1)
  | Pmovss_fm rd a =>
    do a' <- transl_addrmode a;
    OK (Pmovss_fm rd a')
  | Pmovss_mf a r1 =>
    do a' <- transl_addrmode a;
    OK (Pmovss_mf a' r1)
  | Pfldl_m a =>               (**r [fld] double precision *)
    do a' <- transl_addrmode a;
    OK (Pfldl_m a')
  | Pfstpl_m a =>             (**r [fstp] double precision *)
    do a' <- transl_addrmode a;
    OK (Pfstpl_m a')
  | Pflds_m a =>               (**r [fld] simple precision *)
    do a' <- transl_addrmode a;
    OK (Pflds_m a')
  | Pfstps_m a =>              (**r [fstp] simple precision *)
    do a' <- transl_addrmode a;
    OK (Pfstps_m a')
  (** Moves with conversion *)
  | Pmovb_mr a rs =>    (**r [mov] (8-bit int) *)
    do a' <- transl_addrmode a;
    OK (Pmovb_mr a' rs)
  | Pmovw_mr a rs =>    (**r [mov] (16-bit int) *)
    do a' <- transl_addrmode a;
    OK (Pmovw_mr a' rs)
  | Pmovzb_rm rd a => 
    do a' <- transl_addrmode a;
    OK (Pmovzb_rm rd a')
  | Pmovsb_rm rd a =>
    do a' <- transl_addrmode a;
    OK (Pmovsb_rm rd a')
  | Pmovzw_rm rd a =>
    do a' <- transl_addrmode a;
    OK (Pmovzw_rm rd a')
  | Pmovsw_rm rd a =>
    do a' <- transl_addrmode a;
    OK (Pmovsw_rm rd a')
  (** Integer arithmetic *)
  | Pleal rd a =>
    do a' <- transl_addrmode a;
    OK (Pleal rd a')
  | Pleaq rd a =>
    do a' <- transl_addrmode a;
    OK (Pleaq rd a')
  (** Branches and calls *)
  | Pjmp (inr id) sg =>
    match PTree.get id idmap with
    | None => Error (msg "Translation of Pjmp fails: id is not mapped")
    | Some id' => OK (Pjmp (inr id') sg)
    end
  | Pcall (inr id) sg => 
    match PTree.get id idmap with
    | None => Error (msg "Translation of Pcall fails: id is not mapped")
    | Some id' => OK (Pcall (inr id') sg)
    end
  (** Saving and restoring registers *)
  | Pmov_rm_a rd a =>  (**r like [Pmov_rm], using [Many64] chunk *)
    do a' <- transl_addrmode a;
    OK (Pmov_rm_a rd a')
  | Pmov_mr_a a rs =>   (**r like [Pmov_mr], using [Many64] chunk *)
    do a' <- transl_addrmode a;
    OK (Pmov_mr_a a' rs)
  | Pmovsd_fm_a rd a => (**r like [Pmovsd_fm], using [Many64] chunk *)
    do a' <- transl_addrmode a;
    OK (Pmovsd_fm_a rd a')
  | Pmovsd_mf_a a r1 =>  (**r like [Pmovsd_mf], using [Many64] chunk *)
    do a' <- transl_addrmode a;
    OK (Pmovsd_mf_a a' r1)
  | _ => OK i
  end.

Definition transl_code (c: code) : res code :=
  fold_right (fun i r =>
                do r' <- r;
                do i' <- transl_instr i;
                OK (i' :: r'))
             (OK []) c.


(** ** Translation of global data *)

Definition transl_init_data (d:init_data) : res init_data :=
  match d with
  | Init_addrof id ofs =>
    match PTree.get id idmap with
    | None => Error (msg "Translation of Init_addrof fails: id is unmapped")
    | Some id' => OK (Init_addrof id' ofs)
    end
  | _ => OK d
  end.

Definition transl_init_data_list (d: list init_data) : res (list init_data) :=
  fold_right (fun d r =>
                do r' <- r;
                do d' <- transl_init_data d;
                OK (d' :: r'))
             (OK []) d.

Definition transl_section (sec: section) : res section :=
  do v <- 
     match sec_info_ty sec as t 
           return (interp_sec_info_type t -> res (interp_sec_info_type t)) with
     | sec_info_instr => fun c => transl_code c
     | sec_info_init_data => fun d => transl_init_data_list d
     | _=> fun i => OK i
     end (sec_info sec);
  OK {| sec_type := sec_type sec;
        sec_size := sec_size sec;
        sec_info_ty := sec_info_ty sec;
        sec_info := v;
     |}.

End WITH_NORM_ID_MAPPING.

(** ** Translation of programs *)

(** Create a mapping from global ids to normalized symbol indexes *)
Definition create_norm_id_mapping (stbl: symbtable) :=
  let empty_map := PTree.empty ident in
  let '(idmap, _) := 
      fold_left (fun '(idmap, nextid) '(id, e) =>
                    let idmap' := PTree.set id nextid idmap in
                    (idmap', Pos.succ nextid)) 
                 stbl 
                 (PTree.empty ident, 1%positive) in
  idmap.
      
Definition dummy_symbentry :=
  {| symbentry_type  := symb_notype;
     symbentry_value := 0;
     symbentry_secindex := secindex_undef;
     symbentry_size  := 0;
  |}.

(** Transform the program *)
Definition transf_program (p: program) : res program :=
  let idmap := create_norm_id_mapping (prog_symbtable p) in
  let stbl' := (1%positive, dummy_symbentry) :: (prog_symbtable p) in
  do sectbl <- 
     fold_right (fun sec r =>
                   do r' <- r;
                   do sec' <- transl_section idmap sec;
                   OK (sec' :: r'))
     (OK []) 
     (prog_sectable p);
  OK {|
      prog_defs := p.(prog_defs);
      prog_public := p.(prog_public);
      prog_main := p.(prog_main);
      prog_sectable := p.(prog_sectable);
      prog_symbtable := stbl';
      prog_reloctables := p.(prog_reloctables);
      prog_senv := p.(prog_senv);
    |}.
