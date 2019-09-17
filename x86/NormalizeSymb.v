(* *******************  *)
(* Author: Yuting Wang  *)
(* Date:   Sep 16, 2019 *)
(* *******************  *)

Require Import Coqlib Integers AST Maps.
Require Import Asm.
Require Import Errors.
Require Import Memtype.
Require Import RelocProgram RelocAsm.
Import ListNotations.

Set Implicit Arguments.

Local Open Scope error_monad_scope.

(** * Normalize the indexes of symbols to sequential numbers *)

(** Create a mapping from global ids to normalized symbol indexes *)
Definition create_norm_id_mapping (stbl: symbtable) : PTree.t ident :=
  let l := PTree.elements stbl in
  let empty_map := PTree.empty ident in
  let '(map, _) := fold_left (fun '(map, nextid) '(id, e) =>
                                (PTree.set nextid id map, Pos.succ nextid)) 
                             l (empty_map, 1%positive) in
  map.


Section WITH_NORM_ID_MAPPING.

Variable idmap: PTree.t ident.

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

Definition transl_instr (sid:ident) (i:Asm.instruction) : res instr_with_info :=
  match i with
    Pallocframe _ _ _
  | Pfreeframe _ _
  | Pload_parent_pointer _ _ => Error (msg "Source program contains pseudo instructions")
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
  | Pflds_m (a: addrmode)               (**r [fld] simple precision *)
    do a' <- transl_addrmode a;
    OK (Pflds_m a')
  | Pfstps_m (a: addrmode)              (**r [fstp] simple precision *)
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
  | Pmov_rm_a (rd: ireg) (a: addrmode)  (**r like [Pmov_rm], using [Many64] chunk *)
    do a' <- transl_addrmode a;
    
  | Pmov_mr_a (a: addrmode) (rs: ireg)  (**r like [Pmov_mr], using [Many64] chunk *)
    do a' <- transl_addrmode a;
  | Pmovsd_fm_a (rd: freg) (a: addrmode) (**r like [Pmovsd_fm], using [Many64] chunk *)
    do a' <- transl_addrmode a;
  | Pmovsd_mf_a (a: addrmode) (r1: freg) (**r like [Pmovsd_mf], using [Many64] chunk *)
    do a' <- transl_addrmode a;
  | _ => OK i
  end.
