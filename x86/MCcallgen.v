Require Import Coqlib Integers AST Maps.
Require Import Asm FlatAsm Segment.
Require Import Errors.
Require Import FlatAsmBuiltin.
Require Import Memtype.
Require Import FlatAsmProgram MC.
Require Import ValidLabel.
Import ListNotations.

Local Open Scope error_monad_scope.

Section WITH_GID_MAP.

Variable gmap: GID_MAP_TYPE.

Definition get_offset (fid:ident) (sb: segblock) : option ptrofs :=
  match (gmap fid) with
  | Some (s, ofs) =>
    let epos := Ptrofs.add (segblock_start sb) (segblock_size sb) in
    Some (Ptrofs.sub ofs epos)
  | None => None
  end.

Definition transl_instr (i: instruction) (sb:segblock) : instruction :=
  match i with
  | MCAsminstr (Pcall ros sg) =>
    match ros with
    | inl r => i
    | inr id => 
      match (get_offset id sb) with
      | None => i
      | Some ofs => MCshortcall ofs sg
      end
    end
  | _ => i
  end.

(** Tranlsation of an instruction *)
Definition transl_instr' (ii: instr_with_info) : instr_with_info :=
  let '(i, sb, id) := ii in
  (transl_instr i sb, sb, id).

(** Translation of a sequence of instructions in a function *)
Fixpoint transl_instrs (instrs: list instr_with_info) : list instr_with_info :=
  List.map transl_instr' instrs.


(** Tranlsation of a function *)
Definition transl_fun (f:function) : function :=
  let code' := transl_instrs (fn_code f) in
  mkfunction (fn_sig f) code' (fn_range f) (fn_stacksize f) (fn_pubrange f).

Definition transl_globdef (def: (ident * option (@FlatAsmProgram.gdef instruction) * segblock)) 
  : (ident * option (@FlatAsmProgram.gdef instruction) * segblock) :=
  let '(id,def,sb) := def in
  match def with
  | Some (AST.Gfun (Internal f)) =>
    let f' := transl_fun f in
    (id, Some (AST.Gfun (Internal f')), sb)
  | Some (AST.Gfun (External f)) => 
    (id, Some (AST.Gfun (External f)), sb)
  | Some (AST.Gvar v) =>
    (id, Some (AST.Gvar v), sb)
  | None => (id, None, sb)
  end.
    

Fixpoint transl_globdefs defs :=
  List.map transl_globdef defs.

End WITH_GID_MAP.


(** Translation of a program *)
Definition transf_program (p:MC.program) : program := 
  let defs := transl_globdefs (glob_map p) (prog_defs p) in
  (Build_program
        defs
        (prog_public p)
        (prog_main p)
        (data_seg p)
        (code_seg p)
        (glob_map p)
        (lbl_map p)
        (prog_senv p))
      .
