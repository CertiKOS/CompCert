Require Import Coqlib Integers AST Maps.
Require Import Segment.
Require Import Errors.
Require Import Memtype.
Require Import Asm SegAsmProgram TransSegAsm.
Import ListNotations.

Local Open Scope error_monad_scope.

Definition Snop_size := 1%Z.

(** * Fill in Nops for code areas added for alignment *)

Fixpoint gen_nops_iter (n:nat) (fid:ident) (segid:ident) 
         (instrs: list instr_with_info) (sz: ptrofs)
  : list instr_with_info :=
  match n with
  | O => instrs
  | S n' =>
    let sb := {| segblock_id := segid; 
                 segblock_start := sz;
                 segblock_size := (Ptrofs.repr Snop_size); 
              |} in
    let instr := (Snop, sb, fid) in
    gen_nops_iter n' fid segid (instr::instrs) 
                  (Ptrofs.add sz (Ptrofs.repr Snop_size))
  end.

Definition append_nops (fid:ident) (f: TransSegAsm.function) 
  : TransSegAsm.function :=
  let sb := fn_range f in
  let sz := (segblock_size sb) in
  let asz := (fn_actual_size f) in
  let n := Z.to_nat ((Ptrofs.unsigned asz) - (Ptrofs.unsigned sz)) in
  let nops := gen_nops_iter n fid (segblock_id sb)
                            (fn_code f) sz in
  {|
    fn_sig := fn_sig f;
    fn_code := (fn_code f) ++ nops;
    fn_range := {| segblock_id := segblock_id sb;
                   segblock_start := segblock_start sb;
                   segblock_size := asz; 
                |};
    fn_actual_size := asz;
    fn_stacksize := fn_stacksize f;
    fn_pubrange := fn_pubrange f;
  |}.

Definition transl_globdef (def: (ident * option TransSegAsm.gdef * segblock)) 
  : (ident * option TransSegAsm.gdef * segblock) :=
  let '(id,def,sb) := def in
  match def with
  | Some (Gfun (Internal f)) =>
    let f' := (append_nops id f) in
    (id, Some (Gfun (Internal f')), (fn_range f'))
  | _ => (id, def, sb)
  end.

    
Fixpoint transl_globdefs defs :=
  List.map transl_globdef defs.


(** Translation of a program *)
Definition transf_program (p:TransSegAsm.program) : program := 
  let defs := transl_globdefs (prog_defs p) in
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

