Require Import Coqlib Integers AST Maps.
Require Import Asm SegAsm Segment.
Require Import Errors.
Require Import SegAsmBuiltin.
Require Import Memtype.
Require Import SegAsmProgram TransSegAsm.
Require Import ValidLabel.
Import ListNotations.

Local Open Scope error_monad_scope.

Section WITH_LABEL_MAP.
(** A mapping from labels in functions to their offsets in the code section *)
Variable label_map : LABEL_MAP_TYPE.

(** Translation of an instruction *)

Definition get_lbl_offset (fid:ident) (l:label) (sb: segblock) : res ptrofs :=
  match (label_map fid l) with
  | Some lpos =>
    let epos := Ptrofs.add (segblock_start sb) (segblock_size sb) in
    OK (Ptrofs.sub (snd lpos) epos)
  | None => Error (MSG "Inavlid label" :: nil)
  end.

Fixpoint get_lbl_list_offset (fid:ident) (l:list label) (sb: segblock) : res (list ptrofs) :=
  match l with
  | nil => OK nil
  | h::l' => 
    do ofs <- (get_lbl_offset fid h sb);
    do rst <- (get_lbl_list_offset fid l' sb);
    OK (ofs :: rst)
  end.


Definition transl_instr (fid: ident) (i:SegAsm.instr_with_info) : res instr_with_info :=
  let '(i',sb,id) := i in
  do mci <-
     match i' with
     | Pjmp_l l =>  
       do ofs <- get_lbl_offset fid l sb; 
         OK (Sjmp_l ofs)
     | Pjcc c l => 
       do ofs <- get_lbl_offset fid l sb; 
         OK (Sjcc c ofs)
     | Pjcc2 c1 c2 l => 
       do ofs <- get_lbl_offset fid l sb; 
         OK (Sjcc2 c1 c2 ofs)
     | Pjmptbl r tbl => 
       do ol <- get_lbl_list_offset fid tbl sb; 
         OK (Sjmptbl r ol)
     | _ =>
       OK (SAsminstr i')
     end; 
   OK (mci , sb, id).


(** Translation of a sequence of instructions in a function *)
Fixpoint transl_instrs (fid:ident) (instrs: list SegAsm.instr_with_info) : res (list instr_with_info) :=
  match instrs with
  | nil => OK nil
  | i::instrs' =>
    do instr <- transl_instr fid i;
    do tinstrs' <- transl_instrs fid instrs';
    OK (instr :: tinstrs')
  end.

(** Tranlsation of a function *)
Definition transl_fun (fid: ident) (f:SegAsm.function) : res function :=
  do code' <- transl_instrs fid (@fn_code Asm.instruction f);
  OK (mkfunction (fn_sig f) code' (fn_range f) (fn_actual_size f) 
                 (fn_stacksize f) (fn_pubrange f)).


Definition transl_globdef (def: (ident * option SegAsm.gdef * segblock)) 
  : res (ident * option TransSegAsm.gdef * segblock) :=
  let '(id,def,sb) := def in
  match def with
  | Some (AST.Gfun (Internal f)) =>
    do f' <- transl_fun id f;
      OK (id, Some (AST.Gfun (Internal f')), sb)
  | Some (AST.Gfun (External f)) => 
    OK (id, Some (AST.Gfun (External f)), sb)
  | Some (AST.Gvar v) =>
    OK (id, Some (AST.Gvar v), sb)
  | None => OK (id, None, sb)
  end.
    

Fixpoint transl_globdefs defs :=
  match defs with
  | nil => OK nil
  | def::defs' =>
    do tdef <- transl_globdef def;
    do tdefs' <- transl_globdefs defs';
    OK (tdef :: tdefs')
  end.

End WITH_LABEL_MAP.


(** Translation of a program *)
Definition transf_program (p:SegAsm.program) : res program := 
  assertion check_faprog p;
    assertion peq code_segid (segid (code_seg p));
    assertion eq_dec_neq_dec peq code_segid (segid (data_seg p));
  do defs <- transl_globdefs (lbl_map p) (prog_defs p);
  OK (Build_program
        defs
        (prog_public p)
        (prog_main p)
        (data_seg p)
        (code_seg p)
        (glob_map p)
        (lbl_map p)
        (prog_senv p))
      .


