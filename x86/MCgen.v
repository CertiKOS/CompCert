Require Import Coqlib Integers AST Maps.
Require Import Asm FlatAsm Segment.
Require Import Errors.
Require Import FlatAsmBuiltin.
Require Import Memtype.
Require Import FlatAsmProgram MC.
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


Definition transl_instr (fid: ident) (i:FlatAsm.instr_with_info) : res instr_with_info :=
  let '(i',sb,id) := i in
  do mci <-
     match i' with
     | Pjmp_l l =>  
       do ofs <- get_lbl_offset fid l sb; 
         OK (MCjmp_l ofs)
     | Pjcc c l => 
       do ofs <- get_lbl_offset fid l sb; 
         OK (MCjcc c ofs)
     | Pjcc2 c1 c2 l => 
       do ofs <- get_lbl_offset fid l sb; 
         OK (MCjcc2 c1 c2 ofs)
     | Pjmptbl r tbl => 
       do ol <- get_lbl_list_offset fid tbl sb; 
         OK (MCjmptbl r ol)
     | _ =>
       OK (MCAsminstr i')
     end; 
   OK (mci , sb, id).


(** Translation of a sequence of instructions in a function *)
Fixpoint transl_instrs (fid:ident) (instrs: list FlatAsm.instr_with_info) : res (list instr_with_info) :=
  match instrs with
  | nil => OK nil
  | i::instrs' =>
    do instr <- transl_instr fid i;
    do tinstrs' <- transl_instrs fid instrs';
    OK (instr :: tinstrs')
  end.

(** Tranlsation of a function *)
Definition transl_fun (fid: ident) (f:@FlatAsmProgram.function Asm.instruction) : res function :=
  do code' <- transl_instrs fid (@fn_code Asm.instruction f);
  OK (mkfunction (fn_sig f) code' (fn_range f) (fn_stacksize f) (fn_pubrange f)).


Definition transl_globdef (def: (ident * option (@FlatAsmProgram.gdef Asm.instruction) * segblock)) 
  : res (ident * option (@FlatAsmProgram.gdef instruction) * segblock) :=
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


Definition is_valid_label_asm (lm: ident -> label -> option seglabel) (fid: ident) (i: Asm.instruction) :=
  match i with
    Pjcc _ l
  | Pjcc2 _ _ l
  | Pjmp_l l => lm fid l <> None
  | Pjmptbl _ ll =>
    Forall (fun l => lm fid l <> None) ll
  | _ => True
  end.

Definition is_valid_label (lm: LABEL_MAP_TYPE) (i: FlatAsm.instr_with_info) :=
  let '(i,_,id) := i in
  match i with
    Pjcc _ l
  | Pjcc2 _ _ l
  | Pjmp_l l => lm id l <> None
  | Pjmptbl _ ll =>
    Forall (fun l => lm id l <> None) ll
  | _ => True
  end.

Arguments is_valid_label: simpl nomatch.
Arguments is_valid_label_asm: simpl nomatch.

Definition eq_dec_neq_dec:
  forall {A} (Adec: forall a b : A, {a=b} + {a <> b}),
  forall a b : A, {a <> b} + {~ a <> b}.
Proof.
  intros.
  destruct (Adec a b); [right|left]; auto.
Defined.

Definition pair_eq:
  forall {A B} (Adec: forall a b : A, {a=b} + {a <> b}) (Bdec: forall a b : B, {a=b} + {a <> b}),
  forall a b : A * B, {a = b} + {a <> b}.
Proof.
  intros.
  destruct (Adec (fst a) (fst b)).
  destruct (Bdec (snd a) (snd b)).
  destruct a, b; simpl in *; subst; left; auto.
  right; intro C; inv C. congruence.
  right; intro C; inv C. congruence.
Defined.

Definition is_valid_label_dec: forall prog i, {is_valid_label prog i} + {~ is_valid_label prog i}.
Proof.
  destruct i as ((i & ?) & id); simpl.
  unfold is_valid_label. destr; try now left.
  apply eq_dec_neq_dec. apply option_eq.
  apply pair_eq. apply peq. apply Ptrofs.eq_dec.
  apply eq_dec_neq_dec. apply option_eq.
  apply pair_eq. apply peq. apply Ptrofs.eq_dec.
  apply eq_dec_neq_dec. apply option_eq.
  apply pair_eq. apply peq. apply Ptrofs.eq_dec.
  apply Forall_dec.  intros. apply eq_dec_neq_dec. apply option_eq.
  apply pair_eq. apply peq. apply Ptrofs.eq_dec.
Defined.

Definition check_fadef prog sbs (igs: ident * option gdef * segblock) : bool :=
  let '(i, d, _) := igs in
  match d with
    Some (Gfun (Internal f)) =>
    forallb (fun '(ins, sb1, ii) =>
               proj_sumbool (ident_eq (segblock_id sb1) (code_segid)) &&
                            proj_sumbool (ident_eq i ii) &&
                            proj_sumbool (is_valid_label_dec prog (ins, sb1, ii))
            ) (fn_code f) &&
            list_norepet_dec Values.Val.eq (map (get_instr_ptr sbs) (fn_code f))
  | _ => true
  end.

Definition check_faprog (p: FlatAsm.program) : bool :=
  forallb (check_fadef (lbl_map p) (gen_segblocks p)) (prog_defs p).

(** Translation of a program *)
Definition transf_program (p:FlatAsm.program) : res program := 
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


