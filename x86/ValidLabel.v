Require Import Coqlib Integers AST Maps.
Require Import Asm Segment.
Require Import Errors.
Require Import FlatAsm FlatAsmProgram.
Import ListNotations.

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