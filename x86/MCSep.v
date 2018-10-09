(* ******************* *)
(* Author: Yuting Wang *)
(* Date:   June 10, 2018 *)
(* ******************* *)

(** Separate compilation proof for the MC generation **)

Require Import Coqlib Integers Values Maps AST.
Require Import Asm FlatAsmProgram MC MCgen.
Require Import Segment.
Require Import Linking Errors FlatAsmSep.
Require Import Num.

Definition de_transl_instr (i: MC.instr_with_info) : FlatAsm.instr_with_info :=
  let '(i',sb,id) := i in 
  let i'' := 
      match i' with
      | MCjmp_l l ofs => Pjmp_l l
      | MCjcc c l ofs => Pjcc c l
      | MCjcc2 c1 c2 l ofs => Pjcc2 c1 c2 l
      | MCjmptbl r tbl ol => Pjmptbl r tbl
      | MCAsminstr i => i
      end in
  (i'', sb, id).
  
Definition de_transl_fun (f : @function MC.instruction) : @function Asm.instruction :=
  let code' := List.map de_transl_instr (fn_code f) in
  FlatAsmProgram.mkfunction (fn_sig f) code' (fn_range f) (fn_stacksize f) (fn_pubrange f).

Definition de_transl_globdef (def: ident * option FlatAsmProgram.gdef * segblock) :=
  let '(id, def, sb) := def in
  match def with
  | None => (id, None, sb)
  | Some (Gfun (Internal f)) => (id, Some (Gfun (Internal (de_transl_fun f))), sb)
  | Some (Gfun (External f)) => (id, Some (Gfun (External f)), sb)
  | Some (Gvar v) => (id, Some (Gvar v), sb)
  end.

Definition mc_to_flatasm (p:FlatAsmProgram.program) : FlatAsm.program :=
  let prog_defs := List.map de_transl_globdef (prog_defs p) in
  let prog_public := (prog_public p) in
  let prog_main := (prog_main p) in
  Build_program prog_defs prog_public prog_main 
                (data_seg p) (code_seg p) (glob_map p) (lbl_map p) (prog_senv p).

Definition link_mcprog (p1 p2: MC.program) : option MC.program :=
  match link (mc_to_flatasm p1) (mc_to_flatasm p2) with
  | None => None
  | Some p => 
    match (transf_program p) with
    | OK p' => Some p'
    | Error _ => None
    end
  end.

Instance Linker_mcprog : Linker MC.program := {
  link := link_mcprog;
  linkorder := fun p1 p2 => True
}.
Proof.
  - auto.
  - auto.
  - auto.
Defined.

Axiom transf_prog_combine : 
  forall (p1 p2: FlatAsm.program) (tp1 tp2: MC.program) p
    (LK: link p1 p2 = Some p)
    (TF1: transf_program p1 = OK tp1)
    (TF2: transf_program p2 = OK tp2),
  exists tp, transf_program p = OK tp.

Lemma transl_instr_inv : forall l fid i i',
    transl_instr l fid i = OK i' ->
    de_transl_instr i' = i.
Proof.
  intros. destruct i. destruct p. destruct i0; simpl in H; monadInv H; auto.
  monadInv EQ. auto.
  monadInv EQ. auto.
  monadInv EQ. auto.
  monadInv EQ. auto.
Qed.

Lemma transl_instrs_inv : forall l fid code code',
    transl_instrs l fid code = OK code' ->
    map de_transl_instr code' = code.
Proof.
  induction code; simpl; intros.
  - inv H. auto.
  - monadInv H. simpl. 
    erewrite transl_instr_inv; eauto.
    erewrite IHcode; eauto.
Qed.

Lemma transl_fun_inv: forall g i f f',
    transl_fun g i f = OK f' ->
    de_transl_fun f' = f.
Proof.
  intros. monadInv H. 
  unfold de_transl_fun. simpl.
  erewrite transl_instrs_inv; eauto. 
  destruct f. auto.
Qed.

Lemma transl_globdef_inv: forall l def def',
  transl_globdef l def = OK def' ->
  de_transl_globdef def' = def.
Proof.
  intros. destruct def. destruct p. destruct o. destruct g. destruct f.
  - monadInv H. simpl.    
    erewrite transl_fun_inv; eauto.
  - monadInv H. simpl. auto.
  - monadInv H. simpl. auto.
  - monadInv H. simpl. auto.
Qed.

Lemma transl_globdefs_inv: forall g defs defs',
  transl_globdefs g defs = OK defs' ->
  map de_transl_globdef defs' = defs.
Proof.
  induction defs; simpl; intros.
  - inv H. auto.
  - destruct a. monadInv H. simpl.
    erewrite transl_globdef_inv; eauto.
    erewrite IHdefs; eauto.
Qed.

Lemma transf_prog_inv : forall p tp,
    transf_program p = OK tp -> mc_to_flatasm tp = p.
Proof.
  intros. monadInv H. unfold mc_to_flatasm; simpl.
  erewrite transl_globdefs_inv; eauto. 
  destruct p; auto.
Qed.

(* Instance TransfFlatAsmLink : TransfLink match_prog. *)
(* Proof. *)
(*   red. unfold match_prog. simpl link. intros p1 p2 tp1 tp2 p LK MC1 MC2. *)
(*   inv MC1. inv MC2. *)
(*   exploit transf_prog_combine; eauto. intros H. *)
(*   destruct H as [p' TF]. *)
(*   exists p'. split. unfold link_flatasmprog. *)
(*   repeat (erewrite transf_prog_inv; eauto).  *)
(*   rewrite LK. rewrite TF. auto. auto. *)
(* Defined. *)
