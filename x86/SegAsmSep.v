(* ******************* *)
(* Author: Yuting Wang *)
(* Date:   June 11, 2018 *)
(* ******************* *)

(** Separate compilation proof for the SegAsm generation **)

Require Import Coqlib Integers Values Maps AST.
Require Import Asm SegAsm SegAsmgen SegAsmProgram SegAsmgenproof.
Require Import Segment.
Require Import Linking Errors.
Require Import Num.

Open Scope Z_scope.

Definition de_transl_instr (i: SegAsm.instr_with_info) : Asm.instruction :=
  let '(i',_,_) := i in i'.
  
Definition de_transl_fun (f : @function instruction) : Asm.function :=
  let code' := List.map de_transl_instr (fn_code f) in
  Asm.mkfunction (fn_sig f) code' (fn_stacksize f) (fn_pubrange f).

Definition de_transl_globdef (def: ident * option SegAsmProgram.gdef * segblock) 
  : (ident * option (globdef Asm.fundef unit)) :=
  let '(id, def, _) := def in
  match def with
  | None => (id, None)
  | Some (Gfun (Internal f)) => (id, Some (Gfun (Internal (de_transl_fun f))))
  | Some (Gfun (External f)) => (id, Some (Gfun (External f)))
  | Some (Gvar v) => (id, Some (Gvar v))
  end.

Definition flatasm_to_asm (p:SegAsm.program) : Asm.program :=
  let prog_defs := List.map  de_transl_globdef (prog_defs p) in
  let prog_public := (prog_public p) in
  let prog_main := (prog_main p) in
  mkprogram prog_defs prog_public prog_main.

Definition link_flatasmprog (p1 p2: SegAsm.program) : option SegAsm.program :=
  match link (flatasm_to_asm p1) (flatasm_to_asm p2) with
  | None => None
  | Some p => 
    match (transf_program p) with
    | OK p' => Some p'
    | Error _ => None
    end
  end.

Instance Linker_flatasmprog : Linker SegAsm.program := {
  link := link_flatasmprog;
  linkorder := fun p1 p2 => True
}.
Proof.
  - auto.
  - auto.
  - auto.
Defined.

Axiom transf_prog_combine : 
  forall (p1 p2: Asm.program) (tp1 tp2: SegAsm.program) p
    (LK: link p1 p2 = Some p)
    (TF1: transf_program p1 = OK tp1)
    (TF2: transf_program p2 = OK tp2),
  exists tp, transf_program p = OK tp.

Lemma transl_instr_inv : forall fid sid ofs i i',
    transl_instr ofs fid sid i = OK i' ->
    de_transl_instr i' = i.
Proof.
  intros. destruct i; monadInv H; auto.
Qed.

Lemma transl_instrs_inv : forall code fid sid ofs ofs' code',
    transl_instrs fid sid ofs code = OK (ofs', code') ->
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
  intros. monadInvX H. destr_in EQ2. inv EQ2. 
  unfold de_transl_fun. simpl.
  erewrite transl_instrs_inv; eauto. 
  destruct f. auto.
Qed.

Lemma transl_globdef_inv: forall g i def def',
  transl_globdef g i def = OK def' ->
  de_transl_globdef def' = (i, def).
Proof.
  intros. destruct def. destruct g0. destruct f.
  - monadInv H. simpl.    
    erewrite transl_fun_inv; eauto.
  - monadInv H. simpl. auto.
  - monadInvX H. simpl. auto.
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

Lemma transl_prog_with_map_inv : forall g l dz cz p tp,
    transl_prog_with_map g l p dz cz = OK tp -> flatasm_to_asm tp = p.
Proof.
  intros. monadInv H. unfold flatasm_to_asm. simpl.
  erewrite transl_globdefs_inv; eauto. 
  destruct p. auto.
Qed.

Lemma transf_prog_inv : forall p tp,
    transf_program p = OK tp -> flatasm_to_asm tp = p.
Proof.
  intros. unfold transf_program in H. repeat destr_in H.  
  eapply transl_prog_with_map_inv; eauto.
Qed.

Instance TransfSegAsmLink : TransfLink match_prog.
Proof.
  red. unfold match_prog. simpl link. intros p1 p2 tp1 tp2 p LK MC1 MC2.
  inv MC1. inv MC2.
  exploit transf_prog_combine; eauto. intros H.
  destruct H as [p' TF].
  exists p'. split. unfold link_flatasmprog.
  repeat (erewrite transf_prog_inv; eauto). 
  rewrite LK. rewrite TF. auto. auto.
Defined.

