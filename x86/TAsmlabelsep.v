(* ******************* *)
(* Author: PLDI-authors *)
(* Date:   June 10, 2018 *)
(* ******************* *)

(** Separate compilation proof for the MC generation phase 1 (elimiantion of labels) **)

Require Import Coqlib Integers Values Maps AST.
Require Import Asm FlatAsmProgram MC MClabelgen MClabelgenproof.
Require Import Segment.
Require Import Linking Errors FlatAsmSep.
Require Import Num ValidLabel.

Definition de_transl_instr (i: MC.instr_with_info) : FlatAsm.instr_with_info :=
  let '(i',sb,id) := i in 
  let l := 1%positive in
  let tbl := 1%positive :: nil in
  let i'' := 
      match i' with
      | MCjmp_l ofs => Pjmp_l l
      | MCjcc c ofs => Pjcc c l
      | MCjcc2 c1 c2 ofs => Pjcc2 c1 c2 l
      | MCjmptbl r ol => Pjmptbl r tbl
      | MCmov_rs r val => Pmov_rs r l
      | MCshortcall ofs sg => Pcall (inr l) sg
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


Lemma transl_instr_from_flat_asm_succeeds:
  forall o i s0 i1 l i1',
    is_valid_label l i1' ->
    FlatAsmgen.transl_instr o i s0 i1 = OK i1' ->
    exists ins, transl_instr l i i1' = OK ins.
Proof.
  unfold FlatAsmgen.transl_instr.
  intros o i s0 i1 l i1' H0 H1.
  repeat destr_in H1; simpl in *; eauto.
  - unfold get_lbl_offset. destr. simpl. eauto.
  - unfold get_lbl_offset. destr. simpl. eauto.
  - unfold get_lbl_offset. destr. simpl. eauto.
  - assert (forall s, exists o, get_lbl_list_offset l i tbl s = OK o).
    {
      revert H0. induction 1; simpl; intros; eauto.
      unfold get_lbl_offset. destr. simpl. edestruct IHForall as (oo & EQ); eauto.
      rewrite EQ. simpl; eauto.
    }
    edestruct H as (oo & EQ). erewrite EQ. simpl. eauto.
Qed.

Lemma transl_instrs_from_flat_asm_succeeds:
  forall i s0 c i0 x0 x1 l,
    Forall (is_valid_label l) x1 ->
    FlatAsmgen.transl_instrs i s0 i0 c = OK (x0, x1) ->
    exists ins, transl_instrs l i x1 = OK ins.
Proof.
  induction c; simpl; intros; eauto.
  inv H0; simpl; eauto.
  monadInv H0.
  simpl. inv H.
  edestruct transl_instr_from_flat_asm_succeeds as (ins & TI); eauto.
  rewrite TI. simpl.
  edestruct IHc as (inss & TIS); eauto.
  rewrite TIS. simpl; eauto.
Qed.

Lemma transl_globdef_from_flat_asm_succeeds:
  forall g l i d1 d2,
    (forall f, snd (fst d2) = Some (Gfun (Internal f)) -> Forall (is_valid_label l) (fn_code f)) ->
    FlatAsmgen.transl_globdef g i d1 = OK d2 ->
    exists d3, transl_globdef l d2 = OK d3.
Proof.
  unfold FlatAsmgen.transl_globdef, transl_globdef.
  intros g l i d1 d2 VL TG.
  repeat destr_in TG; eauto.
  monadInv H0.
  unfold FlatAsmgen.transl_fun in EQ. repeat destr_in EQ.
  monadInv H0. repeat destr_in EQ0. simpl. unfold transl_fun. simpl.
  edestruct transl_instrs_from_flat_asm_succeeds as (inss & TIS).
  simpl in VL. apply VL. eauto. eauto. simpl in TIS.
  rewrite TIS. simpl. eauto.
Qed.

Lemma
  transl_globdefs_from_flat_asm_succeeds:
  forall g l d1 d2,
    Forall (fun '(_,d,_) => forall f, d = Some (Gfun (Internal f)) -> Forall (is_valid_label l) (fn_code f)) d2 ->
    FlatAsmgen.transl_globdefs g d1 = OK d2 ->
    exists d3, transl_globdefs l d2 = OK d3.
Proof.
  induction d1; simpl; intros; eauto.
  inv H0; simpl; eauto.
  destr_in H0. monadInv H0. simpl.
  edestruct transl_globdef_from_flat_asm_succeeds as (oo & EQQ); eauto.
  inv H. repeat destr_in H2. simpl; intros; subst. simpl. eauto.
  inv H.
  edestruct IHd1 as (ins & TG); eauto. rewrite TG. rewrite EQQ. simpl; eauto.
Qed.

Lemma transl_globdefs_back:
  forall defs g tdefs x,
    FlatAsmgen.transl_globdefs g defs = OK tdefs ->
    In x tdefs ->
    exists i y, In (i,y) defs /\ FlatAsmgen.transl_globdef g i y = OK x.
Proof.
  induction defs; simpl; intros; eauto. inv H; easy.
  destr_in H. monadInv H. simpl in H0. destruct H0.
  - subst. do 2 eexists; split. left; eauto. auto.
  - edestruct IHdefs as (ii & y & IN & TG); eauto.
Qed.

Lemma update_maps_labels:
  forall defs g l c d g' l' c' d',
    list_norepet (map fst defs) ->
    (forall i, In i (map fst defs) -> forall lab, l i lab = None) ->
    FlatAsmgen.update_maps g l c d defs = (g',l',c',d') ->
    forall i lab,
      l' i lab <> None <-> (l i lab <> None \/ exists f, In (i,Some (Gfun (Internal f))) defs /\ In lab (FlatAsmgen.labels (Asm.fn_code f))).
Proof.
  induction defs; simpl; intros g l c d g' l' c' d' LNR NOLAB UM i lab.
  - inv UM. split. tauto. intros [A|(? & [] & ?)]; auto.
  - destruct a. rewrite FlatAsmgenproof.update_maps_cons in UM. repeat destr_in UM. 
    erewrite IHdefs. 4: eauto.
    split.
    + intros [A | (f & IN1 & IN2)]; eauto.
      * erewrite FlatAsmgenproof.update_lmap in A. 2: eauto.
        repeat destr_in A. subst.
        right. eexists; split. left. eauto.
        simpl in LNR. inv LNR.
        simpl in *. destr_in Heqp.
        simpl in *.
        inv Heqp.
        destruct (in_dec peq lab (FlatAsmgen.labels (Asm.fn_code f0))). auto.
        eapply FlatAsmgenproof.update_instrs_other_label in Heqp0; eauto.
        rewrite Heqp0 in A. destruct A. apply NOLAB. auto.
    + intros [A | (f & IN1 & IN2)]; eauto.
      * erewrite FlatAsmgenproof.update_lmap. 2: eauto.
        repeat destr. subst.
        simpl in *. destr_in Heqp.
        simpl in *.
        inv Heqp.
        rewrite NOLAB in A. congruence. auto.
      * destruct IN1 as [A|IN1]; eauto. inv A.
        simpl in *. repeat destr_in Heqp.
        edestruct FlatAsmgenproof.update_instrs_in_lbl as (sid & ofs & EQ); eauto.
        rewrite EQ. left; congruence.
    + inv LNR; auto.
    + intros. erewrite FlatAsmgenproof.update_lmap. 2: eauto.
      simpl in LNR. inv LNR.
      erewrite <- (NOLAB i1) with (lab := lab0); auto.
      repeat destr. 
Qed.


Lemma make_maps_labels:
  forall p g l c d,
    list_norepet (map fst (AST.prog_defs p)) ->
    FlatAsmgen.make_maps p = (g,l,c,d) ->
    forall i lab,
      l i lab <> None <-> exists f, In (i,Some (Gfun (Internal f))) (AST.prog_defs p) /\ In lab (FlatAsmgen.labels (Asm.fn_code f)).
Proof.
  unfold FlatAsmgen.make_maps. intros.
  erewrite update_maps_labels. 4: eauto.
  unfold FlatAsmgen.default_label_map. intuition tauto.
  auto.
  unfold FlatAsmgen.default_label_map. auto.
Qed.

Lemma transl_instrs_valid_label:
  forall labs i l c s0 i0 x x0,
    Forall
      (fun i1 : Asm.instruction =>
         forall lab : label, FlatAsmgen.has_label i1 lab -> In lab labs) c ->
    (forall lab : label, In lab labs -> l i lab <> None) ->
    (* list_norepet (FlatAsmgen.labels c) -> *)
    FlatAsmgen.transl_instrs i s0 i0 c = OK (x, x0) ->
    Forall (is_valid_label l) x0.
Proof.
  induction c; simpl; intros s0 i0 x x0 H H0 H1; eauto.
  inv H1. constructor.
  monadInv H1.
  inv H.
  constructor; eauto.
  - destruct a; simpl in EQ; inv EQ; simpl in *; auto.
    rewrite Forall_forall; intros; apply H0. auto.
Qed.

Lemma transl_fun_valid_label:
  forall g i f tf l,
    FlatAsmgen.transl_fun g i f = OK tf ->
    Forall (fun i => forall lab, FlatAsmgen.has_label i lab -> In lab (FlatAsmgen.labels (Asm.fn_code f)))
           (Asm.fn_code f) ->
    (forall lab,
        In lab (FlatAsmgen.labels (Asm.fn_code f)) ->
        l i lab <> None) ->
    Forall (is_valid_label l) (fn_code tf).
Proof.
  intros g i f tf l TF FC LS.
  unfold FlatAsmgen.transl_fun in TF.
  repeat destr_in TF. monadInv H0.
  repeat destr_in EQ0. simpl.
  eapply transl_instrs_valid_label. 3: eauto.
  eauto. auto.
Qed.

Lemma transf_prog_combine : 
  forall (p1 p2: FlatAsm.program) (tp1 tp2: MC.program) p
    (LK: link p1 p2 = Some p)
    (TF1: transf_program p1 = OK tp1)
    (TF2: transf_program p2 = OK tp2),
  exists tp, transf_program p = OK tp.
Proof.
  simpl.
  unfold link_flatasmprog.
  intros p1 p2 tp1 tp2 p LK TF1 TF2.
  repeat destr_in LK.
  unfold transf_program in *.
  repeat destr_in TF1. repeat destr_in TF2.
  monadInv H0. monadInv H1.
  unfold FlatAsmgen.transf_program in Heqr.
  repeat destr_in Heqr.
  rewrite pred_dec_true.
  rewrite pred_dec_true.
  replace (check_faprog p) with (true).
  unfold FlatAsmgen.transl_prog_with_map in H0.
  monadInv H0. simpl.
  cut (exists l', transl_globdefs l x1 = OK l').
  intros (l' & TG). rewrite TG; simpl; eauto.
  eapply transl_globdefs_from_flat_asm_succeeds.
  {
    rewrite Forall_forall. intros x2 IN.
    eapply transl_globdefs_back in IN. 2: eauto. simpl in IN.
    destruct IN as (i & y & IN & TG).
    repeat destr. intros; subst.
    inv w.
    pose proof (make_maps_labels _ _ _ _ _ wf_prog_norepet_defs Heqp3) as LABSPEC.
    unfold FlatAsmgen.transl_globdef in TG. repeat destr_in TG.
    monadInv H0.
    red in wf_prog_valid_labels.
    rewrite Forall_forall in wf_prog_valid_labels.
    specialize (wf_prog_valid_labels _ IN).
    simpl in wf_prog_valid_labels.
    red in wf_prog_valid_labels.
    eapply transl_fun_valid_label; eauto.
    intros. rewrite LABSPEC. eexists; split; eauto.
  }
  eauto.
  {
    erewrite FlatAsmgenproof.transf_check_faprog. auto. red. unfold FlatAsmgen.transf_program.
    rewrite pred_dec_true. rewrite Heqp3. destr. auto. auto.
  }
  unfold FlatAsmgen.transl_prog_with_map in H0. monadInv H0. simpl.
  unfold code_segid, data_segid. congruence.
  unfold FlatAsmgen.transl_prog_with_map in H0. monadInv H0. simpl.
  auto.
Qed.

Lemma transl_instr_inv : forall l fid i i',
    transl_instr l fid i = OK i' ->
    de_transl_instr i' = i.
Proof.
(*   intros. destruct i. destruct p. destruct i0; simpl in H; monadInv H; auto. *)
(*   monadInv EQ. auto. *)
(*   monadInv EQ. auto. *)
(*   monadInv EQ. auto. *)
(*   monadInv EQ. auto. *)
(* Qed. *)
Admitted.

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

Instance TransfMCLink : TransfLink match_prog.
Proof.
  red. unfold match_prog. simpl link. intros p1 p2 tp1 tp2 p LK MC1 MC2.
  exploit transf_prog_combine; eauto. intros H.
  destruct H as [p' TF].
  exists p'. split. unfold link_mcprog.
  repeat (erewrite transf_prog_inv; eauto). simpl link.
  rewrite LK. rewrite TF. auto. auto.
Defined.
