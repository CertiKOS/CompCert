(* *******************  *)
(* Author: Pierre Wilke *)
(* Date:   Jan 30, 2020 *)
(* *******************  *)

Require Import Coqlib Errors.
Require Import Integers Floats AST Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Op Locations Mach Conventions Asm RealAsm.
Require Import RelocProgram RelocProgSemantics RelocProgSemantics1.
Require Import Symbtablegen.
Require Import Reloctablesgen.
Require Import SizeBoundAxioms.
Import ListNotations.
Require Import Lia.

Definition match_prog p tp :=
  exists tp',
    transf_program false p = OK tp' /\
    prog_defs tp = prog_defs tp' /\
    prog_public tp = prog_public tp' /\
    prog_main tp = prog_main tp' /\
    prog_sectable tp = prog_sectable tp' /\
    prog_symbtable tp = prog_symbtable tp' /\
    prog_strtable tp = prog_strtable tp' /\
    Permutation.Permutation
      (reloctable_code (prog_reloctables tp)) (reloctable_code (prog_reloctables tp')) /\
    Permutation.Permutation
      (reloctable_data (prog_reloctables tp)) (reloctable_data (prog_reloctables tp')) /\
    prog_senv tp = prog_senv tp'.

Lemma transf_program_match:
  forall p tp, transf_program false p = OK tp -> match_prog p tp.
Proof.
  unfold match_prog. intros. exists tp; intuition.
Qed.


Definition prog_eq prog tprog:=
  prog.(prog_defs) = tprog.(prog_defs)
  /\  prog.(prog_main) = tprog.(prog_main)
  /\ prog.(prog_public) = tprog.(prog_public)
  /\ prog.(prog_symbtable) = tprog.(prog_symbtable)
  /\ prog.(prog_senv) = tprog.(prog_senv)
  /\ prog.(prog_strtable) = tprog.(prog_strtable).

Lemma prog_tprog_prog_eq: forall prog tprog,
    transf_program false prog = OK tprog
    ->prog_eq prog tprog.
Proof.
  intros prog tprog TRANSF.
  unfold prog_eq.
  monadInv TRANSF.
  destruct list_norepet_dec; inversion EQ2.
  destruct list_norepet_dec; inversion H0.
  simpl.
  repeat split; auto.
Qed.




Lemma fold_acc_instrs_error:
  forall l sim e,
    fold_left (acc_instrs sim false) l (Error e) = Error e.
Proof.
  induction l; simpl; intros; eauto.
Qed.

Lemma acc_instrs_instr_ready: forall map c init ofs tbl i,
    fold_left (acc_instrs map false) c init = OK(ofs, tbl) ->
    In i c -> 
    ready_for_proof i = true.
Proof.
  induction c as [|i' c'].
  - cbn. intros. auto.
  - cbn. intros. inv H0; subst; eauto.
    unfold acc_instrs in H at 2. cbn in H.
    destr_in H. cbn in H.
    destruct init; cbn in H.
    + destruct p. rewrite fold_acc_instrs_error in H. congruence.
    + rewrite fold_acc_instrs_error in H. congruence.
Qed.


Lemma transf_program_instr_ready: forall c i p p',
    match_prog p p' ->
    SecTable.get sec_code_id (prog_sectable p) = Some (sec_text c) ->
    In i c ->
    ready_for_proof i = true.
Proof.
  intros c i p p' TRANSF GET IN. 
  red in TRANSF.
  destruct TRANSF. destruct H. clear H0.
  monadInv H.
  destr_in EQ2. destr_in EQ2. inv EQ2.
  unfold transl_sectable in EQ.
  destr_in EQ; try congruence. 
  destruct v; try congruence.
  destr_in EQ; try congruence.
  destr_in EQ; try congruence.
  destruct v; try congruence.
  destr_in EQ; try congruence. inv EQ.
  monadInv Heqr. inv GET.
  eapply acc_instrs_instr_ready; eauto.
Qed.


Section PRESERVATION.
  Existing Instance inject_perm_all.
Context `{external_calls_prf: ExternalCalls}.

Local Existing Instance mem_accessors_default.


Variables prog tprog: RelocProgram.program.

Hypothesis TRANSF: match_prog prog tprog.

Let ge := RelocProgSemantics.globalenv prog.
Let tge := globalenv tprog.

(* (* Given relocentry [e] and symtable [stbl], updates the mapping [m] that *)
(* associates relocation offsets with their identifiers. *) *)
(* Definition acc_reloc_ofs_symb (stbl:symbtable) (e:relocentry) (m:ZTree.t ident) : ZTree.t ident := *)
(*   match SeqTable.get (reloc_symb e) stbl with *)
(*   | None => m *)
(*   | Some s => *)
(*     match symbentry_id s with *)
(*     | None => m *)
(*     | Some id => ZTree.set (reloc_offset e) id m *)
(*     end *)
(*   end. *)

(* Definition gen_reloc_ofs_symb (stbl: symbtable) (rtbl: reloctable) : ZTree.t ident := *)
(*   fold_right (acc_reloc_ofs_symb stbl) (ZTree.empty ident) rtbl. *)

Lemma acc_reloc_ofs_symb_ok:
  forall stbl e m s id,
    SymbTable.get (reloc_symb e) stbl = Some s ->
    symbentry_id s = id ->
    Maps.ZTree.get (reloc_offset e) (acc_reloc_ofs_symb stbl e m) = Some id.
Proof.
  unfold acc_reloc_ofs_symb. intros stbl e m s id STBL ID.
  rewrite STBL, ID. rewrite Maps.ZTree.gss. auto.
Qed.

Lemma acc_reloc_ofs_symb_other:
  forall stbl e m o,
    o <> reloc_offset e ->
    Maps.ZTree.get o (acc_reloc_ofs_symb stbl e m) = Maps.ZTree.get o m.
Proof.
  unfold acc_reloc_ofs_symb. intros stbl e m o DIFF.
  destr. rewrite Maps.ZTree.gso. auto. auto.
Qed.

Lemma gen_reloc_ofs_symb_ok:
  forall stbl rtbl e s id,
    In e rtbl ->
    list_norepet (map (fun e => reloc_offset e) rtbl) ->
    SymbTable.get (reloc_symb e) stbl = Some s ->
    symbentry_id s = id ->
    Maps.ZTree.get (reloc_offset e) (gen_reloc_ofs_symb stbl rtbl) = Some id.
Proof.
  induction rtbl; simpl. easy.
  intros e s id [EQ|IN] NR STBL ID.
  - subst.
    eapply acc_reloc_ofs_symb_ok; eauto.
  - rewrite acc_reloc_ofs_symb_other.
    eapply IHrtbl; eauto. inv NR; auto.
    inv NR. intro EQ.
    apply H1.
    rewrite in_map_iff. exists e; split; eauto.
Qed.

Lemma gen_reloc_ofs_symb_other:
  forall stbl rtbl o,
    ~ In o (map reloc_offset rtbl) ->
    Maps.ZTree.get o (gen_reloc_ofs_symb stbl rtbl) = None.
Proof.
  induction rtbl; simpl. intros. rewrite Maps.ZTree.gempty. auto.
  intros o NIN.
  rewrite acc_reloc_ofs_symb_other. 2: intuition.
  apply IHrtbl. intuition.
Qed.

(* Definition add_reloc_ofs_symb (stbl: symbtable) (i:reloctable_id)  (rmap: reloctable_map) *)
(*            (ofsmap: reloctable_id -> ZTree.t ident) := *)
(*   let rtbl := get_reloctable i rmap in *)
(*   let m := gen_reloc_ofs_symb stbl rtbl in *)
(*   fun i' => if reloctable_id_eq i i' then m else ofsmap i'. *)

Lemma add_reloc_ofs_symb_diff_rtbl_id:
  forall stbl rtbl_id rtbl_id' rmap ofsmap o,
    rtbl_id <> rtbl_id' ->
    Maps.ZTree.get o ((add_reloc_ofs_symb stbl rtbl_id rmap ofsmap) rtbl_id') =
    Maps.ZTree.get o (ofsmap rtbl_id').
Proof.
  intros. unfold add_reloc_ofs_symb. destr.
Qed.

Lemma add_reloc_ofs_symb_same_rtbl_id_in:
  forall stbl rtbl_id rmap ofsmap e s id,
    let rtbl := get_reloctable rtbl_id rmap in
    In e rtbl ->
    list_norepet (map (fun e => reloc_offset e) rtbl) ->
    SymbTable.get (reloc_symb e) stbl = Some s ->
    symbentry_id s = id ->
    Maps.ZTree.get (reloc_offset e) ((add_reloc_ofs_symb stbl rtbl_id rmap ofsmap) rtbl_id) = Some id.
Proof.
  intros. unfold add_reloc_ofs_symb. destr.
  eapply gen_reloc_ofs_symb_ok; eauto.
Qed.

Lemma add_reloc_ofs_symb_same_rtbl_id_not_in:
  forall stbl rtbl_id rmap ofsmap o,
    let rtbl := get_reloctable rtbl_id rmap in
    ~ In o (map reloc_offset rtbl) ->
    Maps.ZTree.get o ((add_reloc_ofs_symb stbl rtbl_id rmap ofsmap) rtbl_id) =
    None.
Proof.
  intros. unfold add_reloc_ofs_symb. destr.
  eapply gen_reloc_ofs_symb_other; eauto.
Qed.

(* Definition gen_reloc_ofs_symbs (p:program) := *)
(*   let stbl := p.(prog_symbtable) in *)
(*   let rmap := p.(prog_reloctables) in *)
(*   let ofsmap := fun i => ZTree.empty ident in *)
(*   let ofsmap1 := add_reloc_ofs_symb stbl RELOC_DATA rmap ofsmap in *)
(*   let ofsmap2 := add_reloc_ofs_symb stbl RELOC_CODE rmap ofsmap1 in *)
(*   ofsmap2. *)

Lemma gen_reloc_ofs_symbs_ok:
  forall p rtbl_id e s id,
    let rtbl := get_reloctable rtbl_id (prog_reloctables p) in
    In e rtbl ->
    list_norepet (map reloc_offset rtbl) ->
    SymbTable.get (reloc_symb e) (prog_symbtable p) = Some s ->
    symbentry_id s = id ->
    Maps.ZTree.get (reloc_offset e) (gen_reloc_ofs_symbs p rtbl_id) = Some id.
Proof.
  intros. unfold gen_reloc_ofs_symbs.
  destruct rtbl_id.
  - eapply add_reloc_ofs_symb_same_rtbl_id_in; eauto.
  - rewrite add_reloc_ofs_symb_diff_rtbl_id; eauto. 2: congruence.
    eapply add_reloc_ofs_symb_same_rtbl_id_in; eauto.
Qed.

Lemma gen_reloc_ofs_symbs_not_in:
  forall p rtbl_id o,
    let rtbl := get_reloctable rtbl_id (prog_reloctables p) in
    ~ In o (map reloc_offset rtbl) ->
    Maps.ZTree.get o (gen_reloc_ofs_symbs p rtbl_id) = None.
Proof.
  intros. unfold gen_reloc_ofs_symbs.
  destruct rtbl_id.
  - eapply add_reloc_ofs_symb_same_rtbl_id_not_in; eauto.
  - rewrite add_reloc_ofs_symb_diff_rtbl_id; eauto. 2: congruence.
    eapply add_reloc_ofs_symb_same_rtbl_id_not_in; eauto.
Qed.

(* Definition globalenv (p: program) : Genv.t := *)
(*   let ofsmap := gen_reloc_ofs_symbs p in *)
(*   let genv1 := RelocProgSemantics.globalenv p in *)
(*   Genv.mkgenv ofsmap genv1. *)


Lemma genv_reloc_ofs_symb_ok:
  forall p rtbl_id e s id,
    let rtbl := get_reloctable rtbl_id (prog_reloctables p) in
    In e rtbl ->
    list_norepet (map reloc_offset rtbl) ->
    SymbTable.get (reloc_symb e) (prog_symbtable p) = Some s ->
    symbentry_id s = id ->
    Maps.ZTree.get (reloc_offset e) (Genv.genv_reloc_ofs_symb (globalenv p) rtbl_id) = Some id.
Proof.
  intros. unfold globalenv. simpl.
  eapply gen_reloc_ofs_symbs_ok; eauto.
Qed.

Lemma genv_reloc_ofs_symb_not_in:
  forall p rtbl_id o,
    let rtbl := get_reloctable rtbl_id (prog_reloctables p) in
    ~ In o (map reloc_offset rtbl) ->
    Maps.ZTree.get o (Genv.genv_reloc_ofs_symb (globalenv p) rtbl_id) = None.
Proof.
  intros. unfold globalenv; simpl.
  eapply gen_reloc_ofs_symbs_not_in; eauto.
Qed.

Lemma transl_sectable_ok:
  forall sim stbl creloc dreloc,
    transl_sectable sim false stbl = OK (creloc, dreloc) ->
    exists c l,
      SecTable.get sec_code_id stbl = Some (sec_text c) /\
      SecTable.get sec_data_id stbl = Some (sec_data l) /\
      transl_code sim false c = OK creloc /\
      transl_init_data_list sim l = OK dreloc.
Proof.
  unfold transl_sectable. intros sim stbl creloc dreloc TRANSL.
  repeat destr_in TRANSL. do 2 eexists; eauto.
Qed.

Lemma transl_init_data_ok:
  forall sim dofs id ofs dreloc,
    transl_init_data sim dofs (Init_addrof id ofs) = OK dreloc ->
    exists idx,
      Maps.PTree.get id sim = Some idx /\
      dreloc = [ {| reloc_offset := dofs; reloc_type := reloc_abs; reloc_symb := idx; reloc_addend := Ptrofs.unsigned ofs |}].
Proof.
  unfold transl_init_data.
  intros sim dofs id ofs dreloc TID.
  destr_in TID. inv TID.
  eexists; split; eauto.
Qed.

Lemma transl_init_data_nil:
  forall sim dofs d,
    (forall id ofs, d <> Init_addrof id ofs) ->
    transl_init_data sim dofs d = OK [].
Proof.
  unfold transl_init_data.
  intros sim dofs d NO. destr.
Qed.

Lemma acc_init_data_ok:
  forall sim ofs l d ofs' l',
    acc_init_data sim (OK (ofs, l)) d = OK (ofs', l') ->
    exists d',
      transl_init_data sim ofs d = OK d' /\
      ofs' = ofs + init_data_size d /\ l' = d' ++ l.
Proof.
  intros sim ofs l d ofs' l' AID.
  unfold acc_init_data in AID.
  monadInv AID. destr_in EQ0.
  monadInv EQ0. inv EQ. eauto.
Qed.

Lemma transl_init_data_translate:
  forall sim ofs d,
    transl_init_data sim ofs d =
    bind (transl_init_data sim 0 d) (fun rtbl =>
                                       OK (map (fun d => {|
                                                reloc_offset := reloc_offset d + ofs;
                                                reloc_type := reloc_type d;
                                                reloc_symb := reloc_symb d;
                                                reloc_addend := reloc_addend d
                                              |}) rtbl)).
Proof.
  intros sim ofs d.
  unfold transl_init_data.
  destr. destr.
Qed.

Lemma fold_acc_init_data_error:
  forall sim l e,
    fold_left (acc_init_data sim) l (Error e) = Error e.
Proof.
  induction l ; simpl; intros; eauto.
Qed.

Lemma fold_acc_init_data_ok:
  forall sim l ofs rtbl,
  fold_left (acc_init_data sim) l (OK (ofs, rtbl)) =
  bind (fold_left (acc_init_data sim) l (OK (0, [])))
       (fun '(ofs', rtbl') =>
          OK (ofs + ofs', map (fun d => {|
                                   reloc_offset := reloc_offset d + ofs;
                                   reloc_type := reloc_type d;
                                   reloc_symb := reloc_symb d;
                                   reloc_addend := reloc_addend d
                                 |}) rtbl' ++ rtbl)).
Proof.
  induction l; simpl; intros; eauto. repeat f_equal. omega.
  rewrite transl_init_data_translate.
  destruct (transl_init_data sim 0 a) eqn:?; simpl; auto.
  - rewrite (IHl (ofs + init_data_size a)).
    rewrite (IHl (init_data_size a)).
    destruct (fold_left (acc_init_data sim) l (OK (0, []))); simpl; auto.
    destr. simpl.
    f_equal. f_equal. omega. simpl.
    simpl.
    rewrite ! app_assoc.
    f_equal. rewrite app_nil_r.
    rewrite list_append_map. f_equal.
    rewrite map_map. simpl.
    apply list_map_exten. intros. f_equal. omega.
  - rewrite fold_acc_init_data_error. simpl. reflexivity.
Qed.

Lemma fold_acc_init_data_not_in:
  forall sim l ofs rtbl ofs' rtbl',
    fold_left (acc_init_data sim) l (OK (ofs, rtbl)) = OK (ofs', rtbl') ->
    forall x, In x rtbl -> In x rtbl'.
Proof.
  induction l; simpl; intros; eauto.
  inv H. auto.
  destruct (transl_init_data sim ofs a); simpl in *.
  eapply IHl. eauto. rewrite in_app. auto.
  rewrite fold_acc_init_data_error in H; easy.
Qed.

Lemma transl_init_data_list_ok:
  forall sim l dreloc l1 id o l2 symb_idx,
    transl_init_data_list sim l = OK dreloc ->
    l = l1 ++ Init_addrof id o :: l2 ->
    Maps.PTree.get id sim = Some symb_idx ->
    exists e ofs rtbl',
      In e dreloc /\
      fold_left (acc_init_data sim) l1 (OK (0, [])) = OK (ofs, rtbl') /\
      reloc_offset e = ofs /\
      reloc_type e = reloc_abs /\
      reloc_symb e = symb_idx /\
      reloc_addend e = Ptrofs.unsigned o.
Proof.
  intros sim l dreloc l1 id o l2 symb_idx TIDL SPLIT SYMB.
  unfold transl_init_data_list in TIDL.
  subst.
  rewrite fold_left_app in TIDL.
  monadInv TIDL.
  destruct (fold_left (acc_init_data sim) l1 (OK (0, []))) eqn:?.
  2: rewrite fold_acc_init_data_error in EQ; simpl in EQ; easy.
  destr_in EQ0. inv EQ0.
  simpl in EQ. destr_in EQ.
  rewrite SYMB in EQ. simpl in EQ.
  do 3 eexists. split. eapply fold_acc_init_data_not_in. apply EQ. left. reflexivity. simpl.
  split. eauto. auto.
Qed.


Lemma symb_address_ok:
  forall i b o ofs,
  RelocProgSemantics.Genv.find_symbol ge i = Some (b, o) ->
  RelocProgSemantics.Genv.symbol_address ge i ofs = Vptr b (Ptrofs.add ofs o).
Proof.
  intros.
  unfold RelocProgSemantics.Genv.symbol_address. rewrite H. auto.
Qed.

Lemma add_external_global_symb_unchanged:
  forall t e ge tge,
    Genv.genv_symb ge = Genv.genv_symb tge ->
    Genv.genv_next ge = Genv.genv_next tge ->
    Genv.genv_symb (add_external_global t ge e) =
    Genv.genv_symb (add_external_global t tge e) /\
    Genv.genv_next (add_external_global t ge e) =
    Genv.genv_next (add_external_global t tge e).
Proof.
  unfold add_external_global.
  intros. destr. simpl. split; congruence.
Qed.

Lemma add_external_globals_symb_unchanged:
  forall t stbl ge tge,
    Genv.genv_symb ge = Genv.genv_symb tge ->
    Genv.genv_next ge = Genv.genv_next tge ->
    Genv.genv_symb (add_external_globals t ge stbl) =
    Genv.genv_symb (add_external_globals t tge stbl) /\
    Genv.genv_next (add_external_globals t ge stbl) =
    Genv.genv_next (add_external_globals t tge stbl)
.
Proof.
  induction stbl; simpl; intros; eauto.
  apply IHstbl.
  apply add_external_global_symb_unchanged; auto.
  apply add_external_global_symb_unchanged; auto.
Qed.

Lemma genv_symb_ok:
  Genv.genv_symb (RelocProgSemantics.globalenv prog) =
  Genv.genv_symb (RelocProgSemantics.globalenv tprog).
Proof.
  unfold match_prog in TRANSF.
  decompose [ex and] TRANSF.
  unfold transf_program in H0.
  monadInv H0.
  repeat destr_in EQ2.
  unfold RelocProgSemantics.globalenv. simpl. simpl in *.
  rewrite H, H4, H3.
  apply add_external_globals_symb_unchanged. simpl. auto. simpl. auto.
Qed.

Lemma symb_address_2:
  forall e i
         idx idofs b o s,
    let rtbl := reloctable_data (prog_reloctables tprog) in
    In e rtbl ->
    list_norepet reloc_offset ## rtbl ->
    SymbTable.get idx (prog_symbtable tprog) = Some s ->
    symbentry_id s = i ->
    (* Maps.PTree.get i sim = Some idx -> *)
    reloc_symb e = idx ->
    reloc_offset e = idofs ->
    RelocProgSemantics.Genv.find_symbol ge i = Some (b, o) ->
    Genv.find_symbol tge RELOC_DATA idofs = Some (b, o).
Proof.
  unfold Genv.find_symbol.
  intros.
  subst. unfold tge. erewrite genv_reloc_ofs_symb_ok. all: eauto.
  unfold globalenv. simpl.
  revert H5.
  unfold RelocProgSemantics.Genv.find_symbol.
  unfold ge.
  rewrite genv_symb_ok. auto.
Qed.

Lemma nr_defs:
  list_norepet (map fst (prog_defs tprog)).
Proof.
  unfold match_prog in TRANSF.
  decompose [ex and] TRANSF.
  unfold transf_program in H0.
  monadInv H0.
  repeat destr_in EQ2.
  rewrite H. simpl; auto.
Qed.


Lemma genv_symb_add_external_global:
  forall t ge se id b o,
    Maps.PTree.get id (Genv.genv_symb (add_external_global t ge se)) = Some (b,o) ->
    Maps.PTree.get id (Genv.genv_symb ge) = Some (b,o) \/
    (symbentry_id se =  id /\ is_symbentry_internal se = false /\ b = Genv.genv_next ge /\ o = Ptrofs.zero).
Proof.
  unfold add_external_global. simpl. intros.
  destr_in H.
  rewrite Maps.PTree.gsspec in H.
  destr_in H.
Qed.

Require Import Lia.

Lemma genv_symb_add_external_globals:
  forall t stbl ge id b o,
    Maps.PTree.get id (Genv.genv_symb (add_external_globals t ge stbl)) = Some (b,o) ->
    Maps.PTree.get id (Genv.genv_symb ge) = Some (b,o) \/
    (exists se l1 l2,
        stbl = l1 ++ se :: l2 /\
        symbentry_id se = id /\
        is_symbentry_internal se = false /\
        b = Pos.of_nat (Pos.to_nat (Genv.genv_next ge) + length (filter (fun s => negb (is_symbentry_internal s)) l1)) /\
        o = Ptrofs.zero
    ).
Proof.
  induction stbl. simpl. auto.
  simpl. intros.
  eapply IHstbl in H.
  destruct H.
  - apply genv_symb_add_external_global in H. destruct H; auto.
    decompose [and] H.
    right. eexists; exists nil; eexists; split. simpl. reflexivity.
    repeat split; auto. simpl. rewrite Nat.add_0_r.
    rewrite Pos2Nat.id. auto.
  - destruct H as (se & l1 & l2 & SPLIT & EQ & EXT & B & O).
    right; exists se; exists (a::l1); exists l2; repeat split; auto.
    subst. simpl. reflexivity.
    subst.
    apply Nat2Pos.inj_iff. lia. lia.
    unfold add_external_global. simpl.
    destr. simpl.
    lia.
Qed.

Lemma fold_acc_symb_map_in_stbl:
  forall (id : positive) (stbl : symbtable) t0 (b : block) (o : ptrofs),
  Maps.PTree.get id (fold_right acc_symb_map t0 stbl) = Some (b, o) ->
  (exists se : symbentry, In se stbl /\ symbentry_id se = id) \/
  Maps.PTree.get id t0 = Some (b, o).
Proof.
  induction stbl; simpl; intros; eauto.
  unfold acc_symb_map in H at 1.
  destr_in H.
  - rewrite Maps.PTree.gsspec in H. destr_in H.
    inv H.
    left; eexists; split; eauto. eapply IHstbl in H; eauto.
    destruct H; eauto. decompose [ex and] H. eauto.
  - eapply IHstbl in H; eauto.
    destruct H; eauto. decompose [ex and] H. eauto.
  - eapply IHstbl in H; eauto.
    destruct H; eauto. decompose [ex and] H. eauto.
Qed.

Lemma gen_symb_map_in_stbl:
  forall id stbl b o,
    Maps.PTree.get id (gen_symb_map stbl) = Some (b, o) ->
    exists se, In se stbl /\ symbentry_id se = id.
Proof.
  unfold gen_symb_map.
  intros.
  edestruct fold_acc_symb_map_in_stbl; eauto.
  rewrite Maps.PTree.gempty in H0. congruence.
Qed.

(* Can be more precise if needed *)
Lemma genv_symb_in_defs:
  forall p id b o,
    Maps.PTree.get id (Genv.genv_symb (RelocProgSemantics.globalenv p)) = Some (b,o) ->
    (exists se,
        In se (prog_symbtable p) /\
        symbentry_id se = id
    ).
Proof.
  unfold RelocProgSemantics.globalenv.
  intros.
  eapply genv_symb_add_external_globals in H.
  destruct H.
  simpl in H.
  - eapply gen_symb_map_in_stbl; eauto.
  - simpl in H. decompose [ex and] H; eauto.
    eexists; split; eauto.
    rewrite H1. rewrite in_app. right. left. reflexivity.
Qed.

Lemma prog_symtable_same:
  prog_symbtable prog = prog_symbtable tprog.
Proof.
  unfold match_prog in TRANSF.
  decompose [ex and] TRANSF.
  unfold transf_program in H0.
  monadInv H0.
  repeat destr_in EQ2.
  rewrite H4. simpl; auto.
Qed.

Lemma symb_address_has_symtable_entry:
  forall i b o,
    RelocProgSemantics.Genv.find_symbol ge i = Some (b, o) ->
    exists idx s,
      SymbTable.get idx (prog_symbtable tprog) = Some s /\
      symbentry_id s = i /\
      idx <> N0.
Proof.
  intros i b o FS.
  unfold SymbTable.get.
  rewrite <- prog_symtable_same.
  unfold RelocProgSemantics.Genv.find_symbol in FS.
  edestruct genv_symb_in_defs as (se & IN & ID); eauto.
  destruct (In_nth_error _ _ IN).
  exists (N.add SymbTblParams.ofs (N.of_nat x)); eexists.
  split; eauto. rewrite <- H. f_equal.
  unfold SymbTable.idx.
  rewrite N.add_comm.
  rewrite <- N.add_sub_assoc. 2: apply N.le_refl.
  rewrite N.sub_diag. rewrite N.add_0_r.
  rewrite Nnat.Nat2N.id. eauto.
  split; auto.
  unfold SymbTblParams.ofs. lia.
Qed.

Lemma fold_acc_symb_index_map_acc:
  forall stbl i t0 t1 n ofs ofs',
    (* list_norepet (map symbentry_id stbl) -> *)
    ~ In (i) (map symbentry_id stbl) ->
    Maps.PTree.get i t0 = Some n ->
    fold_left acc_symb_index_map stbl (ofs, t0) = (ofs', t1) ->
  Maps.PTree.get i t1 = Some n.
Proof.
  induction stbl; simpl; intros i t0 t1 n ofs ofs' NR GET FL.
  - inv FL. auto.
  - eapply IHstbl. 3: eauto. intuition.
    rewrite Maps.PTree.gso; auto.
Qed.

Lemma fold_acc_symb_index_map_ok:
  forall (stbl1 stbl stbl2 : list symbentry) (e : symbentry) (i : ident) ofs t0,
  stbl = stbl1 ++ e :: stbl2 ->
  symbentry_id e = i ->
  list_norepet (map symbentry_id stbl) ->
  exists n junk,
    fold_left acc_symb_index_map stbl1 (ofs, t0) = (n, junk) /\
    Maps.PTree.get i
                   (let '(_, map) := fold_left acc_symb_index_map stbl (ofs, t0) in map) =
    Some n.
Proof.
  induction stbl1; simpl; intros; eauto.
  - (do 2 eexists); split; eauto. subst. simpl. destr.
    erewrite fold_acc_symb_index_map_acc; eauto. simpl in H1.
    inv H1.
    intro IN; apply H2. auto.
    rewrite Maps.PTree.gss. auto.
  - destruct stbl. inv H. inv H. simpl.
    eapply IHstbl1. eauto. auto.
    simpl in H1. inv H1; auto.
Qed.

Lemma gen_symb_index_map_ok:
  forall stbl stbl1 stbl2 e i,
  stbl = stbl1 ++ e :: stbl2 ->
  symbentry_id e = i ->
  list_norepet (map symbentry_id stbl) ->
  exists n junk,
    fold_left acc_symb_index_map stbl1 (SymbTblParams.ofs, Maps.PTree.empty _) = (n, junk) /\
    Maps.PTree.get i (gen_symb_index_map stbl) = Some n.
Proof.
  unfold gen_symb_index_map.
  intros. eapply fold_acc_symb_index_map_ok; eauto.
Qed.


Lemma fold_acc_sym_len:
  forall stbl1 o t0 n junk,
    fold_left acc_symb_index_map stbl1 (o, t0) = (n, junk) ->
    n = N.add (N.of_nat (length stbl1)) o.
Proof.
  induction stbl1; intros; eauto.
  simpl in H; inv H. auto.
  simpl in H. eapply IHstbl1 in H. subst.
  simpl length.
  lia.
Qed.

Lemma nth_error_nodup:
  forall {T U} (l: list T) n1 n2 x y (f: T -> U),
  nth_error l n1 = Some x ->
  nth_error l n2 = Some y ->
  list_norepet f ## l ->
  f x = f y ->
  n1 = n2.
Proof.
  induction l; simpl; intros; eauto.
  rewrite nth_error_nil in H. easy.
  destruct n1, n2; simpl in *; auto.
  - inv H. exfalso. inv H1. apply H4.
    rewrite in_map_iff. exists y; split; auto.
    eapply nth_error_in; eauto.
  - inv H0. exfalso. inv H1. apply H4.
    rewrite in_map_iff. exists x; split; auto.
    eapply nth_error_in; eauto.
  - f_equal. eapply IHl; eauto. inv H1; eauto.
Qed.

Lemma transl_init_data_ok_all_symbs_in_sim:
  forall i0 i1 init sim rdata,
    In (Init_addrof i0 i1) init ->
    transl_init_data_list sim init = OK rdata ->
    Maps.PTree.get i0 sim <> None.
Proof.
  unfold transl_init_data_list.
  intros i0 i1 init sim rdata IN.
  generalize (OK (0, @nil RelocTblParams.V)).
  revert init rdata IN.
  induction init; simpl; intros; eauto.
  monadInv H. destr_in EQ0. inv EQ0.
  destruct IN.
  - subst.
    unfold acc_init_data at 2 in EQ.
    destruct r; simpl in EQ. repeat destr_in EQ.
    rewrite fold_acc_init_data_error in H0. congruence.
    rewrite fold_acc_init_data_error in H0. congruence.
    rewrite fold_acc_init_data_error in EQ. congruence.
  - eapply IHinit. auto. rewrite EQ. simpl. reflexivity.
Qed.

Lemma in_acc_symb_index_map_in_stbl:
  forall (i0 : positive) (stbl : symbtable) o map o' map',
    fold_left acc_symb_index_map stbl (o, map) = (o', map') ->
    Maps.PTree.get i0 map' <> None ->
    Maps.PTree.get i0 map <> None \/
    exists s : symbentry, In s stbl /\ symbentry_id s = i0.
Proof.
  induction stbl; simpl; intros; eauto. inv H. auto.
  eapply IHstbl in H.
  destruct H.
  rewrite Maps.PTree.gsspec in H. destr_in H. subst. right; eauto.
  destruct H as (s & IN & ID); eauto. auto.
Qed.

Lemma symbtable_cons:
  forall n a l s,
    (SymbTblParams.ofs <= n)%N ->
    SymbTable.get n l = Some s ->
    SymbTable.get (N.succ n) (a::l) = Some s.
Proof.
  unfold SymbTable.get.
  unfold SymbTable.idx.
  intros.
  rewrite N.sub_succ_l. 2: lia.
  rewrite Nnat.N2Nat.inj_succ. simpl. auto.
Qed.

Lemma in_acc_symb_index_map_in_stbl_nth:
  forall (i0 : positive) (stbl : symbtable) o map o' map' n,
    fold_left acc_symb_index_map stbl (o, map) = (o', map') ->
    N.le SymbTblParams.ofs o ->
    (forall i n, Maps.PTree.get i map = Some n -> N.lt n o /\ N.le SymbTblParams.ofs n) ->
    Maps.PTree.get i0 map' = Some n ->
    (N.lt n o /\ Maps.PTree.get i0 map = Some n) \/
    (N.le o n /\ exists s : symbentry,
        nth_error stbl (N.to_nat (N.sub n o)) = Some s /\
        symbentry_id s = i0).
Proof.
  induction stbl; simpl; intros; eauto.
  - inv H. left. split; eauto. eapply H1; eauto.
  - exploit IHstbl. eauto.
    + lia.
    + intros i n0. rewrite Maps.PTree.gsspec.
      destr.
      * intro A; inv A. split. lia. lia.
      * intro A; apply H1 in A. intuition lia.
    + eauto.
    + intros [(LT & GET) | (GT & s & GET & EQ)].
      * rewrite Maps.PTree.gsspec in GET. repeat destr_in GET.
        -- right. split. lia. exists a; split; auto. rewrite N.sub_diag. reflexivity.
        -- left; split; eauto. eapply H1; eauto.
      * right; split. lia. exists s; split; auto.
        replace (n - o)%N with (N.succ (n - N.succ o)). 2: lia.
        rewrite Nnat.N2Nat.inj_succ. simpl. auto.
Qed.

Lemma in_sim_in_stbl:
  forall i0 stbl,
    Maps.PTree.get i0 (gen_symb_index_map stbl) <> None ->
    exists s, In s stbl /\ symbentry_id s = i0.
Proof.
  unfold gen_symb_index_map. intros. destr_in H.
  eapply in_acc_symb_index_map_in_stbl in H; eauto.
  rewrite Maps.PTree.gempty in H. intuition congruence.
Qed.

Lemma in_sim_in_stbl_nth:
  forall i0 stbl n,
    Maps.PTree.get i0 (gen_symb_index_map stbl) = Some n ->
    exists s, SymbTable.get n stbl = Some s /\ symbentry_id s = i0.
Proof.
  unfold gen_symb_index_map. intros. destr_in H.
  eapply in_acc_symb_index_map_in_stbl_nth in H; eauto.
  - rewrite Maps.PTree.gempty in H.
    destruct H. intuition congruence.
    decompose [and ex] H. clear H.
    eexists; split; eauto.
  - lia.
  - intros i n1. rewrite Maps.PTree.gempty; congruence.
Qed.

Lemma in_stbl_in_gen_symb_map:
  forall s i0 i stbl,
    In s stbl ->
    symbentry_id s = i0 ->
    symbentry_secindex s = secindex_normal i ->
    Maps.PTree.get i0 (gen_symb_map stbl) <> None.
Proof.
  unfold gen_symb_map.
  intros s i0 i stbl.
  generalize (Maps.PTree.empty (block * ptrofs)).
  revert stbl.
  induction stbl; simpl; intros; eauto.
  destruct H.
  - subst.
    unfold acc_symb_map at 1. rewrite H1.
    rewrite Maps.PTree.gss. congruence.
  - specialize (IHstbl t H H0 H1).
    unfold acc_symb_map at 1.
    destr.
    rewrite Maps.PTree.gsspec. destr.
Qed.

Lemma add_external_globals_acc:
  forall stbl ge i0 extfuns,
    Maps.PTree.get i0 (Genv.genv_symb ge) <> None ->
    Maps.PTree.get i0 (Genv.genv_symb (add_external_globals extfuns ge stbl)) <> None.
Proof.
  induction stbl; simpl; intros; eauto.
  apply IHstbl.
  unfold add_external_global.
  destr. simpl.
  rewrite Maps.PTree.gsspec. destr.
Qed.

Lemma in_stbl_external_in_genv_symb:
  forall s i0 extfuns stbl ge,
    In s stbl ->
    symbentry_id s = i0 ->
    is_symbentry_internal s = false ->
    Maps.PTree.get i0 (Genv.genv_symb (add_external_globals extfuns ge stbl)) <> None.
Proof.
  induction stbl; simpl; intros; eauto.
  destruct H.
  - subst.
    apply add_external_globals_acc.
    unfold add_external_global. simpl.
    rewrite H1.
    rewrite Maps.PTree.gss. congruence.
  - eauto.
Qed.

Lemma in_stbl_in_genv_symb:
  forall s i0,
    In s (prog_symbtable prog) ->
    symbentry_id s = i0 ->
    Maps.PTree.get i0 (Genv.genv_symb ge) <> None.
Proof.
  intros.
  unfold ge. unfold RelocProgSemantics.globalenv.
  destruct (is_symbentry_internal s) eqn:INT.
  - apply add_external_globals_acc. simpl.
    unfold is_symbentry_internal in INT. destr_in INT.
    eapply in_stbl_in_gen_symb_map; eauto.
  - eapply in_stbl_external_in_genv_symb; eauto.
Qed.

Lemma in_sim_find_symbol_not_none:
  forall i0,
    Maps.PTree.get i0 (gen_symb_index_map (prog_symbtable prog)) <> None ->
    RelocProgSemantics.Genv.find_symbol ge i0 <> None.
Proof.
  unfold RelocProgSemantics.Genv.find_symbol.
  intros.
  edestruct in_sim_in_stbl as (s & IN & ID); eauto.
  eapply in_stbl_in_genv_symb; eauto.
Qed.

Lemma norepet_symbentry_id:
  list_norepet symbentry_id ## (prog_symbtable tprog).
Proof.
  unfold match_prog in TRANSF.
  decompose [ex and] TRANSF.
  unfold transf_program in H0.
  monadInv H0.
  repeat destr_in EQ2.
  rewrite H4. simpl; auto.
Qed.

Lemma transl_init_data_norepet:
  forall sim z0 a r,
    transl_init_data sim z0 a = OK r ->
    list_norepet reloc_offset ## r.
Proof.
  destruct a; simpl; intros; inv H; simpl ; try econstructor.
  repeat destr_in H1. simpl. repeat constructor. easy.
Qed.

Lemma transl_init_data_range:
  forall sim z0 a r,
    transl_init_data sim z0 a = OK r ->
    Forall (fun e => z0 <= reloc_offset e < z0 + init_data_size a) r.
Proof.
  destruct a; simpl; intros; inv H; simpl ; try econstructor.
  repeat destr_in H1. constructor. 2: constructor.
  simpl. destr; omega.
Qed.

Lemma norepet_fold_acc_init_data:
  forall sim init z0 rdata0 z1 rdata1,
    list_norepet reloc_offset ## rdata0 ->
    Forall (fun e => reloc_offset e < z0) rdata0 ->
    fold_left (acc_init_data sim) init (OK (z0, rdata0)) = OK (z1, rdata1) ->
    list_norepet reloc_offset ## rdata1.
Proof.
  induction init; simpl; intros z0 rdata0 z1 rdata1 NR0 LT0 FL; eauto.
  - inv FL; auto.
  - destruct (transl_init_data sim z0 a) eqn:TID.
    + simpl in *.
      exploit IHinit. 3: eauto.
      * rewrite map_app. rewrite list_norepet_app.
        split; [|split]; auto.
        eapply transl_init_data_norepet; eauto.
        red. intros.
        intro EQ; subst.
        rewrite Forall_forall in LT0.
        apply transl_init_data_range in TID.
        rewrite Forall_forall in TID.
        rewrite in_map_iff in H, H0.
        decompose [ex and] H.
        decompose [ex and] H0. subst.
        specialize (LT0 _ H5).
        specialize (TID _ H3).
        omega.
      * rewrite Forall_forall. intros x. rewrite in_app.
        apply transl_init_data_range in TID.
        rewrite Forall_forall in LT0, TID.
        destruct 1. apply TID in H. omega.
        apply LT0 in H. generalize (init_data_size_pos a). omega.
      * auto.
    + simpl in FL. rewrite fold_acc_init_data_error in FL. congruence.
Qed.

Lemma norepet_reloctables:
  forall sim init rdata,
    transl_init_data_list sim init = OK rdata ->
    list_norepet reloc_offset ## rdata.
Proof.
  unfold transl_init_data_list. intros.
  monadInv H. repeat destr_in EQ0.
  eapply norepet_fold_acc_init_data; eauto. constructor.
Qed.

Lemma store_init_data_ok:
  forall i m b o m' l1 l2 rtbl init dreloc,
    let sim := gen_symb_index_map (prog_symbtable prog) in
    init = l1 ++ i :: l2 ->
    transl_init_data_list sim init = OK dreloc ->
    Permutation.Permutation dreloc (reloctable_data (prog_reloctables tprog)) ->
    fold_left (acc_init_data sim) l1 (OK (0, [])) = OK (o, rtbl) ->
    RelocProgSemantics.store_init_data ge m b o i = Some m' ->
    store_init_data tge m b o i = Some m'.
Proof.
  intros i m b o m' l1 l2 rtbl init dreloc sim SPLIT TIDL PERM FOLD SID.
  unfold RelocProgSemantics.store_init_data, store_init_data in *.
  destr_in SID.
  unfold RelocProgSemantics.Genv.symbol_address in SID.
  unfold Genv.symbol_address.
  destr_in SID. destr_in SID.
  edestruct symb_address_has_symtable_entry as (idx & s & GET & ID & idxPOS). eauto.
  edestruct in_split as (stbl1 & stbl2 & EQ). eapply nth_error_In.
  unfold SymbTable.get in GET. apply GET.
  edestruct gen_symb_index_map_ok as (n & junk & FL & SYMGET). eauto. eauto.
  eapply norepet_symbentry_id.
  edestruct transl_init_data_list_ok as (e & ofs & rtbl' & INreloc & FL2 & ROFS & TYP & RSYM & RADD).
  3: eauto. eauto. eauto.
  rewrite <- prog_symtable_same. fold sim. apply TIDL. eauto.
  exploit fold_acc_sym_len. apply FL. intro Neq.
  exploit (@nth_error_nodup). exact GET.
  rewrite EQ. rewrite nth_error_app2. instantiate (2:= length stbl1).
  rewrite Nat.sub_diag. reflexivity. omega.
  instantiate (1:= symbentry_id).
  exact norepet_symbentry_id. congruence. intro idxEQ.
  erewrite symb_address_2. eauto. 3: eauto.
  eapply Permutation.Permutation_in. eauto. eauto.
  eauto.
  eapply LocalLib.Permutation_pres_list_norepet.
  eapply norepet_reloctables. eauto. apply Permutation.Permutation_map. eauto.
  eauto.  3: eauto.
  rewrite RSYM. rewrite Neq.
  setoid_rewrite <- idxEQ. unfold SymbTable.idx. rewrite Nnat.N2Nat.id.
  unfold SymbTblParams.ofs. lia.
  rewrite ROFS.
  revert FL2 FOLD. rewrite <- prog_symtable_same. fold sim.
  congruence.
  eapply in_sim_find_symbol_not_none in Heqo0. easy.
  eapply transl_init_data_ok_all_symbs_in_sim. 2: eauto. rewrite SPLIT.
  apply in_app. right. left. reflexivity.
Qed.

Lemma transl_init_data_list_inv:
  forall sim init dreloc a,
    transl_init_data_list sim init = OK dreloc ->
    In a init ->
    exists o ri, transl_init_data sim o a = OK ri.
Proof.
  unfold transl_init_data_list.
  intros sim init dreloc a.
  generalize (OK (0, @nil RelocTblParams.V)).
  revert init dreloc a.
  induction init; simpl; intros; eauto. easy.
  destruct H0; subst; eauto.
  unfold acc_init_data at 2 in H.
  monadInv H. repeat destr_in EQ0.
  destruct r; simpl in *; eauto.
  destruct p; simpl in *; eauto.
  destruct (transl_init_data sim z0 a0) eqn:?; simpl in *.
  eauto.
  rewrite fold_acc_init_data_error in EQ; congruence.
  rewrite fold_acc_init_data_error in EQ; congruence.
Qed.


Lemma store_init_data_list_ok:
  forall i m b o m' init l1 rtbl dreloc,
    let sim := gen_symb_index_map (prog_symbtable prog) in
    init = l1 ++ i ->
    transl_init_data_list sim init = OK dreloc ->
    Permutation.Permutation dreloc (reloctable_data (prog_reloctables tprog)) ->
    fold_left (acc_init_data sim) l1 (OK (0, [])) = OK (o, rtbl) ->
    RelocProgSemantics.store_init_data_list ge m b o i = Some m' ->
    store_init_data_list tge m b o i = Some m'.
Proof.
  induction i; simpl; intros; eauto.
  destr_in H3.
  erewrite store_init_data_ok.
  3: eauto. 2: eauto. 3: eauto. 3: eauto. 2: auto.
  edestruct (transl_init_data_list_inv) as (oo & ri & TID). apply H0. subst.
  rewrite in_app; right; left; eauto.
  rewrite transl_init_data_translate in TID.
  monadInv TID.
  eapply IHi. 2: eauto. instantiate (1:=l1 ++ a :: nil). rewrite <- app_assoc. simpl. auto.
  eauto.
  rewrite fold_left_app. rewrite H2. simpl.
  rewrite transl_init_data_translate, EQ. simpl.
  f_equal.  auto.
Qed.

Lemma prog_sectable_eq:
  exists init c c' creloc dreloc,
    prog_sectable prog = [sec_data init; sec_text c] /\
    transl_code' false c = OK c' /\
    transl_code (gen_symb_index_map (prog_symbtable prog)) false c = OK creloc /\
    Permutation.Permutation creloc (reloctable_code (prog_reloctables tprog)) /\
    0 <= code_size c' < Ptrofs.max_unsigned /\
    prog_sectable tprog = [sec_data init; sec_text c'] /\
    transl_init_data_list (gen_symb_index_map (prog_symbtable prog)) init = OK dreloc /\
    Permutation.Permutation dreloc (reloctable_data (prog_reloctables tprog)).
Proof.
  unfold match_prog in TRANSF.
  decompose [ex and] TRANSF.
  unfold transf_program in H0.
  monadInv H0. simpl in *.
  repeat destr_in EQ2.
  exploit transl_sectable_ok. eauto.
  intros (c & ll & CODE & DATA & TCODE & TDATA).
  unfold transl_sectable' in EQ1. repeat destr_in EQ1. monadInv H8.
  repeat destr_in EQ1. simpl.
  (do 5 eexists). split. eauto. split. eauto.
  split. vm_compute in CODE. inv CODE. eauto.
  split. apply Permutation.Permutation_sym. auto.
  split. split. generalize (code_size_non_neg x); lia. auto.
  split. eauto.
  split. vm_compute in DATA. inv DATA. eauto.
  apply Permutation.Permutation_sym. auto.
Qed.

Lemma alloc_data_section_ok:
  forall m0 m,
    RelocProgSemantics.alloc_data_section ge (prog_sectable prog) m0 = Some m ->
    alloc_data_section tge (prog_sectable tprog) m0 = Some m.
Proof.
  intros m0 m ADS.
  unfold RelocProgSemantics.alloc_data_section, alloc_data_section in *.
  repeat destr_in ADS.
  destruct (prog_sectable_eq) as (init' & c & c' & creloc & dreloc & PS1 & TC & TC' & PERMc & CodeRng &PS2 & TIDL & PERMd).
  rewrite PS2. simpl.
  rewrite PS1 in Heqo. vm_compute in Heqo. inv Heqo.
  simpl in *.
  rewrite Heqp. rewrite Heqo0.
  erewrite store_init_data_list_ok; eauto. rewrite app_nil_l. auto. reflexivity.
Qed.

Lemma code_size_app:
  forall l1 l2,
    code_size (l1 ++ l2) = code_size l1 + code_size l2.
Proof.
  induction l1; simpl; intros; eauto. rewrite IHl1. omega.
Qed.

Lemma code_size_rev:
  forall l,
    code_size l = code_size(rev l).
Proof.
  induction l; simpl; intros; eauto.
  rewrite code_size_app. rewrite IHl. simpl. omega.
Qed.

Lemma id_eliminate_size:
  forall i1 i2,
    id_eliminate' i1 = OK i2 ->
    instr_size i1 = instr_size i2.
Proof.
  intros i1 i2 IE.
  unfold id_eliminate' in IE.
  repeat destr_in IE; simpl; auto.
Qed.

Lemma fold_acc_id_eliminate_error:
  forall c e,
    fold_left (acc_id_eliminate false) c (Error e) = Error e.
Proof.
  induction c; simpl; intros; eauto.
Qed.

Lemma transl_code_fold_size:
  forall c r x,
    fold_left (acc_id_eliminate false) c (OK r) = OK x ->
    code_size (rev x) = code_size (r) + code_size c.
Proof.
  induction c; simpl; intros; eauto. inv H. rewrite <- code_size_rev. omega.
  destruct (ready_for_proof a).
  destruct (id_eliminate' a) eqn:?.
  simpl in H.
  apply IHc in H. rewrite H. simpl.
  apply id_eliminate_size in Heqr0; rewrite Heqr0. omega.
  simpl in H. rewrite fold_acc_id_eliminate_error in H; congruence.
  cbn [bind] in H.
  generalize (fold_acc_id_eliminate_error c  ([MSG (instr_to_string a);
                                               MSG " not ready for id_eliminate"])).
  intros HError.
  rewrite HError in H. inversion H.
Qed.

Lemma transl_code_size:
  forall c c',
    transl_code' false c = OK c' ->
    code_size c' = code_size c.
Proof.
  unfold transl_code'.
  intros c c' FL.
  monadInv FL.
  erewrite transl_code_fold_size; eauto. simpl. omega.
Qed.

Lemma alloc_code_section_ok:
  forall m0 m,
    RelocProgSemantics.alloc_code_section (prog_sectable prog) m0 = Some m ->
    alloc_code_section (prog_sectable tprog) m0 = Some m.
Proof.
  intros m0 m ACS.
  unfold RelocProgSemantics.alloc_code_section, alloc_code_section in *.
  repeat destr_in ACS.
  destruct (prog_sectable_eq) as (init' & c & c' & dreloc & creloc & PS1 & TC & TC' &
                                  PERMc & CodeRng & PS2 & TIDL & PERMd).
  rewrite PS2. simpl.
  rewrite PS1 in Heqo. vm_compute in Heqo. inv Heqo.
  erewrite transl_code_size; eauto.
  simpl in *.
  rewrite Heqp. auto.
Qed.

Lemma alloc_external_symbol_ok:
  forall m1 s m2,
    RelocProgSemantics.alloc_external_symbol m1 s = Some m2 ->
    alloc_external_symbol m1 s = Some m2.
Proof.
  unfold RelocProgSemantics.alloc_external_symbol.
  unfold alloc_external_symbol.
  intros.
  repeat destr_in H.
Qed.

Lemma alloc_external_symbols_ok:
  forall m1 m2,
    RelocProgSemantics.alloc_external_symbols m1 (prog_symbtable prog) = Some m2 ->
    alloc_external_symbols m1 (prog_symbtable tprog) = Some m2.
Proof.
  rewrite prog_symtable_same.
  generalize (prog_symbtable tprog).
  induction s; simpl; intros; eauto.
  destr_in H.
  erewrite alloc_external_symbol_ok; eauto.
Qed.

Lemma init_mem_ok:
  forall m,
    RelocProgSemantics.init_mem prog = Some m ->
    init_mem tprog = Some m.
Proof.
  intros m IM.
  unfold RelocProgSemantics.init_mem, init_mem in *.
  repeat destr_in IM.
  erewrite alloc_data_section_ok; eauto.
  erewrite alloc_code_section_ok; eauto.
  rewrite H0.
  eapply alloc_external_symbols_ok; eauto.
Qed.

Lemma main_preserved:
  prog_main prog = prog_main tprog.
Proof.
  unfold match_prog in TRANSF.
  decompose [ex and] TRANSF. clear TRANSF.
  unfold transf_program in H0.
  monadInv H0. simpl in *. repeat destr_in EQ2. simpl in *. congruence.
Qed.

Lemma main_ok:
  RelocProgSemantics.Genv.symbol_address ge (prog_main prog) Ptrofs.zero =
  RelocProgSemantics.Genv.symbol_address (Genv.genv_genv tge) (prog_main tprog) Ptrofs.zero.
Proof.
  rewrite main_preserved.
  unfold RelocProgSemantics.Genv.symbol_address.
  unfold tge.
  unfold ge.
  unfold globalenv. simpl.
  unfold RelocProgSemantics.Genv.find_symbol.
  rewrite genv_symb_ok. auto.
Qed.

Lemma defs_preserved:
  prog_defs prog = prog_defs tprog.
Proof.
  unfold match_prog in TRANSF.
  decompose [ex and] TRANSF. clear TRANSF.
  unfold transf_program in H0.
  monadInv H0. repeat destr_in EQ2. simpl in *. congruence.
Qed.

Lemma ext_funs_add_external_global:
  forall efs s ge1 ge2,
    Genv.genv_ext_funs ge1 = Genv.genv_ext_funs ge2 ->
    Genv.genv_next ge1 = Genv.genv_next ge2 ->
    Genv.genv_ext_funs (add_external_global efs ge1 s) =
    Genv.genv_ext_funs (add_external_global efs ge2 s) /\
    Genv.genv_next (add_external_global efs ge1 s) =
    Genv.genv_next (add_external_global efs ge2 s).
Proof.
  unfold add_external_global. intros.
  repeat destr; simpl; intuition congruence.
Qed.

Lemma ext_funs_add_external_globals:
  forall efs stbl ge1 ge2,
    Genv.genv_ext_funs ge1 = Genv.genv_ext_funs ge2 ->
    Genv.genv_next ge1 = Genv.genv_next ge2 ->
    Genv.genv_ext_funs (add_external_globals efs ge1 stbl) =
    Genv.genv_ext_funs (add_external_globals efs ge2 stbl) /\
    Genv.genv_next (add_external_globals efs ge1 stbl) =
    Genv.genv_next (add_external_globals efs ge2 stbl).
Proof.
  induction stbl; simpl; intros; eauto.
  exploit ext_funs_add_external_global; eauto. intros (A & B).
  apply IHstbl; eauto.
Qed.

Lemma find_ext_funct_ok:
  forall v,
  RelocProgSemantics.Genv.find_ext_funct ge v =
  Genv.find_ext_funct tge v.
Proof.
  unfold Genv.find_ext_funct, RelocProgSemantics.Genv.find_ext_funct.
  intros. destr.
  unfold tge, globalenv. simpl. unfold ge.
  unfold RelocProgSemantics.globalenv.
  f_equal.
  rewrite defs_preserved.
  rewrite prog_symtable_same.
  apply ext_funs_add_external_globals; reflexivity.
Qed.


Lemma instrs_add_external_global:
  forall efs s ge1,
    Genv.genv_instrs (add_external_global efs ge1 s) = Genv.genv_instrs ge1.
Proof.
  unfold add_external_global. intros.
  repeat destr.
Qed.

Lemma instrs_add_external_globals:
  forall efs stbl ge1,
    Genv.genv_instrs (add_external_globals efs ge1 stbl) =
    Genv.genv_instrs ge1.
Proof.
  induction stbl; simpl; intros; eauto.
  erewrite IHstbl. erewrite instrs_add_external_global; eauto.
Qed.

Lemma fold_acc_id_eliminate_app:
  forall c c0,
    fold_left (acc_id_eliminate false) c (OK c0) =
    bind (fold_left (acc_id_eliminate false) c (OK [])) (fun c1 => OK (c1 ++ c0)).
Proof.
  induction c; simpl; intros; eauto.
  destruct (ready_for_proof a).
  destruct (id_eliminate' a) eqn:?.
  simpl.
  rewrite (IHc (i::c0)).
  rewrite (IHc ([i])).
  destruct (fold_left (acc_id_eliminate false) c (OK [])) eqn:?.
  simpl. rewrite <- app_assoc. simpl. reflexivity.
  simpl. auto.
  simpl. rewrite ! fold_acc_id_eliminate_error. reflexivity.
  destruct (id_eliminate' a) eqn:?.
  simpl. rewrite ! fold_acc_id_eliminate_error. simpl. auto.
  simpl. rewrite ! fold_acc_id_eliminate_error. simpl. auto.
Qed.

Lemma gen_instr_map_ok:
  forall c ofs0 map0 map0' ofs1 ofs1' map1 map1' c1
         (REC:
            forall iofs i,
              map0 iofs = Some i ->
              exists i', map0' iofs = Some i' /\ id_eliminate' i = OK i'
         )
         iofs i
         (GenInstrMap: fold_left acc_instr_map c (ofs0, map0) = (ofs1, map1))
         (SrcInstr: map1 iofs = Some i)
         (TranslCode: fold_left (acc_id_eliminate false) c (OK []) = OK (c1))
         (TgtGenInstrMap: fold_left acc_instr_map (rev c1) (ofs0, map0') = (ofs1', map1')),
  ofs1 = ofs1' /\ exists i', map1' iofs = Some i' /\ id_eliminate' i = OK i'.
Proof.
  induction c; simpl; intros; eauto.
  - inv TranslCode. inv GenInstrMap.
    simpl in TgtGenInstrMap. inv TgtGenInstrMap.
    (* apply (f_equal (@length _)) in H0. rewrite app_length in H0. *)
    (* assert (length c1 = O) by omega. destruct c1. simpl in H1. inv H1; auto. *)
    (* simpl in H. omega. *)
    eauto.
  -
    destruct (ready_for_proof a).
    destruct (id_eliminate' a) eqn:?.
    + simpl in TranslCode.
      rewrite fold_acc_id_eliminate_app in TranslCode. monadInv TranslCode.
      subst.
      rewrite rev_app_distr in TgtGenInstrMap. simpl in TgtGenInstrMap.
      eapply IHc. 2: eauto. 2: eauto. 2: eauto.
      2: erewrite id_eliminate_size; eauto.
      simpl.
      intros. destr_in H. inv H. eauto. eauto.
    + simpl in TranslCode.
      rewrite fold_acc_id_eliminate_error in TranslCode. congruence.
    +
      cbn [bind] in TranslCode.
      rewrite fold_acc_id_eliminate_error in TranslCode. inversion TranslCode.
Qed.


Lemma find_instr_ok:
  forall v i,
  RelocProgSemantics.Genv.find_instr ge v = Some i ->
  exists i',
    Genv.find_instr tge v = Some i' /\
    id_eliminate' i = OK i'.
Proof.
  unfold Genv.find_instr.
  unfold tge.
  unfold globalenv. simpl.
  unfold RelocProgSemantics.Genv.find_instr.
  intros. destr.
  unfold ge in H.
  unfold RelocProgSemantics.globalenv in *.
  rewrite instrs_add_external_globals in *. simpl in *.
  destruct (prog_sectable_eq) as (init & c & c' & creloc & dreloc & PS1 & TC & TC' &
                                  PERMc & CodeRng & PS2 & TIDL & PERMd).
  rewrite PS1, PS2 in *.
  simpl in *.
  unfold gen_instr_map, transl_code' in *.
  destr_in H. monadInv TC. destr.
  intros.
  eapply gen_instr_map_ok. 3: apply H. 2: eauto. 3: eauto. 2: eauto.
  simpl. easy.
Qed.


Definition addrmode_reloc_id (a:addrmode) : res ident :=
  let '(Addrmode base ofs const) := a in
  match const with
  | inr (id, _) => OK id
  | _ => Error (msg "addrmode_reloc_id")
  end.

Definition instr_reloc_id (i:instruction) : res ident :=
  match i with
  | Pmov_rs _ id => OK id
  | Pcall (inr id) _ => OK id
  | Pjmp (inr id) _ => OK id
  | Pleal _ a
  | Pmovl_rm _ a
  | Pmovl_mr a _
  | Pmov_rm_a _ a
  | Pmov_mr_a a _ => addrmode_reloc_id a
  | _ => Error (msg "Calculation of relocation offset failed: Either there is no possible relocation location or the instruction is not supported yet by relocation")
  end.



Lemma exec_instr_ok:
  forall i rs m rs' m' i' bpc opc
         (PC: rs PC = Vptr bpc opc)
         (SYMBS: forall idofs id ofs,
             instr_reloc_id i = OK id ->
             id_reloc_offset (Ptrofs.unsigned opc) i = Some idofs ->
             Genv.symbol_address tge RELOC_CODE idofs ofs =
             RelocProgSemantics.Genv.symbol_address ge id ofs)
         (EI: RelocProgSemantics.exec_instr ge i rs m = Next rs' m')
         (ELIM : id_eliminate false i = OK i'),
    exec_instr tge i' rs m = Next rs' m'.
Proof.
  intros.
  unfold id_eliminate in ELIM.
  destruct (ready_for_proof i) eqn:EQProof.
  unfold id_eliminate' in ELIM.
  destr_in ELIM.
  destruct i; simpl in *; inv EI; inv ELIM; simpl; eauto;
    try (unfold exec_instr, get_pc_offset; rewrite PC; auto; fail);
    try (intuition congruence).
  - unfold exec_instr. unfold get_pc_offset; rewrite PC; auto.
    simpl in *.
    erewrite SYMBS. 2: eauto. 2: reflexivity. auto.
  -
    assert (i' =  Pmovl_rm rd match a with
                              | Addrmode rb ss (inl _) => a
                              | Addrmode rb ss (inr (_, ptrofs)) =>
                                Addrmode rb ss (inr (1%positive, ptrofs))
                              end).
    repeat destr_in H1; inv H1. clear H1. subst.
    unfold exec_instr. unfold get_pc_offset.
    rewrite PC. unfold id_reloc_offset. Opaque Z.add. simpl.
    unfold exec_load. unfold RelocProgSemantics.exec_load.
    match goal with
    | |-
      match Mem.loadv _ _ ?v1 with _ => _ end =
      match Mem.loadv _ _ ?v2 with _ => _ end =>
      let x := fresh in
      assert (x: v1 = v2); [|rewrite x; auto]
    end.
    {
      destr. destr. destr.
      unfold eval_addrmode, RelocProgSemantics.eval_addrmode.
      destr.
      unfold eval_addrmode64, RelocProgSemantics.eval_addrmode64.
      f_equal. f_equal. apply  SYMBS. reflexivity. reflexivity.
      unfold eval_addrmode32, RelocProgSemantics.eval_addrmode32.
      f_equal. f_equal. apply  SYMBS. reflexivity. reflexivity.
    }
    repeat destr.
  - assert (i' =  Pmovl_mr match a with
                           | Addrmode rb ss (inl _) => a
                           | Addrmode rb ss (inr (_, ptrofs)) =>
                             Addrmode rb ss (inr (1%positive, ptrofs))
                           end rs0).
    repeat destr_in H1; inv H1. clear H1. subst.
    unfold exec_instr. unfold get_pc_offset.
    rewrite PC. unfold id_reloc_offset. Opaque Z.add. simpl.
    unfold exec_store. unfold RelocProgSemantics.exec_store.
    match goal with
    | |-
      match Mem.storev _ _ ?v1 _ with _ => _ end =
      match Mem.storev _ _ ?v2 _ with _ => _ end =>
      let x := fresh in
      assert (x: v1 = v2); [|rewrite x; auto]
    end.
    {
      destr. destr. destr.
      unfold eval_addrmode, RelocProgSemantics.eval_addrmode.
      destr.
      unfold eval_addrmode64, RelocProgSemantics.eval_addrmode64.
      f_equal. f_equal. apply  SYMBS. reflexivity. reflexivity.
      unfold eval_addrmode32, RelocProgSemantics.eval_addrmode32.
      f_equal. f_equal. apply  SYMBS. reflexivity. reflexivity.
    }
    repeat destr.
  - assert (i' =  Pleal rd match a with
                           | Addrmode rb ss (inl _) => a
                           | Addrmode rb ss (inr (_, ptrofs)) =>
                             Addrmode rb ss (inr (1%positive, ptrofs))
                           end).
    repeat destr_in H0; inv H0. clear H0. subst.
    unfold exec_instr. unfold get_pc_offset.
    rewrite PC. unfold id_reloc_offset. Opaque Z.add. simpl.
    f_equal. f_equal. f_equal.
    + repeat destr.
      unfold eval_addrmode32, RelocProgSemantics.eval_addrmode32.
      f_equal. f_equal. apply  SYMBS. reflexivity. reflexivity.
    + repeat destr.
  - destr_in H0. destr_in H1.
    + inv H0. inv H1. unfold exec_instr.
      unfold get_pc_offset.
      replace (instr_size (Pcall (inr xH) sg)) with (instr_size (Pcall (inr i) sg)).
      rewrite PC. rewrite <- PC. rewrite Heqo. simpl. f_equal. f_equal.
      f_equal. eapply SYMBS; eauto.
      reflexivity.
  (* - destr. *)
  (*   + inv H0. inv H1. unfold exec_instr. *)
  (*     unfold get_pc_offset. *)
  (*     rewrite PC. auto. *)
  (*   + inv H0. inv H1. unfold exec_instr. *)
  (*     unfold get_pc_offset. *)
  (*     rewrite PC. simpl. f_equal. f_equal. eapply SYMBS; eauto. *)
  - assert (i' =  Pmov_rm_a rd match a with
       | Addrmode rb ss (inl _) => a
       | Addrmode rb ss (inr (_, ptrofs)) =>
         (Addrmode rb ss (inr (1%positive, ptrofs)))
                               end).
    repeat destr_in H1. clear H1. subst.
    unfold exec_instr. unfold get_pc_offset. rewrite PC.
    unfold exec_load, RelocProgSemantics.exec_load.
    match goal with
    | |-
      match Mem.loadv _ _ ?v1 with _ => _ end =
      match Mem.loadv _ _ ?v2 with _ => _ end =>
      let x := fresh in
      assert (x: v1 = v2); [|rewrite x; auto]
    end.
    {
      destr. destr. destr.
      unfold eval_addrmode, RelocProgSemantics.eval_addrmode.
      destr.
      unfold eval_addrmode64, RelocProgSemantics.eval_addrmode64.
      f_equal. f_equal. simpl. apply  SYMBS. reflexivity. reflexivity.
      unfold eval_addrmode32, RelocProgSemantics.eval_addrmode32.
      f_equal. f_equal. simpl. apply  SYMBS. reflexivity. reflexivity.
    }
    destr. f_equal. f_equal. simpl. f_equal. repeat destr.
  - assert (i' =  Pmov_mr_a  match a with
       | Addrmode rb ss (inl _) => a
       | Addrmode rb ss (inr (_, ptrofs)) =>
         (Addrmode rb ss (inr (1%positive, ptrofs)))
                               end rs0).
    repeat destr_in H1. clear H1. subst.
    unfold exec_instr. unfold get_pc_offset. rewrite PC.
    unfold exec_store, RelocProgSemantics.exec_store.
    match goal with
    | |-
      match Mem.storev _ _ ?v1 _ with _ => _ end =
      match Mem.storev _ _ ?v2 _ with _ => _ end =>
      let x := fresh in
      assert (x: v1 = v2); [|rewrite x; auto]
    end.
    {
      destr. destr. destr.
      unfold eval_addrmode, RelocProgSemantics.eval_addrmode.
      destr.
      unfold eval_addrmode64, RelocProgSemantics.eval_addrmode64.
      f_equal. f_equal. simpl. apply  SYMBS. reflexivity. reflexivity.
      unfold eval_addrmode32, RelocProgSemantics.eval_addrmode32.
      f_equal. f_equal. simpl. apply  SYMBS. reflexivity. reflexivity.
    }
    destr. f_equal. f_equal. simpl. f_equal. repeat destr.
  - congruence.
Qed.

Lemma transl_instr_gen_reloc_ofs_symb:
  forall stbl ofs0 i0 l l' id0 idofs0
    (RNG: 0 <= ofs0 <= Ptrofs.max_unsigned)
    (TI: transl_instr (gen_symb_index_map stbl) false ofs0 i0 = OK l)
    (IR_id: instr_reloc_id i0 = OK id0)
    (IR_ofs: id_reloc_offset (Ptrofs.unsigned (Ptrofs.repr ofs0)) i0 = Some idofs0),
    Maps.ZTree.get idofs0 (gen_reloc_ofs_symb stbl (l ++ l')) = Some id0.
Proof.
  intros.
  assert (exists e,
             l = [e] /\
             reloc_offset e = idofs0 /\
             Maps.PTree.get id0 (gen_symb_index_map stbl) = Some (reloc_symb e)
         ).
  destruct i0; simpl in *; inv IR_id.
  - monadInv TI. unfold compute_instr_abs_relocentry in EQ.
    unfold id_reloc_offset in IR_ofs. destr_in IR_ofs. simpl in *. inv IR_ofs.
    destr_in EQ. inv EQ.
    eexists; repeat split; eauto. simpl. rewrite Ptrofs.unsigned_repr; auto.
  - repeat destr_in TI. simpl in *. inv H0.
    monadInv H1. unfold compute_instr_disp_relocentry in EQ.
    unfold id_reloc_offset in IR_ofs. destr_in EQ.
    unfold compute_instr_abs_relocentry in EQ.
    destr_in IR_ofs. simpl in *. inv IR_ofs. inv H0.
    destr_in EQ. inv EQ.
    eexists; repeat split; eauto. simpl. rewrite Ptrofs.unsigned_repr; auto.
  - repeat destr_in TI. simpl in *. inv H0.
    monadInv H1. unfold compute_instr_disp_relocentry in EQ.
    unfold id_reloc_offset in IR_ofs. destr_in EQ.
    unfold compute_instr_abs_relocentry in EQ.
    destr_in IR_ofs. simpl in *. inv IR_ofs. inv H0.
    destr_in EQ. inv EQ.
    eexists; repeat split; eauto. simpl. rewrite Ptrofs.unsigned_repr; auto.

  - repeat destr_in TI. simpl in *. inv H0.
    monadInv H1. unfold compute_instr_disp_relocentry in EQ.
    unfold id_reloc_offset in IR_ofs. destr_in EQ.
    unfold compute_instr_abs_relocentry in EQ.
    destr_in IR_ofs. simpl in *. inv IR_ofs. inv H0.
    destr_in EQ. inv EQ.
    eexists; repeat split; eauto. simpl. rewrite Ptrofs.unsigned_repr; auto.

  - congruence.
  - repeat destr_in TI.
    monadInv H1. inv H0. unfold compute_instr_rel_relocentry in EQ.
    unfold id_reloc_offset in IR_ofs. destr_in IR_ofs.
    simpl in EQ.
    destr_in EQ. inv EQ.
    eexists; repeat split; eauto. simpl. inv IR_ofs. rewrite Ptrofs.unsigned_repr; auto.

  (* - repeat destr_in TI. *)
  (*   monadInv H1. inv H0. unfold compute_instr_rel_relocentry in EQ. *)
  (*   unfold id_reloc_offset in IR_ofs. destr_in IR_ofs. *)
  (*   simpl in EQ. *)
  (*   destr_in EQ. inv EQ. *)
  (*   eexists; repeat split; eauto. simpl. inv IR_ofs. rewrite Ptrofs.unsigned_repr; auto. *)

  - repeat destr_in TI. simpl in *. inv H0.
    monadInv H1. simpl in *. destr_in H0. inv H0. unfold compute_instr_disp_relocentry in EQ.
    unfold id_reloc_offset in IR_ofs.
    unfold compute_instr_abs_relocentry in EQ.
    destr_in IR_ofs. simpl in *. inv IR_ofs.
    destr_in EQ. inv EQ.
    eexists; repeat split; eauto. simpl. rewrite Ptrofs.unsigned_repr; auto.
  - repeat destr_in TI. simpl in *. inv H0.
    monadInv H1. simpl in *. destr_in H0. inv H0.
    unfold compute_instr_disp_relocentry in EQ.
    unfold id_reloc_offset in IR_ofs.
    unfold compute_instr_abs_relocentry in EQ.
    destr_in IR_ofs. simpl in *. inv IR_ofs.
    destr_in EQ. inv EQ.
    eexists; repeat split; eauto. simpl. rewrite Ptrofs.unsigned_repr; auto.
  - destruct H as (e & EQ & OFS & SYMB). subst.
    edestruct in_sim_in_stbl_nth as (s & GET & EQ). rewrite SYMB. reflexivity.
    simpl.
    eapply acc_reloc_ofs_symb_ok. eauto. eauto.
Qed.

Lemma gen_reloc_ofs_symb_app:
  forall (stbl : symbtable) (rtbl1 rtbl2 : list relocentry) (o : Z),
    ~ In o reloc_offset ## rtbl1 ->
    Maps.ZTree.get o (gen_reloc_ofs_symb stbl (rtbl1 ++ rtbl2)) =
    Maps.ZTree.get o (gen_reloc_ofs_symb stbl rtbl2).
Proof.
  induction rtbl1; simpl; intros; eauto.
  rewrite acc_reloc_ofs_symb_other. 2: intuition. eauto.
Qed.

Lemma addrmode_reloc_offset_addrmode_size:
  forall a,
    0 <= addrmode_reloc_offset a < addrmode_size a.
Proof.
  Transparent addrmode_size.
  unfold addrmode_size, addrmode_reloc_offset. intros; split. 2: lia.
  generalize (addrmode_size_aux_pos a). lia.
  Opaque addrmode_size.
Qed.

Lemma instr_size_reloc_offset:
  forall i z,
    instr_reloc_offset i = OK z ->
    0 <= z < instr_size i.
Proof.
  Transparent instr_size.
  destruct i; simpl; intros z IRO; inv IRO; try destr; try lia.
  1-17:generalize (addrmode_reloc_offset_addrmode_size a); lia.
  inv H0; lia.
  inv H0; lia.
  1-4:generalize (addrmode_reloc_offset_addrmode_size a); lia.
  Opaque instr_size.
Qed.

Lemma transl_instr_reloc_offset_range:
  forall sim ofs a l,
    transl_instr sim false ofs a = OK l ->
    forall o, In o reloc_offset ## l ->
              ofs <= o < ofs + instr_size a.
Proof.
  intros sim ofs a. generalize (instr_size_reloc_offset a). intro RNG.
  intros l TI o IN.

  Ltac autoinv :=
    repeat match goal with
           | H : OK _ = OK _ |- _ => inv H
           | H : OK _ = Error _ |- _ => inv H
           | H : Error _ = OK _ |- _ => inv H
           | H : In _ (_ ## []) |- _ => simpl in H; inv H
           | H : In _ (_ ## [_]) |- _ => simpl in H; destruct H as [H|[]]
           | H : bind _ _ = OK _ |- _ => monadInv H
           | H : context [match ?a with _ => _ end] |- _ => destr_in H
           | H1 : (forall _, instr_reloc_offset _ = OK _ -> _),
                  H2 : instr_reloc_offset ?a = _ |- _ =>
             specialize (H1 _ H2)
           | H: compute_instr_abs_relocentry _ _ _ _ _ = OK _ |- _ =>
             unfold compute_instr_abs_relocentry in H
           | H: compute_instr_disp_relocentry _ _ _ _ = OK _ |- _ =>
             unfold compute_instr_disp_relocentry in H
           | H: compute_instr_rel_relocentry _ _ _ _ = OK _ |- _ =>
             unfold compute_instr_rel_relocentry in H
           end.

  destruct a; simpl in TI; autoinv; simpl; try lia.
Qed.

Lemma gen_instr_map_gen_reloc_ofs_symb_ok:
  forall c ofs i id idofs
         ofs0 map0 ofs1 map1
         (GIM: fold_left acc_instr_map c (Ptrofs.repr ofs0, map0) = (Ptrofs.repr ofs1, map1))
         (INSTR : map1 ofs = Some i)
         (IRI : instr_reloc_id i = OK id)
         (IRO : id_reloc_offset (Ptrofs.unsigned ofs) i = Some idofs)
         creloc0 creloc1 stbl
         (FL : fold_left (acc_instrs (gen_symb_index_map stbl) false) c
                         (OK (ofs0, creloc0)) =
               OK (ofs1, creloc1))
         (REPR: 0 <= ofs0 <= Ptrofs.max_unsigned)
         (REPR2: 0 <= ofs0 + code_size c <= Ptrofs.max_unsigned)
         (MAP0OFS: forall ofs i,
             map0 ofs = Some i -> Ptrofs.unsigned ofs + instr_size i <= ofs0
         )
         (REC: forall ofs i id idofs,
             map0 ofs = Some i ->
             instr_reloc_id i = OK id ->
             id_reloc_offset (Ptrofs.unsigned ofs) i = Some idofs ->
             Maps.ZTree.get idofs (gen_reloc_ofs_symb stbl creloc0) = Some id
         ),
    Maps.ZTree.get idofs (gen_reloc_ofs_symb stbl creloc1) = Some id.
Proof.
  induction c; simpl; intros; eauto.
  - inv FL. inv GIM. eauto.
  - destruct (ready_for_proof a) eqn:RF; try congruence.
    + destruct (transl_instr' (gen_symb_index_map stbl) (ofs0) a) eqn:?.
      * cbn in FL.
        eapply IHc in FL. eauto.
        rewrite <- GIM. f_equal. f_equal.
        unfold Ptrofs.add. rewrite ! Ptrofs.unsigned_repr. auto.
        apply instr_size_repr. auto.
        reflexivity. eauto. auto. auto.
        generalize (code_size_non_neg c). split. 2: lia.
        generalize (instr_size_positive a); lia. lia.
        {
          simpl. intros. destr_in H; eauto. inv H.
          rewrite Ptrofs.unsigned_repr. generalize (instr_size_positive i0). lia. auto.
          eapply MAP0OFS in H. generalize (instr_size_positive a). lia.
        }
        {
          simpl. intros. destr_in H. inv H.
          eapply transl_instr_gen_reloc_ofs_symb. 
          Focus 2. unfold transl_instr. rewrite RF. eauto.
          all: eauto.
          erewrite gen_reloc_ofs_symb_app. eauto.
          intro IN.
          exploit transl_instr_reloc_offset_range. 
          unfold transl_instr. rewrite RF. eauto. 
          eauto.
          generalize (MAP0OFS _ _ H).
          unfold id_reloc_offset in H1.
          destr_in H1. inv H1.
          exploit instr_size_reloc_offset. apply Heqr0. lia.
        }
      * simpl in FL.
        rewrite fold_acc_instrs_error in FL. inv FL.
    + cbn in FL.
      rewrite fold_acc_instrs_error in FL. congruence.
Qed.

Lemma acc_instr_map_acc_instrs_same_size:
  forall c ofs0 map0 ofs1 map1 sim creloc0 creloc1 x,
    0 <= ofs0 <= Ptrofs.max_unsigned ->
     0 <= ofs0 + code_size c <= Ptrofs.max_unsigned ->
        fold_left acc_instr_map c (Ptrofs.repr ofs0, map0) = (ofs1, map1) ->
        fold_left (acc_instrs sim false) c (OK (ofs0, creloc0)) = OK (x, creloc1) ->
        Ptrofs.repr x = ofs1 /\ x = code_size c + ofs0.
Proof.
  induction c; simpl; intros; eauto.
  - inv H1; inv H2. auto.
  - destruct (ready_for_proof a) eqn:RF.
    + destruct (transl_instr' sim ofs0 a) eqn:?; simpl in *.
      *  exploit IHc. 3: eauto.
         rewrite ! Ptrofs.unsigned_repr.
         generalize (instr_size_positive a) (code_size_non_neg c). lia.
         generalize (instr_size_positive a) (code_size_non_neg c). lia.
         auto.
         rewrite ! Ptrofs.unsigned_repr. lia.
         generalize (instr_size_positive a) (code_size_non_neg c). lia.
         auto.
         rewrite ! Ptrofs.unsigned_repr. eauto.
         generalize (instr_size_positive a) (code_size_non_neg c). lia.
         auto.
         intros (A & B). split; auto.
         subst.
         rewrite ! Ptrofs.unsigned_repr. lia.
         generalize (instr_size_positive a) (code_size_non_neg c). lia.
         auto.
      *  rewrite fold_acc_instrs_error in H2; inv H2.
    + cbn in H2.
      rewrite fold_acc_instrs_error in H2. congruence.
Qed.

Lemma set_set:
  forall {A} k1 (t: Maps.PTree.t A) v1 k2 v2,
    (k1 = k2 -> v1 = v2) ->
    Maps.PTree.set k1 v1 (Maps.PTree.set k2 v2 t) =
    Maps.PTree.set k2 v2 (Maps.PTree.set k1 v1 t).
Proof.
  induction k1; simpl; intros; eauto.
  - destruct t.
    + destruct k2; simpl; auto. rewrite IHk1. auto. intros; apply H; congruence.
    + destruct k2; simpl; auto. rewrite IHk1. auto. intros; apply H; congruence.
  - destruct t.
    + destruct k2; simpl; auto. rewrite IHk1. auto. intros; apply H; congruence.
    + destruct k2; simpl; auto. rewrite IHk1. auto. intros; apply H; congruence.
  - destruct t.
    + destruct k2; simpl; auto. rewrite H; auto.
    + destruct k2; simpl; auto. rewrite H; auto.
Qed.

Lemma gen_reloc_ofs_symb_permut:
  forall stbl rtbl1 rtbl2,
    Permutation.Permutation rtbl1 rtbl2 ->
    list_norepet reloc_offset ## rtbl1 ->
    gen_reloc_ofs_symb stbl rtbl1 = gen_reloc_ofs_symb stbl rtbl2.
Proof.
  induction 1; simpl; intros; eauto.
  - unfold acc_reloc_ofs_symb. inv H0. destr.
  - inv H. inv H3. unfold acc_reloc_ofs_symb. destr. destr.
    apply set_set.
    intros EQ; apply Maps.ZIndexed.index_inj in EQ.
    exfalso. apply H2. rewrite EQ. left; auto.
  - rewrite IHPermutation1.  apply IHPermutation2.
    eapply LocalLib.Permutation_pres_list_norepet; eauto. apply Permutation.Permutation_map; auto.
    auto.
Qed.

Lemma transl_instr_norepet:
  forall sim z a l,
    transl_instr sim false z a = OK l ->
    list_norepet reloc_offset ## l.
Proof.
  unfold transl_instr. 
  intros.
  destr_in H. unfold transl_instr' in H.
  repeat destr_in H; simpl; try constructor; try (cbn in *; try congruence).
  - unfold compute_instr_abs_relocentry in *.
    monadInv H1. repeat constructor. simpl. auto.
  - unfold compute_instr_disp_relocentry in *.
    destr_in H1. monadInv H1. repeat constructor; simpl; auto.
  - unfold compute_instr_disp_relocentry in *.
    destr_in H1. monadInv H1. repeat constructor; simpl; auto.
  - unfold compute_instr_disp_relocentry in *.
    destr_in H1. monadInv H1. repeat constructor; simpl; auto.
  - unfold compute_instr_rel_relocentry in *.
    monadInv H1. repeat constructor; simpl; auto.
  - unfold compute_instr_rel_relocentry in *.
    monadInv H1. repeat constructor; simpl; auto.
  - unfold compute_instr_disp_relocentry in *.
    destr_in H1. monadInv H1. repeat constructor; simpl; auto.
Qed.


Lemma transl_code_norepet:
  forall sim c cr0 cr1 z0 z1,
    list_norepet reloc_offset ## cr0 ->
    Forall (fun e => reloc_offset e < z0) cr0 ->
    fold_left (acc_instrs sim false) c (OK (z0, cr0)) = OK (z1, cr1) ->
    list_norepet reloc_offset ## cr1.
Proof.
  induction c; simpl; intros; eauto.
  inv H1. auto.
  unfold bind in H1. destr_in H1.
  - apply IHc in H1. auto.
    + rewrite map_app. rewrite list_norepet_app. split; [|split].
      eapply transl_instr_norepet; eauto. auto.
      red; intros.
      (* rewrite in_map_iff in H2. destruct H2 as (x0 & EQ & INl). subst. *)
      rewrite in_map_iff in H3. destruct H3 as (x1 & EQ & INcr0). subst.
      rewrite Forall_forall in H0. apply H0 in INcr0.
      eapply transl_instr_reloc_offset_range in Heqr. 2: eauto. lia.
    + rewrite Forall_forall in H0 |- *.
      intros.
      rewrite in_app in H2. destruct H2; eauto.
      eapply transl_instr_reloc_offset_range in Heqr. 2: apply in_map; eauto. lia.
      apply H0 in H2. generalize (instr_size_positive a); lia.
  - rewrite fold_acc_instrs_error in H1. congruence.
Qed.

Lemma instr_map_reloc_id_ok:
  forall ofs i id idofs,
    gen_instr_map' (SecTable.get sec_code_id (prog_sectable prog)) ofs = Some i ->
    instr_reloc_id i = OK id ->
    id_reloc_offset (Ptrofs.unsigned ofs) i = Some idofs ->
    Maps.ZTree.get idofs (gen_reloc_ofs_symbs tprog RELOC_CODE) = Some id.
Proof.
  intros ofs i id idofs GIM IRI IRO.
  unfold gen_reloc_ofs_symbs.
  unfold add_reloc_ofs_symb at 1. destr.
  destruct (prog_sectable_eq) as (init & c & c' & creloc & dreloc & PS1 & TC & TC' &
                                  PERMc & CodeRng & PS2 & TIDL & PERMd).
  unfold transl_code in TC'. monadInv TC'.
  unfold get_reloctable.
  erewrite <- gen_reloc_ofs_symb_permut. 2: eauto.
  2: eapply transl_code_norepet; eauto. 2: constructor.
  rewrite PS1 in GIM. simpl in GIM.
  unfold gen_instr_map in GIM. destr_in GIM.
  rewrite <- (Ptrofs.repr_unsigned Ptrofs.zero) in Heqp.
  rewrite <- (Ptrofs.repr_unsigned i0) in Heqp.
  eapply gen_instr_map_gen_reloc_ofs_symb_ok.
  apply Heqp. eauto. auto. auto.
  rewrite <- prog_symtable_same. rewrite Ptrofs.unsigned_zero.
  rewrite EQ. f_equal. f_equal.
  exploit acc_instr_map_acc_instrs_same_size; eauto.
  vm_compute. intuition congruence.
  erewrite <- transl_code_size by eauto. rewrite Ptrofs.unsigned_zero. lia.
  rewrite Ptrofs.unsigned_zero.
  intros (A & B).
  subst.
  rewrite <- (Ptrofs.unsigned_repr (code_size c + 0)).
  rewrite A. rewrite Ptrofs.repr_unsigned. auto. 
  erewrite <- transl_code_size by eauto. lia.
  rewrite Ptrofs.unsigned_zero. lia.
  rewrite Ptrofs.unsigned_zero.   erewrite <- transl_code_size by eauto. lia.
  simpl. congruence.
  simpl. congruence.
Qed.

Lemma symbol_address_code_transl:
  forall b ofs i
         (H2 : RelocProgSemantics.Genv.find_instr ge (Vptr b ofs) = Some i),
  forall (idofs : Z) (id : ident) (ofs0 : ptrofs),
    instr_reloc_id i = OK id ->
    id_reloc_offset (Ptrofs.unsigned ofs) i = Some idofs ->
    RelocProgSemantics.Genv.symbol_address ge id ofs0 = Genv.symbol_address tge RELOC_CODE idofs ofs0.
Proof.
  unfold Genv.symbol_address.
  unfold RelocProgSemantics.Genv.symbol_address.
  unfold Genv.find_symbol.
  unfold RelocProgSemantics.Genv.find_symbol.
  unfold tge, ge.
  unfold globalenv. simpl.
  unfold RelocProgSemantics.globalenv. simpl.
  intros.
  rewrite instrs_add_external_globals in H2. simpl in H2.
  erewrite instr_map_reloc_id_ok; eauto.
  rewrite prog_symtable_same.
  rewrite defs_preserved.
  match goal with
  | |- match ?a with _ => _ end = match ?b with _ => _ end =>
    assert (a = b)
  end.
  f_equal.
  apply add_external_globals_symb_unchanged.
  simpl. auto.
  simpl. auto.
  rewrite H1. reflexivity.
Qed.


Lemma eval_builtin_arg_ok:
  forall preg rs0 sp m a1 b1,
    RelocProgSemantics.eval_builtin_arg preg ge rs0 sp m a1 b1 ->
    ok_builtin_arg a1 = true ->
    eval_builtin_arg preg tge None rs0 sp m a1 b1.
Proof.
  induction 1; simpl; intros; eauto; try (econstructor; eauto; fail).
  easy. easy.
  rewrite andb_true_iff in H1.
  destruct H1. econstructor; eauto.
Qed.

Lemma eval_builtin_args_ok:
  forall preg rs0 sp m args vargs,
    forallb ok_builtin_arg args = true ->
    RelocProgSemantics.eval_builtin_args preg
                                         ge rs0
                                         sp m args vargs ->
    eval_builtin_args preg tge None rs0
                      sp m args vargs.
Proof.
  induction 2; simpl; intros; eauto. constructor.
  simpl in H. rewrite andb_true_iff in H. destruct H.
  constructor; eauto.
  eapply eval_builtin_arg_ok; eauto.
  eapply IHlist_forall2. auto.
Qed.

Lemma senv_preserved:
  Genv.genv_senv ge = Genv.genv_senv (Genv.genv_genv tge).
Proof.
  intros.
  unfold tge, ge.
  unfold globalenv. simpl.
  unfold RelocProgSemantics.globalenv.
  rewrite ! genv_senv_add_external_globals. simpl.
  unfold match_prog in TRANSF.
  decompose [ex and] TRANSF. clear TRANSF.
  unfold transf_program in H0.
  monadInv H0. repeat destr_in EQ2. simpl in *. congruence.
Qed.

Lemma external_call_ok:
  forall ef vargs m t vres m',
    external_call ef (Genv.genv_senv ge) vargs m t vres m' ->
    external_call ef (Genv.genv_senv (Genv.genv_genv tge)) vargs m t vres m'.
Proof.
  intros. rewrite <- senv_preserved. eauto.
Qed.



Lemma transf_program_correct:
  forall rs, forward_simulation (RelocProgSemantics.semantics prog rs)
                                (RelocProgSemantics1.semantics tprog rs).
Proof.
  intro rs.
  eapply forward_simulation_step with (match_states := fun a b : Asm.state => a = b).
  - simpl.
    intros.
    fold ge.
    rewrite senv_preserved.
    unfold genv_senv. fold ge. reflexivity.
  - intros s1 IS. eexists; split; eauto.
    unfold semantics. simpl. inv IS. simpl in *.
    exploit init_mem_ok; eauto. intro IM.
    econstructor. eauto.
    inv H0.
    unfold rs0, ge0. fold ge. rewrite main_ok.
    econstructor; eauto.
  - intros. subst. simpl in *.
    inv H0. constructor; auto.
  - simpl.
    intros. subst. inv H.
    + edestruct find_instr_ok as (i' & FI & ELIM); eauto.
      exploit exec_step_internal. eauto.
      erewrite <- find_ext_funct_ok; eauto.
      eauto.
      eapply exec_instr_ok; eauto.
      intros; symmetry; eapply symbol_address_code_transl; eauto.
      exploit global_env_find_instr_inv; eauto.
      intros (c & GETC & IN).
      cbn. erewrite transf_program_instr_ready; eauto.

      intro STEP. eexists; split; eauto.
    + edestruct find_instr_ok as (i' & FI & ELIM); eauto.
      unfold id_eliminate' in ELIM. destr_in ELIM. inv ELIM. simpl in Heqb0.
      apply negb_false_iff in Heqb0.
      exploit exec_step_builtin. eauto.
      erewrite <- find_ext_funct_ok; eauto.
      eauto. reflexivity.
      eapply eval_builtin_args_ok; eauto.
      eapply external_call_ok; eauto. auto. reflexivity.
      intro STEP. eexists; split; eauto.
    + exploit exec_step_external. eauto.
      erewrite <- find_ext_funct_ok; eauto. eauto. auto.
      eauto. eapply external_call_ok; eauto.
      reflexivity.
      intro STEP.
      eexists; split; eauto.
Qed.

End PRESERVATION.

Require Import RelocLinking RelocLinking1.


Lemma transl_sectable'_code:
  forall stbl stbl' v,
    transl_sectable' false stbl = OK stbl' ->
    SecTable.get sec_code_id stbl = Some v ->
    exists c c',
      v = sec_text c /\ transl_code' false c = OK c' /\
      SecTable.get sec_code_id stbl' = Some (sec_text c').
Proof.
  unfold transl_sectable'; intros. repeat destr_in H.
  monadInv H2. repeat destr_in EQ0. eauto.
  vm_compute in H0. inv H0. unfold SecTable.get. simpl. eauto.
Qed.

Lemma transl_sectable'_data:
  forall stbl stbl' v,
    transl_sectable' false stbl = OK stbl' ->
    SecTable.get sec_data_id stbl = Some v ->
    SecTable.get sec_data_id stbl' = Some v.
Proof.
  unfold transl_sectable'; intros. repeat destr_in H.
  monadInv H2. repeat destr_in EQ0. eauto.
Qed.



Lemma transl_instrs_acc:
  forall sim sim' z a e,
    (forall x y,
        Maps.PTree.get x sim = Some y ->
        Maps.PTree.get x sim' = Some y
    ) ->
    transl_instr sim false z a = OK e ->
    transl_instr sim' false z a = OK e.
Proof.
  intros.
  destruct a; simpl in *; eauto.
  - unfold compute_instr_abs_relocentry in *.
    monadInv H0. monadInv EQ. rewrite EQ0. destr_in EQ1.
    erewrite H; eauto. inv EQ1. simpl. auto.
  - repeat destr_in H0.
    unfold compute_instr_disp_relocentry in *.
    destr_in H2. monadInv H2.
    unfold compute_instr_abs_relocentry in *.
    monadInv EQ. rewrite EQ0. destr_in EQ1.
    erewrite H; eauto.
  - repeat destr_in H0.
    unfold compute_instr_disp_relocentry in *.
    destr_in H2. monadInv H2.
    unfold compute_instr_abs_relocentry in *.
    monadInv EQ. rewrite EQ0. destr_in EQ1.
    erewrite H; eauto.
  - repeat destr_in H0.
    unfold compute_instr_disp_relocentry in *.
    destr_in H2. monadInv H2.
    unfold compute_instr_abs_relocentry in *.
    monadInv EQ. rewrite EQ0. destr_in EQ1.
    erewrite H; eauto.
  - repeat destr_in H0.
    unfold compute_instr_rel_relocentry in *.
    monadInv H2. monadInv EQ. rewrite EQ0. rewrite EQ. simpl.
    destr_in EQ2.
    erewrite H; eauto.
  (* - repeat destr_in H0. *)
  (*   unfold compute_instr_rel_relocentry in *. *)
  (*   monadInv H2. monadInv EQ. rewrite EQ0. rewrite EQ. simpl. *)
  (*   destr_in EQ2. *)
  (*   erewrite H; eauto. *)
  - repeat destr_in H0.
    unfold compute_instr_disp_relocentry in *.
    destr_in H2. monadInv H2.
    unfold compute_instr_abs_relocentry in *.
    monadInv EQ. rewrite EQ0. destr_in EQ1.
    erewrite H; eauto.
  - repeat destr_in H0.
    unfold compute_instr_disp_relocentry in *.
    destr_in H2. monadInv H2.
    unfold compute_instr_abs_relocentry in *.
    monadInv EQ. rewrite EQ0. destr_in EQ1.
    erewrite H; eauto.
Qed.

Lemma fold_acc_instrs_acc:
  forall sim sim' c1 z l z1 l1,
    (forall x y,
        Maps.PTree.get x sim = Some y ->
        Maps.PTree.get x sim' = Some y
    ) ->
    fold_left (acc_instrs sim false) c1 (OK (z, l)) = OK (z1, l1) ->
    fold_left (acc_instrs sim' false) c1 (OK (z, l)) = OK (z1, l1).
Proof.
  induction c1; simpl; intros; eauto.
  destruct (ready_for_proof a) eqn:?; cbn in *.
  - destruct (transl_instr' sim z a) eqn:?; simpl in *.
    2: rewrite fold_acc_instrs_error in H0; simpl in H0; congruence.
    exploit transl_instrs_acc; eauto.
    cbn. rewrite Heqb. eauto.
    intros. cbn in H1. rewrite Heqb in H1.
    rewrite H1. cbn. auto.
  - rewrite fold_acc_instrs_error in H0. congruence.
Qed.


Lemma get_symbtable_to_tree:
  forall stbl,
    (symbtable_to_tree stbl) =
    (Maps.PTree_Properties.of_list (fun s => (symbentry_id s, s)) ## stbl).
Proof.
  reflexivity.
Qed.

Lemma link_sectable_ok:
  forall stbl1 stbl2 s stbl1' stbl2',
    link_sectable stbl1 stbl2 = Some s ->
    transl_sectable' false stbl1 = OK stbl1' ->
    transl_sectable' false stbl2 = OK stbl2' ->
    exists init1 init2 c1 c2 c1' c2',
      stbl1 = [sec_data init1; sec_text c1] /\
      stbl2 = [sec_data init2; sec_text c2] /\
      transl_code' false c1 = OK c1' /\
      transl_code' false c2 = OK c2' /\
      link_sectable stbl1' stbl2' = Some [sec_data (init1 ++ init2); sec_text (c1' ++ c2')].
Proof.
  intros.
  unfold link_sectable in *. repeat destr_in H.
  unfold transl_sectable' in H0, H1.
  repeat destr_in H0; repeat destr_in H1.
  monadInv H0; monadInv H2.
  repeat destr_in EQ0; repeat destr_in EQ2.
  unfold SecTable.get in *; simpl in *. inv Heqo. inv Heqo0. inv Heqo1. inv Heqo2.
  simpl in *. inv Heqo3. inv Heqo4.
  (do 6 eexists); repeat split; eauto.
Qed.

Lemma transl_init_data_list_gets:
  forall stbl1 l x0,
    transl_init_data_list (gen_symb_index_map stbl1) l = OK x0 ->
    Forall (fun e =>
              exists se i,
                SymbTable.get (reloc_symb e) stbl1 = Some se /\
                Maps.PTree.get (symbentry_id se) (gen_symb_index_map stbl1) = Some i
           ) x0.
Proof.
  unfold transl_init_data_list.
  intros. monadInv H. repeat destr_in EQ0.
  assert (
      forall l z0 x0 z1 x1,
        fold_left (acc_init_data (gen_symb_index_map stbl1)) l (OK (z0, x0)) = OK (z1, x1) ->
        Forall
          (fun e : relocentry =>
             exists (se : SymbTblParams.V) (i : N),
               SymbTable.get (reloc_symb e) stbl1 = Some se /\
               Maps.PTree.get (symbentry_id se) (gen_symb_index_map stbl1) = Some i) x0 ->
        Forall
          (fun e : relocentry =>
             exists (se : SymbTblParams.V) (i : N),
               SymbTable.get (reloc_symb e) stbl1 = Some se /\
               Maps.PTree.get (symbentry_id se) (gen_symb_index_map stbl1) = Some i) x1).
  {
    clear. induction l; simpl; intros; eauto.
    - inv H; auto.
    - destruct (transl_init_data (gen_symb_index_map stbl1) z0 a) eqn:?.
      2: simpl in H. 2: rewrite fold_acc_init_data_error in H; congruence.
      simpl in H.
      exploit IHl. eauto.
      rewrite Forall_forall in *.
      intro x. rewrite in_app. intros [INr | INx0]; eauto.
      unfold transl_init_data in Heqr.
      repeat destr_in Heqr; simpl in *; try intuition congruence.
      destruct INr as [EQ|[]]. subst. simpl.
      exploit in_sim_in_stbl_nth. eauto. intros (s & GET & ID).
      (do 2 eexists); split. eauto. subst. eauto. auto.
  }
  eapply H. eauto. constructor.
Qed.

Lemma update_reloctable_symb_ok:
  forall stbl1 x0 s1,
    Forall (fun e =>
              exists se i,
                SymbTable.get (reloc_symb e) stbl1 = Some se /\
                Maps.PTree.get (symbentry_id se) (gen_symb_index_map s1) = Some i
           ) x0 ->
    exists t1',
      update_reloctable_symb stbl1 (gen_symb_index_map s1) x0 = Some t1'.
Proof.
  unfold update_reloctable_symb.
  intros.
  assert (
      forall t0,
      exists t1' : reloctable,
        fold_right (acc_update_reloc_symb stbl1 (gen_symb_index_map s1)) (Some t0) x0 = Some (t1' ++ t0)
    ).
  {
    revert x0 H; induction 1; simpl; intros; eauto.
    exists nil; reflexivity.
    edestruct IHForall as (t1' & EQ). rewrite EQ.
    destruct H as (se & i & GET & GET').
    unfold acc_update_reloc_symb. unfold update_reloc_symb. rewrite GET. rewrite GET'.
    eexists; eauto. f_equal. rewrite app_comm_cons. reflexivity.
  }
  edestruct H0. rewrite H1. rewrite app_nil_r. eauto.
Qed.



Lemma list_norepet_map_inv:
  forall {A B} (f: A -> B) (l: list A) (lnr: list_norepet f ## l)
         x1 x2 (IN1 : In x1 l) (IN2: In x2 l)
         (EQ: f x1 = f x2),
    x1 = x2.
Proof.
  induction l; simpl; intros; eauto. easy.
  inv lnr. trim IHl. auto.
  destruct IN1, IN2; eauto.
  - subst. auto.
  - subst. exfalso; apply H1; rewrite in_map_iff; eauto.
  - subst. exfalso; apply H1; rewrite in_map_iff; eauto.
Qed.

Lemma in_in_symbtable_to_tree:
  forall stbl se,
    list_norepet symbentry_id ## stbl ->
    In se stbl ->
    Maps.PTree.get (symbentry_id se) (symbtable_to_tree stbl) = Some se.
Proof.
  intros.
  rewrite get_symbtable_to_tree.
  erewrite Maps.PTree_Properties.of_list_norepet. eauto.
  rewrite map_map. apply H.
  rewrite in_map_iff. eauto.
Qed.

Lemma get_symbentry_ids_eq:
  forall l,
    get_symbentry_ids l = symbentry_id ## l.
Proof.
  unfold get_symbentry_ids. reflexivity.
Qed.

Lemma list_norepet_map_inv':
  forall
    {A B} (f: A -> B) l,
    list_norepet f ## l ->
    list_norepet l.
Proof.
  induction l; simpl; intros; eauto. constructor.
  inv H. constructor; auto. intro AA; apply H2; rewrite in_map_iff; eauto.
Qed.

Lemma link_symbtable_ok_l:
  forall stbl1 stbl2 s,
    link_symbtable stbl1 stbl2 = Some s ->
    forall se,
      Maps.PTree.get (symbentry_id se) (symbtable_to_tree s) =
      link_symb_merge (Maps.PTree.get (symbentry_id se) (symbtable_to_tree stbl1))
                      (Maps.PTree.get (symbentry_id se) (symbtable_to_tree stbl2)).
Proof.
  unfold link_symbtable. intros stbl1 stbl2 s LINK se.
  destr_in LINK.
  repeat rewrite andb_true_iff in Heqb.
  destruct Heqb as ((nr1 & nr2) & check).
  apply proj_sumbool_true in nr1.
  apply proj_sumbool_true in nr2.
  rewrite Maps.PTree_Properties.for_all_correct in check.
  inv LINK.
  unfold symbtable_to_tree.
  unfold symbtable_to_idlist.
  
  assert (forall {A} P (f: option A -> option A -> option A) t1 t2,
             f None None = None ->
             Forall P (Maps.PTree.elements t1) ->
             Forall P (Maps.PTree.elements t2) ->
             (forall a1 a2 i a,
                 (forall aa1, a1 = Some aa1 -> P (i, aa1)) ->
                 (forall aa2, a2 = Some aa2 -> P (i, aa2)) ->
                 f a1 a2 = Some a ->
                 P (i, a)
             ) ->
             Forall P (Maps.PTree.elements (Maps.PTree.combine f t1 t2))
         ).
  {
    intros A P f t1 t2 FN P1 P2 FP.
    rewrite Forall_forall in *.
    intros (i & a) IN.
    apply Maps.PTree.elements_complete in IN.
    rewrite Maps.PTree.gcombine in IN; auto.
    destruct (Maps.PTree.get i t1) eqn:G1.
    - exploit P1. eapply Maps.PTree.elements_correct; eauto.
      intros.
      destruct (Maps.PTree.get i t2) eqn:G2. exploit P2. eapply Maps.PTree.elements_correct; eauto.
      intros.
      eapply FP; eauto. inversion 1; subst; eauto. inversion 1; subst; eauto.
      eapply FP; eauto. inversion 1; subst; eauto. inversion 1; subst; eauto.
    - destruct (Maps.PTree.get i t2) eqn:G2. exploit P2. eapply Maps.PTree.elements_correct; eauto.
      intros.
      eapply FP; eauto. inversion 1; subst; eauto. inversion 1; subst; eauto.
      eapply FP; eauto. inversion 1; subst; eauto. inversion 1; subst; eauto.
  }
  assert (
    forall s,
      In s (Maps.PTree.elements
                    (Maps.PTree.combine link_symb_merge
                       (Maps.PTree_Properties.of_list
                          (fun s : symbentry => (symbentry_id s, s)) ## stbl1)
                       (Maps.PTree_Properties.of_list
                          (fun s : symbentry => (symbentry_id s, s)) ## stbl2))) ->
      symbentry_id (snd s) = fst s
  ).
  {
    rewrite <- Forall_forall.
    apply H. reflexivity.
     - rewrite Forall_forall; intros.
      destruct x.
      apply Maps.PTree.elements_complete in H0. simpl.
      apply Maps.PTree_Properties.in_of_list in H0. rewrite in_map_iff in H0.
      decompose [ex and] H0; eauto. inv H2; eauto.
    - rewrite Forall_forall; intros.
      destruct x.
      apply Maps.PTree.elements_complete in H0. simpl.
      apply Maps.PTree_Properties.in_of_list in H0. rewrite in_map_iff in H0.
      decompose [ex and] H0; eauto. inv H2; eauto.
    - simpl.
      intros. destruct a1, a2; simpl in H2; repeat destr_in H2.
      specialize (H0 _ eq_refl). specialize (H1 _ eq_refl). subst.
      unfold link_symb in H4. repeat destr_in H4; simpl; auto.
      specialize (H0 _ eq_refl). auto.
      specialize (H1 _ eq_refl). auto.
  }

  rewrite map_map.
  erewrite list_map_exten. rewrite map_id.
  rewrite Maps.PTree_Properties.of_list_elements.
  rewrite Maps.PTree.gcombine. 2: reflexivity. auto.
  {
    simpl. intros. apply H0 in H1. destruct x; simpl in *; subst; auto.
  }
Qed.

Lemma get_symbtable_to_tree':
  forall stbl se,
    list_norepet symbentry_id ## stbl ->
    In se stbl ->
    Maps.PTree.get (symbentry_id se) (symbtable_to_tree stbl) = Some se.
Proof.
  intros.
  rewrite get_symbtable_to_tree.
  erewrite Maps.PTree_Properties.of_list_norepet. eauto.
  - rewrite map_map. simpl. apply H.
  - rewrite in_map_iff. eexists; split; eauto.
Qed.

Lemma symbtable_to_tree_get_symb_index_map:
  forall stbl x se,
    list_norepet symbentry_id ## stbl ->
    Maps.PTree.get x (symbtable_to_tree stbl) = Some se ->
    x = symbentry_id se /\
    exists n,
      Maps.PTree.get x (gen_symb_index_map stbl) = Some n.
Proof.
  intros. rewrite get_symbtable_to_tree in H0.
  apply Maps.PTree_Properties.in_of_list in H0.
  rewrite in_map_iff in H0.
  decompose [ex and] H0; clear H0. subst. inv H2. split; eauto.
  edestruct in_split as (l1 & l2 & SPLIT). eauto.
  exploit gen_symb_index_map_ok. eauto. eauto. auto.
  intro A; decompose [ex and] A. eauto.
Qed.

Lemma get_symb_index_map_symbtable_to_tree:
  forall stbl x n,
    list_norepet symbentry_id ## stbl ->
    Maps.PTree.get x (gen_symb_index_map stbl) = Some n ->
    exists se,
      SymbTable.get n stbl = Some se /\
      x = symbentry_id se /\
      Maps.PTree.get x (symbtable_to_tree stbl) = Some se.
Proof.
  intros.
  exploit in_sim_in_stbl_nth. eauto.
  intros (s & GET & EQ). eexists; split; eauto. split; auto.
  rewrite get_symbtable_to_tree.
  apply Maps.PTree_Properties.of_list_norepet.
  rewrite map_map. simpl. apply H.
  rewrite in_map_iff. subst. eexists; split; eauto.
  unfold SymbTable.get in GET.
  eapply nth_error_In; eauto.
Qed.

Lemma link_symbtable_norepet:
  forall s1 s2 s,
    link_symbtable s1 s2 = Some s ->
    list_norepet symbentry_id ## s1 /\
    list_norepet symbentry_id ## s2 /\
    list_norepet symbentry_id ## s /\
    forall (x : Maps.PTree.elt) (a : symbentry),
      Maps.PTree.get x (symbtable_to_tree s1) = Some a ->
      link_symbtable_check (symbtable_to_tree s2) x a = true
.
Proof.
  intros.
  unfold link_symbtable in H.
  destr_in H.
  repeat rewrite andb_true_iff in Heqb.
  destruct Heqb as ((nr1 & nr2) & check).
  apply proj_sumbool_true in nr1.
  apply proj_sumbool_true in nr2.
  rewrite Maps.PTree_Properties.for_all_correct in check.
  rewrite get_symbentry_ids_eq in *. eauto.
  intuition.
  inv H.
  rewrite map_map.
  erewrite list_map_exten.
  apply Maps.PTree.elements_keys_norepet.
  intros x IN.
  destruct x.
  apply Maps.PTree.elements_complete in IN.
  rewrite Maps.PTree.gcombine in IN. simpl.
  2: reflexivity.
  rewrite ! get_symbtable_to_tree in IN.
  unfold link_symb_merge in IN. destr_in IN.
  apply Maps.PTree_Properties.in_of_list in Heqo.
  rewrite in_map_iff in Heqo.
  decompose [ex and] Heqo; eauto. inv H0; eauto.
  rename Heqo into EX.
  destr_in IN.
  apply Maps.PTree_Properties.in_of_list in Heqo.
  rewrite in_map_iff in Heqo.
  decompose [ex and] Heqo; eauto. inv H0; eauto.
  unfold link_symb in IN. repeat destr_in IN; simpl; auto.
  apply Maps.PTree_Properties.in_of_list in IN.
  rewrite in_map_iff in IN.
  decompose [ex and] IN; eauto. inv H0; eauto.
Qed.


Lemma link_symb_merge_ok:
  forall s1 s2 x se,
    link_symbtable_check (symbtable_to_tree s2) x se = true ->
    Maps.PTree.get x (symbtable_to_tree s1) = Some se ->
    exists se',
      link_symb_merge (Some se) (Maps.PTree.get x (symbtable_to_tree s2)) = Some se'.
Proof.
  unfold link_symb_merge, link_symbtable_check.
  intros. repeat destr_in H; eauto.
Qed.

Lemma ursymb_ok:
  forall stbl a r0 stbl' s,
    link_symbtable stbl stbl' = Some s ->
    update_reloc_symb stbl (gen_symb_index_map stbl) a = Some r0 ->
    exists r1,
      update_reloc_symb stbl (gen_symb_index_map s) a = Some r1.
Proof.
  unfold update_reloc_symb.
  intros. repeat destr_in H0.
  exploit link_symbtable_norepet. eauto. intros (nr1 & nr2 & nr3 & check).
  exploit (get_symb_index_map_symbtable_to_tree). 2: eauto. eauto.
  intros (se & GET & EQ & stree).
  exploit link_symbtable_ok_l. eauto. intro EQsymb. rewrite stree in EQsymb.
  edestruct link_symb_merge_ok. eauto. eauto.
  exploit symbtable_to_tree_get_symb_index_map. 3: intros (A & n0 & B).
  3: rewrite B; eauto. auto.
  erewrite link_symbtable_ok_l. 2: eauto.
  rewrite stree. eauto.
Qed.

Lemma reloc_symbtable_eq:
  forall get_reloc_offset stbl stbl',
    reloc_symbtable get_reloc_offset stbl = Some stbl' ->
    list_forall2 (fun se se' =>
                    reloc_symbol get_reloc_offset se = Some se'
                 ) stbl stbl'.
Proof.
  unfold reloc_symbtable. induction stbl; simpl; intros; eauto.
  - inv H. constructor.
  - destruct (fold_right (reloc_iter get_reloc_offset) (Some []) stbl) eqn:?.
    + simpl in H. destr_in H. inv H. constructor; auto.
    + simpl in H. congruence.
Qed.

Lemma norepet_reloc_symbtable:
  forall get_reloc_offset stbl stbl',
    list_norepet symbentry_id ## stbl ->
    reloc_symbtable get_reloc_offset stbl = Some stbl' ->
    list_norepet symbentry_id ## stbl'.
Proof.
  intros.
  apply reloc_symbtable_eq in H0.
  revert H0 H; induction 1; simpl; intros; eauto.
  inv H1; constructor; auto.
  assert (symbentry_id a1 = symbentry_id b1).
  unfold reloc_symbol in H.  repeat destr_in H; simpl in *; eauto.
  intro IN; apply H4.
  rewrite in_map_iff in IN |- *. decompose [ex and] IN.
  eapply list_forall2_in_right in H6. 2: eauto.
  decompose [ex and] H6. exists x0; split; auto.
  unfold reloc_symbol in H8.  repeat destr_in H8; simpl in *; eauto. congruence.
Qed.

Lemma reloc_symbtable_to_tree:
  forall stbl stbl' get_reloc_ofs x se
         (NR: list_norepet symbentry_id ## stbl'),
    Maps.PTree.get x (symbtable_to_tree stbl) = Some se ->
    reloc_symbtable get_reloc_ofs stbl = Some stbl' ->
    exists se',
      reloc_symbol get_reloc_ofs se = Some se' /\
      Maps.PTree.get x (symbtable_to_tree stbl') = Some se'.
Proof.
  intros. rewrite get_symbtable_to_tree in H |- *.
  apply reloc_symbtable_eq in H0.
  apply Maps.PTree_Properties.in_of_list in H.
  rewrite in_map_iff in H. destruct H as (x0 & eq & IN). inv eq.
  edestruct list_forall2_in_left as (se' & IN' & EQ). eauto. eauto. simpl in EQ.
  exists se'. split. auto.
  apply Maps.PTree_Properties.of_list_norepet.
  rewrite map_map. auto. 
  rewrite in_map_iff. eexists; split. 2: eauto.
  f_equal.
  unfold reloc_symbol in EQ; repeat destr_in EQ; auto.
Qed.

Lemma ursymb_ok_r:
  forall stbl a r0 stbl' s stbl2 get_reloc_ofs,
    link_symbtable stbl stbl' = Some s ->
    reloc_symbtable get_reloc_ofs stbl2 = Some stbl' ->
    update_reloc_symb stbl2 (gen_symb_index_map stbl2) a = Some r0 ->
    exists r1,
      update_reloc_symb stbl2 (gen_symb_index_map s) a = Some r1.
Proof.
  unfold update_reloc_symb.
  intros. repeat destr_in H1.
  exploit link_symbtable_norepet. eauto. intros (nr1 & nr2 & nr3 & check).
  assert (NR2: list_norepet symbentry_id ## stbl2).
  {
    clear - H0 nr2.
    apply reloc_symbtable_eq in H0.
    revert H0 nr2.
    induction 1; simpl; intros; eauto.
    inv nr2. constructor; auto.
    assert (symbentry_id a1 = symbentry_id b1).
    unfold reloc_symbol in H.  repeat destr_in H; simpl in *; eauto.
    intro IN; apply H3.
    rewrite in_map_iff in IN |- *. decompose [ex and] IN.
    eapply list_forall2_in_left in H6. 2: eauto.
    decompose [ex and] H6. exists x0; split; auto.
    unfold reloc_symbol in H8.  repeat destr_in H8; simpl in *; eauto. congruence.
  }
  exploit (get_symb_index_map_symbtable_to_tree). 2: eauto. auto.
  intros (se & GET & EQ & stree).
  edestruct reloc_symbtable_to_tree as (se' & RELSYMB & GET'). 3: eauto. 2: eauto. auto.
  exploit link_symbtable_ok_l. eauto. intro EQsymb. rewrite GET' in EQsymb.
  destruct (Maps.PTree.get (symbentry_id v) (symbtable_to_tree stbl)) eqn:STBLGET.
  specialize (check _ _ STBLGET).
  unfold link_symbtable_check in check. rewrite GET' in check.
  unfold link_symb_merge in EQsymb.
  destr_in check.
  exploit symbtable_to_tree_get_symb_index_map. 3: intros (A & n0 & B).
  3: rewrite B; eauto. auto.
  erewrite link_symbtable_ok_l. 2: eauto.
  rewrite GET'. rewrite STBLGET. simpl. eauto.
  simpl in EQsymb.
  exploit symbtable_to_tree_get_symb_index_map. 3: intros (A & n0 & B).
  3: rewrite B; eauto. auto.
  erewrite link_symbtable_ok_l. 2: eauto.
  rewrite GET'. rewrite STBLGET. simpl. eauto.
Qed.

Lemma urs_ok:
  forall stbl x x' stbl' s,
    link_symbtable stbl stbl' = Some s ->
    update_reloctable_symb stbl (gen_symb_index_map stbl) x = Some x' ->
    exists x'',
      update_reloctable_symb stbl (gen_symb_index_map s) x = Some x''.
Proof.
  unfold update_reloctable_symb.
  intros stbl x x' stbl' s LS.
  generalize (@nil RelocTblParams.V).
  revert x x'.
  induction x; simpl; intros; eauto.
  destruct (fold_right (acc_update_reloc_symb stbl (gen_symb_index_map stbl)) (Some l) x) eqn:?.
  - simpl in H.
    repeat destr_in H.
    edestruct IHx. eauto. rewrite H. simpl.
    edestruct ursymb_ok; eauto. rewrite H0. eauto.
  - simpl in H. congruence.
Qed.

Lemma urs_ok_r:
  forall stbl x x' stbl' s stbl2 get_reloc_ofs,
    link_symbtable stbl stbl' = Some s ->
    reloc_symbtable get_reloc_ofs stbl2 = Some stbl' ->
    update_reloctable_symb stbl2 (gen_symb_index_map stbl2) x = Some x' ->
    exists x'',
      update_reloctable_symb stbl2 (gen_symb_index_map s) x = Some x''.
Proof.
  unfold update_reloctable_symb.
  intros stbl x x' stbl' s stbl2 get_reloc_ofs LS RS.
  generalize (@nil RelocTblParams.V).
  revert x x'.
  induction x; simpl; intros; eauto.
  destruct (fold_right (acc_update_reloc_symb stbl2 (gen_symb_index_map stbl2)) (Some l) x) eqn:?.
  - simpl in H.
    repeat destr_in H.
    edestruct IHx. eauto. rewrite H. simpl.
    edestruct ursymb_ok_r; eauto. rewrite H0. eauto.
  - simpl in H. congruence.
Qed.


Lemma list_forall2_nth:
  forall {A B} P (l1 : list A) (l2: list B)
         (LF: list_forall2 P l1 l2)
         n x1
         (NTH: nth_error l1 n = Some x1),
  exists x2,
    nth_error l2 n = Some x2 /\ P x1 x2.
Proof.
  induction 1; simpl; intros; eauto.
  rewrite nth_error_nil in NTH. easy.
  destruct n.
  - simpl in *. inv NTH. eauto.
  - simpl in *. eauto.
Qed.

Lemma update_reloc_reloc:
  forall dsize csize stbl stbl'
         (RS : list_forall2
                 (fun se se' : symbentry => reloc_symbol (reloc_offset_fun dsize csize) se = Some se') stbl
                 stbl')
         sim a r0
         (URS: update_reloc_symb stbl sim a = Some r0),
  exists r1, update_reloc_symb stbl' sim a = Some r1.
Proof.
  unfold update_reloc_symb.
  intros. repeat destr_in URS.
  unfold SymbTable.get in *.
  edestruct @list_forall2_nth as (v2 & NTH & P). eauto. eauto.
  setoid_rewrite NTH. simpl in P.
  unfold reloc_symbol in P. repeat destr_in P; simpl; rewrite Heqo0; eauto.
Qed.

Lemma update_reloctable_reloc:
  forall stbl sim x x' dsize csize stbl',
    update_reloctable_symb stbl sim x = Some x' ->
    reloc_symbtable (reloc_offset_fun dsize csize) stbl = Some stbl' ->
    exists x'', update_reloctable_symb stbl' sim x = Some x''.
Proof.
  unfold update_reloctable_symb.
  intros stbl sim x x' dsize csize stbl' URS RS.
  apply reloc_symbtable_eq in RS.
  revert x x' URS.
  induction x; simpl; intros; eauto.
  destruct (fold_right (acc_update_reloc_symb stbl sim) (Some []) x) eqn:?; simpl in URS; try congruence.
  destr_in URS. inv URS.
  edestruct IHx. eauto. rewrite H. simpl.
  edestruct update_reloc_reloc. eauto. eauto. rewrite H0; eauto.
Qed.

Lemma fold_acc_init_data_size:
  forall sim l z0 l0 z1 l1,
    fold_left (acc_init_data sim) l (OK (z0, l0)) = OK (z1, l1) ->
    z1 = init_data_list_size l + z0.
Proof.
  induction l; simpl; intros; eauto.
  inv H; auto.
  unfold bind in H; destr_in H. apply IHl in H. subst. omega.
  rewrite fold_acc_init_data_error in H; congruence.
Qed.

Lemma tidl_app:
  forall sim l1 l2 l1' l2',
    transl_init_data_list sim l1 = OK l1' ->
    transl_init_data_list sim l2 = OK l2' ->
    transl_init_data_list sim (l1 ++ l2) =
    OK ((shift_relocentry_offset (init_data_list_size l1)) ## l2' ++ l1').
Proof.
  intros. unfold transl_init_data_list in *.
  monadInv H. monadInv H0. repeat destr_in EQ0. repeat destr_in EQ2.
  rewrite fold_left_app.
  rewrite fold_acc_init_data_ok. rewrite EQ. simpl.
  rewrite fold_acc_init_data_ok. rewrite EQ1. simpl.
  rewrite app_nil_r. f_equal. f_equal.
  unfold shift_relocentry_offset.
  apply list_map_exten. intros. f_equal. f_equal.
  apply fold_acc_init_data_size in EQ. omega.
  erewrite list_map_exten. apply map_id. intros. simpl. destruct x; simpl. f_equal. omega.
Qed.


Lemma acc_update_reloc_symb_eq:
  forall stbl sim l l',
    update_reloctable_symb stbl sim l = Some l' ->
    list_forall2 (fun a b => update_reloc_symb stbl sim a = Some b) l l'.
Proof.
  unfold update_reloctable_symb.
  induction l; simpl; intros; eauto. inv H; constructor.
  destruct (fold_right (acc_update_reloc_symb stbl sim) (Some []) l) eqn:?.
  simpl in H. destr_in H. inv H.
  constructor; eauto.
  simpl in H. congruence.
Qed.

Lemma nat_diff_S_add:
  forall n m,
    n <> Datatypes.S (m + n).
Proof.
  intros. omega.
Qed.

Lemma list_forall2_app_inv_l:
  forall {A B} (P: A -> B -> Prop) l1 l2 l',
    list_forall2 P (l1 ++ l2) l' ->
    exists l1' l2',
      list_forall2 P l1 l1' /\
      list_forall2 P l2 l2' /\
      l' = l1' ++ l2'.
Proof.
  induction l1; simpl; intros; eauto.
  exists [], l'; repeat split. constructor. auto.
  inv H. edestruct IHl1 as (l1' & l2' & LF1 & LF2 & SPLIT). eauto. subst.
  exists (b1::l1'), l2'; repeat split; auto. constructor; auto.
Qed.

Lemma list_forall2_map:
  forall {A} (P: A -> A -> Prop) f
         (Fprop: forall x y, P x y -> P (f x) (f y))
         l l',
    list_forall2 P l l' ->
    list_forall2 P (f ## l) (f ## l').
Proof.
  induction 2; simpl; intros; eauto. constructor.
  constructor; eauto.
Qed.

Lemma aurs_aid_ok:
  forall stbl sim l l' l'' l0' z0 l0 z1
         (LF: list_forall2 (fun a b => update_reloc_symb stbl sim a = Some b) l' l'')
         (LF: list_forall2 (fun a b => update_reloc_symb stbl sim a = Some b) l0 l0')
         (FL : fold_left (acc_init_data (gen_symb_index_map stbl)) l (OK (z0, l0)) = OK (z1, l' ++ l0)),
    fold_left (acc_init_data sim) l (OK (z0, l0')) = OK (z1, l'' ++ l0').
Proof.
  induction l; simpl; intros; eauto. inv FL.
  destruct l'. inv LF. simpl. auto.
  apply (f_equal (@length _)) in H1. rewrite app_length in H1. simpl in H1. exfalso.
  apply nat_diff_S_add in H1. auto.
  unfold bind in FL. destr_in FL.
  rewrite fold_acc_init_data_ok in FL. unfold bind in FL. destr_in FL. destr_in FL. inv FL.
  rewrite app_assoc in H1. apply app_inv_tail in H1. subst.
  edestruct @list_forall2_app_inv_l as (l1' & l2' & LF1 & LF2 & SPLIT). apply LF. subst.
  assert (transl_init_data sim z0 a = OK l2').
  {
    revert LF2 Heqr. clear.
    unfold transl_init_data. intros LF2 EQ.
    repeat destr_in EQ; inv LF2; auto.
    unfold update_reloc_symb in H1. simpl in H1. repeat destr_in H1.
    edestruct in_sim_in_stbl_nth as (se & GET & ID). eauto. subst.
    rewrite Heqo0 in GET; inv GET. rewrite Heqo1. inv H3. reflexivity.
  }
  rewrite H. simpl.
  rewrite fold_acc_init_data_ok.
  erewrite IHl. 3: constructor. simpl. f_equal. f_equal.
  rewrite app_assoc. f_equal. f_equal. rewrite app_nil_r.
  instantiate (1:=
 (fun d : relocentry =>
   {|
   reloc_offset := reloc_offset d - (z0 + init_data_size a);
   reloc_type := reloc_type d;
   reloc_symb := reloc_symb d;
   reloc_addend := reloc_addend d |}) ## l1'
              ). rewrite map_map. simpl. erewrite list_map_exten. apply map_id. simpl; intros.
  destruct x; f_equal. simpl. omega.
  apply list_forall2_map.
  {
    clear. unfold update_reloc_symb. simpl. intros.
    repeat destr_in H. simpl. auto.
  }
  apply LF1.
  setoid_rewrite Heqr0. f_equal. f_equal.
  rewrite map_map. simpl. rewrite app_nil_r.
  erewrite list_map_exten. symmetry. apply map_id. simpl; intros. destruct x; f_equal; simpl; auto. omega.
  rewrite fold_acc_init_data_error in FL. congruence.
Qed.

Lemma tidl_urs:
  forall stbl sim l l' l'',
    transl_init_data_list (gen_symb_index_map stbl) l = OK l' ->
    update_reloctable_symb stbl sim l' = Some l'' ->
    transl_init_data_list sim l = OK l''.
Proof.
  unfold transl_init_data_list.
  intros. monadInv H. repeat destr_in EQ0.
  erewrite aurs_aid_ok. 3: constructor.
  3: rewrite app_nil_r; eauto.
  2: apply acc_update_reloc_symb_eq; eauto.
  simpl. rewrite app_nil_r; auto.
Qed.

Lemma tidl_link_reloctable:
  forall stbl1 stbl2 csize s0 s1 l l' x0 x3,
    link_symbtable stbl1 s0 = Some s1 ->
    reloc_symbtable (reloc_offset_fun (sec_size (sec_data l)) csize)
                    stbl2 = Some s0 ->
    transl_init_data_list (gen_symb_index_map stbl1) l = OK x0 ->
    transl_init_data_list (gen_symb_index_map stbl2) l' = OK x3 ->
    exists t1' t2',
      update_reloctable_symb stbl1 (gen_symb_index_map s1) x0 = Some t1' /\
      update_reloctable_symb stbl2 (gen_symb_index_map s1) x3 = Some t2' /\
      link_reloctable (init_data_list_size l) stbl1 stbl2
                      (gen_symb_index_map s1) x0 x3 =
      Some (t1' ++ (shift_relocentry_offset (init_data_list_size l)) ## t2') /\
      transl_init_data_list (gen_symb_index_map s1) (l ++ l') =
      OK((shift_relocentry_offset (init_data_list_size l)) ## t2' ++ t1').
Proof.
  intros.
  unfold link_reloctable.
  
  edestruct update_reloctable_symb_ok.
  eapply transl_init_data_list_gets in H1. eauto.

  edestruct update_reloctable_symb_ok.
  eapply transl_init_data_list_gets in H2. eauto.

  edestruct urs_ok. eauto. apply H3.
  edestruct urs_ok_r. eauto. eauto. eauto.
  rewrite H5. rewrite H6.

  exists x2, x4; repeat split.
  erewrite tidl_app.
  2: eapply tidl_urs; eauto.
  2: eapply tidl_urs; eauto.
  auto.
Qed.

Lemma transl_code_gets :
  forall (stbl1 : symbtable) c (x0 : reloctable),
    transl_code (gen_symb_index_map stbl1) false c = OK x0 ->
    Forall
      (fun e : relocentry =>
         exists (se : SymbTblParams.V) (i : N),
           SymbTable.get (reloc_symb e) stbl1 = Some se /\
           Maps.PTree.get (symbentry_id se) (gen_symb_index_map stbl1) = Some i) x0.
Proof.
  unfold transl_code.
  intros. monadInv H.
  revert x x0 EQ.

  assert (
      forall z0 x0 z1 x1,
        fold_left (acc_instrs (gen_symb_index_map stbl1) false) c (OK (z0, x0)) = OK (z1, x1) ->
        Forall
          (fun e : relocentry =>
             exists (se : SymbTblParams.V) (i : N),
               SymbTable.get (reloc_symb e) stbl1 = Some se /\
               Maps.PTree.get (symbentry_id se) (gen_symb_index_map stbl1) = Some i) x0 ->
        Forall
          (fun e : relocentry =>
             exists (se : SymbTblParams.V) (i : N),
               SymbTable.get (reloc_symb e) stbl1 = Some se /\
               Maps.PTree.get (symbentry_id se) (gen_symb_index_map stbl1) = Some i) x1
    ).
  {
    clear. induction c; simpl; intros; eauto.
    - inv H; auto.
    - destruct (ready_for_proof a) eqn:?.
      + destruct (transl_instr' (gen_symb_index_map stbl1) z0 a) eqn:?.
        2: simpl in H. 2: rewrite fold_acc_instrs_error in H; congruence.
        simpl in H.
        exploit IHc. eauto.
        rewrite Forall_forall in *.
        intro x. rewrite in_app. intros [INr | INx0]; eauto.
        unfold transl_instr' in Heqr.
        repeat destr_in Heqr; simpl in *; try intuition congruence.
        * monadInv H2. unfold compute_instr_abs_relocentry in EQ.
          monadInv EQ. repeat destr_in EQ1.
          destruct INr as [EQ|[]]. subst. simpl.
          exploit in_sim_in_stbl_nth. eauto. intros (s & GET & ID).
          (do 2 eexists); split. eauto. subst. eauto.
        * monadInv H2. unfold compute_instr_disp_relocentry in EQ.
          destr_in EQ.  unfold compute_instr_abs_relocentry in EQ.
          monadInv EQ. repeat destr_in EQ1.
          destruct INr as [EQ|[]]. subst. simpl.
          exploit in_sim_in_stbl_nth. eauto. intros (s & GET & ID).
          (do 2 eexists); split. eauto. subst. eauto.
        * monadInv H2. unfold compute_instr_disp_relocentry in EQ.
          destr_in EQ.  unfold compute_instr_abs_relocentry in EQ.
          monadInv EQ. repeat destr_in EQ1.
          destruct INr as [EQ|[]]. subst. simpl.
          exploit in_sim_in_stbl_nth. eauto. intros (s & GET & ID).
          (do 2 eexists); split. eauto. subst. eauto.
        * monadInv H2. unfold compute_instr_disp_relocentry in EQ.
          destr_in EQ.  unfold compute_instr_abs_relocentry in EQ.
          monadInv EQ. repeat destr_in EQ1.
          destruct INr as [EQ|[]]. subst. simpl.
          exploit in_sim_in_stbl_nth. eauto. intros (s & GET & ID).
          (do 2 eexists); split. eauto. subst. eauto.
        * monadInv H2. unfold compute_instr_rel_relocentry in EQ.
          monadInv EQ. repeat destr_in EQ2.
          destruct INr as [EQr|[]]. subst. simpl.
          exploit in_sim_in_stbl_nth. eauto. intros (s & GET & ID).
          (do 2 eexists); split. eauto. subst. eauto.
        (* * monadInv H2. unfold compute_instr_rel_relocentry in EQ. *)
        (*   monadInv EQ. repeat destr_in EQ2. *)
        (*   destruct INr as [EQr|[]]. subst. simpl. *)
        (*   exploit in_sim_in_stbl_nth. eauto. intros (s & GET & ID). *)
        (*   (do 2 eexists); split. eauto. subst. eauto. *)
        * monadInv H2. unfold compute_instr_disp_relocentry in EQ.
          destr_in EQ.  unfold compute_instr_abs_relocentry in EQ.
          monadInv EQ. repeat destr_in EQ1.
          destruct INr as [EQ|[]]. subst. simpl.
          exploit in_sim_in_stbl_nth. eauto. intros (s & GET & ID).
          (do 2 eexists); split. eauto. subst. eauto.
        * monadInv H2. unfold compute_instr_disp_relocentry in EQ.
          destr_in EQ.  unfold compute_instr_abs_relocentry in EQ.
          monadInv EQ. repeat destr_in EQ1.
          destruct INr as [EQ|[]]. subst. simpl.
          exploit in_sim_in_stbl_nth. eauto. intros (s & GET & ID).
          (do 2 eexists); split. eauto. subst. eauto.
        * auto.
      + cbn in H.
        rewrite fold_acc_instrs_error in H. congruence.
  }
  intros. eapply H. eauto. constructor.
Qed.


Lemma fold_acc_instrs_split:
  forall c1 sim z0 cr1 cr2 z1,
    fold_left (acc_instrs sim false) c1 (OK (z0, cr1)) = OK (z1, cr2) ->
    exists cr2',
      cr2 = cr2' ++ cr1.
Proof.
  induction c1; simpl; intros; eauto.
  inv H.
  exists nil. reflexivity.
  destruct (ready_for_proof a) eqn:?.
  - destruct (transl_instr' sim z0 a) eqn:?.
    simpl in H.
    apply IHc1 in H.
    destruct H. subst. exists (x ++ l). rewrite <- app_assoc. reflexivity.
    simpl in H; rewrite fold_acc_instrs_error in H; congruence.
  - cbn in H.
    rewrite fold_acc_instrs_error in H. congruence. 
Qed.


Lemma update_reloctable_symb_gen:
  forall stbl1 sim l1 l1' l2',
    fold_right (acc_update_reloc_symb stbl1 sim) (Some []) l1 = Some l1' ->
    fold_right (acc_update_reloc_symb stbl1 sim) (Some l2') l1 = Some (l1' ++ l2').
Proof.
  induction l1; simpl; intros; eauto. inv H. reflexivity.
  destruct (fold_right (acc_update_reloc_symb stbl1 sim) (Some []) l1) eqn:?; simpl in *; try congruence.
  repeat destr_in H.
  erewrite IHl1; eauto. simpl. rewrite Heqo0. auto.
Qed.

Lemma update_reloctable_symb_gen':
  forall stbl1 sim l1 l2' l12,
    fold_right (acc_update_reloc_symb stbl1 sim) (Some l2') l1 = Some l12 ->
    exists l1',
      fold_right (acc_update_reloc_symb stbl1 sim) (Some []) l1 = Some l1' /\
      l12 = l1' ++ l2'.
Proof.
  induction l1; simpl; intros; eauto. inv H. eexists; split; eauto.
  destruct (fold_right (acc_update_reloc_symb stbl1 sim) (Some l2') l1) eqn:?; simpl in *; try congruence.
  repeat destr_in H.
  edestruct IHl1 as (l1' & FR & EQ); eauto. rewrite FR. simpl. rewrite Heqo0.
  eexists; split; eauto. simpl. subst. reflexivity.
Qed.


Lemma update_reloctable_symb_app:
  forall stbl1 sim l1 l2 l1' l2',
    update_reloctable_symb stbl1 sim l1 = Some l1' ->
    update_reloctable_symb stbl1 sim l2 = Some l2' ->
    update_reloctable_symb stbl1 sim (l1 ++ l2) = Some (l1' ++ l2').
Proof.
  unfold update_reloctable_symb.
  intros.
  rewrite fold_right_app. setoid_rewrite H0.
  eapply update_reloctable_symb_gen; eauto.
Qed.

Lemma fold_acc_update_error:
  forall stbl1 sim l1,
    fold_right (acc_update_reloc_symb stbl1 sim) None l1 = None.
Proof.
  induction l1; simpl; intros; eauto.
  rewrite IHl1. simpl. auto.
Qed.

Lemma update_reloctable_symb_split:
  forall stbl1 sim l1 l2 l12,
    update_reloctable_symb stbl1 sim (l1 ++ l2) = Some l12 ->
    exists l1' l2',
      l12 = l1' ++ l2' /\
      update_reloctable_symb stbl1 sim l1 = Some l1' /\
      update_reloctable_symb stbl1 sim l2 = Some l2'.

Proof.
  unfold update_reloctable_symb.
  intros.
  rewrite fold_right_app in H.
  destruct (fold_right (acc_update_reloc_symb stbl1 sim) (Some []) l2) eqn:?.
  setoid_rewrite Heqo in H.
  edestruct update_reloctable_symb_gen' as (l1' & Fr & EQ). apply H.
  setoid_rewrite Fr.
  subst. (do 2 eexists); repeat split.
  setoid_rewrite Heqo in H. rewrite fold_acc_update_error in H. congruence.
Qed.

Lemma transl_instr_reloc:
  forall stbl1 s1 z0 a l l2',
    transl_instr (gen_symb_index_map stbl1) false z0 a = OK l ->
    update_reloctable_symb stbl1 (gen_symb_index_map s1) l = Some l2' ->
    transl_instr (gen_symb_index_map s1) false z0 a = OK l2'.
Proof.
  intros. cbn in H. destr_in H.
  unfold transl_instr' in *.
  repeat destr_in H; simpl in *; repeat destr_in H0; auto; try congruence.
  - monadInv H2. unfold compute_instr_abs_relocentry in *. monadInv EQ. repeat destr_in EQ1.
    rewrite EQ0. simpl. simpl in *. repeat destr_in H1.
    unfold update_reloc_symb in Heqo0. simpl in *. repeat destr_in Heqo0.
    edestruct in_sim_in_stbl_nth as (se & GET & ID). apply Heqo. rewrite Heqo1 in GET. inv GET.
    rewrite Heqo2. simpl. auto.
  - monadInv H2. unfold compute_instr_disp_relocentry in *. destr_in EQ.
    unfold compute_instr_abs_relocentry in *.
    monadInv EQ. repeat destr_in EQ1.
    rewrite EQ0. simpl. simpl in *. repeat destr_in H1.
    unfold update_reloc_symb in Heqo0. simpl in *. repeat destr_in Heqo0.
    edestruct in_sim_in_stbl_nth as (se & GET & ID). apply Heqo. rewrite Heqo1 in GET. inv GET.
    rewrite Heqo2. simpl. auto.
  - monadInv H2. unfold compute_instr_disp_relocentry in *. destr_in EQ.
    unfold compute_instr_abs_relocentry in *.
    monadInv EQ. repeat destr_in EQ1.
    rewrite EQ0. simpl. simpl in *. repeat destr_in H1.
    unfold update_reloc_symb in Heqo0. simpl in *. repeat destr_in Heqo0.
    edestruct in_sim_in_stbl_nth as (se & GET & ID). apply Heqo. rewrite Heqo1 in GET. inv GET.
    rewrite Heqo2. simpl. auto.
  - monadInv H2. unfold compute_instr_disp_relocentry in *. destr_in EQ.
    unfold compute_instr_abs_relocentry in *.
    monadInv EQ. repeat destr_in EQ1.
    rewrite EQ0. simpl. simpl in *. repeat destr_in H1.
    unfold update_reloc_symb in Heqo0. simpl in *. repeat destr_in Heqo0.
    edestruct in_sim_in_stbl_nth as (se & GET & ID). apply Heqo. rewrite Heqo1 in GET. inv GET.
    rewrite Heqo2. simpl. auto.
  - monadInv H2. unfold compute_instr_rel_relocentry in *. monadInv EQ.
    repeat destr_in EQ2.
    rewrite EQ0. rewrite EQ. simpl. simpl in *. repeat destr_in H1.
    unfold update_reloc_symb in Heqo0. simpl in *. repeat destr_in Heqo0.
    edestruct in_sim_in_stbl_nth as (se & GET & ID). apply Heqo. rewrite Heqo1 in GET. inv GET.
    rewrite Heqo2. simpl. auto.
  (* - monadInv H2. unfold compute_instr_rel_relocentry in *. monadInv EQ. *)
  (*   repeat destr_in EQ2. *)
  (*   rewrite EQ0. rewrite EQ. simpl. simpl in *. repeat destr_in H1. *)
  (*   unfold update_reloc_symb in Heqo0. simpl in *. repeat destr_in Heqo0. *)
  (*   edestruct in_sim_in_stbl_nth as (se & GET & ID). apply Heqo. rewrite Heqo1 in GET. inv GET. *)
  (*   rewrite Heqo2. simpl. auto. *)
  - monadInv H2. unfold compute_instr_disp_relocentry in *. destr_in EQ.
    unfold compute_instr_abs_relocentry in *.
    monadInv EQ. repeat destr_in EQ1.
    rewrite EQ0. simpl. simpl in *. repeat destr_in H1.
    unfold update_reloc_symb in Heqo0. simpl in *. repeat destr_in Heqo0.
    edestruct in_sim_in_stbl_nth as (se & GET & ID). apply Heqo. rewrite Heqo1 in GET. inv GET.
    rewrite Heqo2. simpl. auto.
  - monadInv H2. unfold compute_instr_disp_relocentry in *. destr_in EQ.
    unfold compute_instr_abs_relocentry in *.
    monadInv EQ. repeat destr_in EQ1.
    rewrite EQ0. simpl. simpl in *. repeat destr_in H1.
    unfold update_reloc_symb in Heqo0. simpl in *. repeat destr_in Heqo0.
    edestruct in_sim_in_stbl_nth as (se & GET & ID). apply Heqo. rewrite Heqo1 in GET. inv GET.
    rewrite Heqo2. simpl. auto.
Qed.


Lemma transl_instr_translate:
  forall sim z a l n,
    transl_instr sim false z a = OK l ->
    transl_instr sim false (z + n) a = OK (shift_relocentry_offset n) ## l.
Proof.
  unfold transl_instr.
  intros. destr_in H.
  unfold transl_instr' in H.
  repeat destr_in H; simpl in *; auto; try congruence.
  - monadInv H1. unfold compute_instr_abs_relocentry in *.
    monadInv EQ. repeat destr_in EQ1. unfold shift_relocentry_offset.
    rewrite EQ0; simpl. f_equal. f_equal. f_equal. omega.
  - monadInv H1. unfold compute_instr_disp_relocentry in *. destr_in EQ.
    unfold compute_instr_abs_relocentry in *.
    monadInv EQ. repeat destr_in EQ1. unfold shift_relocentry_offset.
    rewrite EQ0; simpl. f_equal. f_equal. f_equal. omega.
  - monadInv H1. unfold compute_instr_disp_relocentry in *. destr_in EQ.
    unfold compute_instr_abs_relocentry in *.
    monadInv EQ. repeat destr_in EQ1. unfold shift_relocentry_offset.
    rewrite EQ0; simpl. f_equal. f_equal. f_equal. omega.
  - monadInv H1. unfold compute_instr_disp_relocentry in *. destr_in EQ.
    unfold compute_instr_abs_relocentry in *.
    monadInv EQ. repeat destr_in EQ1. unfold shift_relocentry_offset.
    rewrite EQ0; simpl. f_equal. f_equal. f_equal. omega.
  - monadInv H1. unfold compute_instr_rel_relocentry in *.
    monadInv EQ. repeat destr_in EQ2. unfold shift_relocentry_offset.
    rewrite EQ0, EQ; simpl. f_equal. f_equal. f_equal. omega.
  (* - monadInv H1. unfold compute_instr_rel_relocentry in *. *)
  (*   monadInv EQ. repeat destr_in EQ2. unfold shift_relocentry_offset. *)
  (*   rewrite EQ0, EQ; simpl. f_equal. f_equal. f_equal. omega. *)
  - monadInv H1. unfold compute_instr_disp_relocentry in *. destr_in EQ.
    unfold compute_instr_abs_relocentry in *.
    monadInv EQ. repeat destr_in EQ1. unfold shift_relocentry_offset.
    rewrite EQ0; simpl. f_equal. f_equal. f_equal. omega.
  - monadInv H1. unfold compute_instr_disp_relocentry in *. destr_in EQ.
    unfold compute_instr_abs_relocentry in *.
    monadInv EQ. repeat destr_in EQ1. unfold shift_relocentry_offset.
    rewrite EQ0; simpl. f_equal. f_equal. f_equal. omega.
Qed.

Lemma fold_acc_instrs_translate:
  forall sim c z0 z1 l1 l2 n,
    fold_left (acc_instrs sim false) c (OK (z0, l1)) = OK (z1, l2) ->
    fold_left (acc_instrs sim false) c (OK (z0 + n, (shift_relocentry_offset n) ## l1)) =
    OK (z1 + n, (shift_relocentry_offset n) ## l2).
Proof.
  induction c; simpl; intros; eauto.
  - inv H. auto.
  - destruct (ready_for_proof a) eqn:?.
    + destruct (transl_instr' sim z0 a) eqn:?; simpl in *.
      assert (transl_instr sim false z0 a = OK l).
      { cbn. rewrite Heqb. auto. }
      eapply transl_instr_translate in H0. 
      cbn in H0. rewrite Heqb in H0. rewrite H0.
      eauto. simpl.
      erewrite  <- IHc. 2: eauto.
      f_equal. rewrite map_app.
      f_equal. f_equal. omega.
      rewrite fold_acc_instrs_error in H. congruence.
    + cbn in H.
      rewrite fold_acc_instrs_error in H. congruence. 
Qed.

Lemma update_shift:
  forall stbl sim n c c',
    update_reloctable_symb stbl sim c = Some c' ->
    update_reloctable_symb stbl sim ((shift_relocentry_offset n) ## c) = Some (shift_relocentry_offset n) ## c'.
Proof.
  induction c; simpl; intros; eauto.
  - inv H; auto.
  - destruct (update_reloctable_symb stbl sim c) eqn:?.
    simpl in H. repeat destr_in H.
    erewrite IHc; eauto. simpl. unfold update_reloc_symb in *. repeat destr_in Heqo0. simpl.
    rewrite Heqo1, Heqo2. auto.
    simpl in H; congruence.
Qed.

Lemma fold_acc_instrs_list:
  forall sim c z0 cr1,
    fold_left (acc_instrs sim false) c (OK (z0, cr1)) =
    bind2 (fold_left (acc_instrs sim false) c (OK (z0, [])))
          (fun z cr0 => OK (z, cr0 ++ cr1)).
Proof.
  induction c; simpl; intros; eauto.
  - destruct (ready_for_proof a) eqn:?.
    + destruct (transl_instr' sim z0 a) eqn:?; simpl in *; try congruence.
      rewrite (IHc _ (l ++ cr1)).
      rewrite (IHc _ (l ++ [])).
      rewrite app_nil_r.
      unfold bind2. destr. destr. rewrite <- app_assoc. auto.
      rewrite fold_acc_instrs_error. reflexivity.
    + cbn.
      rewrite fold_acc_instrs_error. cbn. auto.
Qed.


Lemma transl_code_size':
  forall sim c z1 l z2 l',
    fold_left (acc_instrs sim false) c (OK (z1, l)) = OK (z2, l') ->
    z2 = z1 + code_size c.
Proof.
  induction c; simpl; intros; eauto.
  inv H. omega.
  unfold bind in H. destr_in H; simpl in H.
  2: rewrite fold_acc_instrs_error in H; congruence.
  apply IHc in H. omega.
Qed.

Lemma transl_code_app:
  forall stbl1 stbl2 stbl2' s1 c1 c2 c1' c2' dsize,
    reloc_symbtable (reloc_offset_fun dsize (code_size c1)) stbl2 = Some stbl2' ->
    link_symbtable stbl1 stbl2' = Some s1 ->
    transl_code (gen_symb_index_map stbl1) false c1 = OK c1' ->
    transl_code (gen_symb_index_map stbl2) false c2 = OK c2' ->
    exists c2'' c2''',
      link_reloctable (code_size c1) stbl1 stbl2 (gen_symb_index_map s1) c1' c2' = Some c2'' /\
      transl_code (gen_symb_index_map s1) false (c1 ++ c2) = OK (c2''') /\
      Permutation.Permutation c2'' c2'''.
Proof.
  intros.
  unfold transl_code, link_reloctable in *.

  edestruct update_reloctable_symb_ok.
  eapply transl_code_gets in H1. eauto.
  edestruct urs_ok. eauto. eauto. rewrite H4.

  edestruct update_reloctable_symb_ok.
  eapply transl_code_gets in H2. eauto.
  edestruct urs_ok_r. eauto. eauto. eauto.
  rewrite H6.

  rewrite fold_left_app.

  monadInv H1. monadInv H2.
  assert (
      forall stbl1 s1 c1 z0 cr1 z1 cr2 cr3 cr1',
        fold_left (acc_instrs (gen_symb_index_map stbl1) false) c1 (OK (z0, cr1)) = OK (z1, cr2 ++ cr1) ->
        update_reloctable_symb stbl1 (gen_symb_index_map s1) cr2 = Some cr3 ->
        update_reloctable_symb stbl1 (gen_symb_index_map s1) cr1 = Some cr1' ->
        fold_left (acc_instrs (gen_symb_index_map s1) false) c1 (OK (z0, cr1')) = OK (z1, cr3 ++ cr1')
    ).
  {
    clear.
    induction c1; simpl; intros; eauto.
    - inv H. destruct cr2. simpl in H0. inv H0. simpl.  auto.
      apply (f_equal (@length _)) in H4.
      simpl in H4. rewrite app_length in H4. omega.
    - destruct (ready_for_proof a) eqn:?.
      + destruct (transl_instr' (gen_symb_index_map stbl1) z0 a) eqn:?.
        2: simpl in H; rewrite fold_acc_instrs_error in H; congruence.
        simpl in H.

        edestruct fold_acc_instrs_split. apply H.
        rewrite app_assoc in H2. apply app_inv_tail in H2. subst.

        edestruct update_reloctable_symb_split as (l1' & l2' & SPLIT & UR1 & UR2). apply H0.
        rewrite <- app_assoc in H.
        exploit IHc1. apply H. eauto.
        eapply update_reloctable_symb_app. eauto. eauto.

        eapply transl_instr_reloc in UR2. 
        Focus 2. cbn. rewrite Heqb. eauto.
        cbn in UR2. rewrite Heqb in UR2. rewrite UR2.
         simpl. subst. rewrite app_assoc. auto.
      + cbn in H.
        rewrite fold_acc_instrs_error in H. congruence.

  }

  erewrite H1 with (cr1:=[]). 2: rewrite app_nil_r; eauto. 3: reflexivity. 2: eauto.
  simpl.
  rewrite app_nil_r.

  generalize (fold_acc_instrs_translate _ _ _ _ _ _ x3 EQ0). intro EQ1.
  simpl in EQ1.


  rewrite fold_acc_instrs_list.
  erewrite H1 with(cr1:=[]). 4: reflexivity. 3: apply update_shift. 3: apply H6.
  2: rewrite app_nil_r; eauto.
  simpl.
  eauto.

  eexists; eexists. split; [|split]. eauto. eauto.
  rewrite app_nil_r.

  apply transl_code_size' in EQ. rewrite EQ. simpl.
  apply Permutation.Permutation_app_comm.
Qed.


Lemma transl_code'_app:
  forall c1 c2 c1' c2',
    transl_code' false c1 = OK c1' ->
    transl_code' false c2 = OK c2' ->
    transl_code' false (c1 ++ c2) = OK (c1' ++ c2').
Proof.
  unfold transl_code'. intros.
  monadInv H. monadInv H0.
  rewrite fold_left_app. rewrite EQ.
  rewrite fold_acc_id_eliminate_app. rewrite EQ0. simpl. rewrite rev_app_distr. auto.
Qed.

Lemma update_reloctable_symb_permut:
  forall stbl s dreloc1 dreloc2,
    Permutation.Permutation dreloc1 dreloc2 ->
    forall dreloc1',
      update_reloctable_symb stbl s dreloc1 = Some dreloc1' ->
      exists dreloc2',
        update_reloctable_symb stbl s dreloc2 = Some dreloc2' /\
        Permutation.Permutation dreloc1' dreloc2'.
Proof.
  unfold update_reloctable_symb.
  induction 1; simpl; intros; eauto.
  - unfold acc_update_reloc_symb in H0 at 1. repeat destr_in H0.
    edestruct IHPermutation as (dreloc2' & FR & PERM). eauto.
    rewrite FR. simpl. rewrite Heqo0. eexists; split; eauto.
  - unfold acc_update_reloc_symb in H at 1 2.
    unfold acc_update_reloc_symb at 1 2.
    repeat destr_in H. repeat destr_in Heqo.
    eexists; split; eauto.
    apply Permutation.perm_swap.
  - edestruct IHPermutation1 as (dreloc2' & FR & PERM); eauto.
    edestruct IHPermutation2 as (dreloc3' & FR' & PERM'); eauto.
    rewrite FR'. eexists; split; eauto.
    eapply Permutation.perm_trans; eauto.
Qed.


Lemma link_reloctable_permut:
  forall sz stbl1 stbl2 s1 dreloc1 dreloc2 dreloc1' dreloc2' dreloc,
    link_reloctable sz stbl1 stbl2 s1 dreloc1 dreloc2 = Some dreloc ->
    Permutation.Permutation dreloc1 dreloc1' ->
    Permutation.Permutation dreloc2 dreloc2' ->
    exists dreloc',
      link_reloctable sz stbl1 stbl2 s1 dreloc1' dreloc2' = Some dreloc' /\
      Permutation.Permutation dreloc dreloc'.
Proof.
  unfold link_reloctable.
  intros.
  repeat destr_in H.

  edestruct update_reloctable_symb_permut as (r' & URS1 & PERM1). 2: apply Heqo. eauto.
  edestruct update_reloctable_symb_permut as (r0' & URS2 & PERM2). 2: apply Heqo0. eauto.
  rewrite URS1. rewrite URS2.
  eexists; split; eauto.
  apply Permutation.Permutation_app. auto.
  apply Permutation.Permutation_map. auto.
Qed.

Instance reloctablesgen_transflink : @TransfLink _ _ RelocLinking.Linker_reloc_prog RelocLinking1.Linker_reloc_prog match_prog.
Proof.
  red. simpl. 
  unfold match_prog.
  intros. simpl.
  unfold link_reloc_prog.
  unfold transf_program.
  unfold RelocLinking.link_reloc_prog in *.
  simpl in *.
  repeat destr_in H. simpl in *.
  destruct H0 as (tp1' & TP1 & defs1 & public1 & main1 & sectable1 & symbtable1 & strtable1
                  & creloc1 & dreloc1 & senv1).
  destruct H1 as (tp2' & TP2 & defs2 & public2 & main2 & sectable2 & symbtable2 & strtable2
                  & creloc2 & dreloc2 & senv2).
  unfold transf_program in TP1, TP2.
  monadInv TP1; monadInv TP2. simpl in *.
  repeat destr_in EQ2. repeat destr_in EQ5. simpl in *.
  repeat rewrite ? defs1, ? public1, ? main1, ? sectable1, ? symbtable1, ? strtable1, ? senv1 in *.
  repeat rewrite ? defs2, ? public2, ? main2, ? sectable2, ? symbtable2, ? strtable2, ? senv2 in *.
  rewrite Heqo.
  edestruct transl_sectable'_code as (code1 & code1' & EQcode1 & TC1 & EQcode1'). apply EQ1. eauto.
  erewrite transl_sectable'_data. 2: apply EQ1. 2: eauto.
  rewrite EQcode1'.
  exploit link_sectable_ok. eauto. eauto. eauto.
  intros (init1 & init2 & c1 & c2 & c1' & c2' & PS1 & PS2 & TC1' & TC2 & LINK).
  rewrite LINK. simpl.
  rewrite PS1 in Heqo1. vm_compute in Heqo1. inv Heqo1. simpl in Heqo3.
  erewrite transl_code_size. 2: eauto. rewrite Heqo3. rewrite Heqo4. simpl.
  unfold link_data_reloctable. simpl.
  erewrite transl_sectable'_data. 2: eauto. 2: eauto.
  rewrite PS1 in Heqo0. vm_compute in Heqo0. inv Heqo0. simpl.
  exploit transl_sectable_ok. apply EQ. rewrite PS1. cbn. simpl.
  intros (c & ll & EQ10 & EQ11 & TC & TIDL). inv EQ10; inv EQ11. inv H0.
  exploit transl_sectable_ok. apply EQ0. rewrite PS2. cbn. simpl.
  intros (c' & l' & EQ10 & EQ11 & TC' & TIDL'). inv EQ10; inv EQ11.
  unfold link_code_reloctable. simpl.
  rewrite EQcode1'.
  unfold transf_program. simpl.
  unfold transl_sectable.

  rewrite PS1, PS2 in Heqo2. simpl in Heqo2.
  unfold link_sectable in Heqo2. repeat destr_in Heqo2.
  vm_compute in Heqo0; inv Heqo0.
  vm_compute in Heqo1; inv Heqo1.
  vm_compute in Heqo5; inv Heqo5.
  vm_compute in Heqo6; inv Heqo6.
  unfold SecTable.get. simpl.
  simpl in Heqo7. inv Heqo7.
  simpl in Heqo8; inv Heqo8.

  exploit tidl_link_reloctable. eauto. eauto. eauto. eauto.
  intros (t1' & t2' & URS1 & URS2 & LR' & TIDLtp).
  rewrite symbtable1, symbtable2.



  erewrite transl_code'_app by eauto. simpl.
  exploit transl_code_app. eauto. eauto. eauto. eauto.
  intros (c2'' & c2''' & LR & TCtp & PERM).
  
  
  exploit link_reloctable_permut. apply LR.
  apply Permutation.Permutation_sym. eauto.
  apply Permutation.Permutation_sym. eauto.
  intros (creloc' & LRcode & PERMCODE).

  exploit link_reloctable_permut. apply LR'.
  apply Permutation.Permutation_sym. eauto.
  apply Permutation.Permutation_sym. eauto.
  intros (dreloc' & LRdata & PERMDaTA).

  rewrite LRdata.
  erewrite transl_code_size by eauto. rewrite LRcode.

  rewrite TCtp. rewrite TIDLtp. eexists; split. eauto. simpl.
  destruct zlt.
  simpl.

  rewrite ! pred_dec_true.
  eexists; split; eauto. simpl.
  repeat split.
  eapply Permutation.perm_trans.
  apply Permutation.Permutation_sym; eauto. auto.

  eapply Permutation.perm_trans.
  apply Permutation.Permutation_sym; eauto.
  apply Permutation.Permutation_app_comm.

  exploit link_symbtable_norepet; eauto. intuition.

  simpl in Heqo.
  apply link_prog_inv in Heqo. intuition subst. simpl.
  apply Maps.PTree.elements_keys_norepet.

  exfalso.
  
  generalize (code_size_bound (c1' ++ c2')).
  intros. omega.
Qed.
