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
Import ListNotations.

Definition match_prog p tp :=
  transf_program p = OK tp.

Lemma transf_program_match:
  forall p tp, transf_program p = OK tp -> match_prog p tp.
Proof.
  unfold match_prog; intuition.
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
    transl_sectable sim stbl = OK (creloc, dreloc) ->
    exists c l,
      SecTable.get sec_code_id stbl = Some (sec_text c) /\
      SecTable.get sec_data_id stbl = Some (sec_data l) /\
      transl_code sim c = OK creloc /\
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
  unfold transf_program in TRANSF.
  monadInv TRANSF.
  unfold RelocProgSemantics.globalenv. simpl.
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

Axiom nr_defs:
  list_norepet (map fst (prog_defs tprog)).

Axiom symb_table_ok:
  forall id d,
    In (id, d) (prog_defs tprog) ->
    exists dofs1 cofs1,
      In (Symbtablegen.get_symbentry sec_data_id sec_code_id dofs1 cofs1 id d) (prog_symbtable tprog).

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
  clear ge tge.
  unfold match_prog, Reloctablesgen.transf_program in TRANSF.
  monadInv TRANSF. reflexivity.
Qed.
Require Import Lia.


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

Axiom norepet_symbentry_id:
  list_norepet symbentry_id ## (prog_symbtable tprog).

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
  forall i m b o m' l1 l2 rtbl init,
    let sim := gen_symb_index_map (prog_symbtable prog) in
    init = l1 ++ i :: l2 ->
    transl_init_data_list sim init = OK (reloctable_data (prog_reloctables tprog)) ->
    fold_left (acc_init_data sim) l1 (OK (0, [])) = OK (o, rtbl) ->
    RelocProgSemantics.store_init_data ge m b o i = Some m' ->
    store_init_data tge m b o i = Some m'.
Proof.
  intros i m b o m' l1 l2 rtbl init sim SPLIT TIDL FOLD SID.
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
  erewrite symb_address_2. eauto. 3: eauto. eauto.
  eapply norepet_reloctables. eauto.
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
  forall i m b o m' init l1 rtbl,
    let sim := gen_symb_index_map (prog_symbtable prog) in
    init = l1 ++ i ->
    transl_init_data_list sim init = OK (reloctable_data (prog_reloctables tprog)) ->
    fold_left (acc_init_data sim) l1 (OK (0, [])) = OK (o, rtbl) ->
    RelocProgSemantics.store_init_data_list ge m b o i = Some m' ->
    store_init_data_list tge m b o i = Some m'.
Proof.
  induction i; simpl; intros; eauto.
  destr_in H2.
  erewrite store_init_data_ok.
  3: eauto. 2: eauto. 2: eauto. 2: eauto.
  edestruct (transl_init_data_list_inv) as (oo & ri & TID). apply H0. subst.
  rewrite in_app; right; left; eauto.
  rewrite transl_init_data_translate in TID.
  monadInv TID.
  eapply IHi. 2: eauto. instantiate (1:=l1 ++ a :: nil). rewrite <- app_assoc. simpl. auto.
  rewrite fold_left_app. rewrite H1. simpl.
  rewrite transl_init_data_translate, EQ. simpl.
  f_equal.  auto.
Qed.

Lemma prog_sectable_eq:
  exists init c c',
    prog_sectable prog = [sec_data init; sec_text c] /\
    transl_code' c = OK c' /\
    transl_code (gen_symb_index_map (prog_symbtable prog)) c =
    OK (reloctable_code (prog_reloctables tprog)) /\
    0 <= code_size c' < Ptrofs.max_unsigned /\
    prog_sectable tprog = [sec_data init; sec_text c'] /\
    transl_init_data_list (gen_symb_index_map (prog_symbtable prog)) init =
    OK (reloctable_data (prog_reloctables tprog)).
Proof.
  unfold match_prog, transf_program in TRANSF.
  monadInv TRANSF. simpl in *.
  exploit transl_sectable_ok. eauto.
  intros (c & l & CODE & DATA & TCODE & TDATA).
  unfold transl_sectable' in EQ1. repeat destr_in EQ1. monadInv H0.
  repeat destr_in EQ1. simpl.
  (do 3 eexists). split. eauto. split. eauto.
  split. vm_compute in CODE. inv CODE. auto.
  split. split. generalize (code_size_non_neg x2); lia. auto.
  split. eauto.
  vm_compute in DATA. inv DATA. auto.
Qed.

Lemma alloc_data_section_ok:
  forall m0 m,
    RelocProgSemantics.alloc_data_section ge (prog_sectable prog) m0 = Some m ->
    alloc_data_section tge (prog_sectable tprog) m0 = Some m.
Proof.
  intros m0 m ADS.
  unfold RelocProgSemantics.alloc_data_section, alloc_data_section in *.
  repeat destr_in ADS.
  destruct (prog_sectable_eq) as (init' & c & c' & PS1 & TC & TC' & CodeRng &PS2 & TIDL).
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
    id_eliminate i1 = OK i2 ->
    instr_size i1 = instr_size i2.
Proof.
  intros i1 i2 IE.
  unfold id_eliminate in IE.
  repeat destr_in IE; simpl; auto.
Qed.

Lemma fold_acc_id_eliminate_error:
  forall c e,
    fold_left acc_id_eliminate c (Error e) = Error e.
Proof.
  induction c; simpl; intros; eauto.
Qed.

Lemma transl_code_fold_size:
  forall c r x,
    fold_left acc_id_eliminate c (OK r) = OK x ->
    code_size (rev x) = code_size (r) + code_size c.
Proof.
  induction c; simpl; intros; eauto. inv H. rewrite <- code_size_rev. omega.
  destruct (id_eliminate a) eqn:?.
  simpl in H.
  apply IHc in H. rewrite H. simpl.
  apply id_eliminate_size in Heqr0; rewrite Heqr0. omega.
  simpl in H. rewrite fold_acc_id_eliminate_error in H; congruence.
Qed.

Lemma transl_code_size:
  forall c c',
    transl_code' c = OK c' ->
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
  destruct (prog_sectable_eq) as (init' & c & c' & PS1 & TC & TC' & CodeRng & PS2 & TIDL).
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
  unfold match_prog, transf_program in TRANSF.
  monadInv TRANSF. reflexivity.
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
  unfold match_prog, transf_program in TRANSF.
  monadInv TRANSF. reflexivity.
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
    fold_left acc_id_eliminate c (OK c0) =
    bind (fold_left acc_id_eliminate c (OK [])) (fun c1 => OK (c1 ++ c0)).
Proof.
  induction c; simpl; intros; eauto.
  destruct (id_eliminate a) eqn:?.
  simpl.
  rewrite (IHc (i::c0)).
  rewrite (IHc ([i])).
  destruct (fold_left acc_id_eliminate c (OK [])) eqn:?.
  simpl. rewrite <- app_assoc. simpl. reflexivity.
  simpl. auto.
  simpl. rewrite ! fold_acc_id_eliminate_error. reflexivity.
Qed.

Lemma gen_instr_map_ok:
  forall c ofs0 map0 map0' ofs1 ofs1' map1 map1' c1
         (REC:
            forall iofs i,
              map0 iofs = Some i ->
              exists i', map0' iofs = Some i' /\ id_eliminate i = OK i'
         )
         iofs i
         (GenInstrMap: fold_left acc_instr_map c (ofs0, map0) = (ofs1, map1))
         (SrcInstr: map1 iofs = Some i)
         (TranslCode: fold_left acc_id_eliminate c (OK []) = OK (c1))
         (TgtGenInstrMap: fold_left acc_instr_map (rev c1) (ofs0, map0') = (ofs1', map1')),
  ofs1 = ofs1' /\ exists i', map1' iofs = Some i' /\ id_eliminate i = OK i'.
Proof.
  induction c; simpl; intros; eauto.
  - inv TranslCode. inv GenInstrMap.
    simpl in TgtGenInstrMap. inv TgtGenInstrMap.
    (* apply (f_equal (@length _)) in H0. rewrite app_length in H0. *)
    (* assert (length c1 = O) by omega. destruct c1. simpl in H1. inv H1; auto. *)
    (* simpl in H. omega. *)
    eauto.
  - destruct (id_eliminate a) eqn:?.
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
Qed.


Lemma find_instr_ok:
  forall v i,
  RelocProgSemantics.Genv.find_instr ge v = Some i ->
  exists i',
    Genv.find_instr tge v = Some i' /\
    id_eliminate i = OK i'.
Proof.
  unfold Genv.find_instr.
  unfold tge.
  unfold globalenv. simpl.
  unfold RelocProgSemantics.Genv.find_instr.
  intros. destr.
  unfold ge in H.
  unfold RelocProgSemantics.globalenv in *.
  rewrite instrs_add_external_globals in *. simpl in *.
  destruct (prog_sectable_eq) as (init & c & c' & PS1 & TC & TC' & CodeRng & PS2 & TIDL).
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
         (ELIM : id_eliminate i = OK i'),
    exec_instr tge i' rs m = Next rs' m'.
Proof.
  intros.
  unfold id_eliminate in ELIM. destr_in ELIM.
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
  - destr.
    + inv H0. inv H1. unfold exec_instr.
      unfold get_pc_offset.
      rewrite PC. auto.
    + inv H0. inv H1. unfold exec_instr.
      unfold get_pc_offset.
      rewrite PC. simpl. f_equal. f_equal. eapply SYMBS; eauto.
  - destr_in H0. destr_in H1.
    + inv H0. inv H1. unfold exec_instr.
      unfold get_pc_offset.
      rewrite PC. rewrite <- PC. rewrite Heqo. f_equal.
    + inv H0. inv H1. unfold exec_instr.
      unfold get_pc_offset.
      replace (instr_size (Pcall (inr xH) sg)) with (instr_size (Pcall (inr i) sg)).
      rewrite PC. rewrite <- PC. rewrite Heqo. simpl. f_equal. f_equal.
      f_equal. eapply SYMBS; eauto.
      reflexivity.
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
Qed.

Lemma transl_instr_gen_reloc_ofs_symb:
  forall stbl ofs0 i0 l l' id0 idofs0
    (RNG: 0 <= ofs0 <= Ptrofs.max_unsigned)
    (TI: transl_instr (gen_symb_index_map stbl) ofs0 i0 = OK l)
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

  - repeat destr_in TI.
    monadInv H1. inv H0. unfold compute_instr_rel_relocentry in EQ.
    unfold id_reloc_offset in IR_ofs. destr_in IR_ofs.
    simpl in EQ.
    destr_in EQ. inv EQ.
    eexists; repeat split; eauto. simpl. inv IR_ofs. rewrite Ptrofs.unsigned_repr; auto.

  - repeat destr_in TI.
    monadInv H1. inv H0. unfold compute_instr_rel_relocentry in EQ.
    unfold id_reloc_offset in IR_ofs. destr_in IR_ofs.
    simpl in EQ.
    destr_in EQ. inv EQ.
    eexists; repeat split; eauto. simpl. inv IR_ofs. rewrite Ptrofs.unsigned_repr; auto.

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
  generalize (addrmode_reloc_offset_addrmode_size a); lia.
  generalize (addrmode_reloc_offset_addrmode_size a); lia.
  generalize (addrmode_reloc_offset_addrmode_size a); lia.
  inv H0; lia.
  inv H0; lia.
  generalize (addrmode_reloc_offset_addrmode_size a); lia.
  generalize (addrmode_reloc_offset_addrmode_size a); lia.
  Opaque instr_size.
Qed.

Lemma transl_instr_reloc_offset_range:
  forall sim ofs a l,
    transl_instr sim ofs a = OK l ->
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

Lemma fold_acc_instrs_error:
  forall l sim e,
    fold_left (acc_instrs sim) l (Error e) = Error e.
Proof.
  induction l; simpl; intros; eauto.
Qed.

Lemma gen_instr_map_gen_reloc_ofs_symb_ok:
  forall c ofs i id idofs
         ofs0 map0 ofs1 map1
         (GIM: fold_left acc_instr_map c (Ptrofs.repr ofs0, map0) = (Ptrofs.repr ofs1, map1))
         (INSTR : map1 ofs = Some i)
         (IRI : instr_reloc_id i = OK id)
         (IRO : id_reloc_offset (Ptrofs.unsigned ofs) i = Some idofs)
         creloc0 creloc1 stbl
         (FL : fold_left (acc_instrs (gen_symb_index_map stbl)) c
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
  - destruct (transl_instr (gen_symb_index_map stbl) (ofs0) a) eqn:?.
    + simpl in FL.
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
        eapply transl_instr_gen_reloc_ofs_symb. 2: eauto. all: eauto.
        erewrite gen_reloc_ofs_symb_app. eauto.
        intro IN.
        exploit transl_instr_reloc_offset_range. eauto. eauto.
        generalize (MAP0OFS _ _ H).
        unfold id_reloc_offset in H1.
        destr_in H1. inv H1.
        exploit instr_size_reloc_offset. apply Heqr0. lia.
      }
    + simpl in FL.
      rewrite fold_acc_instrs_error in FL. inv FL.
Qed.

Lemma acc_instr_map_acc_instrs_same_size:
  forall c ofs0 map0 ofs1 map1 sim creloc0 creloc1 x,
    0 <= ofs0 <= Ptrofs.max_unsigned ->
     0 <= ofs0 + code_size c <= Ptrofs.max_unsigned ->
        fold_left acc_instr_map c (Ptrofs.repr ofs0, map0) = (ofs1, map1) ->
        fold_left (acc_instrs sim) c (OK (ofs0, creloc0)) = OK (x, creloc1) ->
        Ptrofs.repr x = ofs1 /\ x = code_size c + ofs0.
Proof.
  induction c; simpl; intros; eauto.
  - inv H1; inv H2. auto.
  - destruct (transl_instr sim ofs0 a) eqn:?; simpl in *.
    + exploit IHc. 3: eauto.
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
    + rewrite fold_acc_instrs_error in H2; inv H2.
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
  destruct (prog_sectable_eq) as (init & c & c' & PS1 & TC & TC' & CodeRng & PS2 & _).
  unfold transl_code in TC'. monadInv TC'.
  unfold get_reloctable.
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
  unfold match_prog, transf_program in TRANSF.
  monadInv TRANSF. reflexivity.
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
  - simpl. unfold globalenv. simpl. unfold genv_senv. simpl.
    unfold match_prog in TRANSF.
    unfold transf_program in TRANSF.
    monadInv TRANSF. unfold RelocProgSemantics.globalenv. intro id. simpl.
    rewrite ! genv_senv_add_external_globals. simpl. auto.
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
      intro STEP. eexists; split; eauto.
    + edestruct find_instr_ok as (i' & FI & ELIM); eauto.
      unfold id_eliminate in ELIM. destr_in ELIM. inv ELIM. simpl in Heqb0.
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

Instance reloctablesgen_transflink : @TransfLink _ _ RelocLinking.Linker_reloc_prog RelocLinking1.Linker_reloc_prog match_prog.
Proof.
  red. simpl.
  unfold match_prog.
  intros. simpl.
Admitted.
