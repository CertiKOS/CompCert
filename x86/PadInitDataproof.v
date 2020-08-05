(* *******************  *)
(* Author: Yuting Wang  *)
(* Date:   Dec 2, 2019 *)
(* *******************  *)

Require Import Coqlib Errors.
Require Import Integers Floats AST Linking Maps.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Op Locations Mach Conventions Asm RealAsm.
Require Import LocalLib.
Require Import AsmFacts AsmInject.
Require Import PadInitData.
Import ListNotations.


Lemma transf_globdef_pres_id : forall def,
    fst def = fst (transf_globdef def).
Proof.
  unfold transf_globdef. destruct def. cbn. auto.
Qed.

Lemma genv_symb_pres: forall defs (ge1 ge2: Genv.t fundef unit),
    Genv.genv_next ge1 = Genv.genv_next ge2 ->
    Genv.genv_symb ge1 = Genv.genv_symb ge2 ->
    Genv.genv_symb (fold_left (Genv.add_global (V:=unit)) (map transf_globdef defs) ge1) =
    Genv.genv_symb (fold_left (Genv.add_global (V:=unit)) defs ge2).
Proof.
  induction defs as [| def defs].
  - intros ge1 ge2 GN GS.
    cbn. auto.
  - intros ge1 ge2 GN GS.
    cbn. apply IHdefs.
    + unfold Genv.add_global; cbn.
      congruence.
    + unfold Genv.add_global; cbn.    
      rewrite <- transf_globdef_pres_id. 
      congruence.
Qed.


Lemma genv_find_funct_ptr_add_global_pres: forall def ge1 ge2 b,
  Genv.genv_next ge1 = Genv.genv_next ge2 ->
  Genv.find_funct_ptr ge1 b = Genv.find_funct_ptr ge2 b ->
  Genv.find_funct_ptr (Genv.add_global ge1 (transf_globdef def)) b =
  Genv.find_funct_ptr (Genv.add_global ge2 def) b.
Proof.
  intros def ge1 ge2 b NEXT FIND.
  unfold Genv.find_funct_ptr.
  destruct (peq b (Genv.genv_next ge1)).
  - subst. erewrite Genv.add_global_find_def_eq.
    rewrite NEXT. erewrite Genv.add_global_find_def_eq.
    unfold transf_globdef. destruct def.
    destruct o; cbn; auto.
    destruct g; cbn; auto.
  - erewrite Genv.add_global_find_def_neq; eauto.
    erewrite Genv.add_global_find_def_neq; try congruence.
    auto.
Qed.

Lemma genv_find_funct_ptr_pres: forall defs (ge1 ge2: Genv.t fundef unit) b,
    Genv.genv_next ge1 = Genv.genv_next ge2 ->
    Genv.find_funct_ptr ge1 b = Genv.find_funct_ptr ge2 b ->
    Genv.find_funct_ptr (fold_left (Genv.add_global (V:=unit)) (map transf_globdef defs) ge1) b =
    Genv.find_funct_ptr (fold_left (Genv.add_global (V:=unit)) defs ge2) b.
Proof.
  induction defs as [| def defs].
  - intros ge1 ge2 b GE FPTR.
    cbn. congruence.
  - intros ge1 ge2 b GE FPTR.
    cbn. apply IHdefs.
    unfold Genv.add_global. cbn. congruence.
    apply genv_find_funct_ptr_add_global_pres; auto.
Qed.


Definition match_prog (p tp:Asm.program) :=
  tp = transf_program p.

Lemma transf_program_match:
  forall p tp, transf_program p = tp -> match_prog p tp.
Proof.
  intros. subst. red. 
  auto.
Qed.


Section PRESERVATION.

Existing Instance inject_perm_all.
Context `{external_calls_prf: ExternalCalls}.

Local Existing Instance mem_accessors_default.


Lemma transl_globvar_gvar_init: forall v,
    gvar_init (transl_globvar v) = (gvar_init v) \/
    exists sz, gvar_init (transl_globvar v) = (gvar_init v) ++ [Init_space sz].
Proof.
  intros. cbn.
  destr; auto. repeat destr; eauto.
Qed.

Lemma transl_globvar_perm_globvar: forall v,
    Genv.perm_globvar (transl_globvar v) = Genv.perm_globvar v.
Proof.
  intros. unfold transl_globvar, Genv.perm_globvar; cbn.
  auto.
Qed.

Lemma transl_globvar_init_data_list_size: forall v, 
    init_data_list_size (gvar_init v) <= init_data_list_size (gvar_init (transl_globvar v)).
Proof.
  intros. generalize (transl_globvar_gvar_init v).
  intros [GI | GI].
  - rewrite GI. omega.
  - destruct GI as (sz & GI). rewrite GI.
    rewrite init_data_list_size_app. 
    cbn. generalize (Z.le_max_r sz 0).
    intros. omega.
Qed.        

Lemma store_init_data_list_extends': forall {F} (ge tge: Genv.t F unit) v m1 m1' m2 b ofs,
    (forall b, Genv.find_symbol ge b = Genv.find_symbol tge b) ->
    Mem.extends m1 m1' ->
    Genv.store_init_data_list ge m1 b ofs (gvar_init v) = Some m2 ->
    exists m2', Genv.store_init_data_list tge m1' b ofs (gvar_init (transl_globvar v)) = Some m2' /\
           Mem.extends m2 m2'.
Proof.
  intros.
  generalize (transl_globvar_gvar_init v).
  destruct 1.
  - rewrite H2. 
    replace (gvar_init v) with (gvar_init v ++ []).
    eapply store_init_data_list_extends; eauto.
    rewrite app_nil_r; auto.
  - destruct H2. rewrite H2.
    eapply store_init_data_list_extends; eauto.
Qed.

Lemma alloc_global_extends: forall ge tge def m1 m1' m2,
    (forall b, Genv.find_symbol ge b = Genv.find_symbol tge b) ->
    Mem.extends m1 m1' ->
    Genv.alloc_global ge m1 def = Some m2 ->
    exists m2', Genv.alloc_global tge m1' (transf_globdef def) = Some m2' /\
           Mem.extends m2 m2'.
Proof.
  intros ge tge def m1 m1' m2 FS EXT ALLOC.
  destruct def. destruct o. destruct g.
  - cbn in *. 
    destr_in ALLOC.
    edestruct Mem.alloc_extends as (m' & ALLOC1 & EXT1); eauto.
    instantiate (1:=0); omega.
    instantiate (1:=1); omega.
    rewrite ALLOC1.
    eapply Mem.drop_extends; eauto.
    cbn. auto.
  - cbn in ALLOC. 
    repeat destr_in ALLOC.
    cbn - [transl_globvar].

    generalize (transl_globvar_init_data_list_size v).
    intros LE.
    set (sz := init_data_list_size (gvar_init v)) in *.
    set (sz' := init_data_list_size (gvar_init (transl_globvar v))) in *.
    assert (exists m2', Mem.alloc m1' 0 sz' = (m2', b) /\ Mem.extends m m2') as ALLOC'.
    { eapply Mem.alloc_extends; eauto. omega. }
    destruct ALLOC' as (m2' & ALLOC' & EXT1).
    rewrite ALLOC'.
    assert (exists m3', store_zeros m2' b 0 sz' = Some m3' /\ Mem.extends m0 m3') as STZ.
    { eapply store_zeros_extend; eauto. omega.
      intros. destruct H. omega.
      erewrite alloc_perm; eauto.
      rewrite peq_true. intros RNG.
      assert (0 <= sz).
      { unfold sz. generalize (init_data_list_size_pos (gvar_init v)). intros. omega. }
      omega.
    }
    destruct STZ as (m3' & STZ & EXT2).
    rewrite STZ.
    assert (exists m4', Genv.store_init_data_list tge m3' b 0 (gvar_init (transl_globvar v)) = Some m4' /\
                   Mem.extends m3 m4') as SI.
    { eapply store_init_data_list_extends'; eauto. }
    destruct SI as (m4' & SI & EXT3).
    rewrite SI.
    rewrite transl_globvar_perm_globvar.
    eapply Mem.drop_extended_extends; eauto.
    cbn. auto.
    omega.
    red. intros.
    erewrite <- Genv.store_init_data_list_perm; eauto.
    erewrite <- Genv.store_zeros_perm; eauto.
    eapply Mem.perm_alloc_2; eauto.
    intros ofs k p0 PERM [RNG|RNG]; try omega.
    erewrite <- Genv.store_init_data_list_perm in PERM; eauto.
    erewrite <- Genv.store_zeros_perm in PERM; eauto.
    generalize (Mem.perm_alloc_3 _ _ _ _ _ Heqp _ _ _ PERM).
    intro. omega.
  - cbn in *.
    destr_in ALLOC. inv ALLOC.
    edestruct Mem.alloc_extends as (m' & ALLOC1 & EXT1); eauto.
    instantiate (1:=0); omega.
    instantiate (1:=0); omega.
    rewrite ALLOC1. eauto.
Qed.

Lemma alloc_globals_extends: forall ge tge defs m1 m1' m2,
    (forall b, Genv.find_symbol ge b = Genv.find_symbol tge b) ->
    Mem.extends m1 m1' ->
    Genv.alloc_globals ge m1 defs = Some m2 ->
    exists m2', Genv.alloc_globals tge m1' (map transf_globdef defs) = Some m2' /\
           Mem.extends m2 m2'.
Proof.
  induction defs as [| def defs].
  - cbn. intros m1 m1' m2 FS EXT EQ.
    inv EQ. eauto.
  - cbn. intros m1 m1' m2 FS EXT EQ.
    destr_in EQ.
    exploit alloc_global_extends; eauto.
    intros (m2' & ALLOC1 & EXT1).
    exploit IHdefs; eauto.
    intros (m3' & ALLOC2 & EXT2).
    eexists; split; eauto.
    rewrite ALLOC1. eauto.
Qed.


Variable prog: Asm.program.
Variable tprog: Asm.program.

Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Hypothesis TRANSF: match_prog prog tprog.

Lemma prog_main_eq: prog_main prog = prog_main tprog.
Proof.
  red in TRANSF. unfold transf_program in TRANSF.
  subst. cbn. auto.
Qed.
 
Inductive match_states : Asm.state -> Asm.state -> Prop :=
|match_states_intro m m' rs rs':
   Mem.stack m = Mem.stack m' ->
   Mem.extends m m' ->
   regset_lessdef rs rs' ->
   match_states (Asm.State rs m) (Asm.State rs' m').

Lemma find_symbol_transf: forall s,
    Genv.find_symbol tge s =
    Genv.find_symbol ge s.
Proof.
  red in TRANSF. unfold transf_program in TRANSF.
  subst. cbn.
  unfold Genv.globalenv, Genv.add_globals.
  unfold Genv.find_symbol. 
  intros. f_equal.
  apply genv_symb_pres.
  reflexivity.
  reflexivity.
Qed.

Lemma symbol_address_transf: forall id ofs,
    Genv.symbol_address tge id ofs =
    Genv.symbol_address ge id ofs.
Proof.
  intros. unfold Genv.symbol_address.
  rewrite find_symbol_transf. auto.
Qed.


Lemma find_funct_ptr_transf: forall b,
    Genv.find_funct_ptr tge b =
    Genv.find_funct_ptr ge b.
Proof.
  red in TRANSF. unfold transf_program in TRANSF.
  subst. cbn.
  intros. unfold ge. unfold Genv.globalenv.
  unfold Genv.add_globals.
  apply genv_find_funct_ptr_pres; reflexivity.
Qed.

Lemma find_funct_transf: forall v,
    Genv.find_funct tge v =
    Genv.find_funct ge v.
Proof.
  unfold Genv.find_funct.
  intros. destruct v; auto.
  destr; auto.
  rewrite find_funct_ptr_transf; eauto.
Qed.

Lemma senv_equiv: Senv.equiv ge tge.
Proof.
  red in TRANSF. unfold ge, tge.
  subst.
  red. split; cbn.
Admitted.

Lemma init_mem_transf: forall m,
    Genv.init_mem prog = Some m ->
    exists m', Genv.init_mem tprog = Some m' /\ Mem.extends m m'.
Proof.
  unfold Genv.init_mem.
  intros m ALLOC.
  red in TRANSF. unfold transf_program in TRANSF.
  replace (prog_defs tprog) with (map transf_globdef (prog_defs prog)).
  Focus 2. rewrite TRANSF. cbn. auto.
  apply alloc_globals_extends with ge Mem.empty; eauto.
  intros. rewrite find_symbol_transf. auto.
  eapply Mem.extends_refl.
Qed.

Lemma initial_state_extends: forall m m' rs st prog prog',
    (forall b, Genv.find_symbol (Genv.globalenv prog) b = Genv.find_symbol (Genv.globalenv prog') b) ->
    prog_main prog = prog_main prog' ->
    Mem.stack m = nil ->
    Mem.stack m' = nil ->
    Mem.extends m m' ->
    initial_state_gen prog rs m st ->
    exists st', initial_state_gen prog' rs m' st' /\ match_states st st'.
Proof.
  intros m m' rs st prog0 prog' FS MAIN ISNIL ISNIL' EXT IS.
  inv IS.
  assert (exists m1' : mem, Mem.alloc (Mem.push_new_stage m') 0 
                                 (Mem.stack_limit + align (size_chunk Mptr) 8) = (m1', bstack)
                       /\ Mem.extends m1 m1') as MALLOC'.
  { eapply Mem.alloc_extends; eauto.
    eapply Mem.extends_push; eauto. 
    omega. omega.
  }
  destruct MALLOC' as (m1' & MALLOC' & EXT1).
  generalize (Mem.alloc_stack_blocks _ _ _ _ _ MALLOC).
  intros ISNIL1. 
  rewrite Mem.push_new_stage_stack in ISNIL1.
  rewrite ISNIL in ISNIL1.
  generalize (Mem.alloc_stack_blocks _ _ _ _ _ MALLOC').
  intros ISNIL1'. 
  rewrite Mem.push_new_stage_stack in ISNIL1'.
  rewrite ISNIL' in ISNIL1'.
  assert (inject_perm_condition Freeable) as IPF.
  { red. cbn. auto. }
  generalize (Mem.drop_extends _ _ _ _ _ _ _ EXT1 IPF MDROP).
  intros (m2' & MDROP' & EXT2).
  generalize (Mem.drop_perm_stack _ _ _ _ _ _ MDROP).
  intros ISNIL2. rewrite ISNIL1 in ISNIL2.
  generalize (Mem.drop_perm_stack _ _ _ _ _ _ MDROP').
  intros ISNIL2'. rewrite ISNIL1' in ISNIL2'.
  assert (exists m3', Mem.record_stack_blocks 
                   m2' (make_singleton_frame_adt' bstack RawAsm.frame_info_mono 0) = Some m3' /\ Mem.extends m3 m3') 
    as MRSB'.
  { 
    eapply Mem.record_stack_blocks_extends; eauto.
    * rewrite ISNIL2'. auto.
    * red. unfold make_singleton_frame_adt'. simpl.
      intros b fi o k p BEQ PERM. inv BEQ; try contradiction.
      inv H0. unfold RawAsm.frame_info_mono. simpl.
      erewrite drop_perm_perm in PERM; eauto. destruct PERM.
      eapply Mem.perm_alloc_3; eauto.
    * red. repeat rewrite_stack_blocks. constructor. auto.
    * repeat rewrite_stack_blocks.
      rewrite ISNIL, ISNIL'. omega.
  } 
  destruct MRSB' as (m3' & MRSB' & EXT3).
  generalize (Mem.record_stack_blocks_stack _ _ _ _ _ MRSB ISNIL2).
  intros ISNIL3.
  generalize (Mem.record_stack_blocks_stack _ _ _ _ _ MRSB' ISNIL2').
  intros ISNIL3'.

  assert (exists m4', Mem.storev Mptr m3' 
                           (Vptr bstack (Ptrofs.repr (Mem.stack_limit + align (size_chunk Mptr) 8 - size_chunk Mptr))) Vnullptr = Some m4' 
                /\ Mem.extends m4 m4') as STORE_RETADDR'.
  { eapply Mem.storev_extends; eauto. }
  destruct STORE_RETADDR' as (m4' & STORE_RETADDR' & EXT4).
  generalize (Mem.storev_stack _ _ _ _ _ STORE_RETADDR).
  intros ISNIL4. rewrite ISNIL3 in ISNIL4.
  generalize (Mem.storev_stack _ _ _ _ _ STORE_RETADDR').
  intros ISNIL4'. rewrite ISNIL3' in ISNIL4'.
  exists (State rs0 m4'). split.
  - econstructor; eauto.
    rewrite <- FS. rewrite <- MAIN. auto.
  - eapply match_states_intro; eauto. congruence.
    apply regset_lessdef_refl.
Qed.

Lemma eval_addrmode32_lessdef: forall a rs1 rs2,
    regset_lessdef rs1 rs2 ->
    Val.lessdef (Asm.eval_addrmode32 ge a rs1) (eval_addrmode32 tge a rs2).
Proof.
(*   intros. unfold Asm.eval_addrmode32, eval_addrmode32. *)
(*   destruct a.  *)
(*   destruct base, ofs, const; simpl in *.  *)
(*   - destruct p. repeat apply Val.add_inject; auto. *)
(*     destr_pair_if; auto. *)
(*     apply Val.mul_inject; auto. *)
(*   - destruct p,p0. repeat apply Val.add_inject; auto. *)
(*     destr_pair_if; auto. *)
(*     apply Val.mul_inject; auto. *)
(*     apply inject_symbol_address. auto. *)
(*   - repeat apply Val.add_inject; auto. *)
(*   - destruct p. apply Val.add_inject; auto.  *)
(*     inject_match. apply inject_symbol_address; auto. *)
(*     destr_valinj_left H1; inv H1; auto. *)
(*     destr_pair_if. auto. *)
(*     eapply Val.inject_ptr; eauto. *)
(*     repeat unfold Ptrofs.of_int.  *)
(*     repeat rewrite Int.unsigned_zero.  *)
(*     repeat rewrite Ptrofs.add_zero. auto. *)
(*   - destruct p. *)
(*     inject_match. *)
(*     apply Val.add_inject; auto. *)
(*     destr_pair_if; auto. *)
(*     apply Val.mul_inject; auto. *)
(*     destr_valinj_left H1; inv H1; auto. *)
(*     destr_pair_if. auto. *)
(*     eapply Val.inject_ptr; eauto. *)
(*     repeat unfold Ptrofs.of_int.  *)
(*     repeat rewrite Int.unsigned_zero.  *)
(*     repeat rewrite Ptrofs.add_zero. auto. *)
(*   - destruct p,p0. *)
(*     inject_match. *)
(*     apply Val.add_inject; auto. *)
(*     destr_pair_if; auto. *)
(*     apply Val.mul_inject; auto. *)
(*     apply inject_symbol_address; auto. *)
(*     destr_valinj_left H1; inv H1; auto. *)
(*     destr_pair_if. auto. *)
(*     eapply Val.inject_ptr; eauto. *)
(*     repeat unfold Ptrofs.of_int.  *)
(*     repeat rewrite Int.unsigned_zero.  *)
(*     repeat rewrite Ptrofs.add_zero. auto. *)
(*   - repeat apply Val.add_inject; auto. *)
(*   - destruct p.  *)
(*     inject_match. inject_match. *)
(*     apply inject_symbol_address; auto. *)
(*     destr_valinj_left H1; inv H1; auto. *)
(*     destr_pair_if. auto. *)
(*     eapply Val.inject_ptr; eauto. *)
(*     repeat unfold Ptrofs.of_int.  *)
(*     repeat rewrite Int.unsigned_zero.  *)
(*     repeat rewrite Ptrofs.add_zero. auto. *)
(*     destr_valinj_left H1; inv H1; auto. *)
(*     destr_pair_if. auto. *)
(*     eapply Val.inject_ptr; eauto. *)
(*     repeat unfold Ptrofs.of_int.  *)
(*     repeat rewrite Int.unsigned_zero.  *)
(*     repeat rewrite Ptrofs.add_zero. auto. *)
(* Qed.     *)
Admitted.

Lemma eval_addrmode64_lessdef: forall a rs1 rs2,
    regset_lessdef rs1 rs2 ->
    Val.lessdef (Asm.eval_addrmode64 ge a rs1) (eval_addrmode64 tge a rs2).
Proof.
(*   intros. unfold Asm.eval_addrmode32, eval_addrmode32. *)
(*   destruct a.  *)
(*   destruct base, ofs, const; simpl in *. *)
(*   - destruct p. repeat apply Val.addl_inject; auto. *)
(*     destr_pair_if; auto. *)
(*     apply Val.mull_inject; auto. *)
(*   - destruct p,p0. repeat apply Val.addl_inject; auto. *)
(*     destr_pair_if; auto. *)
(*     apply Val.mull_inject; auto. *)
(*     apply inject_symbol_address. auto. *)
(*   - repeat apply Val.addl_inject; auto. *)
(*   - destruct p. apply Val.addl_inject; auto.  *)
(*     inject_match. apply inject_symbol_address; auto. *)
(*     destr_valinj_left H1; inv H1; auto. *)
(*     (* destr_pair_if; auto. *) *)
(*     (* eapply Val.inject_ptr; eauto.  *) *)
(*     (* repeat rewrite Ptrofs.add_assoc.  *) *)
(*     (* rewrite (Ptrofs.add_commut (Ptrofs.repr delta) (Ptrofs.of_int64 Int64.zero)). auto. *) *)
(*   - destruct p.  *)
(*     inject_match. *)
(*     apply Val.addl_inject; auto. *)
(*     destr_pair_if; auto.  *)
(*     apply Val.mull_inject; auto. *)
(*     destr_valinj_left H1; inv H1; auto. *)
(*     (* destr_pair_if; auto. *) *)
(*     (* eapply Val.inject_ptr; eauto.  *) *)
(*     (* repeat rewrite Ptrofs.add_assoc.  *) *)
(*     (* rewrite (Ptrofs.add_commut (Ptrofs.repr delta) (Ptrofs.of_int64 Int64.zero)). auto. *) *)
(*   - destruct p,p0. *)
(*     inject_match. *)
(*     apply Val.addl_inject; auto. *)
(*     destr_pair_if; auto.  *)
(*     apply Val.mull_inject; auto. *)
(*     apply inject_symbol_address; auto. *)
(*     destr_valinj_left H1; inv H1; auto. *)
(*     (* destr_pair_if; auto. *) *)
(*     (* eapply Val.inject_ptr; eauto.  *) *)
(*     (* repeat rewrite Ptrofs.add_assoc.  *) *)
(*     (* rewrite (Ptrofs.add_commut (Ptrofs.repr delta) (Ptrofs.of_int64 Int64.zero)). auto. *) *)
(*   - repeat apply Val.addl_inject; auto. *)
(*   - destruct p. inject_match. inject_match. *)
(*     apply inject_symbol_address; auto. *)
(*     destr_valinj_left H1; inv H1; auto. *)
(*     destr_valinj_left H1; inv H1; auto. *)
(*     (* eapply Val.inject_ptr; eauto.  *) *)
(*     (* repeat rewrite Ptrofs.add_assoc.  *) *)
(*     (* rewrite (Ptrofs.add_commut (Ptrofs.repr delta) (Ptrofs.of_int64 Int64.zero)). auto. *)     *)
(* Qed. *)
Admitted.

Lemma eval_addrmode_lessdef: forall a rs1 rs2,
    regset_lessdef rs1 rs2 ->
    Val.lessdef (Asm.eval_addrmode ge a rs1) (eval_addrmode tge a rs2).
Proof.
  intros. unfold Asm.eval_addrmode, eval_addrmode. destruct Archi.ptr64.
  + eapply eval_addrmode64_lessdef; eauto.
  + eapply eval_addrmode32_lessdef; eauto.
Qed.

Lemma goto_ofs_simulation: forall sz ofs rs1 m1 rs2 m2 rs1' m1',
    goto_ofs ge sz ofs rs1 m1 = Next rs2 m2 ->
    regset_lessdef rs1 rs1' ->
    Mem.extends m1 m1' ->
    Mem.stack m1 = Mem.stack m1' ->
    exists m2' rs2', 
      goto_ofs tge sz ofs rs1' m1' = Next rs2' m2'
      /\ Mem.extends m2 m2' /\ regset_lessdef rs2 rs2' /\ Mem.stack m2 = Mem.stack m2'.
Admitted.

Lemma goto_label_simulation: forall f l rs1 m1 rs2 m2 rs1' m1',
    goto_label ge f l rs1 m1 = Next rs2 m2 ->
    regset_lessdef rs1 rs1' ->
    Mem.extends m1 m1' ->
    Mem.stack m1 = Mem.stack m1' ->
    exists m2' rs2', 
      goto_label tge f l rs1' m1' = Next rs2' m2' 
      /\ Mem.extends m2 m2' /\ regset_lessdef rs2 rs2' /\ Mem.stack m2 = Mem.stack m2'.
Admitted.


Lemma exec_load_simulation: forall a chunk sz rd rs1 m1 rs2 m2 rs1' m1',
    exec_load ge chunk m1 a rs1 rd sz = Next rs2 m2 ->
    regset_lessdef rs1 rs1' ->
    Mem.extends m1 m1' ->
    Mem.stack m1 = Mem.stack m1' ->
    exists m2' rs2', 
      exec_load tge chunk m1' a rs1' rd sz = Next rs2' m2' 
      /\ Mem.extends m2 m2' /\ regset_lessdef rs2 rs2' /\ Mem.stack m2 = Mem.stack m2'.
Admitted.

Lemma exec_store_simulation: forall a chunk sz rd ls rs1 m1 rs2 m2 rs1' m1',
    exec_store ge chunk m1 a rs1 rd ls sz = Next rs2 m2 ->
    regset_lessdef rs1 rs1' ->
    Mem.extends m1 m1' ->
    Mem.stack m1 = Mem.stack m1' ->
    exists m2' rs2', 
      exec_store tge chunk m1' a rs1' rd ls sz = Next rs2' m2' 
      /\ Mem.extends m2 m2' /\ regset_lessdef rs2 rs2' /\ Mem.stack m2 = Mem.stack m2'.
Admitted.


Hint Resolve 
     val_lessdef_set
     set_res_pres_lessdef 
     undef_regs_pres_lessdef 
     set_pair_pres_lessdef
     regset_lessdef_pregset
     regset_lessdef_expand_vundef_left
     Val.zero_ext_lessdef Val.sign_ext_lessdef Val.longofintu_lessdef Val.longofint_lessdef
     Val.singleoffloat_lessdef Val.loword_lessdef Val.floatofsingle_lessdef Val.intoffloat_lessdef Val.maketotal_lessdef
     Val.intoffloat_lessdef Val.floatofint_lessdef Val.intofsingle_lessdef Val.singleofint_lessdef
     Val.longoffloat_lessdef Val.floatoflong_lessdef Val.longofsingle_lessdef Val.singleoflong_lessdef
     eval_addrmode32_lessdef eval_addrmode64_lessdef eval_addrmode_lessdef
     Val.neg_lessdef Val.negl_lessdef Val.add_lessdef Val.addl_lessdef
     Val.sub_lessdef  Val.subl_lessdef Val.mul_lessdef Val.mull_lessdef Val.mulhs_lessdef Val.mulhu_lessdef
     Val.mullhs_lessdef  Val.mullhu_lessdef Val.shr_lessdef Val.shrl_lessdef Val.or_lessdef Val.orl_lessdef
     Val.xor_lessdef Val.xorl_lessdef Val.and_lessdef Val.andl_lessdef Val.notl_lessdef
     Val.shl_lessdef Val.shll_lessdef Val.vzero_lessdef Val.notint_lessdef
     Val.shru_lessdef Val.shrlu_lessdef Val.ror_lessdef Val.rorl_lessdef
     compare_ints_lessdef compare_longs_lessdef compare_floats_lessdef compare_floats32_lessdef
     Val.addf_lessdef Val.subf_lessdef Val.mulf_lessdef Val.divf_lessdef Val.negf_lessdef Val.absf_lessdef
     Val.addfs_lessdef Val.subfs_lessdef Val.mulfs_lessdef Val.divfs_lessdef Val.negfs_lessdef Val.absfs_lessdef
     Val.of_optbool_lessdef  Val.offset_ptr_lessdef
     eval_testcond_lessdef eval_testcond_lessdef_some
     nextinstr_pres_lessdef
     nextinstr_nf_pres_lessdef.


Ltac solve_simple_exec :=
  match goal with
  | [ |- context [Genv.symbol_address _ _ _] ] =>
    erewrite symbol_address_transf; solve_simple_exec
  | [ |- exists _ _, Next _ _ = Next _ _ /\ Mem.extends _ _ /\ regset_lessdef _ _ /\ Mem.stack _ = Mem.stack _ ] =>
    eexists; eexists; repeat (split; eauto); solve_simple_exec
  | [ |- exists _ _, exec_load _ _ _ _ _ _ _ = Next _ _ /\ Mem.extends _ _ /\ regset_lessdef _ _ /\ Mem.stack _ = Mem.stack _ ] =>
    eapply exec_load_simulation; eauto
  | [ |- exists _ _, exec_store _ _ _ _ _ _ _ _ = Next _ _ /\ Mem.extends _ _ /\ regset_lessdef _ _ /\ Mem.stack _ = Mem.stack _ ] =>
    eapply exec_store_simulation; eauto
  | [ |- exists _ _, goto_ofs _ _ _ _ _ = Next _ _ /\ Mem.extends _ _ /\ regset_lessdef _ _ /\ Mem.stack _ = Mem.stack _ ] =>
    eapply goto_ofs_simulation; eauto
  | [ |- exists _ _, goto_label _ _ _ _ _ = Next _ _ /\ Mem.extends _ _ /\ regset_lessdef _ _ /\ Mem.stack _ = Mem.stack _ ] =>
    eapply goto_label_simulation; eauto
  | [ |- regset_lessdef (nextinstr_nf _ _) (nextinstr_nf _ _) ] =>
    eapply nextinstr_nf_pres_lessdef; eauto
  | _ => eauto
  end.


Lemma exec_instr_simulation: forall f i rs1 m1 rs2 m2 rs1' m1',
    exec_instr ge f i rs1 m1 = Next rs2 m2 ->
    regset_lessdef rs1 rs1' ->
    Mem.extends m1 m1' ->
    Mem.stack m1 = Mem.stack m1' ->
    exists m2' rs2', exec_instr tge f i rs1' m1' = Next rs2' m2' 
           /\ Mem.extends m2 m2' /\ regset_lessdef rs2 rs2' /\ Mem.stack m2 = Mem.stack m2'.
Proof.
  intros f i rs1 m1 rs2 m2 rs1' m1' EXEC RSL EXT STKEQ.
  destruct i; cbn in *; inv EXEC; try solve_simple_exec. 
  - (* Pdivl *)
    repeat destr_in H0. red in RSL.
    generalize (RSL RDX). rewrite Heqv. inversion 1; subst. 
    generalize (RSL RAX). rewrite Heqv0. inversion 1; subst. 
    generalize (RSL r1). rewrite Heqv1. inversion 1; subst.
    rewrite Heqo. 
    solve_simple_exec.
  - (* Pdivq *)
    repeat destr_in H0. red in RSL.
    generalize (RSL RDX). rewrite Heqv. inversion 1; subst. 
    generalize (RSL RAX). rewrite Heqv0. inversion 1; subst. 
    generalize (RSL r1). rewrite Heqv1. inversion 1; subst.
    rewrite Heqo. 
    solve_simple_exec.
  - (* Pidivl *)
    repeat destr_in H0. red in RSL.
    generalize (RSL RDX). rewrite Heqv. inversion 1; subst. 
    generalize (RSL RAX). rewrite Heqv0. inversion 1; subst. 
    generalize (RSL r1). rewrite Heqv1. inversion 1; subst.
    rewrite Heqo. 
    solve_simple_exec.
  - (* Pidivq *)
    repeat destr_in H0. red in RSL.
    generalize (RSL RDX). rewrite Heqv. inversion 1; subst. 
    generalize (RSL RAX). rewrite Heqv0. inversion 1; subst. 
    generalize (RSL r1). rewrite Heqv1. inversion 1; subst.
    rewrite Heqo. 
    solve_simple_exec.
  - (* Pcmov *)
    destr_in H0; inv H0.
    + erewrite eval_testcond_lessdef_some; eauto.
      destruct b; inv H1; solve_simple_exec.
    + destr. destruct b; solve_simple_exec.
      solve_simple_exec.
  - (* Pjmp *)
    destr_in H0; inv H0.
    destruct (eval_ros ge ros rs1) eqn:ROS; cbn in Heqo; inv Heqo.
    destr_in H0; inv H0.
    destruct ros; cbn in *.
    + red in RSL. generalize (RSL i). rewrite ROS.
      inversion 1; subst. cbn.
      destruct Ptrofs.eq_dec; try congruence.
      rewrite find_funct_ptr_transf. rewrite H1.
      solve_simple_exec.
    + rewrite symbol_address_transf.
      rewrite ROS. cbn.
      destruct Ptrofs.eq_dec; try congruence.
      rewrite find_funct_ptr_transf. rewrite H1.
      solve_simple_exec.
  - (* Pjcc *)
    destr_in H0; inv H0.
    destr_in H1; inv H1.
    + erewrite eval_testcond_lessdef_some; eauto.
      cbn. solve_simple_exec.
    + erewrite eval_testcond_lessdef_some; eauto. 
      cbn. solve_simple_exec.
  - (* Pjcc2 *) 
    destr_in H0; inv H0.
    destr_in H1; inv H1.
    + destr_in H0; inv H0.
      destr_in H1; inv H1.
      * erewrite eval_testcond_lessdef_some; eauto. cbn.
        erewrite eval_testcond_lessdef_some; eauto. cbn.
        solve_simple_exec.
      * erewrite eval_testcond_lessdef_some; eauto. cbn.
        erewrite eval_testcond_lessdef_some; eauto. cbn.
        solve_simple_exec.
    + destr_in H0; inv H0.
      erewrite eval_testcond_lessdef_some; eauto. cbn.
      erewrite eval_testcond_lessdef_some; eauto. cbn.
      solve_simple_exec.
  - (* Pjmptbl *)
    destr_in H0; inv H0.
    destr_in H1; inv H1.
    red in RSL.
    generalize (RSL r). rewrite Heqv. inversion 1; subst.
    rewrite Heqo.
    solve_simple_exec.
  - (* Pcall *)
    destr_in H0; inv H0.
    edestruct Mem.storev_extends as (m2' & SV & EXT1).
    exact EXT. exact Heqo. 
    instantiate (1:= (Val.offset_ptr (rs1' RSP) (Ptrofs.neg (Ptrofs.repr (size_chunk Mptr))))); eauto.
    instantiate (1:= (Val.offset_ptr (rs1' PC) (Ptrofs.repr (instr_size (Pcall ros sg))))); eauto.
    rewrite SV.
    solve_simple_exec.
    repeat eapply regset_lessdef_pregset; eauto.
    destruct ros; cbn; eauto.
    rewrite symbol_address_transf. auto.
    erewrite (Mem.storev_stack m1); eauto.
    erewrite (Mem.storev_stack m1' _ _ _ m2'); eauto.
  - (* Pfreeframe *) 
    destr_in H0; inv H0.
    edestruct Mem.loadv_extends as (m2' & SV & EXT1).
    exact EXT. exact Heqo. 
    instantiate (1:= (rs1' RSP)); eauto.
    rewrite SV.
    solve_simple_exec.
  - (* Pallocframe *) 
    eapply nextinstr_pres_lessdef; eauto.
  - (* Pjcc_rel *)
    destr_in H0; inv H0.
    destr_in H1; inv H1.
    + erewrite eval_testcond_lessdef_some; eauto.
      cbn. solve_simple_exec.
    + erewrite eval_testcond_lessdef_some; eauto. 
      cbn. solve_simple_exec.
  - (* Pjcc2_rel *) 
    destr_in H0; inv H0.
    destr_in H1; inv H1.
    + destr_in H0; inv H0.
      destr_in H1; inv H1.
      * erewrite eval_testcond_lessdef_some; eauto. cbn.
        erewrite eval_testcond_lessdef_some; eauto. cbn.
        solve_simple_exec.
      * erewrite eval_testcond_lessdef_some; eauto. cbn.
        erewrite eval_testcond_lessdef_some; eauto. cbn.
        solve_simple_exec.
    + destr_in H0; inv H0.
      erewrite eval_testcond_lessdef_some; eauto. cbn.
      erewrite eval_testcond_lessdef_some; eauto. cbn.
      solve_simple_exec.
  - (* Pjmptbl_rel *)
    destr_in H0; inv H0.
    destr_in H1; inv H1.
    red in RSL.
    generalize (RSL r). rewrite Heqv. inversion 1; subst.
    rewrite Heqo.
    solve_simple_exec.
Qed.    

Theorem step_simulation:
  forall S1 t S2, step ge S1 t S2 ->
                  forall S1' (MS: match_states S1 S1'),
                    (exists S2', step tge S1' t S2' /\ match_states S2 S2').
Proof.
  destruct 1; intros; inv MS.
  
  - (* Internal Step *)
    exploit exec_instr_simulation; eauto.
    intros (m2' & rs2' & EXEC & EXT & RS & STK).
    exists (State rs2' m2'). split; [|constructor; auto].
    eapply exec_step_internal; eauto.
    red in H8. generalize (H8 PC). rewrite H.
    inversion 1. eauto.
    rewrite find_funct_ptr_transf. auto.
  
  - (* Builtin step *)
    exploit eval_builtin_args_lessdef''; eauto.
    intros (vargs' & EB & VLE).
    exploit external_call_mem_extends; eauto.
    intros (vres' & m2' & EC & VLER & EXT & UCHG).
    eexists. split.
    eapply exec_step_builtin; eauto.
    red in H10. generalize (H10 PC).
    rewrite H. inversion 1. eauto.
    rewrite find_funct_ptr_transf. auto.
    eapply eval_builtin_args_preserved with (ge1 := ge); eauto.
    intros. rewrite find_symbol_transf. auto.
    eapply external_call_symbols_preserved; eauto. exact senv_equiv.
    constructor; eauto.
    erewrite <- (external_call_stack_blocks _ _ _ m'0 _ _ m2'); eauto.
    erewrite <- (external_call_stack_blocks _ _ _ m _ _ m'); eauto.

  - (* External Step *)
    edestruct extcall_arguments_match as (args' & EXTARGS & VLE).
    Focus 3. exact H1.
    instantiate (1:= rs'0 # RSP <- (Val.offset_ptr (rs'0 RSP) (Ptrofs.repr (size_chunk Mptr)))).
    eapply regset_lessdef_pregset; eauto.
    eauto.
    exploit external_call_mem_extends; eauto.
    intros (vres' & m2' & EXTCALL & VLER & EXT2 & CHG).
    eexists. split.
    eapply exec_step_external; eauto.
    red in H9. generalize (H9 PC). rewrite H.
    inversion 1. eauto.
    rewrite find_funct_ptr_transf. auto.
    red in H9. generalize (H9 RSP). inversion 1; congruence.
    edestruct Mem.loadv_extends as (ra' & LV & VLRA). 
    exact H7. exact LOADRA. red in H9. eauto.
    inv VLRA; congruence.
    red in H9. generalize (H9 RSP).
    intros VLRSP. inv VLRSP; congruence.
    apply external_call_symbols_preserved with ge; eauto.
    exact senv_equiv.
    constructor; auto.
    erewrite <- (external_call_stack_blocks _ _ _ m'0 _ _ m2'); eauto.
    erewrite <- (external_call_stack_blocks _ _ _ m _ _ m'); eauto.
    (** Regset lessdef *)
    eapply regset_lessdef_pregset; eauto.
    eapply regset_lessdef_pregset; eauto.
Qed.


Lemma transf_initial_states:
  forall st1 rs, initial_state prog rs st1 ->
         exists st2, initial_state tprog rs st2 /\ match_states st1 st2.
Proof.
  intros st1 rs HInit.
  inv HInit.
  generalize (init_mem_transf _ H).
  intros (m' & INIT & EXT).
  assert (exists st', initial_state_gen tprog rs m' st' /\ match_states st1 st') as IS.
  { apply initial_state_extends with m prog; eauto.
    intros. rewrite find_symbol_transf. auto. 
    rewrite prog_main_eq. auto.
    erewrite Genv.init_mem_stack; eauto.
    erewrite Genv.init_mem_stack; eauto.
  }
  destruct IS as (st1' & IS & MS).
  exists st1'. split; eauto.
  econstructor; eauto.
Qed.


Lemma transf_final_states:
  forall st1 st2 r,
  match_states st1 st2 -> final_state st1 r -> final_state st2 r.
Proof.
  intros st1 st2 r MS HFinal.
  inv HFinal.
  inv MS.
  econstructor; eauto.
  red in H6. generalize (H6 PC). 
  rewrite H. inversion 1. auto.
  red in H6. generalize (H6 RAX). 
  rewrite H0. inversion 1. auto.
Qed.


Lemma transf_program_correct:
  forall rs, forward_simulation (semantics prog rs) (semantics tprog rs).
Proof.
  intro rs.
  apply forward_simulation_step with match_states.
  + intros id. unfold match_prog in TRANSF.
    generalize senv_equiv. intros SENV_EQ.
    red in SENV_EQ.
    destruct SENV_EQ as (S1 & S2 & S3 & S4). auto.
  + simpl. intros s1 Hinit.
    exploit transf_initial_states; eauto.
  + simpl. intros s1 s2 r MS HFinal. eapply transf_final_states; eauto.
  + simpl. intros s1 t s1' STEP s2 MS.
    edestruct step_simulation as (STEP' & MS' ); eauto.
Qed.
  

End PRESERVATION.
