(* *******************  *)
(* Author: Xiangzhe Xu  *)
(* Date:   Sep 16, 2019 *)
(* *******************  *)

Require Import Coqlib Errors.
Require Import Integers Floats AST Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Op Locations Mach Conventions Asm RealAsm.
Require Import Asmlabelgen.
Require Import LocalLib.
Require Import SizeBoundAxioms.
Import ListNotations.
Require AsmFacts.


Definition match_prog (p tp:Asm.program) :=
  match_program (fun _ f tf => transf_fundef f = OK tf) eq p tp.


Lemma transf_program_match:
  forall p tp, transf_program p = OK tp -> match_prog p tp.
Proof.
  intros. eapply match_transform_partial_program; eauto.
Qed.


Section PRESERVATION.
  Existing Instance inject_perm_all.
Context `{external_calls_prf: ExternalCalls}.

Local Existing Instance mem_accessors_default.


Variable prog: Asm.program.
Variable tprog: Asm.program.

Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Hypothesis TRANSF: match_prog prog tprog.

Inductive match_states : Asm.state -> Asm.state -> Prop :=
|match_states_intro m rs:
   match_states (Asm.State rs m) (Asm.State rs m).

(* Variable init_stk: stack. *)

(* Lemma globalenv_eq: ge = tge. *)
(* Proof. *)
(*   unfold ge, tge. *)
(*   unfold Genv.globalenv. *)
(*   destruct TRANSF as (A & B & C). *)
(*   setoid_rewrite C. *)
(*   fold fundef. *)
(*   generalize (Genv.empty_genv fundef unit (prog_public prog)). *)
(*   revert A. *)
(*   fold fundef. *)
(*   generalize (prog_defs prog) (prog_defs tprog). *)
(*   induction 1; simpl; intros; eauto. *)
(*   inv H. destruct a1, b1; simpl in *. subst. inv H1. *)
(*   apply IHA. *)
(*   inv H. unfold transf_fundef, transf_partial_fundef in H1. *)
(*   repeat destr_in H1. unfold bind in H2. destr_in H2. inv H2. *)
(*   unfold trans_function in Heqr. repeat destr_in Heqr. *)
(*   monadInv H1. cbn *)
(*   inv H1. apply IHA. *)
(* Qed. *)


Fixpoint transl_code_spec ofs allcode code code' : Prop :=
  match code, code' with
  | nil, nil => True
  | h::t, h'::t' =>
    transl_instr h ofs allcode = OK h' /\
    transl_code_spec (ofs + instr_size h) allcode t t'
  | _, _ => False
  end.

Definition transl_code_spec_base allcode code' :=
  transl_code_spec 0 allcode allcode code'.

Lemma find_instr_inv : forall  code ofs i,
    find_instr ofs code = Some i ->
    exists l1 l2, code = l1 ++ (i :: l2) /\ code_size l1 = ofs.
Proof.
  induction code as [|i code].
  - cbn. intros. congruence.
  - cbn. intros ofs i' FI.
    destruct zeq; subst.
    + inv FI. exists nil. cbn. eauto.
    + exploit IHcode; eauto.
      intros (l1 & l2 & C & SZ). subst.
      exists (i::l1), l2. cbn. split; eauto.
      omega.
Qed.


Lemma app_cons_comm: forall (A:Type) (l1:list A) a l2,
    (l1 ++ [a]) ++ l2 = l1 ++ a :: l2.
Proof.
  induction l1; intros. 
  - simpl. auto.
  - simpl. f_equal. apply IHl1.
Qed.

Lemma transl_code_spec_app : forall code1 ofs allcode code2 i i',
    transl_code_spec ofs allcode code1 code2 ->
    transl_instr i (ofs + code_size code1) allcode = OK i' ->
    transl_code_spec ofs allcode (code1 ++ [i]) (code2 ++ [i']).
Proof.
  induction code1 as [|h1 code1].
  - intros ofs allcode code2 i i' TL TI.
    cbn in *. destr_in TL. subst. cbn. split; auto.
    rewrite <- TI. f_equal. omega.
  - intros ofs allcode code2 i i' TL TI.
    cbn in *. destr_in TL. destruct TL as (TIH & TL).
    cbn. split; auto.
    eapply IHcode1; eauto.
    rewrite <-TI. f_equal. omega.
Qed.


Lemma transl_code_err: forall allcode code e r,
    fold_left (acc_transl_instr allcode) code (Error e) <> OK r.
Proof.
  induction code as [|i code].
  - cbn. intros. intros H. congruence.
  - cbn. eauto.
Qed.

Lemma transl_code_spec_pf : forall allcode ofs0 code2 ofs1 code1 rcode1 rcode2,
    transl_code_spec ofs0 allcode code1 (rev rcode1) ->
    fold_left (acc_transl_instr allcode) code2 (OK (ofs0 + code_size code1, rcode1)) = OK (ofs1, rcode2) ->
    transl_code_spec ofs0 allcode (code1 ++ code2) (rev rcode2).
Proof.
  induction code2 as [ | i code2'].
  - intros ofs1 code1 rcode1 rcode2 TLSPEC FL.
    rewrite app_nil_r. simpl in FL. inv FL. auto.
  - intros ofs1 code1 rcode1 rcode2 TLSPEC FL.
    simpl in FL.
    unfold bind in FL.
    destruct (transl_instr i (ofs0 + code_size code1) allcode) eqn:TLEQ.
    rewrite <- app_cons_comm.
    eapply IHcode2'.
    instantiate (1:= (i0::rcode1)). simpl.
    apply transl_code_spec_app; auto.
    rewrite code_size_app. simpl.
    rewrite <- FL. f_equal. f_equal. f_equal. omega.
    apply transl_code_err in FL. contradiction.
Qed.
    

Lemma transl_code_prop_pf : forall allcode code ofs rcode',
    fold_left (acc_transl_instr allcode) code (OK (0, nil)) = OK (ofs, rcode') ->
    transl_code_spec 0 allcode code (rev rcode').
Proof.
  intros.
  replace code with ([] ++ code) by auto.
  eapply transl_code_spec_pf; eauto.
  red. simpl. auto.
Qed.

Lemma transl_instr_pres_size: forall i i' ofs code,
    transl_instr i ofs code = OK i' -> instr_size i = instr_size i'.
Proof.
  intros i i' ofs code TL.
  destruct i; cbn in *; inv TL; auto.
  Transparent instr_size.
  - destr_in H0. inv H0. cbn; auto.
  - destr_in H0. inv H0. cbn; auto.
  - destr_in H0. inv H0. cbn; auto.
  - monadInv H0. cbn. auto.
Qed.


Lemma transl_code_spec_inv : forall l1 i l2 l ofs code,
    transl_code_spec ofs code (l1 ++ i :: l2) l ->
    exists l1' l2' i', l = (l1' ++ i' :: l2')
                  /\ transl_instr i (code_size l1 + ofs) code = OK i'
                  /\ find_instr (code_size l1) l = Some i'.
Proof.
  induction l1; simpl.
  - intros i l2 l ofs code SPEC.
    destruct l. contradiction.
    destruct SPEC as [TL TLSPEC].
    exists nil, l, i0. repeat split; auto.
  - intros i l2 l ofs code SPEC.
    destruct l. contradiction.
    destruct SPEC as [TL TLSPEC].
    apply IHl1 in TLSPEC.
    destruct TLSPEC as (l1' & l2' & i' & L & TI & FIND).
    subst.
    exists (i0 :: l1'), l2', i'. split.
    simpl. auto. split.
    rewrite <- TI. f_equal. omega.
    assert (instr_size i0 = instr_size a) as EQ. 
    { erewrite <- transl_instr_pres_size; eauto. }
    rewrite <- EQ. simpl.
    destruct zeq.
    generalize (instr_size_positive i0). intros IPOS.
    generalize (code_size_non_neg l1). intros CPOS.
    omega.
    rewrite <- FIND. f_equal. omega.
Qed.


Lemma find_instr_in_tprog: forall code ofs code' i,
    transl_code code = OK code'
    -> find_instr ofs code = Some i
    -> exists i', transl_instr i ofs code = OK i'
            /\ find_instr ofs code' = Some i'.
Proof.
  intros code ofs code' i TL FIND.
  exploit find_instr_inv; eauto.
  destruct 1 as (l1 & l2 & CD & CSZ). subst.
  monadInv TL. destruct x. inv EQ0.
  apply transl_code_prop_pf in EQ. 
  apply transl_code_spec_inv in EQ.
  destruct EQ as (l1' & l2' & i' & RV & TLI & FIND').
  rewrite Z.add_0_r in TLI.
  eauto.
Qed.




Lemma transf_refl:
  forall f f' ofs i,
    trans_function f = OK f' ->
    find_instr ofs (fn_code f) = Some i ->
    exists i',
      find_instr ofs (fn_code f') = Some i' /\
      (((forall cond  cond1 cond2  r tbl lbl, i <> Pjmp_l lbl /\ i <> Pjcc cond lbl /\ i <> Pjcc2 cond1 cond2 lbl /\ i <> Pjmptbl r tbl ) /\ i = i')
       \/(exists l, i = Pjmp_l l /\ (exists relOfs, i' = Pjmp_l_rel relOfs))
       \/(exists condition l, i = Pjcc condition l /\ (exists relOfs cond', i' = Pjcc_rel cond' relOfs))
       \/(exists condition1 condition2 l, i = Pjcc2 condition1 condition2 l /\ (exists relOfs cond1' cond2', i' = Pjcc2_rel cond1' cond2' relOfs))
       \/(exists reg tl, i = Pjmptbl reg tl /\ (exists r' ofsLst, i' = Pjmptbl_rel r' ofsLst))). 
Proof.
  intros f f' ofs i Htrans HfindInstr.
  
  destruct i eqn:EQI;
  try  (exists i;
       split;
       unfold trans_function in Htrans;
       destruct (func_no_jmp_rel_dec f) eqn:EQF;
       [now( set (I := i) in EQI;
         monadInv Htrans;
         simpl;
         rewrite <- EQI in HfindInstr;
         generalize (find_instr_in_tprog (fn_code f) ofs x I EQ HfindInstr);
         intros HtInstr;
         destruct HtInstr as [i' [HElim HtFind]];
         rewrite HtFind;
         rewrite EQI in HElim;
         unfold transl_code in HElim;
         simpl in HElim;      
         monadInv HElim;
         rewrite <- EQI;
         auto) | inversion Htrans | try (left; repeat split; try (intros HN;inversion HN); auto) | inversion Htrans]). 
  +
    set (I := i) in EQI.
    unfold trans_function in Htrans.
    destruct (func_no_jmp_rel_dec f) eqn:EQF.
    monadInv  Htrans.
    rewrite <- EQI in HfindInstr.
    generalize (find_instr_in_tprog _ ofs _ I EQ HfindInstr).
    intros Hinstr.
    destruct Hinstr as (i' & HTransI' & HTfindInstr).
    rewrite EQI in HTransI'.
    simpl in HTransI'.
    destruct (label_pos l 0 (fn_code f)) eqn: EQFL.
    ++    
    exists ( Pjmp_l_rel (z - (ofs + instr_size (Pjmp_l l)))).
    split.
    simpl. rewrite HTfindInstr. f_equal. inversion HTransI'. auto.
    right. left. eauto.
    ++ inversion HTransI'.
    ++ inversion Htrans.
       
  + set (I := i) in EQI.
    unfold trans_function in Htrans.
    destruct (func_no_jmp_rel_dec f) eqn:EQF.
    monadInv  Htrans.
    rewrite <- EQI in HfindInstr.
    generalize (find_instr_in_tprog _ ofs _ I EQ HfindInstr).
    intros Hinstr.
    destruct Hinstr as (i' & HTransI' & HTfindInstr).
    rewrite EQI in HTransI'.
    simpl in HTransI'.
    destruct (label_pos l 0 (fn_code f)) eqn: EQFL.
    ++ inversion HTransI'. exists i'. simpl. split. auto. right.
       right. left. exists c,l. split. auto. eauto.
    ++ inversion HTransI'.
    ++ inversion Htrans.
  + set (I := i) in EQI.
    unfold trans_function in Htrans.
    destruct (func_no_jmp_rel_dec f) eqn:EQF.
    monadInv  Htrans.
    rewrite <- EQI in HfindInstr.
    generalize (find_instr_in_tprog _ ofs _ I EQ HfindInstr).
    intros Hinstr.
    destruct Hinstr as (i' & HTransI' & HTfindInstr).
    rewrite EQI in HTransI'.
    simpl in HTransI'.
    destruct (label_pos l 0 (fn_code f)) eqn: EQFL.
    ++ inversion HTransI'. exists i'. simpl. split. auto. right.
       right. right. left. exists c1, c2, l. split. auto. eauto.
    ++ inversion HTransI'. ++ inversion Htrans.                              
  + set (I := i) in EQI.
    unfold trans_function in Htrans.
    destruct (func_no_jmp_rel_dec f) eqn:EQF.
    monadInv  Htrans.
    rewrite <- EQI in HfindInstr.
    generalize (find_instr_in_tprog _ ofs _ I EQ HfindInstr).
    intros Hinstr.
    destruct Hinstr as (i' & HTransI' & HTfindInstr).
    rewrite EQI in HTransI'.
    simpl in HTransI'.
    destruct (findAllLabel tbl (fn_code f)) eqn: EQFL.
    ++ inversion HTransI'. exists i'. simpl. split. auto. right. right.
       right. right. exists r, tbl. split. auto. eauto.
    ++ inversion HTransI'.
    ++ inversion Htrans.
Qed.


Lemma transf_symbol_refl: forall id ofs,
    (Genv.symbol_address tge id ofs) = (Genv.symbol_address ge id ofs).
Proof.
  intros id.
  unfold Genv.symbol_address.
  red in TRANSF.
  unfold ge, tge.
  rewrite (Genv.find_symbol_transf_partial TRANSF id). auto.
Qed.

Lemma transf_addrmode32_refl: forall a rs,
    eval_addrmode32 ge a rs = eval_addrmode32 tge a rs.
Proof.
  eapply AsmFacts.eval_addrmode32_same; eauto.
  intros. erewrite transf_symbol_refl; eauto.
Qed.

Lemma transf_addrmode64_refl: forall a rs,
    eval_addrmode64 ge a rs = eval_addrmode64 tge a rs.
Proof.
  eapply AsmFacts.eval_addrmode64_same; eauto.
  intros. erewrite transf_symbol_refl; eauto.
Qed.

Lemma transf_addrmode_refl: forall a rs,
    eval_addrmode ge a rs = eval_addrmode tge a rs.
Proof.
  intros. unfold eval_addrmode. destruct Archi.ptr64.
  - eapply transf_addrmode64_refl; eauto.
  - eapply transf_addrmode32_refl; eauto.
Qed.

Lemma transf_ros_refl: forall ros rs,
    eval_ros tge ros rs = eval_ros ge ros rs.
Proof.
  unfold eval_ros. intros.
  destruct ros; auto.
  apply transf_symbol_refl.
Qed.

Lemma list_nth_z_findAllLabel_comm: forall t n l c l',
    list_nth_z t n = Some l ->
    findAllLabel t c = OK l' ->
    exists ofs, label_pos l 0 c = Some ofs /\
           list_nth_z l' n = Some ofs.
Proof.
  induction t as [|h t'].
  - cbn. intros. congruence.
  - cbn. intros n l c l' EQ LP.
    destruct zeq.
    + subst. inv EQ. destr_in LP.
      monadInv LP. eauto.
    + destr_in LP. monadInv LP.
      exploit IHt'; eauto.
      intros (ofs & LP' & NTH).
      eexists; split; eauto.
      cbn. destruct zeq; try congruence.
Qed.



Theorem step_simulation:
  forall S1 t S2, step ge S1 t S2 ->
                  forall S1' (MS: match_states S1 S1'),
                    (exists S2', step tge S1' t S2' /\ match_states S2 S2').
Proof.
  intros S1 t S2 HStep S1' MS.
  inversion MS.
  exists S2.
  split.
  + induction HStep.
  ++ (* *)
    generalize(Mem.extends_refl m).
    intros MEXT.
    generalize (Genv.find_funct_ptr_transf_partial TRANSF _ H2).
    destruct 1 as [tf [FPTR TF]].
    unfold tge. eauto.
    monadInv TF.
    unfold trans_function in EQ. destruct (func_no_jmp_rel_dec f);inversion EQ.
    monadInv H5.
    generalize (find_instr_in_tprog _ _ _ _ EQ0 H3).
    intros (i' & HInstrTransf & Hfind).
    econstructor; subst; eauto.
    inversion H.
    auto.
    assert(In i (fn_code f)) as Hin. {
      eapply Asmgenproof0.find_instr_in; eauto.
    }
      
    destruct i eqn:EQI;
      try (
          simpl in HInstrTransf; inversion HInstrTransf; simpl; simpl in H4;
          try (rewrite <- H4; inversion MS; auto);
          (* symbol *)
          try ( generalize (transf_symbol_refl id);
                intros Hid;
                rewrite <- Hid; auto);
          try (
              (* load/store *)
              try unfold exec_load;
              try unfold exec_store;
              generalize(transf_addrmode_refl a rs);
              intros HAddrmode; rewrite HAddrmode; 
              auto);
          try (
              (* lea *)
              try generalize(transf_addrmode32_refl a rs);
              intros HAddrmode32;
              try generalize(transf_addrmode64_refl a rs);
              intros HAddrmode64;
              unfold eval_addrmode in HAddrmode32;
              unfold eval_addrmode in HAddrmode64;
              try rewrite HAddrmode32;
              try rewrite HAddrmode64;
              auto);
          try (
              (* ros *)
              rewrite transf_ros_refl;
              destruct ( Genv.find_funct ge (eval_ros ge ros rs0)) eqn:EQF; inversion H4;
              rewrite <- H8;
              rewrite EQF;
              generalize (Genv.find_funct_transf_partial TRANSF _ EQF);
              intros(tf & HfunctionFind & HfunctionTransf);
              rewrite HfunctionFind;
              auto
            );
          try (
              (* rel *)
              unfold func_no_jmp_rel in f0;
              generalize (Forall_forall instr_not_jmp_rel (fn_code f));
              intros HForall;
              destruct HForall;
              rewrite <- EQI in Hin;
              generalize (H0 f0 i Hin);
              intros HNRel; rewrite EQI in HNRel;
              simpl in HNRel; inversion HNRel
            )
        ).
    +++
      (* jmp_l *)
      destruct (label_pos l 0 (fn_code f)) eqn:EQLb; inversion H5.
      monadInv HInstrTransf.
      simpl.
      unfold goto_label.
      rewrite EQLb.
      rewrite H1.
      rewrite H2.
      unfold goto_ofs.
      rewrite H1.
      rewrite FPTR.
      f_equal.
      f_equal.
      f_equal.
      Transparent instr_size.
      cbn.
      repeat rewrite Ptrofs.add_unsigned.
      f_equal. repeat rewrite unsigned_repr. 
      omega.
    +++
      (* Pjcc c l *)
      rewrite <- H8.
      destruct (eval_testcond c rs0) eqn:EQC;inversion H4.
      destruct b0.
      ++++
        rewrite <- H9.
        rewrite H4.
        unfold goto_label in H12.
        destruct (label_pos l 0 (fn_code f)) eqn:EQLb; inversion H12.
        rewrite H1.
        rewrite H2.
        monadInv  H5.
        simpl.
        rewrite EQC.
        simpl.
        unfold goto_ofs.
        rewrite H1.
        rewrite FPTR.
        simpl.
        f_equal.
        f_equal.
        f_equal.
        repeat rewrite Ptrofs.add_unsigned.      
        f_equal.
        repeat rewrite unsigned_repr.
        omega.
      ++++
        rewrite <- H9. rewrite H4.
        destruct (label_pos l 0 (fn_code f)) eqn:EQLb; inversion H5.
        monadInv  H5.
        simpl.
        rewrite EQC.
        inversion H12.
        f_equal.
    +++
      (* pjcc2 *)
      rewrite <- H8.
      rewrite <- H9.
      rewrite H4.
      destruct (label_pos l 0 (fn_code f)) eqn:EQLb; inversion H5.
      simpl.
      destruct (eval_testcond c1 rs0); inversion H4.
      destruct b0 eqn:EQB.
      ++++
        destruct (eval_testcond c2 rs0); inversion H4.
        destruct b1 eqn:EQB1.
        +++++ unfold goto_ofs.
        rewrite H1. rewrite FPTR.
        unfold goto_label. rewrite EQLb. rewrite H1. rewrite H2.
        f_equal. f_equal. f_equal.
        repeat rewrite Ptrofs.add_unsigned.
        f_equal.
        repeat rewrite unsigned_repr.
        omega.
        +++++
          auto.
      ++++ auto.
    +++
    (* pjmptbl *)
      subst.
      unfold bind in H5. destr_in H5; try congruence.
      replace (instr_size (Pjmptbl r tbl)) with 1 in H5.
      assert ((Pjmptbl_rel r (Z.add (- (1 + Ptrofs.unsigned ofs))) ## l) = i') as IEQ. 
      { inversion H5; auto. }
      subst i'. cbn[exec_instr Asm.exec_instr].
      destr; auto.
      symmetry.
      destr. 
      exploit list_nth_z_findAllLabel_comm; eauto.
      intros (ofs1 & LPOS & NTH).
      rewrite list_nth_z_map. rewrite NTH. 
      cbn [option_map].
      Transparent instr_size. cbn [instr_size Asm.instr_size'].
      unfold goto_label. rewrite LPOS.
      unfold goto_ofs.
      destr; try congruence.
      destr.
      ++++ assert (exists tf, Genv.find_funct_ptr tge b0 = Some tf /\ transf_fundef f1 = OK tf) as TF.
           { eapply Genv.find_funct_ptr_transf_partial; eauto. }
           destruct TF as (tf & FIND & TRANSF').
           unfold tge in FIND. rewrite FIND.
           f_equal. f_equal. f_equal.
           rewrite (Ptrofs.add_unsigned (Ptrofs.repr 1)).
           repeat rewrite unsigned_repr; auto.
           rewrite Pregmap.gso in Heqv0.
           rewrite Pregmap.gso in Heqv0.
           rewrite H1 in Heqv0. inv Heqv0.
           rewrite Ptrofs.add_unsigned.
           rewrite unsigned_repr. f_equal. omega.
           intros NREG. congruence.
           intros NREG. congruence.
      ++++ assert (Genv.find_funct_ptr (Genv.globalenv tprog) b0 = None) as FP.
           { unfold ge in Heqo0. 
             unfold match_prog in TRANSF. 
             eapply (@Genv.find_funct_ptr_transf_none_partial fundef fundef); eauto.
           }
           rewrite FP. auto.
      ++++ cbn. auto.

    +++ 
      destr; try congruence.
      f_equal.
      f_equal.
      f_equal.
      rewrite transf_ros_refl. auto.
          
  ++
    generalize(Genv.find_funct_ptr_transf_partial TRANSF _  H2).
    intros (tf & FPTR & HTransf).
    unfold tge.  monadInv HTransf.
    subst. rewrite H.
    eapply exec_step_builtin; eauto.
    unfold trans_function in EQ.
    destruct (func_no_jmp_rel_dec);inversion EQ.
    monadInv EQ.
    generalize (find_instr_in_tprog _ _ _ _ EQ0 H3).
    intros (i' & HTrans & Hfind). simpl.
    rewrite Hfind. inversion HTrans.
    auto.
    apply eval_builtin_args_preserved with (ge1 := ge); eauto.
    intros id.
    generalize (Genv.find_symbol_transf_partial TRANSF id).
    intros Hsmybol.
    auto.
    apply external_call_symbols_preserved with (ge1:=ge); eauto.
    eapply Genv.senv_transf_partial; eauto.
  ++
    generalize(Genv.find_funct_ptr_transf_partial TRANSF _  H2).
    intros (tf & FPTR & HTransf).
    unfold tge.  monadInv HTransf.
    subst. rewrite H.
    eapply exec_step_external; eauto.
    apply external_call_symbols_preserved with (ge1:=ge); eauto.
    eapply Genv.senv_transf_partial; eauto.
        
  + destruct S2. constructor.
Qed.


Lemma transf_initial_states:
  forall st1 rs, initial_state prog rs st1 ->
         exists st2, initial_state tprog rs st2 /\ match_states st1 st2.
Proof.
  intros st1 rs HInit.
  exists st1.
  inv HInit.
  split.
  + econstructor.
    generalize (Genv.init_mem_transf_partial TRANSF H).
    eauto.
    inv H0.
    econstructor; eauto.
    rewrite (match_program_main TRANSF); eauto.
    generalize (Genv.find_symbol_transf_partial TRANSF (prog_main prog)).
    intros HFind.
    rewrite <- H1.
    auto.
  + destruct st1. constructor.
Qed.


Lemma transf_final_states:
  forall st1 st2 r,
  match_states st1 st2 -> final_state st1 r -> final_state st2 r.
Proof.
  intros st1 st2 r MS HFinal.
  inversion HFinal.
  inversion MS. 
  econstructor.
  rewrite <- H1 in H3.
  inversion H3. auto.
  rewrite <- H1 in H3.
  inversion H3.
  auto.
Qed.


(* Lemma senv_equiv: *)
(*   Senv.equiv (Genv.genv_senv ge) (Genv.genv_senv tge). *)
(* Proof. *)
(*   unfold ge, tge, globalenv. rewrite ! add_globals_genv_senv. simpl. *)
(*   unfold match_prog in TRANSF. monadInv TRANSF. simpl. *)
(*   repeat apply conj; auto. *)
(* Qed. *)

Lemma transf_program_correct:
  forall rs, forward_simulation (semantics prog rs) (semantics tprog rs).
Proof.
  intro rs.
  eapply forward_simulation_step with match_states.
  + intros id. unfold match_prog in TRANSF.
    generalize (Genv.senv_match TRANSF). intros SENV_EQ.
    red in SENV_EQ.
    destruct SENV_EQ as (S1 & S2 & S3 & S4). auto.
  + simpl. intros s1 Hinit.
    exploit transf_initial_states; eauto.
  + simpl. intros s1 s2 r MS HFinal. eapply transf_final_states; eauto.
  + simpl. intros s1 t s1' STEP s2 MS.
    edestruct step_simulation as (STEP' & MS' ); eauto.
Qed.

Lemma trans_fun_pres_stacksize: forall f tf,
    Asmlabelgen.trans_function f = OK tf -> 
    Asm.fn_stacksize f = Asm.fn_stacksize tf.
Proof.
  intros f tf HFunc.
  unfold trans_function in HFunc.
  destruct func_no_jmp_rel_dec in HFunc; inversion HFunc.
  monadInv H0.
  simpl. auto.
Qed.


End  PRESERVATION.
