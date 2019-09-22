(* *******************  *)
(* Author: Xiangzhe Xu  *)
(* Date:   Sep 16, 2019 *)
(* *******************  *)




Require Import Coqlib Errors.
Require Import Integers Floats AST Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Op Locations Mach Conventions Asm.
Require Import Asmlabelgen.
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
|match_states_intro:
   forall rs rs' m m'
          (RSEQ: rs = rs')
          (MEXT: Mem.extends m m'),
   match_states (Asm.State rs m) (Asm.State rs' m').

Variable init_stk: stack.



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

Lemma find_instr_inv : forall ofs code i,
    find_instr ofs code = Some i ->
    exists l1 l2, code = l1 ++ (i :: l2) /\ code_size l1 = ofs.
Admitted.

Lemma app_cons_comm: forall (A:Type) (l1:list A) a l2,
    (l1 ++ [a]) ++ l2 = l1 ++ a :: l2.
Proof.
  induction l1; intros. 
  - simpl. auto.
  - simpl. f_equal. apply IHl1.
Qed.

Lemma transl_code_spec_app : forall ofs allcode code1 rcode1 i i',
    transl_code_spec ofs allcode code1 (rev rcode1) ->
    transl_instr i (ofs + code_size code1) allcode = OK i' ->
    transl_code_spec ofs allcode (code1 ++ [i]) (rev rcode1 ++ [i']).
Admitted.

Lemma code_size_app : forall c1 c2,
    code_size (c1 ++ c2) = code_size c1 + code_size c2.
Admitted.

Lemma transl_code_err: forall allcode code e r,
    fold_left (acc_transl_instr allcode) code (Error e) <> OK r.
Admitted.

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
    assert (instr_size i0 = instr_size a) as EQ. admit.
    rewrite <- EQ. simpl.
    destruct zeq.
    admit.
    rewrite <- FIND. f_equal. omega.
Admitted.

  
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
  

(* Lemma find_instr_in_tprog: forall code all_code sofs ofs code' i, *)
(*     eliminate_local_label_aux code sofs all_code = OK code' *)
(*     -> find_instr ofs code = Some i *)
(*     -> exists i', eliminate_local_label_aux (i::nil) (sofs+ofs) all_code = OK (i'::nil) /\ find_instr ofs code' = Some i'. *)
(* Proof. *)
(*   induction code; simpl. *)
(*   intros. congruence. *)
(*   intros. destruct a. *)
(*   - monadInv H.  *)
(*     destruct zeq. inv H0. *)
(*     + eexists. split. auto. auto. *)
(*     + exploit IHcode; eauto. *)
(*       destruct 1 as (i' & ELIM & FIND). *)
(*       exists i'. split. *)
(*       destruct i; auto. *)
(*       simpl in ELIM. *)
(*       destruct (label_pos l 0 all_code) eqn:EQ_POS; try congruence. *)
(*       inv ELIM. f_equal. f_equal; auto. f_equal. omega. *)
(*       admit. *)
(*       admit. *)
(*       admit. *)
(*       simpl. destruct zeq. congruence. *)
(*       auto. *)

      

(*       destruct i; simpl; split; eauto. *)
(*       exists i. split. destruct i; split; eauto. *)

(*   intros f ofs x i HTrans HFind. *)
(*   destruct i eqn:EQI; try(unfold eliminate_local_label_aux; simpl; *)
(*                           exists i; split; rewrite EQI; auto). *)
(*   + *)
    
(*     Lemma elim_lbl_prefix: forall h tail x f ofs, *)
(*       exists i', eliminate_local_label_aux (h::nil) ofs (fn_code f) = OK (i'::nil) -> *)
(*                  eliminate_local_label_aux (tail) (ofs + (instr_size h)) (fn_code f) = OK x -> *)
(*                  eliminate_local_label_aux (h::tail) ofs (fn_code f)  = OK(i'::x). *)
(*     Admitted. *)
    
                 

(* Admitted. *)


Lemma transf_refl:
  forall f f' ofs i cond  cond1 cond2  r tbl lbl,
    trans_function f = OK f' ->
    find_instr ofs (fn_code f) = Some i ->
    exists i',
      find_instr ofs (fn_code f') = Some i' /\
      (((i <> Pjmp_l lbl /\ i <> Pjcc cond lbl /\ i <> Pjcc2 cond1 cond2 lbl /\ i <> Pjmptbl r tbl ) /\ i = i')
       \/(exists l, i = Pjmp_l l /\ (exists relOfs, i' = Pjmp_l_rel relOfs))
       \/(exists condition l, i = Pjcc condition l /\ (exists relOfs cond', i' = Pjcc_rel cond' relOfs))
       \/(exists condition1 condition2 l, i = Pjcc2 condition1 condition2 l /\ (exists relOfs cond1' cond2', i' = Pjcc2_rel cond1' cond2' relOfs))
       \/(exists reg tl, i = Pjmptbl reg tl /\ (exists r' ofsLst, i' = Pjmptbl_rel r' ofsLst))). 
Proof.
  intros f f' ofs i cond cond1 cond2 r tbl lbl Htrans HfindInstr.
  (* destruct i eqn:EQI. *)
  (* 179: exists i; *)
  (*   split; *)
  (*   unfold trans_function in Htrans; *)
  (*   destruct (func_no_jmp_rel_dec f) eqn:EQF. *)
  
  (*   ++ set (I := i) in EQI; *)
  (*     monadInv Htrans; *)
  (*     simpl; *)
  (*     rewrite <- EQI in HfindInstr; *)
  (*     generalize (find_instr_in_tprog (fn_code f) ofs x I EQ HfindInstr); *)
  (*     intros HtInstr; *)
  (*     destruct HtInstr as [i' [HElim HtFind]]; *)
  (*     rewrite HtFind; *)
  (*     rewrite EQI in HElim. *)
  (*     unfold transl_code in HElim; *)
  (*     simpl in HElim; *)
  (*     monadInv HElim; *)
  (*     rewrite <- EQI; *)
  (*     auto. *)

  
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
    exists ( Pjmp_l_rel ((ofs + instr_size (Pjmp_l l) - z))).
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
    destruct (findAllLabel tbl0 (fn_code f)) eqn: EQFL.
    ++ inversion HTransI'. exists i'. simpl. split. auto. right. right.
       right. right. exists r0, tbl0. split. auto. eauto.
    ++ inversion HTransI'.
    ++ inversion Htrans.
Qed.

Theorem step_simulation:
  forall S1 t S2, step init_stk ge S1 t S2 ->
                  forall S1' (MS: match_states S1 S1'),
                    (exists S2', step init_stk tge S1' t S2' /\ match_states S2 S2').
Proof.
  intros S1 t S2 HStep S1' MS.
  induction HStep.
  - (* *)
    generalize (Genv.find_funct_ptr_transf_partial TRANSF _ H0).
    destruct 1 as [tf [FPTR TF]].
    unfold tge. eauto.
    monadInv TF.

    exists (State rs' m').
    split.
    inversion MS.
    econstructor; subst; eauto.

    +
                       
    unfold Genv.find_funct_ptr.
    assert (Genv.find_def tge b = Genv.find_def ge b). {
      (* unfold Mem.extends in MEXT. *)
      
      


      
      inversion H6.
      + unfold Genv.find_def.
        unfold tge.
        unfold Genv.globalenv.
        rewrite <- H10.
        simpl.
        unfold ge.
        unfold Genv.globalenv.
        rewrite <- H9.
        simpl.
        auto.
      + unfold Genv.find_def.
        unfold tge.
        unfold Genv.globalenv.
        rewrite <- H9.
        simpl.
        unfold match_ident_option_globdef in H10.
        unfold Genv.genv_defs.
        
        

        admit.
    }
    unfold Genv.find_funct_ptr in H0.
    rewrite H8.
    apply H0.
  + 

  unfold Mem.extends in MEXT.
  simpl in MEXT.
  exists (State rs0 m').
  split.
  
  

  + destruct i eqn:EQI.
    ++ inversion H2.
       induction MS.

  destruct step .
    induction 1.
  intros S1 t S2 H S1' MS.

  destruct step.
  exists (Asm.State 

Admitted.



(* Lemma transf_initial_states: *)
(*   forall st1, Asm.initial_state prog st1 -> *)
(*          exists st2, Asm.initial_state tprog st2 /\ match_states Vnullptr st1 st2. *)
(* Admitted. *)

End  PRESERVATION.
