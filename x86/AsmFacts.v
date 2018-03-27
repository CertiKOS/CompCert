Require Import Smallstep.
Require Import Machregs.
Require Import Asm.
Require Import Integers.
Require Import List.
Require Import ZArith.
Require Import Memtype.
Require Import Memory.
Require Import Archi.
Require Import Coqlib.
Require Import AST.
Require Import Globalenvs.
Require Import Events.
Require Import Values.
Require Import Conventions1.
Require Asmgen.
Require Asmgenproof0.
Require Import Errors.

Section WITHMEMORYMODEL.

  Context {mem} `{memory_model: Mem.MemoryModel mem}.

  Existing Instance mem_accessors_default.

  Context `{external_calls_ops: !ExternalCallsOps mem}
          `{enable_builtins_instance: EnableBuiltins (memory_model_ops:=memory_model_ops) mem}.

  Definition stack_invar (i: instr_with_info) :=
    match i with
    | (i,_) =>
      match i with
        Pallocframe _ _  
      | Pfreeframe _ _
      | Pcall_s _ _
      | Pcall_r _ _ 
      | Pret => false
      | _ => true
      end
    end.

  (** Instructions other than [Pallocframe] and [Pfreeframe] do not modify the
      content of the RSP register. We prove that Asm programs resulting from the
      Stacking pass satisfy this requirement. *)

  Definition asm_instr_no_rsp (i : Asm.instr_with_info) : Prop :=
    stack_invar i = true ->
    forall {F V} (ge: _ F V) rs1 m1 rs2 m2 f isp,
      Asm.exec_instr isp ge f i rs1 m1 = Next rs2 m2 ->
      rs2 # RSP = rs1 # RSP.

  Definition asm_code_no_rsp (c : Asm.code) : Prop :=
    forall i,
      In i c ->
      asm_instr_no_rsp i.

  Lemma asm_code_no_rsp_cons:
    forall a l,
      asm_instr_no_rsp a ->
      asm_code_no_rsp l ->
      asm_code_no_rsp (a::l).
  Proof.
    unfold asm_code_no_rsp.
    intros. simpl in H2. destruct H2; subst; auto.
  Qed.

  Lemma nextinstr_rsp:
    forall rs sz,
      nextinstr rs sz RSP = rs RSP.
  Proof.
    unfold nextinstr.
    intros; rewrite Pregmap.gso; congruence.
  Qed.

  Lemma nextinstr_nf_rsp:
    forall rs sz,
      nextinstr_nf rs sz RSP = rs RSP.
  Proof.
    unfold nextinstr_nf.
    intros. rewrite nextinstr_rsp.
    rewrite Asmgenproof0.undef_regs_other; auto.
    simpl; intuition subst; congruence. 
  Qed.

  Lemma preg_of_not_rsp:
    forall m x,
      preg_of m = x ->
      x <> RSP.
  Proof.
    unfold preg_of. intros; subst.
    destruct m; congruence.
  Qed.
  
  Lemma ireg_of_not_rsp:
    forall m x,
      Asmgen.ireg_of m = OK x ->
      IR x <> RSP.
  Proof.
    unfold Asmgen.ireg_of.
    intros m x A.
    destr_in A. inv A.
    eapply preg_of_not_rsp in Heqp.
    intro; subst. congruence.
  Qed.

  Lemma freg_of_not_rsp:
    forall m x,
      Asmgen.freg_of m = OK x ->
      FR x <> RSP.
  Proof.
    unfold Asmgen.freg_of.
    intros m x A. destr_in A. 
  Qed.


  Lemma compare_floats_rsp:
    forall a b rs1,
      compare_floats a b rs1 RSP = rs1 RSP.
  Proof.
    unfold compare_floats.
    intros.
    destruct a, b; rewrite ?Asmgenproof0.undef_regs_other by simpl; intuition congruence.
  Qed.


  Lemma compare_floats32_rsp:
    forall a b rs1,
      compare_floats32 a b rs1 RSP = rs1 RSP.
  Proof.
    unfold compare_floats32.
    intros.
    destruct a, b; rewrite ?Asmgenproof0.undef_regs_other by simpl; intuition congruence.
  Qed.


  Lemma exec_load_rsp:
    forall F V (ge: _ F V) K m1 am rs1 f0 rs2 m2 sz,
      IR RSP <> f0->
      exec_load ge K m1 am rs1 f0 sz = Next rs2 m2 ->
      rs2 RSP = rs1 RSP.
  Proof.
    intros F V ge' K m1 am rs1 f0 rs2 m2 sz DIFF LOAD.
    unfold exec_load in LOAD. destr_in LOAD. inv LOAD.
    rewrite nextinstr_nf_rsp. 
    rewrite Pregmap.gso. auto. auto. 
  Qed.

  Lemma exec_store_rsp:
    forall F V (ge: _ F V)  K m1 am rs1 f0 rs2 m2 (l: list preg) sz, (* preg_of m = f0 -> *)
      (forall r' : PregEq.t, In r' l -> r' <> RSP) ->
      exec_store ge K m1 am rs1 f0 l sz = Next rs2 m2 ->
      rs2 RSP = rs1 RSP.
  Proof.
    intros F V ge' K m1 am rs1 f0 rs2 m2 l sz INL STORE.
    unfold exec_store in STORE. repeat destr_in STORE.
    rewrite nextinstr_nf_rsp. 
    rewrite Asmgenproof0.undef_regs_other.
    auto. intros; apply not_eq_sym. auto.
  Qed.

  Ltac solve_rs:=
    repeat match goal with
             H2 : Next _ _ = Next _ _ |- _ =>
             inv H2
           | |- _ :preg <> RSP => eapply preg_of_not_rsp; eauto
           | |- _ :preg<> RSP => eapply ireg_of_not_rsp; eauto
           | |- _ :preg <> RSP => eapply freg_of_not_rsp; eauto
           | |- RSP <> _  => apply not_eq_sym
           | |- _ => rewrite ?nextinstr_nf_rsp, ?nextinstr_rsp, ?compare_floats_rsp, ?compare_floats32_rsp;
                   try rewrite Pregmap.gso by (apply not_eq_sym; eapply ireg_of_not_rsp; eauto);
                   try rewrite Pregmap.gso by (apply not_eq_sym; eapply freg_of_not_rsp; eauto);
                   try reflexivity

           end.


Section WITHINSTRSIZEMAP.

Variable instr_size_map : instruction -> Z.
Hypothesis instr_size_non_zero : forall i, instr_size_map i > 0.

Definition loadind := Asmgen.loadind instr_size_map instr_size_non_zero.
Definition storeind := Asmgen.storeind instr_size_map instr_size_non_zero.
Definition mk_mov := Asmgen.mk_mov instr_size_map instr_size_non_zero.
Definition mk_setcc := Asmgen.mk_setcc instr_size_map instr_size_non_zero.
Definition transl_cond := Asmgen.transl_cond instr_size_map instr_size_non_zero.
Definition mk_jcc := Asmgen.mk_jcc instr_size_map instr_size_non_zero.
Definition transf_function := Asmgen.transf_function instr_size_map instr_size_non_zero.


  Lemma loadind_no_change_rsp:
    forall i t m x0 x1 r,
      asm_code_no_rsp x0 ->
      loadind r i t m x0 = OK x1 ->
      asm_code_no_rsp x1.
  Proof.
    intros i t m x0 x1 r IH EQ.
    unfold loadind in EQ. unfold Asmgen.loadind in EQ.
    unfold Asmgen.instr_to_with_info in EQ; simpl in EQ.
    repeat destr_in EQ; apply asm_code_no_rsp_cons; auto; red; simpl; intros; unfold exec_instr in H1; simpl in H1; 
      eapply exec_load_rsp; eauto; apply not_eq_sym; solve_rs.
  Qed.

  Lemma storeind_no_change_rsp:
    forall i t m x0 x1 r,
      asm_code_no_rsp x0 ->
      storeind m r i t x0 = OK x1 ->
      asm_code_no_rsp x1.
  Proof.
    intros i t m x0 x1 r IH EQ.
    unfold storeind in EQ. unfold Asmgen.storeind in EQ.
    repeat destr_in EQ; apply asm_code_no_rsp_cons; auto; red; simpl; intros; unfold exec_instr in H1; simpl in H1;
      eapply exec_store_rsp; eauto; simpl; intuition subst; congruence.
  Qed.

  Lemma mk_move_nochange_rsp:
    forall x0 x1 m m0,
      asm_code_no_rsp x0 ->
      mk_mov (preg_of m) (preg_of m0) x0 = OK x1 ->
      asm_code_no_rsp x1.
  Proof.
    intros x0 x1 m m0 A B.
    unfold mk_mov in B. unfold Asmgen.mk_mov in B.
    repeat destr_in B; apply asm_code_no_rsp_cons; auto; red; simpl; intros;
      inv H1; rewrite nextinstr_rsp;
        rewrite Pregmap.gso; auto;
          apply not_eq_sym; eapply preg_of_not_rsp; eauto.
  Qed.  
  
    Ltac simpl_cinfo :=
    match goal with
    | [ H: context [Asmgen.code_to_with_info _ _ _] |- _ ] =>
      unfold Asmgen.code_to_with_info in H; simpl_cinfo
    | [ H: context [Asmgen.instr_to_with_info _ _] |- _ ] =>
      unfold Asmgen.instr_to_with_info in H; simpl_cinfo
    | [ H: context [exec_instr _ _ _ _ _ _ = Next _ _] |- _ ] =>
      unfold exec_instr in H; simpl_cinfo
    | [ |- exec_instr _ _ _ _ _ _ = Next _ _ ] =>
      unfold exec_instr; simpl_cinfo
    | _ => simpl in *
    end.

  Ltac invasm :=
    repeat match goal with
             H: bind _ ?x = OK ?x1 |- _ =>
             monadInv H
           | H: exec_instr _ _ _ _ _ _ = _ |- _ =>
             unfold exec_instr in H; simpl in H; inv H
           | |- _ => apply asm_code_no_rsp_cons; auto; red; simpl; intros; solve_rs
           end.

  Lemma mkset_cc_no_rsp:
    forall x0 m x2 i c,
      asm_code_no_rsp x0 ->
      In i (mk_setcc c x2 x0) ->
      Asmgen.ireg_of m = OK x2 ->
      asm_instr_no_rsp i.
  Proof.
    intros x0 m x2 i c A B C.
    unfold mk_setcc in B. unfold Asmgen.mk_setcc in B. destr_in B.
    - destruct c. simpl in *.
      unfold Asmgen.instr_to_with_info in B.
      destruct B; subst; auto; red; intros; unfold Asm.exec_instr in H1; simpl in H1; solve_rs.
      unfold Asmgen.mk_setcc_base, Asmgen.code_to_with_info, Asmgen.instr_to_with_info in B; simpl in B. 
      destruct (ireg_eq x2 RAX) eqn: IEQ; simpl in B.
      destruct B; subst; auto. red. intros IU F V ge rs1 m1 rs2 m2 f isp EI; unfold Asm.exec_instr in *; simpl in EI; solve_rs.
      destruct H0; subst; auto. red. intros IU F V ge rs1 m1 rs2 m2 f isp EI; unfold Asm.exec_instr in *; simpl in EI; solve_rs.
      destruct H0; subst; auto. red. intros IU F V ge rs1 m1 rs2 m2 f isp EI; unfold Asm.exec_instr in *; simpl in EI; solve_rs.
      destruct B; subst; auto. red. intros IU F V ge rs1 m1 rs2 m2 f isp EI; unfold Asm.exec_instr in *; simpl in EI; solve_rs.
      destruct H0; subst; auto. red. intros IU F V ge rs1 m1 rs2 m2 f isp EI; unfold Asm.exec_instr in *; simpl in EI; solve_rs.
      destruct H0; subst; auto. red. intros IU F V ge rs1 m1 rs2 m2 f isp EI; unfold Asm.exec_instr in *; simpl in EI; solve_rs.
      unfold Asmgen.mk_setcc_base, Asmgen.code_to_with_info, Asmgen.instr_to_with_info in B; simpl in B. 
      destruct (ireg_eq x2 RAX) eqn: IEQ; simpl in B.
      destruct B; subst; auto. red. intros IU F V ge rs1 m1 rs2 m2 f isp EI; unfold Asm.exec_instr in *; simpl in EI; solve_rs.
      destruct H0; subst; auto. red. intros IU F V ge rs1 m1 rs2 m2 f isp EI; unfold Asm.exec_instr in *; simpl in EI; solve_rs.
      destruct H0; subst; auto. red. intros IU F V ge rs1 m1 rs2 m2 f isp EI; unfold Asm.exec_instr in *; simpl in EI; solve_rs.
      simpl in B. destr_in B.
      red. intros IU F V ge rs1 m1 rs2 m2 f isp EI; unfold Asm.exec_instr in *; simpl in EI; solve_rs.
      destruct H0; subst; auto. red. intros IU F V ge rs1 m1 rs2 m2 f isp EI; unfold Asm.exec_instr in *; simpl in EI; solve_rs.
      destruct H0; subst; auto. red. intros IU F V ge rs1 m1 rs2 m2 f isp EI; unfold Asm.exec_instr in *; simpl in EI; solve_rs.
    - destruct c.
      unfold Asmgen.mk_setcc_base, Asmgen.code_to_with_info, Asmgen.instr_to_with_info in B; simpl in B.
      destruct B; subst; auto. red. intros IU F V ge rs1 m1 rs2 m2 f isp EI; unfold Asm.exec_instr in EI; simpl in EI; solve_rs.
      destruct H0; subst; auto. red. intros IU F V ge rs1 m1 rs2 m2 f isp EI; unfold Asm.exec_instr in EI; simpl in EI; solve_rs.
      simpl in B.
      destruct B; subst; auto. red. intros IU F V ge rs1 m1 rs2 m2 f isp EI; unfold Asm.exec_instr in EI; simpl in EI; solve_rs.
      destruct H0; subst; auto. red. intros IU F V ge rs1 m1 rs2 m2 f isp EI; unfold Asm.exec_instr in EI; simpl in EI; solve_rs.
      destruct H0; subst; auto. red. intros IU F V ge rs1 m1 rs2 m2 f isp EI; unfold Asm.exec_instr in EI; simpl in EI; solve_rs.
      destruct H0; subst; auto. red. intros IU F V ge rs1 m1 rs2 m2 f isp EI; unfold Asm.exec_instr in EI; simpl in EI; solve_rs.
      simpl in B.
      destruct B; subst; auto. red. intros IU F V ge rs1 m1 rs2 m2 f isp EI;  unfold Asm.exec_instr in EI; simpl in EI; solve_rs.
      destruct H0; subst; auto. red. intros IU F V ge rs1 m1 rs2 m2 f isp EI; unfold Asm.exec_instr in EI; simpl in EI; solve_rs.
      destruct H0; subst; auto. red. intros IU F V ge rs1 m1 rs2 m2 f isp EI; unfold Asm.exec_instr in EI; simpl in EI; solve_rs.
      destruct H0; subst; auto. red. intros IU F V ge rs1 m1 rs2 m2 f isp EI; unfold Asm.exec_instr in EI; simpl in EI; solve_rs.
  Qed.

  Lemma asmgen_transl_cond_rsp:
    forall x0 m x2 x1 cond l,
      asm_code_no_rsp x0 ->
      Asmgen.ireg_of m = OK x2 ->
      transl_cond cond l (mk_setcc (Asmgen.testcond_for_condition cond) x2 x0) = OK x1 ->
      asm_code_no_rsp x1.
  Proof.
    unfold transl_cond, Asmgen.transl_cond; simpl.
    intros x0 m x2 x1 cond l ACNR IREG TRANSL.
    repeat destr_in TRANSL.
    - invasm. eauto. eapply mkset_cc_no_rsp; eauto.
    - invasm. eauto. eapply mkset_cc_no_rsp; eauto.
    - invasm. eauto. eapply mkset_cc_no_rsp; eauto.
    - invasm. eauto. eapply mkset_cc_no_rsp; eauto.
    - invasm. eauto. eapply mkset_cc_no_rsp; eauto.
    - invasm. eauto. eapply mkset_cc_no_rsp; eauto.
    - invasm. eauto. eapply mkset_cc_no_rsp; eauto.
    - invasm. eauto. eapply mkset_cc_no_rsp; eauto.
    - invasm. eauto. eapply mkset_cc_no_rsp; eauto.
    - invasm. eauto. eapply mkset_cc_no_rsp; eauto.
    - destruct c; invasm; eauto; simpl in *; solve_rs; eapply mkset_cc_no_rsp; eauto.
    - destruct c; invasm; eauto; simpl in *; solve_rs; eapply mkset_cc_no_rsp; eauto.
    - destruct c; invasm; eauto; simpl in *; solve_rs; eapply mkset_cc_no_rsp; eauto.
    - destruct c; invasm; eauto; simpl in *; solve_rs; eapply mkset_cc_no_rsp; eauto.
    - invasm. eauto. eapply mkset_cc_no_rsp; eauto.
    - invasm. eauto. eapply mkset_cc_no_rsp; eauto.
  Qed.

  Lemma goto_label_rsp:
    forall F V (ge: _ F V) rs1 rs2 f l m1 m2,
      goto_label ge f l rs1 m1 = Next rs2 m2 ->
      rs2 RSP = rs1 RSP.
  Proof.
    unfold goto_label.
    intros F V ge rs1 rs2 f l m1 m2 A.
    repeat destr_in A. solve_rs.
  Qed.


  Lemma mkjcc_no_rsp:
    forall x0 x2 i c,
      asm_code_no_rsp x0 ->
      In i (mk_jcc c x2 x0) ->
      asm_instr_no_rsp i.
  Proof.
    intros x0 x2 i c A H1.
    unfold mk_jcc, Asmgen.mk_jcc in H1. destr_in H1; simpl_cinfo.
    - destruct H1. subst. red; simpl; intros; simpl_cinfo.
      repeat destr_in H1. eapply goto_label_rsp; eauto. solve_rs.
      eapply A; eauto.
    - destruct H1. subst. red; simpl; intros; simpl_cinfo.
      invasm. repeat destr_in H1. eapply goto_label_rsp; eauto. solve_rs.
      destruct H0. subst. red; simpl; intros; simpl_cinfo. 
      invasm. repeat destr_in H1. eapply goto_label_rsp; eauto. solve_rs.
      simpl in H0. 
      eapply A; eauto.
    - destruct H1. subst.  red; simpl; intros; simpl_cinfo.
      invasm. repeat destr_in H1. eapply goto_label_rsp; eauto. solve_rs. solve_rs.
      intros. eapply A. eauto.
  Qed.
  
  Lemma asmgen_transl_cond_rsp':
    forall x0 x2 x1 cond l,
      asm_code_no_rsp x0 ->
      transl_cond cond l (mk_jcc (Asmgen.testcond_for_condition cond) x2 x0) = OK x1 ->
      asm_code_no_rsp x1.
  Proof.
    unfold transl_cond, Asmgen.transl_cond; simpl.
    intros x0 x2 x1 cond l ACNR TRANSL.
    repeat destr_in TRANSL.
    - invasm. eauto. intuition subst; eauto. red; simpl; intros.
      invasm. repeat destr_in H3; eauto.
      eapply goto_label_rsp; eauto.
    - invasm. eauto. intuition subst; eauto. red; simpl; intros.
      invasm. repeat destr_in H3; eauto.
      eapply goto_label_rsp; eauto.
    - invasm. eauto. intuition subst; eauto. red; simpl; intros.
      invasm. repeat destr_in H3; eauto.
      eapply goto_label_rsp; eauto.
    - invasm. eauto. intuition subst; eauto. red; simpl; intros.
      invasm. repeat destr_in H3; eauto.
      eapply goto_label_rsp; eauto.
    - invasm. eauto. intuition subst; eauto. red; simpl; intros.
      invasm. repeat destr_in H3; eauto.
      eapply goto_label_rsp; eauto.
    - invasm. eauto. intuition subst; eauto. red; simpl; intros.
      invasm. repeat destr_in H3; eauto.
      eapply goto_label_rsp; eauto.
    - invasm. eauto. intuition subst; eauto. red; simpl; intros.
      invasm. repeat destr_in H3; eauto.
      eapply goto_label_rsp; eauto.
    - invasm. eauto. intuition subst; eauto. red; simpl; intros.
      invasm. repeat destr_in H3; eauto.
      eapply goto_label_rsp; eauto.
    - invasm. eauto. intuition subst; eauto. red; simpl; intros.
      invasm. repeat destr_in H3; eauto.
      eapply goto_label_rsp; eauto.
    - invasm. eauto. intuition subst; eauto. red; simpl; intros.
      invasm. repeat destr_in H3; eauto.
      eapply goto_label_rsp; eauto.
    - destruct c; invasm; eauto; intuition subst; eauto; try solve_rs; red; simpl; intros;
      invasm; repeat destr_in H3; eauto;
      eapply goto_label_rsp; eauto.
    - destruct c; invasm; eauto; intuition subst; eauto; try solve_rs; red; simpl; intros;
        invasm; repeat destr_in H3; eauto;
          eapply goto_label_rsp; eauto.
    - destruct c; invasm; eauto; intuition subst; eauto; try solve_rs; red; simpl; intros;
        invasm; repeat destr_in H3; eauto;
          eapply goto_label_rsp; eauto.
    - destruct c; invasm; eauto; intuition subst; eauto; try solve_rs; red; simpl; intros;
        invasm; repeat destr_in H3; eauto;
          eapply goto_label_rsp; eauto.
    - invasm. eauto. intuition subst; eauto. red; simpl; intros.
      invasm. repeat destr_in H3; eauto.
      eapply goto_label_rsp; eauto.
    - invasm. eauto. intuition subst; eauto. red; simpl; intros.
      invasm. repeat destr_in H3; eauto.
      eapply goto_label_rsp; eauto.
  Qed.

  Lemma intconv_no_change_rsp:
    forall x0
      (ACNR : asm_code_no_rsp x0)
      m x3
      (IREG: Asmgen.ireg_of m = OK x3)
      x2 x1 i
      (REC: forall x2,  asm_instr_no_rsp (Asmgen.instr_to_with_info instr_size_map instr_size_non_zero (i x3 x2)))
      (CONV: Asmgen.mk_intconv instr_size_map instr_size_non_zero i x3 x2 x0 = OK x1),
      asm_code_no_rsp x1.
  Proof.
    intros.
    unfold Asmgen.mk_intconv in CONV. inv CONV.
    destr; repeat apply asm_code_no_rsp_cons; auto.
    red; simpl; intros; invasm; solve_rs.
  Qed.

  Lemma asmgen_no_change_rsp:
    forall f tf,
      transf_function f = OK tf ->
      asm_code_no_rsp (Asm.fn_code tf).
  Proof.
    intros f tf TR.
    unfold transf_function, Asmgen.transf_function in TR.
    monadInv TR.
    destr_in EQ0. inv EQ0.
    unfold Asmgen.transl_function in EQ.
    monadInv EQ. simpl.
    apply asm_code_no_rsp_cons. red; simpl. congruence.
    unfold Asmgen.transl_code' in EQ0.
    revert EQ0.
    set (P := fun f => forall x y, f x = OK y -> asm_code_no_rsp x -> asm_code_no_rsp y).
    assert (P (fun c => OK c)).
    { unfold P; simpl. inversion 1; tauto. }
    revert H0.
    generalize (Mach.fn_code f) true (fun c : code => OK c).
    clear g.
    induction c; simpl; intros; eauto.
    eapply H0; eauto. red; easy.
    eapply IHc. 2: apply EQ0.
    unfold P. intros. monadInv H1.
    eapply H0; eauto.

    Ltac t :=
      match goal with
      | EQ: context [match ?a with _ => _ end] |- _ => destr_in EQ
      | EQ: Asmgen.loadind _ _ _ _ _ _ _ = OK ?x |- asm_code_no_rsp ?x => eapply loadind_no_change_rsp in EQ; eauto
      | EQ: Asmgen.storeind _ _ _ _ _ _ _ = OK ?x |- asm_code_no_rsp ?x => eapply storeind_no_change_rsp in EQ; eauto
      | EQ: Asmgen.mk_intconv _ _ _ _ _ _ = OK ?x |- asm_code_no_rsp ?x => eapply intconv_no_change_rsp in EQ; eauto
      | EQ: bind _ _ = OK _ |- _ => monadInv EQ
      | EQ: OK _ = OK _ |- _ => inv EQ
      | |- asm_instr_no_rsp _ => now (red; simpl; intros; invasm; solve_rs)
      | |- asm_code_no_rsp (_ :: _) => eapply asm_code_no_rsp_cons;[red; simpl; intros; invasm; repeat t; solve_rs|eauto]
      | |- _ => intros
      end.
    Hint Resolve not_eq_sym ireg_of_not_rsp freg_of_not_rsp.
    destruct a; simpl in EQ; repeat (t; simpl).
    - unfold Asmgen.transl_op in EQ.
      repeat destr_in EQ; repeat t; try now (invasm; solve_rs).
      + eapply mk_move_nochange_rsp; eauto.
      + repeat (t; simpl).
      + eapply asmgen_transl_cond_rsp; eauto.
    - unfold Asmgen.transl_load in EQ.
      repeat t; eapply exec_load_rsp; eauto.
    - unfold Asmgen.transl_store in EQ.
      repeat t; try eapply exec_store_rsp; eauto; try easy.
      unfold Asmgen.mk_storebyte in EQ4. inv EQ4.
      repeat (t; simpl); eapply exec_store_rsp; eauto; easy.
      unfold Asmgen.mk_storebyte in EQ4. inv EQ4.
      repeat (t; simpl); eapply exec_store_rsp; eauto; easy.
    - repeat t. eapply goto_label_rsp; eauto.
    - eapply asmgen_transl_cond_rsp'; eauto.
    - erewrite goto_label_rsp. 2: eauto. solve_rs.
  Qed.

  Definition asm_instr_no_stack (i : Asm.instr_with_info) : Prop :=
    stack_invar i = true ->
    forall F V (ge: _ F V) rs1 m1 rs2 m2 f isp,
      Asm.exec_instr isp ge f i rs1 m1 = Next rs2 m2 ->
      Mem.stack_adt m2 = Mem.stack_adt m1 /\ (forall b o k p, Mem.perm m2 b o k p <-> Mem.perm m1 b o k p).


  Lemma exec_store_stack:
    forall F V (ge: _ F V) k m1 a rs1 rs l rs2 m2 sz,
      exec_store ge k m1 a rs1 rs l sz = Next rs2 m2 ->
      Mem.stack_adt m2 = Mem.stack_adt m1 /\ (forall b o k p, Mem.perm m2 b o k p <-> Mem.perm m1 b o k p).
  Proof.
    intros F V ge k m1 a rs1 rs l rs2 m2 sz STORE.
    unfold exec_store in STORE; repeat destr_in STORE. 
    unfold Mem.storev in Heqo; destr_in Heqo; inv Heqo.
    erewrite Mem.store_stack_blocks. 2: eauto.
    split; auto.
    split; intros.
    eapply Mem.perm_store_2; eauto.
    eapply Mem.perm_store_1; eauto.
  Qed.

  Lemma exec_load_stack:
    forall F V (ge: _ F V) k m1 a rs1 rs rs2 m2 sz,
      exec_load ge k m1 a rs1 rs sz = Next rs2 m2 ->
      Mem.stack_adt m2 = Mem.stack_adt m1 /\ (forall b o k p, Mem.perm m2 b o k p <-> Mem.perm m1 b o k p).
  Proof.
    intros F V ge k m1 a rs1 rs rs2 m2 sz LOAD.
    unfold exec_load in LOAD; destr_in LOAD.
  Qed.

  Lemma goto_label_stack:
    forall F V (ge: _ F V) f l m1 rs1 rs2 m2,
      goto_label ge f l rs1 m1 = Next rs2 m2 ->
      Mem.stack_adt m2 = Mem.stack_adt m1 /\ (forall b o k p, Mem.perm m2 b o k p <-> Mem.perm m1 b o k p).
  Proof.
    intros F V ge f l m1 rs1 rs2 m2 GOTO.
    unfold goto_label in GOTO; repeat destr_in GOTO.
  Qed.

  Lemma asmgen_no_change_stack i:
    asm_instr_no_stack i.
  Proof.
    red; intros IU F V ge0 rs1 m1 rs2 m2 f isp EI.
    destruct i as (i & info);
      destruct i; simpl in IU; try discriminate;
        unfold exec_instr in EI; simpl in EI; repeat destr_in EI;
          first [ split;[reflexivity|tauto]
                | now (eapply exec_load_stack; eauto)
                | now (eapply exec_store_stack; eauto)
                | now ( eapply goto_label_stack; eauto)
                | idtac ].
    Unshelve. all: auto.
    apply @Genv.empty_genv. exact nil. exact Mint32. exact PC. exact Ptrofs.zero.
  Qed.

  Definition asm_instr_nb_fw i:=
    forall F V (ge: _ F V) f rs1 m1 rs2 m2 isp,
      Asm.exec_instr isp ge f i rs1 m1 = Next rs2 m2 ->
      Ple (Mem.nextblock m1) (Mem.nextblock m2).

  Definition asm_code_nb_fw c :=
    forall i, In i c -> asm_instr_nb_fw i.


    Lemma exec_store_nb:
      forall F V (ge: _ F V) k m1 a rs1 rs l rs2 m2 sz,
        exec_store ge k m1 a rs1 rs l sz = Next rs2 m2 ->
        Ple (Mem.nextblock m1) (Mem.nextblock m2).
    Proof.
      intros F V ge k m1 a rs1 rs l rs2 m2 sz STORE.
      unfold exec_store in STORE; repeat destr_in STORE. 
      unfold Mem.storev in Heqo; destr_in Heqo; inv Heqo.
      erewrite (Mem.nextblock_store _ _ _ _ _ _ H1); apply Ple_refl.
    Qed.

    Lemma exec_load_nb:
      forall F V (ge: _ F V) k m1 a rs1 rs rs2 m2 sz,
        exec_load ge k m1 a rs1 rs sz = Next rs2 m2 ->
        Ple (Mem.nextblock m1) (Mem.nextblock m2).
    Proof.
      intros F V ge k m1 a rs1 rs rs2 m2 sz LOAD.
      unfold exec_load in LOAD; destr_in LOAD. inv LOAD.
      apply Ple_refl.
    Qed.


  Lemma asmgen_nextblock_forward i:
    asm_instr_nb_fw i.
  Proof.
    red. intros F V ge f rs1 m1 rs2 m2 isp EI.
    unfold exec_instr in EI.
    destruct i as(i&info); destruct i; simpl in EI; inv EI; try (apply Ple_refl);
      first [now eapply exec_load_nb; eauto
            | now (eapply exec_store_nb; eauto)
            | idtac ].
    - repeat destr_in H1. apply Ple_refl.
    - repeat destr_in H1. apply Ple_refl.
    - repeat destr_in H1. apply Ple_refl.
    - repeat destr_in H1. apply Ple_refl.
    - repeat destr_in H1; apply Ple_refl.
    - unfold goto_label in H1. repeat destr_in H1; apply Ple_refl.
    - unfold goto_label in H1. repeat destr_in H1; apply Ple_refl.
    - unfold goto_label in H1. repeat destr_in H1; apply Ple_refl.
    - unfold goto_label in H1. repeat destr_in H1; apply Ple_refl.
    - rewrite Mem.push_new_stage_nextblock; xomega.
    - rewrite Mem.push_new_stage_nextblock; xomega.
    - repeat destr_in H1. rewnb. xomega.
    - repeat destr_in H1.
      apply Mem.record_stack_block_nextblock in Heqo0.
      apply Mem.nextblock_store in Heqo.
      apply Mem.nextblock_alloc in Heqp. 
      rewrite Heqo0, Heqo, Heqp. xomega.
    - repeat (destr_in H1; [idtac]). rewnb. xomega.
    - repeat destr_in H1. apply Ple_refl.
  Qed.

  Lemma val_inject_set:
    forall j rs1 rs2
      (RINJ: forall r, Val.inject j (rs1 r) (rs2 r))
      v v' (VINJ: Val.inject j v v') r1 r,
      Val.inject j ((rs1 # r1 <- v) r) ((rs2 # r1 <- v') r).
  Proof.
    intros.
    destruct (PregEq.eq r1 r); subst; auto.
    rewrite ! Pregmap.gss; auto.
    rewrite ! Pregmap.gso by auto. auto.
  Qed.

  Lemma val_inject_undef_regs:
    forall l j rs1 rs2
      (RINJ: forall r, Val.inject j (rs1 r) (rs2 r))
      r,
      Val.inject j (undef_regs l rs1 r) (undef_regs l rs2 r).
  Proof.
    induction l; simpl; intros; eauto.
    apply IHl.
    intros; apply val_inject_set; auto.
  Qed.

  Lemma val_inject_nextinstr:
    forall j rs1 rs2 sz
      (RINJ: forall r, Val.inject j (rs1 r) (rs2 r)) r,
      Val.inject j (nextinstr rs1 r sz) (nextinstr rs2 r sz).
  Proof.
    unfold nextinstr.
    intros.
    apply val_inject_set; auto.
    apply Val.offset_ptr_inject; auto.
  Qed.

  Lemma val_inject_nextinstr_nf:
    forall j rs1 rs2 sz
      (RINJ: forall r, Val.inject j (rs1 r) (rs2 r)) r,
      Val.inject j (nextinstr_nf rs1 r sz) (nextinstr_nf rs2 r sz).
  Proof.
    unfold nextinstr_nf.
    intros.
    apply val_inject_nextinstr; auto.
    intros.
    apply val_inject_undef_regs; auto.
  Qed.

End WITHINSTRSIZEMAP.

End WITHMEMORYMODEL.