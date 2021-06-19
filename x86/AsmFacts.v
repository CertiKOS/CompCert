Require Import Coqlib Coqlib Maps.
Require Import AST Integers Floats Values Memory Events Globalenvs Smallstep.
Require Import Asm Asmgenproof0 eAsm.

(** instructions which have no relationship with stack *)
Definition stk_unrelated_instr (i: instruction) :=
  match i with
    Pallocframe _ _ _
  | Pfreeframe _ _ _
  | Pcall_s _ _
  | Pcall_r _ _
  | Pret => false
  | _ => true
  end.

(** modify RSP register *)
(* Useful Lemmas *)
Lemma nextinstr_rsp:
  forall rs, nextinstr rs RSP = rs RSP.
Proof.
  unfold nextinstr.
  intros; rewrite Pregmap.gso; congruence.
Qed.

Lemma nextinstr_nf_rsp:
  forall rs, nextinstr_nf rs RSP = rs RSP.
Proof.
  unfold nextinstr_nf.
  intros. rewrite nextinstr_rsp.
  rewrite undef_regs_other; auto.
  simpl; intuition subst; congruence.
Qed.

(* Internal Step *)
(* Definition asm_exec_instr_unchange_rsp (i : instruction) : Prop := *)
(*   forall ge rs1 m1 rs2 m2 f, *)
(*     Asm.exec_instr ge f i rs1 m1 = Next rs2 m2 -> *)
(*     rs2 # RSP = rs1 # RSP. *)

Definition asm_instr_unchange_rsp (i : instruction) : Prop :=
  forall ge f rs m rs' m',
    stk_unrelated_instr i = true ->
    eAsm.exec_instr ge f i rs m = Next rs' m' ->
    rs # RSP = rs' # RSP.

(* Lemma find_instr_eq: *)
(*   forall code ofs i, *)
(*     find_instr ofs code = Some i -> In i code. *)
(* Proof. *)
(*   intro code. induction code. *)
(*   - intros. inv H. *)
(*   - intros. simpl in H. *)
(*     destruct (zeq ofs 0) eqn:EQ. *)
(*     + inv H. simpl. auto. *)
(*     + apply IHcode in H. *)
(*       simpl. right. auto. *)
(* Qed. *)

(* Definition asm_code_unchange_rsp (c : Asm.code) : Prop := *)
(*   forall i, *)
(*     In i c -> *)
(*     asm_instr_unchange_rsp i. *)

(* Definition asm_internal_unchange_rsp (ge: Genv.t Asm.fundef unit) : Prop := *)
(*   forall b f, *)
(*     Genv.find_funct_ptr ge b = Some (Internal f) -> *)
(*     asm_code_unchange_rsp (fn_code f). *)

Definition asm_internal_unchange_rsp (ge: Genv.t Asm.fundef unit) : Prop :=
  forall b ofs f i,
    Genv.find_funct_ptr ge b = Some (Internal f) ->
    find_instr (Ptrofs.unsigned ofs) (fn_code f) = Some i ->
    asm_instr_unchange_rsp i.

(* Builtin Step *)
Definition asm_builtin_unchange_rsp (ge: Genv.t Asm.fundef unit) : Prop :=
  forall b ofs f ef args res (rs: regset) m vargs t vres rs' m',
    Genv.find_funct_ptr ge b = Some (Internal f) ->
    find_instr (Ptrofs.unsigned ofs) f.(fn_code) = Some (Pbuiltin ef args res) ->
    eval_builtin_args ge rs (rs RSP) m args vargs ->
    external_call ef ge vargs m t vres m' ->
    rs' = nextinstr_nf
              (set_res res vres
                       (undef_regs (map preg_of (Machregs.destroyed_by_builtin ef)) rs)) ->
    rs # RSP = rs' # RSP.

(* Extenal Step *)
Definition asm_external_unchange_rsp (ge: Genv.t Asm.fundef unit) : Prop :=
  forall b ef args res rs m t rs' m',
    Genv.find_funct_ptr ge b = Some (External ef) ->
    extcall_arguments rs m (ef_sig ef) args ->
    external_call ef ge args m t res m' ->
    rs' = (set_pair (loc_external_result (ef_sig ef)) res (undef_caller_save_regs rs)) #PC <- (rs RA) ->
    rs # RSP = rs' # RSP.

Definition asm_prog_unchange_rsp (ge: Genv.t Asm.fundef unit) : Prop :=
  asm_internal_unchange_rsp ge /\
  asm_builtin_unchange_rsp ge /\
  asm_external_unchange_rsp ge.

(** Proof *)
Definition no_rsp_pair (b: rpair preg) :=
  match b with
  | One r => r <> RSP
  | Twolong hi lo => hi <> RSP /\ lo <> RSP
  end.

Lemma set_pair_no_rsp:
  forall p res rs,
    no_rsp_pair p ->
    set_pair p res rs RSP = rs RSP.
Proof.
  destruct p; simpl; intros; rewrite ! Pregmap.gso; intuition. 
Qed.

Lemma asm_external_unchange_rsp1 (ge: Genv.t Asm.fundef unit) :
  asm_external_unchange_rsp ge.
Proof.
  red. intros.
  subst.
  assert (NORSPPAIR: no_rsp_pair (loc_external_result (ef_sig ef))).
  {
    red. unfold loc_external_result.
    remember (Conventions1.loc_result (ef_sig ef)) as Mpair.
    destruct Mpair; simpl.
    - destruct r; try (simpl; congruence).
    - split. destruct rhi; try (simpl; congruence).
      destruct rlo; try (simpl; congruence).
  }
  repeat rewrite Pregmap.gso by (congruence).
  rewrite set_pair_no_rsp; eauto.
Qed.  
  
(** modify abstract stack *)
Definition asm_instr_unchange_stk (i : instruction) : Prop :=
  stk_unrelated_instr i = true ->
  forall ge rs m rs' m' f,
    eAsm.exec_instr ge f i rs m = Next rs' m' ->
    Mem.stack (Mem.support m) = Mem.stack (Mem.support m') /\
    (forall b o k p, Mem.perm m b o k p <-> Mem.perm m' b o k p).

Lemma asm_prog_unchange_stk (i : instruction) :
  asm_instr_unchange_stk i.
Proof.
Admitted.

(** modify memory *)
Lemma exec_store_unchange_support:
  forall ge k a rs m r l rs' m',
    Asm.exec_store ge k m a rs r l = Next rs' m' ->
    Mem.sup_include (Mem.support m) (Mem.support m').
Proof.
  intros ge k a rs m r l rs' m' STORE.
  unfold exec_store in STORE. repeat destr_in STORE.
  apply Mem.support_storev in Heqo.
  rewrite Heqo. apply Mem.sup_include_refl.  
Qed.

Lemma exec_load_unchange_support:
  forall ge k a m rs rd rs' m',
    exec_load ge k m a rs rd = Next rs' m' ->
    Mem.sup_include (Mem.support m) (Mem.support m').
Proof.
  intros ge k a m rs rd rs' m' LOAD.
  unfold exec_load in LOAD. destr_in LOAD.
Qed.

Definition asm_instr_unchange_support (i : instruction) : Prop :=
  forall ge rs m rs' m' f,
    eAsm.exec_instr ge f i rs m = Next rs' m' ->
    Mem.sup_include (Mem.support m) (Mem.support m').

Lemma asm_prog_unchange_support (i : instruction) :
  asm_instr_unchange_support i.
Proof.
  red. intros *. intros EI. unfold exec_instr in EI.
  destruct i; simpl in EI; inv EI; try (apply Mem.sup_include_refl);
      first [ now (eapply exec_load_unchange_support; eauto)
            | now (eapply exec_store_unchange_support; eauto)
            | now (repeat destr_in H0)
            | unfold goto_label in H0; repeat destr_in H0].
  + remember (Mem.push_stage m0) as mp. symmetry in Heqmp.
    apply Mem.sup_include_alloc in Heqp.
    apply Mem.sup_include_push_stage in Heqmp.
    apply Mem.sup_include_record_frame in Heqo.
    apply Mem.support_store in Heqo0.
    apply Mem.support_store in Heqo1.
    eapply Mem.sup_include_trans. apply Heqp.
    eapply Mem.sup_include_trans. apply Heqmp.
    eapply Mem.sup_include_trans. apply Heqo.
    rewrite <- Heqo0. rewrite Heqo1.
    apply Mem.sup_include_refl.
  + apply Mem.support_free in Heqo1.
    apply Mem.sup_include_pop_stage in Heqo2.
    rewrite <- Heqo1. eauto.
Qed.


