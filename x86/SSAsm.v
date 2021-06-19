Require Import Coqlib Ourlib Maps.
Require Import AST Integers Floats Values Memory Events Globalenvs Smallstep.
Require Import Locations Conventions.
Require Import Asm eAsm.

Section SSASM.

Variable ge: genv.

Definition exec_instr (f: function) (i: instruction) (rs: regset) (m: mem) : outcome :=
  match i with
  | Pallocframe sz ofs_ra ofs_link =>
    let aligned_sz := align sz 8 in
    let sp := Val.offset_ptr (rs RSP) (Ptrofs.neg (Ptrofs.repr aligned_sz)) in
    match Mem.storev Mptr m (Val.offset_ptr sp ofs_link) rs#RSP with
    | None => Stuck
    | Some m1 =>
      match Mem.storev Mptr m1 (Val.offset_ptr sp ofs_ra) rs#RA with
      | None => Stuck
      | Some m2 => Next (nextinstr (rs #RAX <- (rs#RSP) #RSP <- sp)) m2
      end
    end
  | Pfreeframe sz ofs_ra ofs_link =>
    match Mem.loadv Mptr m (Val.offset_ptr rs#RSP ofs_ra) with
    | None => Stuck
    | Some ra =>
      match Mem.loadv Mptr m (Val.offset_ptr rs#RSP ofs_link) with
      | None => Stuck
      | Some sp => Next (nextinstr (rs#RSP <- sp #RA <- ra)) m
      end
    end
  | _ => eAsm.exec_instr ge f i rs m
  end.

Inductive step  : state -> trace -> state -> Prop :=
| exec_step_internal:
    forall b ofs f i rs m rs' m',
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Ptrofs.unsigned ofs) (fn_code f) = Some i ->
      exec_instr f i rs m = Next rs' m' ->
      step (State rs m) E0 (State rs' m')
| exec_step_builtin:
    forall b ofs f ef args res rs m vargs t vres rs' m',
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Ptrofs.unsigned ofs) f.(fn_code) = Some (Pbuiltin ef args res) ->
      eval_builtin_args ge rs (rs RSP) m args vargs ->
      external_call ef ge vargs m t vres m' ->
      rs' = nextinstr_nf
              (set_res res vres
                       (undef_regs (map preg_of (destroyed_by_builtin ef)) rs)) ->
      step (State rs m) t (State rs' m')
| exec_step_external:
    forall b ef args res rs m t rs' m',
      rs PC = Vptr b Ptrofs.zero ->
      Genv.find_funct_ptr ge b = Some (External ef) ->
      extcall_arguments rs m (ef_sig ef) args ->
      external_call ef ge args m t res m' ->
      rs' = (set_pair (loc_external_result (ef_sig ef)) res (undef_caller_save_regs rs)) #PC <- (rs RA) ->
      step (State rs m) t (State rs' m').

End SSASM.

(** Execution of whole programs. *)

Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall m0 m1 m2 stk,
      Genv.init_mem p = Some m0 ->
      Mem.alloc m0 0 (Mem.max_stacksize) = (m1, stk) ->
      Mem.record_frame (Mem.push_stage m1) (Mem.mk_frame Mem.max_stacksize) = Some m2 ->
      let ge := Genv.globalenv p in
      let rs0 :=
        (Pregmap.init Vundef)
        # PC <- (Genv.symbol_address ge p.(prog_main) Ptrofs.zero)
        # RA <- Vnullptr
        # RSP <- (Vptr stk (Ptrofs.repr (Mem.max_stacksize)))  in
      initial_state p (State rs0 m2).

(** The same final_state as defined in the Asm.v *)
Definition semantics (p: program) :=
  Semantics step (initial_state p) final_state (Genv.globalenv p).

Lemma semantics_determinate: forall p, determinate (semantics p).
Proof.
Ltac Equalities :=
  match goal with
  | [ H1: ?a = ?b, H2: ?a = ?c |- _ ] =>
      rewrite H1 in H2; inv H2; Equalities
  | _ => idtac
  end.
  intros; constructor; simpl; intros.
- (* determ *)
  inv H; inv H0; Equalities.
+ split. constructor. auto.
+ discriminate.
+ discriminate.
+ assert (vargs0 = vargs) by (eapply eval_builtin_args_determ; eauto). subst vargs0.
  exploit external_call_determ. eexact H5. eexact H11. intros [A B].
  split. auto. intros. destruct B; auto. subst. auto.
+ assert (args0 = args) by (eapply extcall_arguments_determ; eauto). subst args0.
  exploit external_call_determ. eexact H4. eexact H9. intros [A B].
  split. auto. intros. destruct B; auto. subst. auto.
- (* trace length *)
  red; intros; inv H; simpl.
  lia.
  eapply external_call_trace_length; eauto.
  eapply external_call_trace_length; eauto.
- (* initial states *)
  inv H; inv H0.
  unfold ge, ge0, rs0, rs1 in *; rewrite_hyps. auto.
- (* final no step *)
  assert (NOTNULL: forall b ofs, Vnullptr <> Vptr b ofs).
  { intros; unfold Vnullptr; destruct Archi.ptr64; congruence. }
  inv H. red; intros; red; intros. inv H; rewrite H0 in *; eelim NOTNULL; eauto.
- (* final states *)
  inv H; inv H0. congruence.
Qed.
