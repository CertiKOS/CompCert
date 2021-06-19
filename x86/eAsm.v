Require Import Coqlib Ourlib Maps.
Require Import AST Integers Floats Values Memory Events Globalenvs Smallstep.
Require Import Locations Conventions.
Require Import Asm.

Section EASM.

Variable ge: genv.

(* Need to promise PC points to a function block *)
Definition goto_label (f: function) (lbl: label) (rs: regset) (m: mem) :=
  match label_pos lbl 0 (fn_code f) with
  | None => Stuck
  | Some pos =>
    match rs#PC with
    | Vptr b ofs =>
      match Genv.find_funct_ptr ge b with
      | Some _ => Next (rs#PC <- (Vptr b (Ptrofs.repr pos))) m
      | None => Stuck
      end
    | _ => Stuck
    end
  end.

Definition exec_instr (f: function) (i: instruction) (rs: regset) (m: mem) : outcome :=
  match i with
  (* change goto_label *)
  | Pjmp_l lbl =>
    goto_label f lbl rs m
  | Pjcc cond lbl =>
    match eval_testcond cond rs with
    | Some true => goto_label f lbl rs m
    | Some false => Next (nextinstr rs) m
    | None => Stuck
    end
  | Pjcc2 cond1 cond2 lbl =>
    match eval_testcond cond1 rs, eval_testcond cond2 rs with
    | Some true, Some true => goto_label f lbl rs m
    | Some _, Some _ => Next (nextinstr rs) m
    | _, _ => Stuck
    end
  | Pjmptbl r tbl =>
    match rs#r with
    | Vint n =>
      match list_nth_z tbl (Int.unsigned n) with
      | None => Stuck
      | Some lbl => goto_label f lbl (rs #RAX <- Vundef #RDX <- Vundef) m
      end
    | _ => Stuck
    end        
  | Pallocframe sz ofs_ra ofs_link =>
    (* check size first *)
    if (zle sz 0)
    then Stuck
    else
      let (m1, stk) := Mem.alloc m 0 sz in
      match Mem.record_frame (Mem.push_stage m1) (Mem.mk_frame sz) with
      |None => Stuck
      |Some m2 =>
       let sp := Vptr stk Ptrofs.zero in
       match Mem.storev Mptr m2 (Val.offset_ptr sp ofs_link) rs#RSP with
       | None => Stuck
       | Some m3 =>
         match Mem.storev Mptr m3 (Val.offset_ptr sp ofs_ra) rs#RA with
         | None => Stuck
         | Some m4 => Next (nextinstr (rs #RAX <- (rs#RSP) #RSP <- sp)) m4
         end
       end
      end
  | _ => Asm.exec_instr ge f i rs m
  end.

Inductive step: state -> trace -> state -> Prop :=
  | exec_step_internal:
      forall b ofs f i rs m rs' m',
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Ptrofs.unsigned ofs) f.(fn_code) = Some i ->
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

End EASM.

(** Execution of whole programs. *)

Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall m0 m1 m2 stk,
      Genv.init_mem p = Some m0 ->
      Mem.alloc m0 0 0 = (m1, stk) ->
      Mem.record_frame (Mem.push_stage m1) (Mem.mk_frame 0) = Some m2 -> 
      let ge := Genv.globalenv p in
      let rs0 :=
        (Pregmap.init Vundef)
        # PC <- (Genv.symbol_address ge p.(prog_main) Ptrofs.zero)
        # RA <- Vnullptr
        # RSP <- (Vptr stk Ptrofs.zero) in
      initial_state p (State rs0 m0).

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
