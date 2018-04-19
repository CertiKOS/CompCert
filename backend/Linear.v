(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** The Linear intermediate language: abstract syntax and semantcs *)

(** The Linear language is a variant of LTL where control-flow is not
    expressed as a graph of basic blocks, but as a linear list of
    instructions with explicit labels and ``goto'' instructions. *)

Require Import Coqlib.
Require Import AST Integers Values Memory Events Globalenvs Smallstep.
Require Import Op Locations LTL Conventions.

(** * Abstract syntax *)

Definition label := positive.

Inductive instruction: Type :=
  | Lgetstack: slot -> Z -> typ -> mreg -> instruction
  | Lsetstack: mreg -> slot -> Z -> typ -> instruction
  | Lop: operation -> list mreg -> mreg -> instruction
  | Lload: memory_chunk -> addressing -> list mreg -> mreg -> instruction
  | Lstore: memory_chunk -> addressing -> list mreg -> mreg -> instruction
  | Lcall: signature -> mreg + ident -> instruction
  | Ltailcall: signature -> mreg + ident -> instruction
  | Lbuiltin: external_function -> list (builtin_arg loc) -> builtin_res mreg -> instruction
  | Llabel: label -> instruction
  | Lgoto: label -> instruction
  | Lcond: condition -> list mreg -> label -> instruction
  | Ljumptable: mreg -> list label -> instruction
  | Lreturn: instruction.

Definition code: Type := list instruction.

Record function: Type := mkfunction {
  fn_sig: signature;
  fn_stacksize: Z;
  fn_code: code
}.

Definition fundef := AST.fundef function.

Definition program := AST.program fundef unit.

Definition funsig (fd: fundef) :=
  match fd with
  | Internal f => fn_sig f
  | External ef => ef_sig ef
  end.

Definition genv := Genv.t fundef unit.
Definition locset := Locmap.t.

(** * Operational semantics *)

(** Looking up labels in the instruction list.  *)

Definition is_label (lbl: label) (instr: instruction) : bool :=
  match instr with
  | Llabel lbl' => if peq lbl lbl' then true else false
  | _ => false
  end.

Lemma is_label_correct:
  forall lbl instr,
  if is_label lbl instr then instr = Llabel lbl else instr <> Llabel lbl.
Proof.
  intros.  destruct instr; simpl; try discriminate.
  case (peq lbl l); intro; congruence.
Qed.

(** [find_label lbl c] returns a list of instruction, suffix of the
  code [c], that immediately follows the [Llabel lbl] pseudo-instruction.
  If the label [lbl] is multiply-defined, the first occurrence is
  retained.  If the label [lbl] is not defined, [None] is returned. *)

Fixpoint find_label (lbl: label) (c: code) {struct c} : option code :=
  match c with
  | nil => None
  | i1 :: il => if is_label lbl i1 then Some il else find_label lbl il
  end.

Definition find_function (ge: genv) (ros: mreg + ident) (rs: locset) : option fundef :=
  match ros with
  | inl r => Genv.find_funct ge (rs (R r))
  | inr symb =>
      match Genv.find_symbol ge symb with
      | None => None
      | Some b => Genv.find_funct_ptr ge b
      end
  end.

(** Linear execution states. *)

Inductive stackframe: Type :=
  | Stackframe:
      forall (f: function)         (**r calling function *)
             (sp: val)             (**r stack pointer in calling function *)
             (rs: locset)          (**r location state in calling function *)
             (c: code),            (**r program point in calling function *)
      stackframe.

Inductive state `{memory_model_ops: Mem.MemoryModelOps}: Type :=
  | State:
      forall (stack: list stackframe) (**r call stack *)
             (f: function)            (**r function currently executing *)
             (sp: val)                (**r stack pointer *)
             (c: code)                (**r current program point *)
             (rs: locset)             (**r location state *)
             (m: mem),                (**r memory state *)
      state
  | Callstate:
      forall (stack: list stackframe) (**r call stack *)
             (f: fundef)              (**r function to call *)
             (rs: locset)             (**r location state at point of call *)
             (m: mem) (sz: Z),                (**r memory state *)
      state
  | Returnstate:
      forall (stack: list stackframe) (**r call stack *)
             (rs: locset)             (**r location state at point of return *)
             (m: mem),                (**r memory state *)
      state.

Section WITHEXTERNALCALLSOPS.
Context `{external_calls_prf: ExternalCalls}.

Variable fn_stack_requirements: ident -> Z.

Section RELSEM.

(** [parent_locset cs] returns the mapping of values for locations
  of the caller function. *)

Variable parent_lm: locset.

Definition parent_locset (stack: list stackframe) : locset :=
  match stack with
  | nil => parent_lm
  | Stackframe f sp ls c :: stack' => ls
  end.

Variable ge: genv.

Definition ros_is_function (ros: mreg + ident) (rs: locset) (i: ident) : Prop :=
  match ros with
  | inl r => exists b o, rs (R r) = Vptr b o /\ Genv.find_symbol ge i = Some b
  | inr symb => i = symb
  end.

Inductive step: state -> trace -> state -> Prop :=
  | exec_Lgetstack:
      forall s f sp sl ofs ty dst b rs m rs',
      rs' = Locmap.set (R dst) (rs (S sl ofs ty)) (undef_regs (destroyed_by_getstack sl) rs) ->
      step (State s f sp (Lgetstack sl ofs ty dst :: b) rs m)
        E0 (State s f sp b rs' m)
  | exec_Lsetstack:
      forall s f sp src sl ofs ty b rs m rs',
      rs' = Locmap.set (S sl ofs ty) (rs (R src)) (undef_regs (destroyed_by_setstack ty) rs) ->
      step (State s f sp (Lsetstack src sl ofs ty :: b) rs m)
        E0 (State s f sp b rs' m)
  | exec_Lop:
      forall s f sp op args res b rs m v rs',
      eval_operation ge sp op (reglist rs args) m = Some v ->
      rs' = Locmap.set (R res) v (undef_regs (destroyed_by_op op) rs) ->
      step (State s f sp (Lop op args res :: b) rs m)
        E0 (State s f sp b rs' m)
  | exec_Lload:
      forall s f sp chunk addr args dst b rs m a v rs',
      eval_addressing ge sp addr (reglist rs args) = Some a ->
      Mem.loadv chunk m a = Some v ->
      rs' = Locmap.set (R dst) v (undef_regs (destroyed_by_load chunk addr) rs) ->
      step (State s f sp (Lload chunk addr args dst :: b) rs m)
        E0 (State s f sp b rs' m)
  | exec_Lstore:
      forall s f sp chunk addr args src b rs m m' a rs',
      eval_addressing ge sp addr (reglist rs args) = Some a ->
      Mem.storev chunk m a (rs (R src)) = Some m' ->
      rs' = undef_regs (destroyed_by_store chunk addr) rs ->
      step (State s f sp (Lstore chunk addr args src :: b) rs m)
        E0 (State s f sp b rs' m')
  | exec_Lcall:
      forall s f sp sig ros b rs m f' id (IFI: ros_is_function ros rs id) ,
      find_function ge ros rs = Some f' ->
      sig = funsig f' ->
      step (State s f sp (Lcall sig ros :: b) rs m)
        E0 (Callstate (Stackframe f sp rs b:: s) f' rs (Mem.push_new_stage m) (fn_stack_requirements id))
  | exec_Ltailcall:
      forall s f stk sig ros b rs m rs' f' m' m'' id (IFI: ros_is_function ros rs' id),
      rs' = return_regs (parent_locset s) rs ->
      find_function ge ros rs' = Some f' ->
      sig = funsig f' ->
      Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
      Mem.tailcall_stage m' = Some m'' ->
      step (State s f (Vptr stk Ptrofs.zero) (Ltailcall sig ros :: b) rs m)
        E0 (Callstate s f' rs' m'' (fn_stack_requirements id))
  | exec_Lbuiltin:
      forall s f sp rs m ef args res b vargs t vres rs' m' m'',
      eval_builtin_args ge rs sp m args vargs ->
      external_call ef ge vargs (Mem.push_new_stage m) t vres m' ->
      Mem.unrecord_stack_block m' = Some m'' ->
      rs' = Locmap.setres res vres (undef_regs (destroyed_by_builtin ef) rs) ->
      forall BUILTIN_ENABLED : builtin_enabled ef,
        step (State s f sp (Lbuiltin ef args res :: b) rs m)
             t (State s f sp b rs' m'')
  | exec_Llabel:
      forall s f sp lbl b rs m,
      step (State s f sp (Llabel lbl :: b) rs m)
        E0 (State s f sp b rs m)
  | exec_Lgoto:
      forall s f sp lbl b rs m b',
      find_label lbl f.(fn_code) = Some b' ->
      step (State s f sp (Lgoto lbl :: b) rs m)
        E0 (State s f sp b' rs m)
  | exec_Lcond_true:
      forall s f sp cond args lbl b rs m rs' b',
      eval_condition cond (reglist rs args) m = Some true ->
      rs' = undef_regs (destroyed_by_cond cond) rs ->
      find_label lbl f.(fn_code) = Some b' ->
      step (State s f sp (Lcond cond args lbl :: b) rs m)
        E0 (State s f sp b' rs' m)
  | exec_Lcond_false:
      forall s f sp cond args lbl b rs m rs',
      eval_condition cond (reglist rs args) m = Some false ->
      rs' = undef_regs (destroyed_by_cond cond) rs ->
      step (State s f sp (Lcond cond args lbl :: b) rs m)
        E0 (State s f sp b rs' m)
  | exec_Ljumptable:
      forall s f sp arg tbl b rs m n lbl b' rs',
      rs (R arg) = Vint n ->
      list_nth_z tbl (Int.unsigned n) = Some lbl ->
      find_label lbl f.(fn_code) = Some b' ->
      rs' = undef_regs (destroyed_by_jumptable) rs ->
      step (State s f sp (Ljumptable arg tbl :: b) rs m)
        E0 (State s f sp b' rs' m)
  | exec_Lreturn:
      forall s f stk b rs m m',
        Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
      step (State s f (Vptr stk Ptrofs.zero) (Lreturn :: b) rs m)
        E0 (Returnstate s (return_regs (parent_locset s) rs) m')
  | exec_function_internal:
      forall s f rs m rs' m' stk m'' sz,
        Mem.alloc m 0 f.(fn_stacksize) = (m', stk) ->
        Mem.record_stack_blocks m' (make_singleton_frame_adt stk (fn_stacksize f) sz) = Some m'' ->
      rs' = undef_regs destroyed_at_function_entry (call_regs rs) ->
      step (Callstate s (Internal f) rs m sz)
        E0 (State s f (Vptr stk Ptrofs.zero) f.(fn_code) rs' m'')
  | exec_function_external:
      forall s ef args res rs1 rs2 m t m' sz,
      args = map (fun p => Locmap.getpair p rs1) (loc_arguments (ef_sig ef)) ->
      external_call ef ge args m t res m' ->
      rs2 = Locmap.setpair (loc_result (ef_sig ef)) res (undef_regs destroyed_at_call rs1) ->
      step (Callstate s (External ef) rs1 m sz)
         t (Returnstate s rs2 m')
  | exec_return:
      forall s f sp rs0 c rs m m',
        Mem.unrecord_stack_block m = Some m' ->
      step (Returnstate (Stackframe f sp rs0 c :: s) rs m)
        E0 (State s f sp c rs m').

Variable init_m: mem.

Inductive bounds_stack (m: mem) : list stackframe -> Prop :=
| bs_nil: bounds_stack m nil
| bs_cons f sp ls c cs
    (VB: Mem.valid_block m sp)
    (PERM: forall ofs p,
        Mem.perm m sp ofs Max p ->
        0 <= ofs < fn_stacksize f)
    (BS: bounds_stack m cs):
    bounds_stack m (Stackframe f (Vptr sp Ptrofs.zero) ls c :: cs).

Inductive nextblock_properties_linear: state -> Prop :=
| nextblock_properties_linear_intro:
    forall cs f sp c ls m 
      (INIT_VB: Ple (Mem.nextblock init_m) (Mem.nextblock m))
      (PERM_stack: forall (ofs : Z) (p : permission), Mem.perm m sp ofs Max p -> 0 <= ofs < fn_stacksize f)
      (BS: bounds_stack m cs)
      (VB: Mem.valid_block m sp),
      nextblock_properties_linear (State cs f (Vptr sp Ptrofs.zero) c ls m)
| nextblock_properties_linear_call:
    forall  cs f ls m sz
       (INIT_VB: Ple (Mem.nextblock init_m) (Mem.nextblock m))
       (BS: bounds_stack m cs),
      nextblock_properties_linear (Callstate cs f ls m sz)
| nextblock_properties_linear_return:
    forall cs ls m 
      (INIT_VB: Ple (Mem.nextblock init_m) (Mem.nextblock m))
      (BS: bounds_stack m cs),
      nextblock_properties_linear (Returnstate cs ls m).


Lemma bounds_stack_perm:
  forall s m (BS: bounds_stack m s)
    m' (PERM: forall b ofs p, Mem.valid_block m b -> Mem.perm m' b ofs Max p -> Mem.perm m b ofs Max p)
    (PLE: Ple (Mem.nextblock m) (Mem.nextblock m')),
    bounds_stack m' s.
Proof.
  induction s; simpl; intros; eauto.
  constructor.
  inv BS. constructor; eauto.
  unfold Mem.valid_block in *; xomega.
Qed.

Lemma bounds_stack_store:
  forall s m (BS: bounds_stack m s)
    chunk b o v m'
    (STORE: Mem.store chunk m b o v = Some m'),
    bounds_stack m' s.
Proof.
  intros; eapply bounds_stack_perm; eauto.
  intros. eapply Mem.perm_store_2; eauto.
  erewrite <- Mem.nextblock_store; eauto. xomega.
Qed.

Lemma bounds_stack_free:
  forall s m (BS: bounds_stack m s)
    b lo hi m'
    (FREE: Mem.free m b lo hi = Some m'),
    bounds_stack m' s.
Proof.
  intros.
  eapply bounds_stack_perm; eauto.
  intros; eapply Mem.perm_free_3; eauto.
  intros; erewrite <- Mem.nextblock_free; eauto. xomega.
Qed.


Lemma bounds_stack_unrecord_stack_block:
  forall s m (BS: bounds_stack m s)
    m'
    (FREE: Mem.unrecord_stack_block m = Some m'),
    bounds_stack m' s.
Proof.
  intros.
  generalize (Mem.unrecord_stack_block_mem_unchanged _ _ FREE);
    let A := fresh in
    intro A; decompose [and] A; clear A;
      generalize (fun b => Mem.unrecord_stack_block_get_frame_info _ _ b FREE).
  intros; eapply bounds_stack_perm; eauto.
  intros. eapply H2; eauto.
  rewrite H0; xomega.
Qed.

Lemma bounds_stack_record_stack_block:
  forall s m (BS: bounds_stack m s)
    m' b
    (FREE: Mem.record_stack_blocks m b = Some m'),
    bounds_stack m' s.
Proof.
  intros.
  generalize (Mem.record_stack_blocks_mem_unchanged _ _ _ FREE);
    let A := fresh in
    intro A; decompose [and] A; clear A.
  intros; eapply bounds_stack_perm; eauto.
  intros. eapply H2; eauto.
  rewrite H0; xomega.
Qed.


Lemma bounds_stack_push:
  forall s m (BS: bounds_stack m s),
    bounds_stack (Mem.push_new_stage m) s.
Proof.
  intros.
  eapply bounds_stack_perm; eauto.
  intros. rewrite Mem.push_new_stage_perm in H0. auto.
  rewnb. xomega.
Qed.

Theorem np_linear_step:
  forall s1 t s2,
    step s1 t s2 ->
    nextblock_properties_linear s1 ->
    nextblock_properties_linear s2.
Proof.
  destruct 1; simpl; intros NPL; inv NPL; try econstructor; unfold Mem.valid_block; rewnb; eauto.
  intros ofs p P. eapply PERM_stack. eapply Mem.storev_perm_inv; eauto.
  destruct a; simpl in *; try discriminate.
  eapply bounds_stack_store; eauto.
  apply bounds_stack_push.
  constructor; auto.
  eapply bounds_stack_perm.
  eapply bounds_stack_free; eauto.
  intros b0 ofs p VB2; repeat rewrite_perms. tauto.
  rewnb. xomega.
  intros; eapply PERM_stack. eapply Mem.unrecord_stack_block_perm in H2. 2: eauto.
  eapply external_call_max_perm in H2. 2: eauto.
  rewrite Mem.push_new_stage_perm in H2. eauto.
  red; rewnb; auto.
  eapply bounds_stack_unrecord_stack_block. 2: eauto.
  eapply bounds_stack_perm. apply bounds_stack_push. eauto.
  intros. eapply external_call_max_perm; eauto.
  rewnb; xomega.
  eapply bounds_stack_free; eauto.
  xomega.
  intros.
  eapply Mem.record_stack_block_perm in H1. 2: eauto.
  eapply Mem.perm_alloc_3; eauto.
  eapply bounds_stack_record_stack_block. 2: eauto.
  eapply bounds_stack_perm; eauto.
  intros. eapply Mem.perm_alloc_inv in H2. 2: eauto.
  destruct eq_block; auto. subst. eapply Mem.fresh_block_alloc in H1; eauto. easy.
  rewnb; xomega.
  exploit Mem.alloc_result; eauto. intro; subst. xomega.
  eapply bounds_stack_perm; eauto.
  intros; eapply external_call_max_perm; eauto.
  rewnb. xomega.
  inv BS. constructor; unfold Mem.valid_block; rewnb; eauto; try xomega.
  intros; eapply PERM. eapply Mem.unrecord_stack_block_perm in H0; eauto.
  eapply bounds_stack_unrecord_stack_block; eauto.
Qed.

End RELSEM.

Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall b f m0 m2,
      let ge := Genv.globalenv p in
      Genv.init_mem p = Some m0 ->
      Genv.find_symbol ge p.(prog_main) = Some b ->
      Genv.find_funct_ptr ge b = Some f ->
      funsig f = signature_main ->
      Mem.record_init_sp m0 = Some m2 ->
      initial_state p (Callstate nil f (Locmap.init Vundef) (Mem.push_new_stage m2) (fn_stack_requirements (prog_main p))).

Inductive final_state: state -> int -> Prop :=
  | final_state_intro: forall rs m retcode,
      Locmap.getpair (map_rpair R (loc_result signature_main)) rs = Vint retcode ->
      final_state (Returnstate nil rs m) retcode.

Definition semantics (p: program) :=
  Semantics (step (Locmap.init Vundef)) (initial_state p) final_state (Genv.globalenv p).

End WITHEXTERNALCALLSOPS.
