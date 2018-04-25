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

(** The Mach intermediate language: abstract syntax.

  Mach is the last intermediate language before generation of assembly
  code.
*)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Events.
Require Import Smallstep.
Require Import Op.
Require Import Locations.
Require Import Conventions.
Require Import Stacklayout.

(** * Abstract syntax *)

(** Like Linear, the Mach language is organized as lists of instructions
  operating over machine registers, with default fall-through behaviour
  and explicit labels and branch instructions.

  The main difference with Linear lies in the instructions used to
  access the activation record.  Mach has three such instructions:
  [Mgetstack] and [Msetstack] to read and write within the activation
  record for the current function, at a given word offset and with a
  given type; and [Mgetparam], to read within the activation record of
  the caller.

  These instructions implement a more concrete view of the activation
  record than the the [Lgetstack] and [Lsetstack] instructions of
  Linear: actual offsets are used instead of abstract stack slots, and the
  distinction between the caller's frame and the callee's frame is
  made explicit. *)

Definition label := positive.

Inductive instruction: Type :=
  | Mgetstack: ptrofs -> typ -> mreg -> instruction
  | Msetstack: mreg -> ptrofs -> typ -> instruction
  | Mgetparam: ptrofs -> typ -> mreg -> instruction
  | Mop: operation -> list mreg -> mreg -> instruction
  | Mload: memory_chunk -> addressing -> list mreg -> mreg -> instruction
  | Mstore: memory_chunk -> addressing -> list mreg -> mreg -> instruction
  | Mcall: signature -> mreg + ident -> instruction
  | Mtailcall: signature -> mreg + ident -> instruction
  | Mbuiltin: external_function -> list (builtin_arg mreg) -> builtin_res mreg -> instruction
  | Mlabel: label -> instruction
  | Mgoto: label -> instruction
  | Mcond: condition -> list mreg -> label -> instruction
  | Mjumptable: mreg -> list label -> instruction
  | Mreturn: instruction.

Definition code := list instruction.

Record function: Type := mkfunction
  { fn_sig: signature;
    fn_code: code;
    fn_stacksize: Z;
    (* fn_link_ofs: ptrofs; *)
    fn_retaddr_ofs: ptrofs;
    fn_frame: frame_info;
  }.

Definition fundef := AST.fundef function.

Definition program := AST.program fundef unit.

Definition funsig (fd: fundef) :=
  match fd with
  | Internal f => fn_sig f
  | External ef => ef_sig ef
  end.

Definition genv := Genv.t fundef unit.

(** * Operational semantics *)

(** The semantics for Mach is close to that of [Linear]: they differ only
  on the interpretation of stack slot accesses.  In Mach, these
  accesses are interpreted as memory accesses relative to the
  stack pointer.  More precisely:
- [Mgetstack ofs ty r] is a memory load at offset [ofs * 4] relative
  to the stack pointer.
- [Msetstack r ofs ty] is a memory store at offset [ofs * 4] relative
  to the stack pointer.
- [Mgetparam ofs ty r] is a memory load at offset [ofs * 4]
  relative to the pointer found at offset 0 from the stack pointer.
  The semantics maintain a linked structure of activation records,
  with the current record containing a pointer to the record of the
  caller function at offset 0.

In addition to this linking of activation records, the
semantics also make provisions for storing a back link at offset
[f.(fn_link_ofs)] from the stack pointer, and a return address at
offset [f.(fn_retaddr_ofs)].  The latter stack location will be used
by the Asm code generated by [Asmgen] to save the return address into
the caller at the beginning of a function, then restore it and jump to
it at the end of a function.  The Mach concrete semantics does not
attach any particular meaning to the pointer stored in this reserved
location, but makes sure that it is preserved during execution of a
function.  The [return_address_offset] parameter is used to guess the
value of the return address that the Asm code generated later will
store in the reserved location.
*)

Section WITHMEMORYMODELOPS.
Context `{memory_model_ops: Mem.MemoryModelOps}.

Definition load_stack (m: mem) (sp: val) (ty: typ) (ofs: ptrofs) :=
  Mem.loadv (chunk_of_type ty) m (Val.offset_ptr sp ofs).

Definition store_stack (m: mem) (sp: val) (ty: typ) (ofs: ptrofs) (v: val) :=
  Mem.storev (chunk_of_type ty) m (Val.offset_ptr sp ofs) v.

End WITHMEMORYMODELOPS.

Module RegEq.
  Definition t := mreg.
  Definition eq := mreg_eq.
End RegEq.

Module Regmap := EMap(RegEq).

Definition regset := Regmap.t val.

Notation "a ## b" := (List.map a b) (at level 1).
Notation "a # b <- c" := (Regmap.set b c a) (at level 1, b at next level).

Fixpoint undef_regs (rl: list mreg) (rs: regset) {struct rl} : regset :=
  match rl with
  | nil => rs
  | r1 :: rl' => Regmap.set r1 Vundef (undef_regs rl' rs)
  end.

Lemma undef_regs_other:
  forall r rl rs, ~In r rl -> undef_regs rl rs r = rs r.
Proof.
  induction rl; simpl; intros. auto. rewrite Regmap.gso. apply IHrl. intuition. intuition.
Qed.

Lemma undef_regs_same:
  forall r rl rs, In r rl -> undef_regs rl rs r = Vundef.
Proof.
  induction rl; simpl; intros. tauto.
  destruct H. subst a. apply Regmap.gss.
  unfold Regmap.set. destruct (RegEq.eq r a); auto.
Qed.

Definition set_pair (p: rpair mreg) (v: val) (rs: regset) : regset :=
  match p with
  | One r => rs#r <- v
  | Twolong rhi rlo => rs#rhi <- (Val.hiword v) #rlo <- (Val.loword v)
  end.

Fixpoint set_res (res: builtin_res mreg) (v: val) (rs: regset) : regset :=
  match res with
  | BR r => Regmap.set r v rs
  | BR_none => rs
  | BR_splitlong hi lo => set_res lo (Val.loword v) (set_res hi (Val.hiword v) rs)
  end.

Definition is_label (lbl: label) (instr: instruction) : bool :=
  match instr with
  | Mlabel lbl' => if peq lbl lbl' then true else false
  | _ => false
  end.

Lemma is_label_correct:
  forall lbl instr,
  if is_label lbl instr then instr = Mlabel lbl else instr <> Mlabel lbl.
Proof.
  intros.  destruct instr; simpl; try discriminate.
  case (peq lbl l); intro; congruence.
Qed.

Fixpoint find_label (lbl: label) (c: code) {struct c} : option code :=
  match c with
  | nil => None
  | i1 :: il => if is_label lbl i1 then Some il else find_label lbl il
  end.

Lemma find_label_incl:
  forall lbl c c', find_label lbl c = Some c' -> incl c' c.
Proof.
  induction c; simpl; intros. discriminate.
  destruct (is_label lbl a). inv H. auto with coqlib. eauto with coqlib.
Qed.

Definition find_function_ptr
        (ge: genv) (ros: mreg + ident) (rs: regset) : option block :=
  match ros with
  | inl r =>
      match rs r with
      | Vptr b ofs => if Ptrofs.eq ofs Ptrofs.zero then Some b else None
      | _ => None
      end
  | inr symb =>
      Genv.find_symbol ge symb
  end.

(** Extract the values of the arguments to an external call. *)

Section WITHMEMORYMODELOPS2.
Context `{memory_model_ops: Mem.MemoryModelOps}.

Inductive extcall_arg (rs: regset) (m: mem) (sp: val): loc -> val -> Prop :=
  | extcall_arg_reg: forall r,
      extcall_arg rs m sp (R r) (rs r)
  | extcall_arg_stack: forall ofs ty v,
      load_stack m sp ty (Ptrofs.repr (Stacklayout.fe_ofs_arg + 4 * ofs)) = Some v ->
      extcall_arg rs m sp (S Outgoing ofs ty) v.

Inductive extcall_arg_pair (rs: regset) (m: mem) (sp: val): rpair loc -> val -> Prop :=
  | extcall_arg_one: forall l v,
      extcall_arg rs m sp l v ->
      extcall_arg_pair rs m sp (One l) v
  | extcall_arg_twolong: forall hi lo vhi vlo,
      extcall_arg rs m sp hi vhi ->
      extcall_arg rs m sp lo vlo ->
      extcall_arg_pair rs m sp (Twolong hi lo) (Val.longofwords vhi vlo).

Definition extcall_arguments
    (rs: regset) (m: mem) (sp: val) (sg: signature) (args: list val) : Prop :=
  list_forall2 (extcall_arg_pair rs m sp) (loc_arguments sg) args.

End WITHMEMORYMODELOPS2.

(** Mach execution states. *)

Inductive stackframe: Type :=
  | Stackframe:
      forall (f: block)       (**r pointer to calling function *)
             (sp: block)        (**r stack pointer in calling function *)
             (retaddr: val)   (**r Asm return address in calling function *)
             (c: code),       (**r program point in calling function *)
      stackframe.

Inductive state `{memory_model_ops: Mem.MemoryModelOps}: Type :=
  | State:
      forall (stack: list stackframe)  (**r call stack *)
             (f: block)                (**r pointer to current function *)
             (sp: val)                 (**r stack pointer *)
             (c: code)                 (**r current program point *)
             (rs: regset)              (**r register state *)
             (m: mem),                 (**r memory state *)
      state
  | Callstate:
      forall (stack: list stackframe)  (**r call stack *)
             (f: block)                (**r pointer to function to call *)
             (rs: regset)              (**r register state *)
             (m: mem),                 (**r memory state *)
      state
  | Returnstate:
      forall (stack: list stackframe)  (**r call stack *)
             (rs: regset)              (**r register state *)
             (m: mem),                 (**r memory state *)
      state.

Section WITHEXTERNALCALLSOPS.
Context `{external_calls: ExternalCalls}.

Section RELSEM.
Variables init_ra: val.

Definition parent_ra (s: list stackframe) : val :=
  match s with
  | nil => init_ra
  | Stackframe f sp ra c :: s' => ra
  end.

Variable return_address_offset: function -> code -> ptrofs -> Prop.

Variable invalidate_frame: mem -> option mem.

Variable ge: genv.

Definition check_alloc_frame (f: frame_info) (fn: function) :=
  0 < (frame_size f).



Inductive step: state -> trace -> state -> Prop :=
  | exec_Mlabel:
      forall s f sp lbl c rs m,
      step (State s f sp (Mlabel lbl :: c) rs m)
        E0 (State s f sp c rs m)
  | exec_Mgetstack:
      forall s f sp ofs ty dst c rs m v,
      load_stack m sp ty ofs = Some v ->
      step (State s f sp (Mgetstack ofs ty dst :: c) rs m)
        E0 (State s f sp c (rs#dst <- v) m)
  | exec_Msetstack:
      forall s f sp src ofs ty c rs m m' rs',
      store_stack m sp ty ofs (rs src) = Some m' ->
      rs' = undef_regs (destroyed_by_setstack ty) rs ->
      step (State s f sp (Msetstack src ofs ty :: c) rs m)
        E0 (State s f sp c rs' m')
  | exec_Mgetparam:
      forall s fb f sp ofs ty dst c rs m v rs',
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      (* load_stack m sp Tptr f.(fn_link_ofs) = Some (parent_sp s) -> *)
      load_stack m (parent_sp (Mem.stack m)) ty ofs = Some v ->
      rs' = (rs # temp_for_parent_frame <- Vundef # dst <- v) ->
      step (State s fb sp (Mgetparam ofs ty dst :: c) rs m)
        E0 (State s fb sp c rs' m)
  | exec_Mop:
      forall s f sp op args res c rs m v rs',
      eval_operation ge sp op rs##args m = Some v ->
      rs' = ((undef_regs (destroyed_by_op op) rs)#res <- v) ->
      step (State s f sp (Mop op args res :: c) rs m)
        E0 (State s f sp c rs' m)
  | exec_Mload:
      forall s f sp chunk addr args dst c rs m a v rs',
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.loadv chunk m a = Some v ->
      rs' = ((undef_regs (destroyed_by_load chunk addr) rs)#dst <- v) ->
      step (State s f sp (Mload chunk addr args dst :: c) rs m)
        E0 (State s f sp c rs' m)
  | exec_Mstore:
      forall s f sp chunk addr args src c rs m m' a rs',
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.storev chunk m a (rs src) = Some m' ->
      rs' = undef_regs (destroyed_by_store chunk addr) rs ->
      step (State s f sp (Mstore chunk addr args src :: c) rs m)
        E0 (State s f sp c rs' m')
  | exec_Mcall:
      forall s fb sp sig ros c rs m f f' ra,
        find_function_ptr ge ros rs = Some f' ->
        (exists fd, Genv.find_funct_ptr ge f' = Some fd) ->
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      return_address_offset f c ra ->
      step (State s fb (Vptr sp Ptrofs.zero) (Mcall sig ros :: c) rs m)
        E0 (Callstate (Stackframe fb sp (Vptr fb ra) c :: s)
                       f' rs (Mem.push_new_stage m))
  | exec_Mtailcall:
      forall s fb stk soff sig ros c rs m f f' m' m'',
        find_function_ptr ge ros rs = Some f' ->
        (exists fd, Genv.find_funct_ptr ge f' = Some fd) ->
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      (* load_stack m (Vptr stk soff) Tptr f.(fn_link_ofs) = Some (parent_sp s) -> *)
      load_stack m (Vptr stk soff) Tptr f.(fn_retaddr_ofs) = Some (parent_ra s) ->
      Mem.free m stk (Ptrofs.unsigned soff) (Ptrofs.unsigned soff + f.(fn_stacksize)) = Some m' ->
      Mem.tailcall_stage m' = Some m'' ->
      step (State s fb (Vptr stk soff) (Mtailcall sig ros :: c) rs m)
        E0 (Callstate s f' rs m'')
  | exec_Mbuiltin:
      forall s f sp rs m ef args res b vargs t vres rs' m' m'',
      eval_builtin_args ge rs sp m args vargs ->
      external_call ef ge vargs (Mem.push_new_stage m) t vres m' ->
      Mem.unrecord_stack_block m' = Some m'' ->                                          
      rs' = set_res res vres (undef_regs (destroyed_by_builtin ef) rs) ->
      forall BUILTIN_ENABLED : builtin_enabled ef,
      step (State s f sp (Mbuiltin ef args res :: b) rs m)
         t (State s f sp b rs' m'')
  | exec_Mgoto:
      forall s fb f sp lbl c rs m c',
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      find_label lbl f.(fn_code) = Some c' ->
      step (State s fb sp (Mgoto lbl :: c) rs m)
        E0 (State s fb sp c' rs m)
  | exec_Mcond_true:
      forall s fb f sp cond args lbl c rs m c' rs',
      eval_condition cond rs##args m = Some true ->
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      find_label lbl f.(fn_code) = Some c' ->
      rs' = undef_regs (destroyed_by_cond cond) rs ->
      step (State s fb sp (Mcond cond args lbl :: c) rs m)
        E0 (State s fb sp c' rs' m)
  | exec_Mcond_false:
      forall s f sp cond args lbl c rs m rs',
      eval_condition cond rs##args m = Some false ->
      rs' = undef_regs (destroyed_by_cond cond) rs ->
      step (State s f sp (Mcond cond args lbl :: c) rs m)
        E0 (State s f sp c rs' m)
  | exec_Mjumptable:
      forall s fb f sp arg tbl c rs m n lbl c' rs',
      rs arg = Vint n ->
      list_nth_z tbl (Int.unsigned n) = Some lbl ->
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      find_label lbl f.(fn_code) = Some c' ->
      rs' = undef_regs destroyed_by_jumptable rs ->
      step (State s fb sp (Mjumptable arg tbl :: c) rs m)
        E0 (State s fb sp c' rs' m)
  | exec_Mreturn:
      forall s fb stk soff c rs m f m' m'',
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      load_stack m (Vptr stk soff) Tptr f.(fn_retaddr_ofs) = Some (parent_ra s) ->
      Mem.free m stk (Ptrofs.unsigned soff) (Ptrofs.unsigned soff + f.(fn_stacksize)) = Some m' ->
      invalidate_frame m' = Some m'' ->
      step (State s fb (Vptr stk soff) (Mreturn :: c) rs m)
        E0 (Returnstate s rs m'')
  | exec_function_internal:
      forall s fb rs m f m1 m1_ m3 stk rs',
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      check_alloc_frame (fn_frame f) f  ->
      Mem.alloc m 0 f.(fn_stacksize) = (m1, stk) ->
      let sp := Vptr stk Ptrofs.zero in
      (* store_stack m1 sp Tptr f.(fn_link_ofs) (parent_sp s) = Some m2 -> *)
      store_stack m1 sp Tptr f.(fn_retaddr_ofs) (parent_ra s) = Some m3 ->
      Mem.record_stack_blocks m3 (make_singleton_frame_adt' stk (fn_frame f) (fn_stacksize f)) = Some m1_ ->
      rs' = undef_regs destroyed_at_function_entry rs ->
      step (Callstate s fb rs m)
        E0 (State s fb sp f.(fn_code) rs' m1_)
  | exec_function_external:
      forall s fb rs m t rs' ef args res m',
      Genv.find_funct_ptr ge fb = Some (External ef) ->
      extcall_arguments rs m (parent_sp (Mem.stack m)) (ef_sig ef) args ->
      external_call ef ge args m t res m' ->
      rs' = set_pair (loc_result (ef_sig ef)) res (undef_regs destroyed_at_call rs) ->
      step (Callstate s fb rs m)
         t (Returnstate s rs' m')
  | exec_return:
      forall s f sp ra c rs m m',
        Mem.unrecord_stack_block m = Some m' ->
      step (Returnstate (Stackframe f sp ra c :: s) rs m)
        E0 (State s f (Vptr sp Ptrofs.zero) c rs m').

Inductive callstack_function_defined : list stackframe -> Prop :=
| cfd_empty:
    callstack_function_defined nil
| cfd_cons:
    forall fb sp' ra c' cs' trf
      (FINDF: Genv.find_funct_ptr ge fb = Some (Internal trf))
      (CFD: callstack_function_defined cs')
      (RAU: return_address_offset trf c' ra)
      (TAIL: exists l sg ros, fn_code trf = l ++ (Mcall sg ros :: c')),
      callstack_function_defined (Stackframe fb sp' (Vptr fb ra) c' :: cs').

Variable init_sg: signature.
Variable init_stk: stack.

Inductive single_block_prop (P: block -> frame_info -> Prop) : list (block * frame_info) -> Prop :=
| sbp_intro:
    forall b fi
      (PROP: P b fi),
      single_block_prop P ((b,fi)::nil).

Inductive init_sp_stackinfo : stack -> Prop :=
| iss_intro
    fr tf s
    (PRIV: single_block_prop
             (fun b fi =>
                forall o, fe_ofs_arg <= o < 4 * size_arguments init_sg ->
                     frame_private fi o /\ Ptrofs.unsigned (Ptrofs.repr (fe_ofs_arg + o)) = fe_ofs_arg + o)
             (frame_adt_blocks fr)):
    init_sp_stackinfo ((Some fr,tf)::s).

Inductive list_prefix : list (option (block * frame_info)) -> stack -> Prop :=
| list_prefix_nil s (STKEQ: s = init_stk) (INIT: init_sp_stackinfo s): list_prefix nil s
| list_prefix_cons lsp s f r sp bi
                   (REC: list_prefix lsp s)
                   (FSIZE: frame_adt_size f = frame_size bi)
                   (BLOCKS: frame_adt_blocks f = (sp,bi)::nil):
    list_prefix (Some (sp,bi) :: lsp) ( (Some f , r) :: s).

Definition stack_blocks_of_callstack (l : list stackframe) : list (option (block * frame_info)) :=
  map (fun x =>
         match x with
           Stackframe fb sp _ _ =>
           match Genv.find_funct_ptr ge fb with
             Some (Internal f) =>
             Some (sp, fn_frame f)
           | _ => None
           end
         end) l.

Inductive has_code: state -> Prop :=
| has_code_intro fb f cs sp c rs m
                 (FIND: Genv.find_funct_ptr ge fb = Some (Internal f))
                 (CODE: exists l, fn_code f = l ++ c)
                 (CFD: callstack_function_defined cs):
    has_code (State cs fb sp c rs m)
| has_code_call:
    forall cs fb rs m
      (CFD: callstack_function_defined cs),
      has_code (Callstate cs fb rs m)
| has_code_ret:
    forall cs rs m
      (CFD: callstack_function_defined cs),
      has_code (Returnstate cs rs m).

Lemma find_label_ex:
  forall lbl c c', find_label lbl c = Some c' -> exists l, c = l ++ c'.
Proof.
  induction c; simpl; intros. discriminate.
  destruct (is_label lbl a). inv H.
  exists (a::nil); simpl. auto.
  apply IHc in H. destruct H as (l & CODE); rewrite CODE.
  exists (a::l); simpl. reflexivity.
Qed.


Lemma has_code_step:
  forall s1 t s2,
    step s1 t s2 ->
    has_code s1 ->
    has_code s2.
Proof.
  destruct 1; simpl; intros HC; inv HC; try now (econstructor; eauto).
  - destruct CODE as (l & CODE); econstructor; eauto; rewrite CODE;
    eexists (l ++ _ :: nil); simpl; rewrite app_ass; reflexivity.
  - destruct CODE as (l & CODE); econstructor; eauto; rewrite CODE;
      eexists (l ++ _ :: nil); simpl; rewrite app_ass; reflexivity.
  - destruct CODE as (l & CODE); econstructor; eauto; rewrite CODE;
      eexists (l ++ _ :: nil); simpl; rewrite app_ass; reflexivity.
  - destruct CODE as (l & CODE); econstructor; eauto; rewrite CODE;
      eexists (l ++ _ :: nil); simpl; rewrite app_ass; reflexivity.
  - destruct CODE as (l & CODE); econstructor; eauto; rewrite CODE;
      eexists (l ++ _ :: nil); simpl; rewrite app_ass; reflexivity.
  - destruct CODE as (l & CODE); econstructor; eauto; rewrite CODE;
      eexists (l ++ _ :: nil); simpl; rewrite app_ass; reflexivity.
  - destruct CODE as (l & CODE); econstructor; eauto; rewrite CODE;
      eexists (l ++ _ :: nil); simpl; rewrite app_ass; reflexivity.
  - destruct CODE as (l & CODE).
    repeat econstructor; eauto. congruence.
  - destruct CODE as (l & CODE); econstructor; eauto; rewrite CODE;
      eexists (l ++ _ :: nil); simpl; rewrite app_ass; reflexivity.
  - destruct CODE as (l & CODE).
    rewrite H in FIND; inv FIND.
    econstructor; eauto. eapply find_label_ex. eauto. 
  - destruct CODE as (l & CODE).
    rewrite H0 in FIND; inv FIND.
    econstructor; eauto. eapply find_label_ex. eauto.
  - destruct CODE as (l & CODE); econstructor; eauto; rewrite CODE;
      eexists (l ++ _ :: nil); simpl; rewrite app_ass; reflexivity.
  - destruct CODE as (l & CODE).
    rewrite H1 in FIND; inv FIND.
    econstructor; eauto. eapply find_label_ex. eauto.
  - econstructor; eauto. exists nil; simpl; auto.
  - inv CFD. econstructor; eauto.
    destruct TAIL as (l & sg & ros & EQ); rewrite EQ.
    eexists (l ++ _ :: nil); simpl; rewrite app_ass; reflexivity.
Qed.

Inductive call_stack_consistency: state -> Prop :=
| call_stack_consistency_intro:
    forall c cs' fb sp' rs m' tf
      (FIND: Genv.find_funct_ptr ge fb = Some (Internal tf))
      (CallStackConsistency: list_prefix ((Some (sp', fn_frame tf))::stack_blocks_of_callstack cs') (Mem.stack m'))
    ,
      call_stack_consistency (State cs' fb (Vptr sp' Ptrofs.zero) c rs m')
| call_stack_consistency_call:
    forall cs' fb rs m'
      (CallStackConsistency: list_prefix (stack_blocks_of_callstack cs') (tl (Mem.stack m')))
      (TTNP: top_tframe_tc (Mem.stack m')),
      call_stack_consistency (Callstate cs' fb rs m')
| call_stack_consistency_return:
    forall cs' rs m'
      (CallStackConsistency: list_prefix (stack_blocks_of_callstack cs') (tl (Mem.stack m')))
      (TTNP: Mem.top_frame_no_perm m'),
      call_stack_consistency (Returnstate cs' rs m').

Lemma store_stack_no_abstract:
  forall sp ty o v,
    Mem.stack_unchanged (fun m m' => store_stack m sp ty o v = Some m').
Proof.
  unfold store_stack, Mem.storev.
  red; simpl; intros.
  destruct (Val.offset_ptr sp o); try discriminate.
  eapply Mem.store_no_abstract; eauto.
Qed.

Hypothesis invalidate_frame_tl_stack:
  forall m1 m2,
    invalidate_frame m1 = Some m2 ->
    tl (Mem.stack m2) = tl (Mem.stack m1).

Hypothesis invalidate_frame_top_no_perm:
  forall m1 m2,
    invalidate_frame m1 = Some m2 ->
    Mem.top_frame_no_perm m1 ->
    Mem.top_frame_no_perm m2.


Ltac same_hyps :=
  repeat match goal with
           H1: ?a = _, H2: ?a = _ |- _ => rewrite H1 in H2; inv H2
         end.

Lemma csc_step:
  forall s1 t s2,
    step s1 t s2 ->
    (forall fb f, Genv.find_funct_ptr ge fb = Some (Internal f) ->
             frame_size (fn_frame f) = fn_stacksize f) ->
    has_code s1 ->
    call_stack_consistency s1 ->
    call_stack_consistency s2.
Proof.
  destruct 1; simpl; intros SIZECORRECT HC CSC; inv HC; inv CSC;
    same_hyps;
    try now (econstructor; eauto).
  - econstructor; eauto. erewrite store_stack_no_abstract; eauto.
  - econstructor; eauto. destruct a; simpl in *; try discriminate. erewrite Mem.store_no_abstract; eauto.
  - econstructor. rewrite_stack_blocks. simpl. 
    rewrite H1. auto.
    red. rewrite_stack_blocks. constructor. reflexivity.
  - econstructor. repeat rewrite_stack_blocks. simpl. intro EQ; rewrite EQ in CallStackConsistency.
    inv CallStackConsistency; simpl; auto.
    red. rewrite_stack_blocks. intros; constructor. easy.
  - econstructor; eauto. repeat rewrite_stack_blocks; simpl; eauto.
  - econstructor; eauto.
    erewrite invalidate_frame_tl_stack; eauto. repeat rewrite_stack_blocks; simpl; eauto.
    inv CallStackConsistency. eauto.
    eapply invalidate_frame_top_no_perm; eauto.
    inv CallStackConsistency.
    eapply Mem.free_top_tframe_no_perm; eauto.
    erewrite <- SIZECORRECT; eauto. rewrite Ptrofs.unsigned_zero.
    simpl. rewrite Z.max_r. auto. apply frame_size_pos.
  - econstructor; eauto; repeat rewrite_stack_blocks; simpl; eauto.
    repeat econstructor; eauto.
    rewrite store_stack_no_abstract in EQ1 by eauto.
    revert EQ1; rewrite_stack_blocks. intro. rewrite EQ1 in CallStackConsistency. simpl in *.
    auto.
    simpl.
    erewrite <- SIZECORRECT. apply Z.max_r. apply frame_size_pos. eauto.
  - econstructor; eauto; repeat rewrite_stack_blocks; simpl; eauto.
    red; rewrite_stack_blocks.
    inv TTNP.
    constructor. unfold in_frames; rewrite H3; easy.
  - inv CFD. econstructor; eauto; repeat rewrite_stack_blocks; simpl; eauto.
    simpl in *; eauto. rewrite FINDF in CallStackConsistency. eauto.
Qed.

Definition mem_state (s: state) : mem :=
  match s with
    State _ _ _ _ _ m
  | Callstate _ _ _ m
  | Returnstate _ _ m => m
  end.

Lemma list_prefix_in_init_stk:
  forall cs s,
    list_prefix cs s ->
    forall b,
      in_stack init_stk b ->
      in_stack s b.
Proof.
  induction 1; intros. subst; auto.
  rewrite in_stack_cons; right; eauto.
Qed.

Lemma list_prefix_stack_top_not_init_stk':
  forall b b' f fr cs s,
    nodup (fr::s) ->
    list_prefix (Some (b',f)::cs) (fr::s) ->
    in_frames fr b ->
    get_frame_info init_stk b = None.
Proof.
  intros.
  destruct (get_frame_info init_stk b) eqn:GFI; auto.
  apply get_frame_info_in_stack in GFI. exfalso.
  inv H0.
  inv H.
  eapply H4. eauto.
  eapply list_prefix_in_init_stk. eauto. auto.
Qed.

Lemma list_prefix_stack_top_not_init_stk:
  forall b b' f cs s,
    nodup s ->
    list_prefix (Some (b',f)::cs) s ->
    is_stack_top s b ->
    get_frame_info init_stk b = None.
Proof.
  intros.
  inv H0. red in H1. simpl in H1.
  eapply list_prefix_stack_top_not_init_stk'. eauto. constructor; eauto. auto.
Qed.

Lemma list_prefix_not_in_init_stk:
  forall b f cs s,
    nodup s ->
    list_prefix (Some (b, f)::cs) s ->
    get_frame_info init_stk b = None.
Proof.
  intros.
  destruct (get_frame_info init_stk b) eqn:GFI; auto.
  apply get_frame_info_in_stack in GFI. exfalso.
  inv H0.
  inv H.
  eapply H3. rewrite in_frames_cons. eexists; split. reflexivity. 
  eapply in_frame'_in_frame. red. rewrite BLOCKS. left; reflexivity.
  eapply list_prefix_in_init_stk. eauto. auto.
Qed.

Lemma public_stack_access_init_stk:
  forall cs s b lo hi
         (LP: list_prefix cs s)
         (ND: nodup s)
         (PSA: public_stack_access s b lo hi),
    public_stack_access init_stk b lo hi.
Proof.
  induction 1; simpl; subst; auto.
  intros.
  apply IHLP. inv ND; auto.
  red. red in PSA. destr.
  edestruct (get_assoc_spec _ _ _ Heqo) as (fr & tf & INblocks & INtf & INs).
  erewrite get_assoc_stack_lnr in PSA. eauto. eauto. eauto. eauto. eauto. right; auto.
Qed.

Lemma public_stack_access_init_stk':
  forall cs s b lo hi
         (LP: list_prefix cs s)
         f
         (ND: nodup (f::s))
         (PSA: public_stack_access (f::s) b lo hi),
    public_stack_access init_stk b lo hi.
Proof.
  induction 1; simpl; subst; auto.
  - unfold public_stack_access. simpl.
    intros. destr.
    destr_in PSA. destr_in Heqo0.
    inv ND.
    exfalso; eapply H2; eauto. eapply get_frame_info_in_stack; eauto.
    inv Heqo0; auto.
    repeat destr_in Heqo0.
    inv ND.
    exfalso; eapply H3; eauto. eapply get_frame_info_in_stack; eauto.
  - intros.
    eapply IHLP. inv ND; eauto.
    red. red in PSA. destr.
    edestruct (get_assoc_spec _ _ _ Heqo) as (fr & tf & INblocks & INtf & INs).
    erewrite get_assoc_stack_lnr in PSA. eauto. eauto. eauto.
    eauto. eauto. right; auto.
Qed.


Hypothesis invalidate_frame_unchanged_on:
  forall m1 m2 P,
    invalidate_frame m1 = Some m2 ->
    Mem.unchanged_on P m1 m2.

Lemma csc_unchanged_stack:
  forall s t s',
    step s t s' ->
    call_stack_consistency s ->
    Mem.unchanged_on
      (fun b o => ~ stack_access init_stk b o (o+1))
      (mem_state s) (mem_state s').
Proof.
  intros s t s' STEP CSC. inv STEP; inv CSC; simpl; try apply Mem.unchanged_on_refl.
  - unfold store_stack in H. simpl in H.
    eapply Mem.store_unchanged_on; eauto.
    intros i RNG PSA; apply PSA; clear PSA. red.
    right. red. erewrite list_prefix_not_in_init_stk; eauto. apply Mem.stack_norepet.
  - unfold Mem.storev in H0. destr_in H0.
    eapply Mem.store_unchanged_on; eauto.
    intros i0 RNG PSA; apply PSA; clear PSA.
    edestruct Mem.store_valid_access_3 as (A & B & C). eauto. trim C. constructor.
    destruct C as [IST|NPSA].
    right. red; erewrite list_prefix_stack_top_not_init_stk; eauto. apply Mem.stack_norepet.
    right. eapply public_stack_access_inside.
    eapply public_stack_access_init_stk; eauto. apply Mem.stack_norepet.
    omega. omega.
  - apply Mem.strong_unchanged_on_weak. apply Mem.push_new_stage_unchanged_on.
  - eapply Mem.unchanged_on_trans. eapply Mem.free_unchanged_on; eauto.
    intros i RNG PSA; apply PSA; clear PSA. right; red.
    erewrite list_prefix_not_in_init_stk; eauto. apply Mem.stack_norepet.
    eapply Mem.strong_unchanged_on_weak, Mem.tailcall_stage_unchanged_on; eauto.
  - exploit ec_unchanged_on_private_stack. apply external_call_spec. eauto.
    intros.
    eapply Mem.unchanged_on_trans.
    apply Mem.strong_unchanged_on_weak. eapply Mem.push_new_stage_unchanged_on.
    eapply Mem.unchanged_on_trans.
    eapply Mem.unchanged_on_implies. apply H2.
    simpl.
    intros b0 ofs NPSA VB PSA.
    apply NPSA.
    assert (PSA': stack_access (Mem.stack m) b0 ofs (ofs + 1)).
    {
      red in PSA. revert PSA. red. rewrite_stack_blocks. unfold is_stack_top. simpl.  unfold public_stack_access. simpl. auto.
      intros [[]|P]. right. auto.
    } clear PSA.
    destruct PSA'.
    right; red. erewrite list_prefix_stack_top_not_init_stk; eauto. apply Mem.stack_norepet.
    right.
    eapply public_stack_access_init_stk. 4: eauto. eauto. apply Mem.stack_norepet.
    auto.
    apply Mem.strong_unchanged_on_weak. eapply Mem.unrecord_stack_block_unchanged_on. eauto.
  - eapply Mem.unchanged_on_trans. eapply Mem.free_unchanged_on; eauto.
    intros i RNG PSA; apply PSA; clear PSA. right; red.
    erewrite list_prefix_not_in_init_stk; eauto. apply Mem.stack_norepet.
    eapply invalidate_frame_unchanged_on; eauto.
  - eapply Mem.unchanged_on_trans.
    eapply Mem.alloc_unchanged_on; eauto.
    unfold store_stack in H2. subst. simpl in H2.
    eapply Mem.unchanged_on_trans.
    eapply Mem.store_unchanged_on. eauto.
    intros i0 RNG PSA; apply PSA; clear PSA.
    right; red. destr.
    apply get_frame_info_in_stack in Heqo. exfalso.
    eapply list_prefix_in_init_stk in Heqo; eauto.
    apply in_stack_tl in Heqo. apply Mem.in_frames_valid in Heqo.
    eapply Mem.fresh_block_alloc; eauto.
    apply Mem.strong_unchanged_on_weak. eapply Mem.record_stack_block_unchanged_on. eauto.
  - exploit ec_unchanged_on_private_stack. apply external_call_spec. eauto.
    intros.
    eapply Mem.unchanged_on_implies. apply H2.
    simpl.
    intros b0 ofs NPSA VB PSA.
    apply NPSA. inv TTNP. rewrite <- H3 in CallStackConsistency. simpl in CallStackConsistency.
    destruct PSA.
    right; red.
    destr. eapply get_frame_info_in_stack in Heqo.
    eapply list_prefix_in_init_stk in Heqo; eauto.
    exploit Mem.stack_norepet. rewrite <- H3. intro ND. inv ND. edestruct H9; eauto.
    rewrite <- H3 in H5. red in H5. eauto.
    right.
    rewrite <- H3 in *.
    eapply public_stack_access_init_stk' . 3: eauto. eauto.
    rewrite H3; apply Mem.stack_norepet.
  - apply Mem.strong_unchanged_on_weak. eapply Mem.unrecord_stack_block_unchanged_on. eauto.
Qed.

Definition block_prop P v :=
  match v with
    Vptr b o => P b
  | _ => True
  end.

Lemma store_stack_nextblock:
  forall m v ty p v1 m',
    store_stack m v ty p v1 = Some m' ->
    Mem.nextblock m' = Mem.nextblock m.
Proof.
  unfold store_stack; intros.
  destruct (Val.offset_ptr v p); simpl in *; inv H;  eauto with mem.
Qed.

End RELSEM.

Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall fb m0 m2,
      let ge := Genv.globalenv p in
      Genv.init_mem p = Some m0 ->
      Genv.find_symbol ge p.(prog_main) = Some fb ->
      Mem.record_init_sp m0 = Some m2 ->
      initial_state p (Callstate nil fb (Regmap.init Vundef) (Mem.push_new_stage m2)).

Inductive final_state: state -> int -> Prop :=
  | final_state_intro: forall rs m r retcode,
      loc_result signature_main = One r ->
      rs r = Vint retcode ->
      final_state (Returnstate nil rs m) retcode.

Definition invalidate_frame1 (m: mem) := Some m.

Lemma invalidate_frame1_tl_stack:
  forall m1 m2,
    invalidate_frame1 m1 = Some m2 ->
    tl (Mem.stack m2) = tl (Mem.stack m1).
Proof.
  unfold invalidate_frame1; intros m1 m2 EQ; inv EQ; auto.
Qed.

Lemma invalidate_frame1_top_no_perm:
  forall m1 m2,
    invalidate_frame1 m1 = Some m2 ->
    Mem.top_frame_no_perm m1 ->
    Mem.top_frame_no_perm m2.
Proof.
  unfold invalidate_frame1; intros m1 m2 EQ; inv EQ; auto.
Qed.

Lemma invalidate_frame1_unchanged_on:
  forall m1 m2 P,
    invalidate_frame1 m1 = Some m2 ->
    Mem.unchanged_on P m1 m2.
Proof.
  unfold invalidate_frame1; intros m1 m2 P EQ; inv EQ; eapply Mem.unchanged_on_refl.
Qed.

Definition invalidate_frame2 (m: mem) := Mem.tailcall_stage m.

Lemma invalidate_frame2_tl_stack:
  forall m1 m2,
    invalidate_frame2 m1 = Some m2 ->
    tl (Mem.stack m2) = tl (Mem.stack m1).
Proof.
  unfold invalidate_frame2; intros; rewrite_stack_blocks. intro EQ; rewrite EQ; simpl; auto.
Qed.

Lemma invalidate_frame2_top_no_perm:
  forall m1 m2,
    invalidate_frame2 m1 = Some m2 ->
    Mem.top_frame_no_perm m1 ->
    Mem.top_frame_no_perm m2.
Proof.
  unfold invalidate_frame2; intros m1 m2 EQ TTNP.
  red. apply Mem.tailcall_stage_tc in EQ. inv EQ.
  constructor; unfold in_frames; simpl. rewrite H0; easy.
Qed.

Lemma invalidate_frame2_unchanged_on:
  forall m1 m2 P,
    invalidate_frame2 m1 = Some m2 ->
    Mem.unchanged_on P m1 m2.
Proof.
  unfold invalidate_frame2; intros m1 m2 P EQ.
  eapply Mem.strong_unchanged_on_weak, Mem.tailcall_stage_unchanged_on; eauto.
Qed.

Definition semantics1 (rao: function -> code -> ptrofs -> Prop) (p: program) :=
  Semantics (step Vnullptr rao invalidate_frame1) (initial_state p) final_state (Genv.globalenv p).

Definition semantics2 (rao: function -> code -> ptrofs -> Prop) (p: program) :=
  Semantics (step Vnullptr rao invalidate_frame2) (initial_state p) final_state (Genv.globalenv p).

End WITHEXTERNALCALLSOPS.
