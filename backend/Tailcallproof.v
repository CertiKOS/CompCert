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

(** Recognition of tail calls: correctness proof *)

Require Import Coqlib Maps Integers AST Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Op Registers RTL Conventions Tailcall.
(*SACC:*)
Require Import StackInj.

(** * Syntactic properties of the code transformation *)

(** ** Measuring the number of instructions eliminated *)

(** The [return_measure c pc] function counts the number of instructions
  eliminated by the code transformation, where [pc] is the successor
  of a call turned into a tailcall.  This is the length of the
  move/nop/return sequence recognized by the [is_return] boolean function.
*)

Fixpoint return_measure_rec (n: nat) (c: code) (pc: node)
                            {struct n}: nat :=
  match n with
  | O => O
  | S n' =>
      match c!pc with
      | Some(Inop s) => S(return_measure_rec n' c s)
      | Some(Iop op args dst s) => S(return_measure_rec n' c s)
      | _ => O
      end
  end.

Definition return_measure (c: code) (pc: node) :=
  return_measure_rec niter c pc.

Lemma return_measure_bounds:
  forall f pc, (return_measure f pc <= niter)%nat.
Proof.
  intro f.
  assert (forall n pc, (return_measure_rec n f pc <= n)%nat).
    induction n; intros; simpl.
    omega.
    destruct (f!pc); try omega.
    destruct i; try omega.
    generalize (IHn n0). omega.
    generalize (IHn n0). omega.
  intros. unfold return_measure. apply H.
Qed.

Remark return_measure_rec_incr:
  forall f n1 n2 pc,
  (n1 <= n2)%nat ->
  (return_measure_rec n1 f pc <= return_measure_rec n2 f pc)%nat.
Proof.
  induction n1; intros; simpl.
  omega.
  destruct n2. omegaContradiction. assert (n1 <= n2)%nat by omega.
  simpl. destruct f!pc; try omega. destruct i; try omega.
  generalize (IHn1 n2 n H0). omega.
  generalize (IHn1 n2 n H0). omega.
Qed.

Lemma is_return_measure_rec:
  forall f n n' pc r,
  is_return n f pc r = true -> (n <= n')%nat ->
  return_measure_rec n f.(fn_code) pc = return_measure_rec n' f.(fn_code) pc.
Proof.
  induction n; simpl; intros.
  congruence.
  destruct n'. omegaContradiction. simpl.
  destruct (fn_code f)!pc; try congruence.
  destruct i; try congruence.
  decEq. apply IHn with r. auto. omega.
  destruct (is_move_operation o l); try congruence.
  destruct (Reg.eq r r1); try congruence.
  decEq. apply IHn with r0. auto. omega.
Qed.

(** ** Relational characterization of the code transformation *)

(** The [is_return_spec] characterizes the instruction sequences
  recognized by the [is_return] boolean function.  *)

Inductive is_return_spec (f:function): node -> reg -> Prop :=
  | is_return_none: forall pc r,
      f.(fn_code)!pc = Some(Ireturn None) ->
      is_return_spec f pc r
  | is_return_some: forall pc r,
      f.(fn_code)!pc = Some(Ireturn (Some r)) ->
      is_return_spec f pc r
  | is_return_nop: forall pc r s,
      f.(fn_code)!pc = Some(Inop s) ->
      is_return_spec f s r ->
      (return_measure f.(fn_code) s < return_measure f.(fn_code) pc)%nat ->
      is_return_spec f pc r
  | is_return_move: forall pc r r' s,
      f.(fn_code)!pc = Some(Iop Omove (r::nil) r' s) ->
      is_return_spec f s r' ->
      (return_measure f.(fn_code) s < return_measure f.(fn_code) pc)%nat ->
     is_return_spec f pc r.

Lemma is_return_charact:
  forall f n pc rret,
  is_return n f pc rret = true -> (n <= niter)%nat ->
  is_return_spec f pc rret.
Proof.
  induction n; intros.
  simpl in H. congruence.
  generalize H. simpl.
  caseEq ((fn_code f)!pc); try congruence.
  intro i. caseEq i; try congruence.
  intros s; intros. eapply is_return_nop; eauto. eapply IHn; eauto. omega.
  unfold return_measure.
  rewrite <- (is_return_measure_rec f (S n) niter pc rret); auto.
  rewrite <- (is_return_measure_rec f n niter s rret); auto.
  simpl. rewrite H2. omega. omega.

  intros op args dst s EQ1 EQ2.
  caseEq (is_move_operation op args); try congruence.
  intros src IMO. destruct (Reg.eq rret src); try congruence.
  subst rret. intro.
  exploit is_move_operation_correct; eauto. intros [A B]. subst.
  eapply is_return_move; eauto. eapply IHn; eauto. omega.
  unfold return_measure.
  rewrite <- (is_return_measure_rec f (S n) niter pc src); auto.
  rewrite <- (is_return_measure_rec f n niter s dst); auto.
  simpl. rewrite EQ2. omega. omega.

  intros or EQ1 EQ2. destruct or; intros.
  assert (r = rret). eapply proj_sumbool_true; eauto. subst r.
  apply is_return_some; auto.
  apply is_return_none; auto.
Qed.

(** The [transf_instr_spec] predicate relates one instruction in the
  initial code with its possible transformations in the optimized code. *)

Inductive transf_instr_spec (f: function): instruction -> instruction -> Prop :=
  | transf_instr_tailcall: forall sig ros args res s,
      f.(fn_stacksize) = 0 ->
      is_return_spec f s res ->
      transf_instr_spec f (Icall sig ros args res s) (Itailcall sig ros args)
  | transf_instr_default: forall i,
      transf_instr_spec f i i.

Lemma transf_instr_charact:
  forall f pc instr,
  f.(fn_stacksize) = 0 ->
  transf_instr_spec f instr (transf_instr f pc instr).
Proof.
  intros. unfold transf_instr. destruct instr; try constructor.
  caseEq (is_return niter f n r && tailcall_is_possible s &&
          opt_typ_eq (sig_res s) (sig_res (fn_sig f))); intros.
  destruct (andb_prop _ _ H0). destruct (andb_prop _ _ H1).
  eapply transf_instr_tailcall; eauto.
  eapply is_return_charact; eauto.
  constructor.
Qed.

Lemma transf_instr_lookup:
  forall f pc i,
  f.(fn_code)!pc = Some i ->
  exists i',  (transf_function f).(fn_code)!pc = Some i' /\ transf_instr_spec f i i'.
Proof.
  intros. unfold transf_function.
  destruct (zeq (fn_stacksize f) 0).
  simpl. rewrite PTree.gmap. rewrite H. simpl.
  exists (transf_instr f pc i); split. auto. apply transf_instr_charact; auto.
  exists i; split. auto. constructor.
Qed.

(** * Semantic properties of the code transformation *)

(** ** The ``less defined than'' relation between register states *)

(** A call followed by a return without an argument can be turned
  into a tail call.  In this case, the original function returns
  [Vundef], while the transformed function can return any value.
  We account for this situation by using the ``less defined than''
  relation between values and between memory states.  We need to
  extend it pointwise to register states. *)

Lemma regs_lessdef_init_regs:
  forall params vl vl',
  Val.lessdef_list vl vl' ->
  regs_lessdef (init_regs vl params) (init_regs vl' params).
Proof.
  induction params; intros.
  simpl. red; intros. rewrite Regmap.gi. constructor.
  simpl. inv H.   red; intros. rewrite Regmap.gi. constructor.
  apply set_reg_lessdef. auto. auto.
Qed.

(** * Proof of semantic preservation *)

Definition match_prog (p tp: RTL.program) :=
  match_program (fun cu f tf => tf = transf_fundef f) eq p tp.

Lemma transf_program_match:
  forall p, match_prog p (transf_program p).
Proof.
  intros. apply match_transform_program; auto.
Qed.

(*SACC:*)
Definition regs_inject (j: meminj) (rs1 rs2: Regmap.t val) :=
  forall r,
    Val.inject j (rs1 # r) (rs2 # r).

(*SACC:*)
Definition inject_globals  {F V} (g: Genv.t F V) j:=
  (forall b,
      Plt b (Genv.genv_next g) -> j b = Some (b,0)) /\
  (forall b1 b2 delta,
      j b1 = Some (b2, delta) -> Plt b2 (Genv.genv_next g) -> b2 = b1 /\ delta = 0).

Section PRESERVATION.

Variable prog tprog: program.
Hypothesis TRANSL: match_prog prog tprog.

Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof (Genv.find_symbol_transf TRANSL).

Lemma functions_translated:
  forall (v: val) (f: RTL.fundef),
  Genv.find_funct ge v = Some f ->
  Genv.find_funct tge v = Some (transf_fundef f).
Proof (Genv.find_funct_transf TRANSL).

Lemma funct_ptr_translated:
  forall (b: block) (f: RTL.fundef),
  Genv.find_funct_ptr ge b = Some f ->
  Genv.find_funct_ptr tge b = Some (transf_fundef f).
Proof (Genv.find_funct_ptr_transf TRANSL).

Lemma senv_preserved:
  Senv.equiv ge tge.
Proof (Genv.senv_transf TRANSL).

Lemma sig_preserved:
  forall f, funsig (transf_fundef f) = funsig f.
Proof.
  destruct f; auto. simpl. unfold transf_function.
  destruct (zeq (fn_stacksize f) 0); auto.
Qed.

Lemma stacksize_preserved:
  forall f, fn_stacksize (transf_function f) = fn_stacksize f.
Proof.
  unfold transf_function. intros.
  destruct (zeq (fn_stacksize f) 0); auto.
Qed.

Lemma find_function_translated:
  forall ros rs rs' f (*SACC:*)j,
  find_function ge ros rs = Some f ->
  (*SACC:commented this*)(*regs_lessdef rs rs' ->*)
  (*SACC:*)regs_inject j rs rs' ->
  (*SACC:*)inject_globals ge j ->
  find_function tge ros rs' = Some (transf_fundef f).
Proof.
  intros ros rs rs' f j FF RI IG; destruct ros; simpl in *.
  assert (rs'#r = rs#r).
  {
    exploit Genv.find_funct_inv; eauto. intros [b EQ].
    generalize (RI r). rewrite EQ. intro LD. inv LD.
    rewrite EQ in FF.
    unfold Genv.find_funct in FF; repeat destr_in FF.
    unfold Genv.find_funct_ptr in H0. repeat destr_in H0.
    eapply Genv.genv_defs_range in Heqo.
    destruct IG as (IG1 & IG2).
    erewrite IG1 in H2; eauto. inv H2. reflexivity.
  } 
  rewrite H. apply functions_translated; auto.
  rewrite symbols_preserved. destruct (Genv.find_symbol ge i); intros.
  apply funct_ptr_translated; auto.
  discriminate.
Qed.

(** Consider an execution of a call/move/nop/return sequence in the
  original code and the corresponding tailcall in the transformed code.
  The transition sequences are of the following form
  (left: original code, right: transformed code).
  [f] is the calling function and [fd] the called function.
<<
     State stk f (Icall instruction)       State stk' f' (Itailcall)

     Callstate (frame::stk) fd args        Callstate stk' fd' args'
            .                                       .
            .                                       .
            .                                       .
     Returnstate (frame::stk) res          Returnstate stk' res'

     State stk f (move/nop/return seq)
            .
            .
            .
     State stk f (return instr)

     Returnstate stk res
>>
The simulation invariant must therefore account for two kinds of
mismatches between the transition sequences:
- The call stack of the original program can contain more frames
  than that of the transformed program (e.g. [frame] in the example above).
- The regular states corresponding to executing the move/nop/return
  sequence must all correspond to the single [Returnstate stk' res']
  state of the transformed program.

We first define the simulation invariant between call stacks.
The first two cases are standard, but the third case corresponds
to a frame that was eliminated by the transformation. *)

Inductive match_stackframes: (*SACC:*)meminj -> (*SACC:*)nat -> (*SACC:*)list nat -> list stackframe -> list stackframe -> Prop :=
  | match_stackframes_nil (*SACC:*)j:
      match_stackframes (*SACC:*)j (*SACC:*)0 (*SACC:*)nil nil nil
  | match_stackframes_normal: forall (*SACC:*)j (*SACC:*)n (*SACC:*)l stk stk' res sp (*SACC:*)sp' pc rs rs' f,
      match_stackframes (*SACC:*)j (*SACC:*)n (*SACC:*)l stk stk' ->
  (*SACC:comments this*)(*regs_lessdef rs rs' ->*)
  (*SACC:*)regs_inject j rs rs' ->
  (*SACC:*)j sp = Some (sp',0) ->
      match_stackframes (*SACC:*)j (*SACC:*)0 (*SACC:*)(S n :: l)
        (Stackframe res f (Vptr sp Ptrofs.zero) pc rs :: stk)
        (Stackframe res (transf_function f) (Vptr (*SACC:*)sp' Ptrofs.zero) pc rs' :: stk')
  | match_stackframes_tail: forall (*SACC:*)j (*SACC:*)n (*SACC:*)l stk stk' res sp pc rs f,
      match_stackframes (*SACC:*)j (*SACC:*)n (*SACC:*)l stk stk' ->
      is_return_spec f pc res ->
      f.(fn_stacksize) = 0 ->
      match_stackframes (*SACC:*)j (*SACC:*)(S n) l
        (Stackframe res f (Vptr sp Ptrofs.zero) pc rs :: stk)
        stk'.

(*SACC:*)
Lemma sizes_upstar':
  forall n g s1 s2 f l,
    sizes (n :: g) s1 (f::s2) ->
    sizes (S n :: g) ((None,l) :: s1) ((None,opt_cons (fst f) (snd f))::s2).
Proof.
  intros n g s1 s2 f l SZ.
  inv SZ. simpl in *. repeat destr_in H5.
  econstructor; simpl; auto. rewrite Heqo. eauto. right; auto.
  rewrite size_frames_tc. auto.
Qed.

(*SACC:*)
Lemma sizes_up:
  forall g s1 s2,
    sizes g s1 s2 ->
    sizes (1%nat :: g) ((None,nil) :: s1) ((None,nil) :: s2).
Proof.
  intros g s1 s2 SZ. econstructor; simpl; eauto.
  left. omega.
Qed.

(*SACC:*)
Lemma sizes_record:
  forall g tf1 r1 tf2 r2 fr1 fr2 
    (SZ: sizes g (tf1 :: r1) (tf2 :: r2))
    (EQ: frame_adt_size fr1 = frame_adt_size fr2),
    sizes g ((Some fr1, opt_cons (fst tf1) (snd tf1)) :: r1) ((Some fr2 , opt_cons (fst tf2) (snd tf2)) :: r2).
Proof.
  intros. inv SZ.
  simpl in *. repeat destr_in H4.
  econstructor; simpl; auto. rewrite Heqo. eauto.
  inv H5.
  left.
  rewrite ! size_frames_cons. simpl. unfold size_frame. rewrite EQ. apply Z.max_le_compat_l; auto.
  fold size_frame. unfold size_frames in H0.
  rewrite ! map_opt_cons.
  rewrite <- ! max_opt_size_frame_tailcall. auto.
  rewrite Exists_exists in H0. destruct H0 as (f1 & INf1 & LE).
  rewrite Exists_exists.
  rewrite size_frames_cons.
  rewrite Zmax_spec. destr.
  eexists; split. left. reflexivity.
  rewrite size_frames_cons. simpl.
  unfold size_frame. rewrite EQ. apply Z.le_max_l.
  exists f1; split; simpl; eauto.
  unfold size_frames in LE.
  rewrite map_opt_cons, <- max_opt_size_frame_tailcall. auto.
Qed.

(*SACC:*)
Definition tc_sizes: frameinj -> stack -> stack -> Prop := sizes.

(*SACC:*)
Definition tc_sizes_up:
  forall g s1 s2,
    tc_sizes g s1 s2 ->
    tc_sizes (1%nat :: g) ((None,nil) :: s1) ((None,nil) :: s2) := sizes_up.

(*SACC:*)
Definition tc_sizes_ndown:
  forall n g s1 s2,
    tc_sizes (S n :: g) s1 s2 ->
    tc_sizes g (drop (S n) s1) (tl s2) := compat_sizes_drop.

(*SACC:*)
Definition tc_sizes_size_stack:
  forall g s1 s2,
    tc_sizes g s1 s2 ->
    size_stack s2 <= size_stack s1 := sizes_size_stack.

(*SACC:*)
Definition tc_sizes_record:
  forall g tf1 r1 tf2 r2 fr1 fr2 
    (SZ: tc_sizes g (tf1 :: r1) (tf2 :: r2))
    (EQ: frame_adt_size fr1 = frame_adt_size fr2),
    tc_sizes g ((Some fr1, opt_cons (fst tf1) (snd tf1)) :: r1)
             ((Some fr2, opt_cons (fst tf2) (snd tf2)) :: r2) := sizes_record.

(*SACC:*)
Section STACK_WRAPPER.

(*SACC:*)
Variable fn_stack_requirements: ident -> Z.

(** Here is the invariant relating two states.  The first three
  cases are standard.  Note the ``less defined than'' conditions
  over values and register states, and the corresponding ``extends''
  relation over memory states. *)

Inductive match_states: state -> state -> Prop :=
  | match_states_normal:
      forall s sp (*SACC:*)sp' pc rs m s' rs' m' f (*SACC:*)g (*SACC:*)j (*SACC:*)n (*SACC:*)l
             (STACKS: match_stackframes (*SACC:*)j (*SACC:*)n (*SACC:*)g s s')
    (*SACC:comments this*)(*(RLD: regs_lessdef rs rs')*)
    (*SACC:comments this*)(*(MLD: Mem.extends m m'),*)
    (*SACC:*)(RLD: regs_inject j rs rs')
    (*SACC:*)(MLD: Mem.inject j (S n :: g ++ l) m m')
    (*SACC:*)(SZ: tc_sizes (S n :: g ++ l) (Mem.stack m) (Mem.stack m'))
    (*SACC:*)(IG: inject_globals ge j)
    (*SACC:*)(JB: j sp = Some (sp', 0))
    (*SACC:*)(*(INCR: inject_incr (Mem.flat_inj (Mem.nextblock init_m)) j)*)
    (*SACC:*)(*(SEP: inject_separated (Mem.flat_inj (Mem.nextblock init_m)) j init_m init_m)*),
      match_states (State s f (Vptr sp Ptrofs.zero) pc rs m)
                   (State s' (transf_function f) (Vptr (*SACC:*)sp' Ptrofs.zero) pc rs' m')
  | match_states_call:
      forall s f args m s' args' m' (*SACC:*)sz (*SACC:*)g (*SACC:*)j (*SACC:*)n (*SACC:*)l
      (MS: match_stackframes (*SACC:*)j (*SACC:*)n (*SACC:*)g s s')
      (*SACC:comments this*)(*Val.lessdef_list args args' ->*)
      (*SACC:comments this*)(*Mem.extends m m' ->*)
  (*SACC:*)(LDargs: Val.inject_list j args args')
  (*SACC:*)(MLD: Mem.inject j (S n :: g ++ l) m m')
  (*SACC:*)(SZ: tc_sizes (S n :: g ++ l) (Mem.stack m) (Mem.stack m'))
  (*SACC:*)(IG: inject_globals ge j)
  (*SACC:*)(*(INCR: inject_incr (Mem.flat_inj (Mem.nextblock init_m)) j)*)
  (*SACC:*)(*(SEP: inject_separated (Mem.flat_inj (Mem.nextblock init_m)) j init_m init_m)*),
      match_states (Callstate s f args m (*SACC:*)sz)
                   (Callstate s' (transf_fundef f) args' m' (*SACC:*)sz)
  | match_states_return:
      forall s v m s' v' m' (*SACC:*)g (*SACC:*)j (*SACC:*)n (*SACC:*)l
      (MS: match_stackframes (*SACC:*)j (*SACC:*)n (*SACC:*)g s s')
      (*SACC:comments this*)(*Val.lessdef v v' ->*)
      (*SACC:comments this*)(*Mem.extends m m' ->*)
   (*SACC:*)(LDret: Val.inject j v v')
   (*SACC:*)(MLD: Mem.inject j (S n :: g ++ l) m m')
   (*SACC:*)(SZ: tc_sizes (g ++ l) (drop (S n) (Mem.stack m)) (tl (Mem.stack m')))
   (*SACC:*)(IG: inject_globals ge j)
   (*SACC:*)(*(INCR: inject_incr (Mem.flat_inj (Mem.nextblock init_m)) j)*)
   (*SACC:*)(*(SEP: inject_separated (Mem.flat_inj (Mem.nextblock init_m)) j init_m init_m)*),
      match_states (Returnstate s v m)
                   (Returnstate s' v' m')
  | match_states_interm:
      forall s sp pc rs m s' m' f r v' (*SACC:*)g (*SACC:*)j (*SACC:*)n (*SACC:*)l
            (STACKS: match_stackframes (*SACC:*)j (*SACC:*)n (*SACC:*)g s s')
   (*SACC:comments this*)(*(MLD: Mem.extends m m'),*)
   (*SACC:*)(MLD: Mem.inject j (S n :: g ++ l) m m')
      (RETspec: is_return_spec f pc r)
      (RETspec: f.(fn_stacksize) = 0)
   (*SACC:comments this*)(*Val.lessdef (rs#r) v'*)
   (*SACC:*)(LDret: Val.inject j (rs#r) v')
   (*SACC:*)(SZ: tc_sizes (g++l) (drop (S n) (Mem.stack m)) (tl (Mem.stack m')))
   (*SACC:*)(IG: inject_globals ge j)
   (*SACC:*)(*(INCR: inject_incr (Mem.flat_inj (Mem.nextblock init_m)) j)*)
   (*SACC:*)(*(SEP: inject_separated (Mem.flat_inj (Mem.nextblock init_m)) j init_m init_m)*),
      match_states (State s f (Vptr sp Ptrofs.zero) pc rs m)
                   (Returnstate s' v' m').

(** The last case of [match_states] corresponds to the execution
  of a move/nop/return sequence in the original code that was
  eliminated by the transformation:
<<
     State stk f (move/nop/return seq)  ~~  Returnstate stk' res'
            .
            .
            .
     State stk f (return instr)         ~~  Returnstate stk' res'
>>
  To preserve non-terminating behaviors, we need to make sure
  that the execution of this sequence in the original code cannot
  diverge.  For this, we introduce the following complicated
  measure over states, which will decrease strictly whenever
  the original code makes a transition but the transformed code
  does not. *)

Definition measure (st: state) : nat :=
  match st with
  | State s f sp pc rs m => (List.length s * (niter + 2) + return_measure f.(fn_code) pc + 1)%nat
  | Callstate s f args m sz => 0%nat
  | Returnstate s v m => (List.length s * (niter + 2))%nat
  end.

Ltac TransfInstr :=
  match goal with
  | H: (PTree.get _ (fn_code _) = _) |- _ =>
      destruct (transf_instr_lookup _ _ _ H) as [i' [TINSTR TSPEC]]; inv TSPEC
  end.

Ltac EliminatedInstr :=
  match goal with
  | H: (is_return_spec _ _ _) |- _ => inv H; try congruence
  | _ => idtac
  end.

(*=============================================*)
(*SACC: Addendum for transf_step_correct proof *)
(*=============================================*)

(*SACC:*)
Definition mem_state (s: state) : mem :=
  match s with
    State _ _ _ _ _ m
  | Callstate _ _ _ m _
  | Returnstate _ _ m => m
  end.

(*SACC:*)
Definition current_sp_state (s: state) : option (option (block * Z)) :=
  match s with
    State _ f (Vptr sp _) _ _ _ => Some (Some (sp, fn_stacksize f))
  | State _ _ _ _ _ _ => None
  | _ => Some None
  end.

(*SACC:*)
Definition stackblocks_of_stackframe (sf: stackframe) : option (block * Z) :=
  match sf with
  | (Stackframe _ f (Vptr sp _) _ _) => Some (sp,fn_stacksize f)
  | _ => None
  end.

(*SACC:*)
Definition stackframes_state (s: state) : list stackframe :=
  match s with
    State stk _ _ _ _ _ 
  | Callstate stk _ _ _ _
  | Returnstate stk _ _ => stk
  end.

(*SACC:*)
Definition stack_blocks_of_state (s: state) : list (option (block * Z)) :=
  match current_sp_state s with
    Some (Some x) => Some x :: map stackblocks_of_stackframe (stackframes_state s)
  | Some None => map stackblocks_of_stackframe (stackframes_state s)
  | None => None :: map stackblocks_of_stackframe (stackframes_state s)
  end.

(*SACC:*)
Definition sp_valid (s : state) : Prop :=
  Forall (fun bz => match bz with
                   Some (b,z) => Mem.valid_block (mem_state s) b
                 | None => True
                 end) (stack_blocks_of_state s).

(*SACC:*)
Lemma regs_inject_regs:
  forall j rs1 rs2, regs_inject j rs1 rs2 ->
  forall rl, Val.inject_list j rs1##rl rs2##rl.
Proof.
  induction rl; constructor; auto.
Qed.

(*SACC:*)
Lemma set_reg_inject:
  forall j r v1 v2 rs1 rs2,
  Val.inject j v1 v2 -> regs_inject j rs1 rs2 -> regs_inject j (rs1#r <- v1) (rs2#r <- v2).
Proof.
  intros; red; intros. repeat rewrite Regmap.gsspec.
  destruct (peq r0 r); auto.
Qed.

(*SACC:*)
Lemma set_res_inject:
  forall j res v1 v2 rs1 rs2,
  Val.inject j v1 v2 -> regs_inject j rs1 rs2 ->
  regs_inject j (regmap_setres res v1 rs1) (regmap_setres res v2 rs2).
Proof.
  intros. destruct res; simpl; auto. apply set_reg_inject; auto.
Qed.

(*SACC:*)
Lemma ros_is_function_transf:
  forall j ros rs rs' id,
    inject_globals ge j ->
    ros_is_function ge ros rs id ->
    regs_inject j rs rs' ->
    ros_is_function tge ros rs' id.
Proof.
  unfold ros_is_function. intros.
  destr_in H0. simpl.
  destruct H0 as (b & o & RS & FS).
  specialize (H1 r). rewrite RS in H1; inv H1.
  eexists; eexists; split; eauto.
  rewrite symbols_preserved. rewrite FS.
  f_equal.
  destruct H. erewrite H in H4. inv H4. auto. 
  eapply Genv.genv_symb_range; eauto.
Qed.


(*SACC:*)
Lemma inject_globals_meminj_preserves_globals:
  forall {F V} (g: Genv.t F V) j,
    inject_globals g j ->
    meminj_preserves_globals g j.
Proof.
  intros F V g j (IG1 & IG2); split; [|split].
  - intros id b FS.
    eapply IG1. eapply Genv.genv_symb_range; eauto.
  - intros b gv FVI.
    unfold Genv.find_var_info in FVI.
    repeat destr_in FVI.
    eapply IG1. eapply Genv.genv_defs_range; eauto.
  - intros b1 b2 delta gv FVI JB.
    unfold Genv.find_var_info in FVI.
    repeat destr_in FVI.
    eapply IG2 in JB; eauto. apply JB. eapply Genv.genv_defs_range; eauto.
Qed.

(*
Lemma regs_inject_init_regs:
  forall j params vl vl',
    Val.inject_list j vl vl' ->
    regs_inject j (init_regs vl params) (init_regs vl' params).
Proof.
  induction params; intros.
  simpl. red; intros. rewrite Regmap.gi. constructor.
  simpl. inv H.   red; intros. rewrite Regmap.gi. constructor.
  apply set_reg_inject. auto. auto.
Qed.
*)
(*SACC:*)
Lemma match_stackframes_incr:
  forall f n l s s'
    (MS: match_stackframes f n l s s')
    f' (INCR: inject_incr f f'),
    match_stackframes f' n l s s'.
Proof.
  induction 1; simpl; intros; eauto; try now econstructor; eauto.
  econstructor; eauto.
  red; intros; eauto.
Qed.

(*SACC:*)
Lemma inject_globals_incr:
  forall f f'
    (INCR : inject_incr f f')
    (SEP : forall b1 b2 delta, f b1 = None -> f' b1 = Some (b2, delta) -> Ple (Genv.genv_next ge) b1 /\ Ple (Genv.genv_next ge) b2)
    (IG: inject_globals ge f),
    inject_globals ge f'.
Proof.
  intros f f' INCR SEP (IG1 & IG2); split; intros; eauto.
  eapply IG2; eauto.
  destruct (f b1) eqn:FB1.
  - destruct p. eapply INCR in FB1. congruence.
  - specialize (SEP _ _ _ FB1 H).
    xomega.
Qed.

(*
Lemma tl_iter_commut:
  forall {A} (l: list A) n,
    tl (Nat.iter n (@tl _) l) = Nat.iter n (@tl _) (tl l).
Proof.
  induction n; simpl; intros; eauto. rewrite IHn. auto.
Qed.

Hypothesis init_m_genv_next:
  Ple (Genv.genv_next ge) (Mem.nextblock init_m).

Definition nextblock_inv (s: state) :=
  Ple (Mem.nextblock init_m) (Mem.nextblock (mem_state s)).
*)

(*SACC:*)
Lemma tc_sizes_same_top:
  forall g f1 r1 f2 r2 f1' f2',
    tc_sizes g (f1::r1) (f2::r2) ->
    size_frames f1 = size_frames f1' ->
    size_frames f2 = size_frames f2' ->
    tc_sizes g (f1'::r1) (f2'::r2).
Proof.
  intros g f1 r1 f2 r2 f1' f2' SZ EQ1 EQ2.
  inv SZ. simpl in *. repeat destr_in H4.
  econstructor; simpl. eauto. rewrite Heqo. eauto.
  rewrite <- EQ2.
  inv H5; [left|right]. omega. auto.
Qed.


(*SACC:*)
Lemma match_stackframes_no_perm':
  forall j n g s s' P,
    match_stackframes j n g s s' ->
    forall stk sp,
      stack_agree_perms P stk ->
      match_stack (Some (sp, 0) :: map block_of_stackframe s) stk ->
      forall l0,
        take (S n) stk = Some l0 ->
        Forall (fun tf => forall b, in_frames tf b -> forall o k p, ~ P b o k p) l0.
Proof.
  induction 1; simpl; intros stk0 sp0 SAP MS l0 TAKE; eauto.
  - repeat destr_in TAKE.
    constructor; auto. inv MS. unfold in_frames; simpl.
    unfold get_frame_blocks; rewrite BLOCKS. simpl. intros b [[]|[]].
    intros o k p PERM.
    exploit SAP. left. reflexivity. simpl. reflexivity. rewrite BLOCKS; left; reflexivity.
    eauto. rewrite SIZE. rewrite Z.max_id. omega.
  - repeat destr_in TAKE.
    constructor; auto. inv MS. unfold in_frames; simpl.
    unfold get_frame_blocks; rewrite BLOCKS. simpl. intros b [[]|[]].
    intros o k p PERM.
    exploit SAP. left. reflexivity. simpl. reflexivity. rewrite BLOCKS; left; reflexivity.
    eauto. rewrite SIZE. rewrite Z.max_id. omega.
  - repeat destr_in TAKE. repeat destr_in Heqo.
    constructor; eauto.
    + inv MS. unfold in_frames; simpl.
      unfold get_frame_blocks; rewrite BLOCKS. simpl. intros b [[]|[]].
      intros o k p PERM.
      exploit SAP. left. reflexivity. simpl. reflexivity. rewrite BLOCKS; left; reflexivity.
      eauto. rewrite SIZE. rewrite Z.max_id. omega.
    + inv MS. rewrite H1 in REC. eapply IHmatch_stackframes in REC; eauto.
      eapply stack_agree_perms_tl in SAP; simpl in *; auto.
      simpl. rewrite Heqo0. reflexivity.
Qed.

(*SACC:*)
Lemma match_stackframes_no_perm:
  forall j n g s s',
    match_stackframes j n g s s' ->
    forall m sp sz,
      sz = 0 ->
      match_stack (Some (sp, sz) :: map block_of_stackframe s) (Mem.stack m) ->
      forall l0,
        take (S n) (Mem.stack m) = Some l0 ->
        Forall (fun tf => forall b, in_frames tf b -> forall o k p, ~ Mem.perm m b o k p) l0.
Proof.
  intros; subst; eapply match_stackframes_no_perm'; eauto.
Qed.

(*=============================================*)
(*=============================================*)
(*=============================================*)


(** The proof of semantic preservation, then, is a simulation diagram
  of the ``option'' kind. *)

Lemma transf_step_correct:
  forall s1 t s2, step (*SACC:*)fn_stack_requirements ge s1 t s2 ->
  forall s1' (MS: match_states s1 s1') (*(NI1: nextblock_inv s1) (NI2: nextblock_inv s1')*) ((*SACC:*)SPV: sp_valid s1) ((*SACC:*)MSA: stack_inv s1) ((*SACC:*)MSA': stack_inv s1'),
  (exists s2', step (*SACC:*)fn_stack_requirements tge s1' t s2' /\ match_states s2 s2')
  \/ (measure s2 < measure s1 /\ t = E0 /\ match_states s2 s1')%nat.
Proof.
  induction 1; intros; inv MS; EliminatedInstr.

- (* nop *)
  TransfInstr. left. econstructor; split.
  eapply exec_Inop; eauto. econstructor; eauto.
- (* eliminated nop *)
  assert (s0 = pc') by congruence. subst s0.
  right. split. simpl. omega. split. auto.
  econstructor; eauto.

- (* op *)
  TransfInstr.
  assert (Val.inject_list j (rs##args) (rs'##args)). 
  apply regs_inject_regs; auto.
  exploit eval_operation_inject; eauto.
  eapply inject_globals_meminj_preserves_globals; eauto.
  intros [v' [EVAL' VLD]].
  left. exists (State s' (transf_function f) (Vptr sp' Ptrofs.zero) pc' (rs'#res <- v') m'); split.
  eapply exec_Iop; eauto.  rewrite <- EVAL'.
  rewrite eval_shift_stack_operation.
  apply eval_operation_preserved. exact symbols_preserved.
  econstructor; eauto. apply set_reg_inject; auto.
- (* eliminated move *)
  rewrite H1 in H. clear H1. inv H.
  right. split. simpl. omega. split. auto.
  econstructor; eauto. simpl in H0. rewrite PMap.gss. congruence.

- (* load *)
  TransfInstr.
  assert (Val.inject_list j (rs##args) (rs'##args)). apply regs_inject_regs; auto.
  exploit eval_addressing_inject; eauto.
  eapply inject_globals_meminj_preserves_globals; eauto.
  intros [a' [ADDR' ALD]].
  exploit Mem.loadv_inject; eauto.
  intros [v' [LOAD' VLD]].
  left. exists (State s' (transf_function f) (Vptr sp' Ptrofs.zero) pc' (rs'#dst <- v') m'); split.
  eapply exec_Iload with (a := a'). eauto.  rewrite <- ADDR'.
  rewrite eval_shift_stack_addressing.
  apply eval_addressing_preserved. exact symbols_preserved. eauto.
  econstructor; eauto. apply set_reg_inject; auto.


- (* store *)
  TransfInstr.
  assert (Val.inject_list j (rs##args) (rs'##args)). apply regs_inject_regs; auto.
  exploit eval_addressing_inject; eauto.
  eapply inject_globals_meminj_preserves_globals; eauto.
  intros [a' [ADDR' ALD]].
  exploit Mem.storev_mapped_inject. 2: eexact H1. eauto. eauto. apply RLD.
  intros [m'1 [STORE' MLD']].
  left. exists (State s' (transf_function f) (Vptr sp' Ptrofs.zero) pc' rs' m'1); split.
  eapply exec_Istore with (a := a'). eauto.  rewrite <- ADDR'.
  rewrite eval_shift_stack_addressing.
  apply eval_addressing_preserved. exact symbols_preserved. eauto.
  destruct a; simpl in H1; try discriminate.
  econstructor; eauto.
  repeat rewrite_stack_blocks; eauto.

- (* call *)
  exploit find_function_translated; eauto. intro FIND'.
  TransfInstr.
+ (* call turned tailcall *)
  assert (X: { m'' | Mem.free m' sp' 0 (fn_stacksize (transf_function f)) = Some m''}).
  {
    apply Mem.range_perm_free. rewrite stacksize_preserved. rewrite H8.
    red; intros; omegaContradiction.
  }
  destruct X as [m'' FREE].
  generalize (Mem.free_right_inject _ _ _ _ _ _ _ _ MLD FREE). intro FINJ.
  trim FINJ.
  {
    unfold Mem.flat_inj.
    intros b1 delta ofs k p FI PERM RNG.
    repeat destr_in FI.
    rewrite stacksize_preserved in RNG. rewrite H8 in RNG. omega.
  }
  repeat rewrite_stack_blocks; eauto.

  edestruct Mem.inject_new_stage_left_tailcall_right as (m2' & TCS & INJ'). apply FINJ.

  eapply match_stackframes_no_perm; eauto.
  inv MSA. eauto. 


  inv MSA'. inv MSA1. eapply Mem.free_top_tframe_no_perm; eauto.

  left. eexists (Callstate s' (transf_fundef fd) (rs'##args) m2' (fn_stack_requirements fid)); split.
  eapply exec_Itailcall; eauto.
  eapply ros_is_function_transf; eauto.
  apply sig_preserved.
  econstructor. econstructor; eauto. all: auto.
  apply regs_inject_regs; auto.
  eauto.
  repeat rewrite_stack_blocks. intro.
 
  eapply sizes_upstar'. rewrite <- EQ1. auto.
+ (* call that remains a call *)
  left. exists (Callstate (Stackframe res (transf_function f) (Vptr sp' Ptrofs.zero) pc' rs' :: s')
                     (transf_fundef fd) (rs'##args) (Mem.push_new_stage m') (fn_stack_requirements fid)); split.
  eapply exec_Icall; eauto.
  eapply ros_is_function_transf; eauto.
  apply sig_preserved.
  econstructor. constructor; eauto. all: auto.
  apply regs_inject_regs; auto.
  apply Mem.push_new_stage_inject. eauto.
  repeat rewrite_stack_blocks. eapply tc_sizes_up; eauto.

- (* tailcall *)
  exploit find_function_translated; eauto. intro FIND'.
  exploit Mem.free_parallel_inject; eauto.
  intros [m'1 [FREE EXT]].
  destruct (Mem.tailcall_stage_inject _ _ _ _ _ EXT H4) as (m2' & TC & INJ).
  {
    inv MSA'. inv MSA1.
    eapply Mem.free_top_tframe_no_perm; eauto.
    rewrite stacksize_preserved in SIZE. rewrite Z.add_0_r. auto.
  }
  TransfInstr.
  left. exists (Callstate s' (transf_fundef fd) (rs'##args) m2' (fn_stack_requirements fid)); split.
  eapply exec_Itailcall; eauto.
  eapply ros_is_function_transf; eauto.
  apply sig_preserved.
  rewrite stacksize_preserved; auto. rewrite ! Z.add_0_r in FREE. eauto. auto.
  econstructor; eauto.
  apply regs_inject_regs; auto.
  {
    repeat rewrite_stack_blocks.
    intros A B; rewrite A, B in SZ.
    intros; eapply tc_sizes_same_top; eauto.
    symmetry; apply size_frames_tc.
    symmetry; apply size_frames_tc.
  }

- (* builtin *)
  TransfInstr.
  exploit (@eval_builtin_args_inject _ ge tge (fun r => rs#r) (fun r => rs'#r) (Vptr sp0 Ptrofs.zero)); eauto.
  {
    simpl. intros; rewrite symbols_preserved; auto.
  }
  {
    simpl; intros.
    eapply IG; eauto. eapply Genv.genv_symb_range; eauto.
  }
  intros (vargs' & P & Q).
  exploit external_call_mem_inject; eauto.
  eapply inject_globals_meminj_preserves_globals; eauto.
  apply Mem.push_new_stage_inject. eauto.
  intros [f' [v' [m'1 [A [B [C [D [E [F G]]]]]]]]].
  edestruct Mem.unrecord_stack_block_inject_parallel as (m'2 & USB & INJ'). apply C. eauto.
  left. exists (State s' (transf_function f) (Vptr sp' Ptrofs.zero) pc' (regmap_setres res v' rs') m'2); split.
  eapply exec_Ibuiltin; eauto.
  eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  econstructor. 
  3: eauto. all: eauto.
  eapply match_stackframes_incr; eauto.
  apply set_res_inject; eauto.
  red; intros; eauto.
  repeat rewrite_stack_blocks. simpl. eauto.
  eapply inject_globals_incr; eauto.
  intros.
  specialize (G _ _ _ H3 H4). unfold Mem.valid_block in G.
(*  red in NI1. simpl in NI1.
  red in NI2. simpl in NI2.*)
  rewrite ! Mem.push_new_stage_nextblock in G.

  xomega.
  eapply inject_incr_trans; eauto.
  {
    red. intros b1 b2 delta F1 F2.
    split.
    unfold Mem.flat_inj in F1. now destr_in F1.
    destruct (j b1) as [[b2' delta']|] eqn:JB1.
    exploit F. apply JB1. rewrite F2; intro X; inv X.
    eapply SEP; eauto.
    exploit G. apply JB1. apply F2. unfold Mem.valid_block. rewnb. intros.
    red in NI1, NI2. simpl in *. xomega.
  }

- (* cond *)
  TransfInstr.
  left. exists (State s' (transf_function f) (Vptr sp0 Ptrofs.zero) (if b then ifso else ifnot) rs' m'); split.
  eapply exec_Icond; eauto.
  apply eval_condition_lessdef with (rs##args) m; auto. apply regs_lessdef_regs; auto.
  constructor; auto.

- (* jumptable *)
  TransfInstr.
  left. exists (State s' (transf_function f) (Vptr sp0 Ptrofs.zero) pc' rs' m'); split.
  eapply exec_Ijumptable; eauto.
  generalize (RLD arg). rewrite H0. intro. inv H2. auto.
  constructor; auto.

- (* return *)
  exploit Mem.free_parallel_extends; eauto. intros [m'1 [FREE EXT]].
  TransfInstr.
  left. exists (Returnstate s' (regmap_optget or Vundef rs') m'1); split.
  apply exec_Ireturn; auto. rewrite stacksize_preserved; auto.
  constructor. auto.
  destruct or; simpl. apply RLD. constructor.
  auto.

- (* eliminated return None *)
  assert (or = None) by congruence. subst or.
  right. split. simpl. omega. split. auto.
  constructor. auto.
  simpl. constructor.
  eapply Mem.free_left_extends; eauto.

- (* eliminated return Some *)
  assert (or = Some r) by congruence. subst or.
  right. split. simpl. omega. split. auto.
  constructor. auto.
  simpl. auto.
  eapply Mem.free_left_extends; eauto.

- (* internal call *)
  exploit Mem.alloc_extends; eauto.
    instantiate (1 := 0). omega.
    instantiate (1 := fn_stacksize f). omega.
  intros [m'1 [ALLOC EXT]].
  assert (fn_stacksize (transf_function f) = fn_stacksize f /\
          fn_entrypoint (transf_function f) = fn_entrypoint f /\
          fn_params (transf_function f) = fn_params f).
    unfold transf_function. destruct (zeq (fn_stacksize f) 0); auto.
  destruct H0 as [EQ1 [EQ2 EQ3]].
  left. econstructor; split.
  simpl. eapply exec_function_internal; eauto. rewrite EQ1; eauto.
  rewrite EQ2. rewrite EQ3. constructor; auto.
  apply regs_lessdef_init_regs. auto.

- (* external call *)
  exploit external_call_mem_extends; eauto.
  intros [res' [m2' [A [B [C D]]]]].
  left. exists (Returnstate s' res' m2'); split.
  simpl. econstructor; eauto.
  eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  constructor; auto.

- (* returnstate *)
  inv H2.
+ (* synchronous return in both programs *)
  left. econstructor; split.
  apply exec_return.
  constructor; auto. apply set_reg_lessdef; auto.
+ (* return instr in source program, eliminated because of tailcall *)
  right. split. unfold measure. simpl length.
  change (S (length s) * (niter + 2))%nat
   with ((niter + 2) + (length s) * (niter + 2))%nat.
  generalize (return_measure_bounds (fn_code f) pc). omega.
  split. auto.
  econstructor; eauto.
  rewrite Regmap.gss. auto.
Qed.

Lemma transf_initial_states:
  forall st1, initial_state prog st1 ->
  exists st2, initial_state tprog st2 /\ match_states st1 st2.
Proof.
  intros. inv H.
  exploit funct_ptr_translated; eauto. intro FIND.
  exists (Callstate nil (transf_fundef f) nil m0); split.
  econstructor; eauto. apply (Genv.init_mem_transf TRANSL). auto.
  replace (prog_main tprog) with (prog_main prog).
  rewrite symbols_preserved. eauto.
  symmetry; eapply match_program_main; eauto. 
  rewrite <- H3. apply sig_preserved.
  constructor. constructor. constructor. apply Mem.extends_refl.
Qed.

Lemma transf_final_states:
  forall st1 st2 r,
  match_states st1 st2 -> final_state st1 r -> final_state st2 r.
Proof.
  intros. inv H0. inv H. inv H5. inv H3. constructor.
Qed.


(** The preservation of the observable behavior of the program then
  follows. *)

Theorem transf_program_correct:
  forward_simulation (RTL.semantics prog) (RTL.semantics tprog).
Proof.
  eapply forward_simulation_opt with (measure := measure); eauto.
  apply senv_preserved. 
  eexact transf_initial_states.
  eexact transf_final_states.
  exact transf_step_correct.
Qed.

End PRESERVATION.

