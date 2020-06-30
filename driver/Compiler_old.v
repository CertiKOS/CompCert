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

(** The whole compiler and its proof of semantic preservation *)

(** Libraries. *)
Require Import String.
Require Import Coqlib Errors.
Require Import AST_old Linking_old Smallstep_old.
(** Languages (syntax and semantics). *)
Require Ctypes_old Csyntax_old Csem_old Cstrategy_old Cexec_old.
Require Clight_old.
Require Csharpminor_old.
Require Cminor_old.
Require CminorSel_old.
Require RTL_old.
Require LTL_old.
Require Linear_old.
Require Mach_old.
Require Asm_old.
(** Translation passes. *)
Require SimplExpr_old.
Require SimplLocals_old.
Require Cshmgen_old.
Require Cminorgen_old.
Require Selection_old.
Require RTLgen_old.
Require Tailcall_old.
Require Inlining_old.
Require Renumber_old.
Require Constprop_old.
Require CSE_old.
Require Deadcode_old.
Require Unusedglob_old.
Require Allocation_old.
Require Tunneling_old.
Require Linearize_old.
Require CleanupLabels_old.
Require Debugvar_old.
Require Stacking_old.
Require Mach2Mach2_old.
Require Asmgen_old.
(** Proofs of semantic preservation. *)
Require SimplExprproof_old.
Require SimplLocalsproof_old.
Require Cshmgenproof_old.
Require Cminorgenproof_old.
Require Selectionproof_old.
Require RTLgenproof_old.
Require Tailcallproof_old.
Require Inliningproof_old.
Require Renumberproof_old.
Require Constpropproof_old.
Require CSEproof_old.
Require Deadcodeproof_old.
Require Unusedglobproof_old.
Require Allocproof_old.
Require Tunnelingproof_old.
Require Linearizeproof_old.
Require CleanupLabelsproof_old.
Require Debugvarproof_old.
Require Stackingproof_old.
Require Asmgenproof_old.

(** Command-line flags. *)
Require Import Compopts_old.


(** Pretty-printers (defined in Caml). *)
Parameter print_Clight: Clight_old.program -> unit.
Parameter print_Cminor: Cminor_old.program -> unit.
Parameter print_RTL: Z -> RTL_old.program -> unit.
Parameter print_LTL: LTL_old.program -> unit.
Parameter print_Mach: Mach_old.program -> unit.

Local Open Scope string_scope.

(** * Composing the translation passes *)

(** We first define useful monadic composition operators,
    along with funny (but convenient) notations. *)

Definition apply_total (A B: Type) (x: res A) (f: A -> B) : res B :=
  match x with Error msg => Error msg | OK x1 => OK (f x1) end.

Definition apply_partial (A B: Type)
                         (x: res A) (f: A -> res B) : res B :=
  match x with Error msg => Error msg | OK x1 => f x1 end.

Notation "a @@@ b" :=
   (apply_partial _ _ a b) (at level 50, left associativity).
Notation "a @@ b" :=
   (apply_total _ _ a b) (at level 50, left associativity).

Definition print {A: Type} (printer: A -> unit) (prog: A) : A :=
  let unused := printer prog in prog.

Definition time {A B: Type} (name: string) (f: A -> B) : A -> B := f.

Definition total_if {A: Type}
          (flag: unit -> bool) (f: A -> A) (prog: A) : A :=
  if flag tt then f prog else prog.

Definition partial_if {A: Type}
          (flag: unit -> bool) (f: A -> res A) (prog: A) : res A :=
  if flag tt then f prog else OK prog.

(** We define three translation functions for whole programs: one
  starting with a C program, one with a Cminor program, one with an
  RTL program.  The three translations produce Asm programs ready for
  pretty-printing and assembling. *)

Local Existing Instance ValueAnalysis_old.romem_for_wp_instance.

Definition transf_rtl_program (f: RTL_old.program) : res Asm_old.program :=
   OK f
   @@ print (print_RTL 0)
   @@ total_if Compopts_old.optim_tailcalls (time "Tail calls" Tailcall_old.transf_program)
   @@ print (print_RTL 1)
  @@@ partial_if Compopts_old.optim_inlining (time "Inlining" Inlining_old.transf_program)
   @@ print (print_RTL 2)
   @@ time "Renumbering" Renumber_old.transf_program
   @@ print (print_RTL 3)
   @@ total_if Compopts_old.optim_constprop (time "Constant propagation" Constprop_old.transf_program)
   @@ print (print_RTL 4)
   @@ total_if Compopts_old.optim_constprop (time "Renumbering" Renumber_old.transf_program)
   @@ print (print_RTL 5)
  @@@ partial_if Compopts_old.optim_CSE (time "CSE" CSE_old.transf_program)
   @@ print (print_RTL 6)
  @@@ partial_if Compopts_old.optim_redundancy (time "Redundancy elimination" Deadcode_old.transf_program)
   @@ print (print_RTL 7)
  @@@ time "Unused globals" Unusedglob_old.transform_program
   @@ print (print_RTL 8)
  @@@ time "Register allocation" Allocation_old.transf_program
   @@ print print_LTL
   @@ time "Branch tunneling" Tunneling_old.tunnel_program
  @@@ time "CFG linearization" Linearize_old.transf_program
   @@ time "Label cleanup" CleanupLabels_old.transf_program
  @@@ partial_if Compopts_old.debug (time "Debugging info for local variables" Debugvar_old.transf_program)
  @@@ time "Mach generation" Stacking_old.transf_program
   @@ print print_Mach
   @@@ time "Asm generation" Asmgen_old.transf_program.

Definition transf_cminor_program (p: Cminor_old.program) : res Asm_old.program :=
   OK p
   @@ print print_Cminor
  @@@ time "Instruction selection" Selection_old.sel_program
  @@@ time "RTL generation" RTLgen_old.transl_program
  @@@ transf_rtl_program.

Definition transf_clight_program (p: Clight_old.program) : res Asm_old.program :=
  OK p
   @@ print print_Clight
  @@@ time "Simplification of locals" SimplLocals_old.transf_program
  @@@ time "C#minor generation" Cshmgen_old.transl_program
  @@@ time "Cminor generation" Cminorgen_old.transl_program
  @@@ transf_cminor_program.

Definition transf_c_program (p: Csyntax_old.program) : res Asm_old.program :=
  OK p
  @@@ time "Clight generation" SimplExpr_old.transl_program
  @@@ transf_clight_program.


(** The following lemmas help reason over compositions of passes. *)

Lemma print_identity:
  forall (A: Type) (printer: A -> unit) (prog: A),
  print printer prog = prog.
Proof.
  intros; unfold print. destruct (printer prog); auto.
Qed.

Lemma compose_print_identity:
  forall (A: Type) (x: res A) (f: A -> unit),
  x @@ print f = x.
Proof.
  intros. destruct x; simpl. rewrite print_identity. auto. auto.
Qed.

(** * Relational specification of compilation *)

Definition match_if {A: Type} (flag: unit -> bool) (R: A -> A -> Prop): A -> A -> Prop :=
  if flag tt then R else eq.

Lemma total_if_match:
  forall (A: Type) (flag: unit -> bool) (f: A -> A) (rel: A -> A -> Prop) (prog: A),
  (forall p, rel p (f p)) ->
  match_if flag rel prog (total_if flag f prog).
Proof.
  intros. unfold match_if, total_if. destruct (flag tt); auto.
Qed.

Lemma partial_if_match:
  forall (A: Type) (flag: unit -> bool) (f: A -> res A) (rel: A -> A -> Prop) (prog tprog: A),
  (forall p tp, f p = OK tp -> rel p tp) ->
  partial_if flag f prog = OK tprog ->
  match_if flag rel prog tprog.
Proof.
  intros. unfold match_if, partial_if in *. destruct (flag tt). auto. congruence.
Qed.

Instance TransfIfLink {A: Type} {LA: Linker A}
                      (flag: unit -> bool) (transf: A -> A -> Prop) (TL: TransfLink transf)
                      : TransfLink (match_if flag transf).
Proof.
  unfold match_if. destruct (flag tt).
- auto.
- red; intros. subst tp1 tp2. exists p; auto.
Qed.

(** This is the list of compilation passes of CompCert in relational style.
  Each pass is characterized by a [match_prog] relation between its
  input code and its output code.  The [mkpass] and [:::] combinators,
  defined in module [Linking], ensure that the passes are composable
  (the output language of a pass is the input language of the next pass)
  and that they commute with linking (property [TransfLink], inferred
  by the type class mechanism of Coq). *)

Local Open Scope linking_scope.

Definition CompCert's_passes :=
      mkpass SimplExprproof_old.match_prog
  ::: mkpass SimplLocalsproof_old.match_prog
  ::: mkpass Cshmgenproof_old.match_prog
  ::: mkpass Cminorgenproof_old.match_prog
  ::: mkpass Selectionproof_old.match_prog
  ::: mkpass RTLgenproof_old.match_prog
  ::: mkpass (match_if Compopts_old.optim_tailcalls Tailcallproof_old.match_prog)
  ::: mkpass (match_if Compopts_old.optim_inlining Inliningproof_old.match_prog)
  ::: mkpass Renumberproof_old.match_prog
  ::: mkpass (match_if Compopts_old.optim_constprop Constpropproof_old.match_prog)
  ::: mkpass (match_if Compopts_old.optim_constprop Renumberproof_old.match_prog)
  ::: mkpass (match_if Compopts_old.optim_CSE CSEproof_old.match_prog)
  ::: mkpass (match_if Compopts_old.optim_redundancy Deadcodeproof_old.match_prog)
  ::: mkpass Unusedglobproof_old.match_prog
  ::: mkpass Allocproof_old.match_prog
  ::: mkpass Tunnelingproof_old.match_prog
  ::: mkpass Linearizeproof_old.match_prog
  ::: mkpass CleanupLabelsproof_old.match_prog
  ::: mkpass (match_if Compopts_old.debug Debugvarproof_old.match_prog)
  ::: mkpass Stackingproof_old.match_prog
  ::: mkpass Asmgenproof_old.match_prog
  ::: pass_nil _.

(** Composing the [match_prog] relations above, we obtain the relation
  between CompCert C sources and Asm code that characterize CompCert's
  compilation. *)

Definition match_prog: Csyntax_old.program -> Asm_old.program -> Prop :=
  pass_match (compose_passes CompCert's_passes).

Fixpoint passes_app {A B C} (l1: Passes A B) (l2: Passes B C) : Passes A C :=
  match l1 in (Passes AA BB) return (Passes BB C -> Passes AA C) with
  | pass_nil _ => fun l3 => l3
  | pass_cons _ _ _ P1 l1 => fun l2 => P1 ::: passes_app l1 l2
  end l2.

(* Instance transf_check_link: TransfLink PseudoInstructions.match_check_prog. *)
(* Proof. *)
(*   red. intros p1 p2 tp1 tp2 p LINK (MP1 & O1) (MP2 & O2). *)
(*   exploit (fun lv => @TransfPartialLink Asm_old.function Asm_old.function unit lv (PseudoInstructions.transf_check_function) p1 p2 tp1 tp2 p); eauto. intros (tp & TLINK & TMP). *)
(*   exists tp; split; eauto. *)
(*   split; auto. *)

(*   eauto. eauto. *)
(* Defined. *)


(** The [transf_c_program] function, when successful, produces
  assembly code that is in the [match_prog] relation with the source C program. *)

Theorem transf_c_program_match:
  forall p tp,
  transf_c_program p = OK tp ->
  match_prog p tp.
Proof.
  intros p tp T.
  unfold transf_c_program, time in T. simpl in T.
  destruct (SimplExpr_old.transl_program p) as [p1|e] eqn:P1; simpl in T; try discriminate.
  unfold transf_clight_program, time in T. rewrite ! compose_print_identity in T. simpl in T.
  destruct (SimplLocals_old.transf_program p1) as [p2|e] eqn:P2; simpl in T; try discriminate.
  destruct (Cshmgen_old.transl_program p2) as [p3|e] eqn:P3; simpl in T; try discriminate.
  destruct (Cminorgen_old.transl_program p3) as [p4|e] eqn:P4; simpl in T; try discriminate.
  unfold transf_cminor_program, time in T. rewrite ! compose_print_identity in T. simpl in T.
  destruct (Selection_old.sel_program p4) as [p5|e] eqn:P5; simpl in T; try discriminate.
  destruct (RTLgen_old.transl_program p5) as [p6|e] eqn:P6; simpl in T; try discriminate.
  unfold transf_rtl_program, time in T. rewrite ! compose_print_identity in T. simpl in T.
  set (p7 := total_if optim_tailcalls Tailcall_old.transf_program p6) in *.
  destruct (partial_if optim_inlining Inlining_old.transf_program p7) as [p8|e] eqn:P8; simpl in T; try discriminate.
  set (p9 := Renumber_old.transf_program p8) in *.
  set (p10 := total_if optim_constprop Constprop_old.transf_program p9) in *.
  set (p11 := total_if optim_constprop Renumber_old.transf_program p10) in *.
  destruct (partial_if optim_CSE CSE_old.transf_program p11) as [p12|e] eqn:P12; simpl in T; try discriminate.
  destruct (partial_if optim_redundancy Deadcode_old.transf_program p12) as [p13|e] eqn:P13; simpl in T; try discriminate.
  destruct (Unusedglob_old.transform_program p13) as [p14|e] eqn:P14; simpl in T; try discriminate.
  destruct (Allocation_old.transf_program p14) as [p15|e] eqn:P15; simpl in T; try discriminate.
  set (p16 := Tunneling_old.tunnel_program p15) in *.
  destruct (Linearize_old.transf_program p16) as [p17|e] eqn:P17; simpl in T; try discriminate.
  set (p18 := CleanupLabels_old.transf_program p17) in *.
  destruct (partial_if debug Debugvar_old.transf_program p18) as [p19|e] eqn:P19; simpl in T; try discriminate.
  destruct (Stacking_old.transf_program p19) as [p20|e] eqn:P20; simpl in T; try discriminate.
  unfold match_prog; simpl. 
  exists p1; split. apply SimplExprproof_old.transf_program_match; auto.
  exists p2; split. apply SimplLocalsproof_old.match_transf_program; auto.
  exists p3; split. apply Cshmgenproof_old.transf_program_match; auto.
  exists p4; split. apply Cminorgenproof_old.transf_program_match; auto.
  exists p5; split. apply Selectionproof_old.transf_program_match; auto.
  exists p6; split. apply RTLgenproof_old.transf_program_match; auto.
  exists p7; split. apply total_if_match. apply Tailcallproof_old.transf_program_match.
  exists p8; split. eapply partial_if_match; eauto. apply Inliningproof_old.transf_program_match; auto.
  exists p9; split. apply Renumberproof_old.transf_program_match; auto.
  exists p10; split. apply total_if_match. apply Constpropproof_old.transf_program_match.
  exists p11; split. apply total_if_match. apply Renumberproof_old.transf_program_match.
  exists p12; split. eapply partial_if_match; eauto. apply CSEproof_old.transf_program_match.
  exists p13; split. eapply partial_if_match; eauto. apply Deadcodeproof_old.transf_program_match.
  exists p14; split. apply Unusedglobproof_old.transf_program_match; auto.
  exists p15; split. apply Allocproof_old.transf_program_match; auto.
  exists p16; split. apply Tunnelingproof_old.transf_program_match.
  exists p17; split. apply Linearizeproof_old.transf_program_match; auto.
  exists p18; split. apply CleanupLabelsproof_old.transf_program_match; auto.
  exists p19; split. eapply partial_if_match; eauto. apply Debugvarproof_old.transf_program_match.
  exists p20; split. apply Stackingproof_old.transf_program_match; auto.
  exists tp; split. apply Asmgenproof_old.transf_program_match; auto.
  reflexivity.
Qed.

Lemma compose_passes_app:
  forall {l1 l2} (A: Passes l1 l2) {l3} (B: Passes l2 l3) p tp,
    compose_passes (passes_app A B) p tp <->
    exists pi, compose_passes A p pi /\ compose_passes B pi tp.
Proof.
  induction A; simpl; intros. split. eexists; split; eauto.
  intros (pi & EQ & CP); inv EQ; auto.
  setoid_rewrite IHA. split; intro H; decompose [ex and] H; eauto.
Qed.



(** * Semantic preservation *)

(** We now prove that the whole CompCert compiler (as characterized by the
  [match_prog] relation) preserves semantics by constructing
  the following simulations:
- Forward simulations from [Cstrategy] to [Asm]
  (composition of the forward simulations for each pass).
- Backward simulations for the same languages
  (derived from the forward simulation, using receptiveness of the source
  language and determinacy of [Asm]).
- Backward simulation from [Csem] to [Asm]
  (composition of two backward simulations).
*)

Remark forward_simulation_identity:
  forall {RETVAL: Type},
  forall sem: _ RETVAL, forward_simulation sem sem.
Proof.
  intros. apply forward_simulation_step with (fun s1 s2 => s2 = s1); intros.
- auto.
- exists s1; auto.
- subst s2; auto.
- subst s2. exists s1'; auto.
Qed.

Lemma match_if_simulation:
  forall {RETVAL: Type},
  forall (A: Type) (sem: A -> semantics RETVAL) (flag: unit -> bool) (transf: A -> A -> Prop) (prog tprog: A),
  match_if flag transf prog tprog ->
  (forall p tp, transf p tp -> forward_simulation (sem p) (sem tp)) ->
  forward_simulation (sem prog) (sem tprog).
Proof.
  intros. unfold match_if in *. destruct (flag tt). eauto. subst. apply forward_simulation_identity.
Qed.

Section WITHEXTERNALCALLS.
  Local Existing Instance Events_old.symbols_inject_instance.
  Local Existing Instance StackADT_old.inject_perm_all.
  Context `{external_calls_prf: Events_old.ExternalCalls
                                  (symbols_inject_instance := Events_old.symbols_inject_instance) }.
  Context {i64_helpers_correct_prf: SplitLongproof_old.I64HelpersCorrect mem}.
  Context `{memory_model_x_prf: !Unusedglobproof_old.Mem.MemoryModelX mem}.

Definition fn_stack_requirements (tp: Asm_old.program) (id: ident) : Z :=
  match Globalenvs_old.Genv.find_symbol (Globalenvs_old.Genv.globalenv tp) id with
  | Some b =>
    match Globalenvs_old.Genv.find_funct_ptr (Globalenvs_old.Genv.globalenv tp) b with
    | Some (Internal f) => Asm_old.fn_stacksize f
    | _ => 0
    end
  | None => 0
  end.


Definition printable_oracle (tp: Asm_old.program) : list (ident * Z) :=
  fold_left (fun acc gd =>
               match gd with
                 (id,Some (Gfun (Internal f))) => (id, fn_stack_requirements tp id)::acc
               | _ => acc
               end) (prog_defs tp) nil.

Lemma match_program_no_more_functions:
  forall {F1 V1 F2 V2}
         `{Linker F1} `{Linker V1}
         Mf Mv
         (p1: program F1 V1) (p2: program F2 V2),
    match_program Mf Mv p1 p2 ->
    forall b,
    Globalenvs_old.Genv.find_funct_ptr (Globalenvs_old.Genv.globalenv p1) b = None ->
    Globalenvs_old.Genv.find_funct_ptr (Globalenvs_old.Genv.globalenv p2) b = None.
Proof.
  intros.
  generalize (Globalenvs_old.Genv.find_def_match_2 H1 b).
  inversion 1.
  - destruct (Globalenvs_old.Genv.find_funct_ptr (Globalenvs_old.Genv.globalenv p2) b) eqn:?; auto.
    apply Globalenvs_old.Genv.find_funct_ptr_iff in Heqo. congruence.
  - destruct (Globalenvs_old.Genv.find_funct_ptr (Globalenvs_old.Genv.globalenv p2) b) eqn:?; auto.
    apply Globalenvs_old.Genv.find_funct_ptr_iff in Heqo. rewrite Heqo in H5.  inv H5.
    inv H6.
    symmetry in H4.
    apply Globalenvs_old.Genv.find_funct_ptr_iff in H4. congruence.
Qed.


Lemma fn_stack_requirements_pos:
  forall ps p i,
    Asmgenproof_old.match_prog ps p ->
    0 <= fn_stack_requirements p i.
Proof.
  unfold fn_stack_requirements.
  intros. repeat destr; try omega.
  destruct (Globalenvs_old.Genv.find_funct_ptr (Globalenvs_old.Genv.globalenv ps) b) eqn:FFPMACH.
  - edestruct (Asmgenproof_old.functions_translated _ _ H _ _ FFPMACH) as (if0 & FFPASM & EQ). rewrite Heqo0 in FFPASM. inv FFPASM.
    unfold Asmgen_old.transf_fundef, transf_partial_fundef in EQ.
    destr_in EQ. monadInv EQ.
    unfold Asmgen_old.transf_function in EQ0. monadInv EQ0. repeat destr_in EQ1. unfold Asmgen_old.transl_function in EQ.
    monadInv EQ. repeat destr_in EQ1. simpl.
    unfold StackADT_old.frame_info_of_size_and_pubrange in Heqo1. destr_in Heqo1.
  - eapply match_program_no_more_functions in FFPMACH; eauto. congruence.
Qed.

Definition mk_init_stk {F V} (p: AST_old.program F V) : StackADT_old.stack :=
  (Some (StackADT_old.make_singleton_frame_adt
           (Globalenvs_old.Genv.genv_next (Globalenvs_old.Genv.globalenv p)) 0 0), nil) :: nil .


Theorem cstrategy_semantic_preservation:
  forall p tp,
    match_prog p tp ->
    let init_stk := mk_init_stk tp in
  forward_simulation (Cstrategy_old.semantics (fn_stack_requirements tp) p) (Asm_old.semantics tp init_stk)
  /\ backward_simulation (atomic (Cstrategy_old.semantics (fn_stack_requirements tp) p)) (Asm_old.semantics tp init_stk).
Proof.
  intros p tp M. unfold match_prog, pass_match in M; simpl in M.
Ltac DestructM :=
  match goal with
    [ H: exists p, _ /\ _ |- _ ] => 
      let p := fresh "p" in let M := fresh "M" in let MM := fresh "MM" in
      destruct H as (p & M & MM); clear H
  end.
  repeat DestructM.
  intros init_stk.
  assert (F: forward_simulation (Cstrategy_old.semantics (fn_stack_requirements tp) p) (Asm_old.semantics tp init_stk)).
  {
  eapply compose_forward_simulations.
    eapply SimplExprproof_old.transl_program_correct; try eassumption. intros; eapply fn_stack_requirements_pos. subst; eauto.
  eapply compose_forward_simulations.
    eapply SimplLocalsproof_old.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply Cshmgenproof_old.transl_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply Cminorgenproof_old.transl_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply Selectionproof_old.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply RTLgenproof_old.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. intros; eapply Tailcallproof_old.transf_program_correct; eauto.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. eapply Inliningproof_old.transf_program_correct; eassumption.
  eapply compose_forward_simulations. eapply Renumberproof_old.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. apply Constpropproof_old.transf_program_correct.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. apply Renumberproof_old.transf_program_correct.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. intros; eapply CSEproof_old.transf_program_correct; assumption.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. intros; eapply Deadcodeproof_old.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply Unusedglobproof_old.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply Allocproof_old.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply Tunnelingproof_old.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply Linearizeproof_old.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply CleanupLabelsproof_old.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. apply Debugvarproof_old.transf_program_correct.
  eapply compose_forward_simulations.
    replace (fn_stack_requirements tp) with (Stackingproof_old.fn_stack_requirements p20).
  eapply Stackingproof_old.transf_program_correct with
      (return_address_offset := Asmgenproof0_old.return_address_offset);
    try assumption.
    exact (Asmgenproof_old.return_address_exists).
    {
      clear - M19 MM.
      subst.
      unfold Stackingproof_old.fn_stack_requirements, fn_stack_requirements.
      apply Axioms.extensionality.
      intros i.
      erewrite Asmgenproof_old.symbols_preserved; eauto.
      destruct (Globalenvs_old.Genv.find_symbol (Globalenvs_old.Genv.globalenv p20) i) eqn:?; auto.
      destruct (Globalenvs_old.Genv.find_funct_ptr (Globalenvs_old.Genv.globalenv p20) b) eqn:?; auto.
      eapply Asmgenproof_old.functions_translated in Heqo0. 2: eauto.
      destruct Heqo0 as (tf & FFP & TF); rewrite FFP.
      destruct f; simpl in *; monadInv TF; auto.
      unfold Asmgen_old.transf_function in EQ. monadInv EQ. destr_in EQ1. inv EQ1.
      unfold Asmgen_old.transl_function in EQ0. monadInv EQ0. repeat destr_in EQ1. simpl. auto.
      eapply match_program_no_more_functions in Heqo0; eauto. rewrite Heqo0. auto.
    }
  eapply compose_forward_simulations.
    instantiate (1 := Mach_old.semantics2 Asmgenproof0_old.return_address_offset p20).
    apply Mach2Mach2_old.mach2_simulation.
    eapply Stackingproof_old.stacking_frame_correct; eauto.
    subst. unfold init_stk, mk_init_stk.
    replace (Globalenvs_old.Genv.genv_next (Globalenvs_old.Genv.globalenv tp))
      with (Globalenvs_old.Genv.genv_next (Globalenvs_old.Genv.globalenv p20)).
    eapply Asmgenproof_old.transf_program_correct. eassumption.
    eapply Stackingproof_old.stacking_frame_correct; eauto.
    eapply Globalenvs_old.Genv.senv_transf_partial in M19.
    destruct M19 as (NB & _). simpl in NB. auto.
  }
  split. auto.
  apply forward_to_backward_simulation.
  apply factor_forward_simulation. auto. eapply sd_traces. eapply Asm_old.semantics_determinate.
  apply atomic_receptive. apply Cstrategy.semantics_strongly_receptive.
  apply Asm_old.semantics_determinate.
Qed.

Theorem c_semantic_preservation:
  forall p tp,
    match_prog p tp ->
    let init_stk := mk_init_stk tp in
  backward_simulation (Csem.semantics (fn_stack_requirements tp) p) (Asm_old.semantics tp init_stk).
Proof.
  intros.
  apply compose_backward_simulation with (atomic (Cstrategy.semantics (fn_stack_requirements tp) p)).
  eapply sd_traces; eapply Asm_old.semantics_determinate.
  apply factor_backward_simulation.
  apply Cstrategy.strategy_simulation.
  apply Csem.semantics_single_events.
  eapply ssr_well_behaved; eapply Cstrategy.semantics_strongly_receptive.
  exact (proj2 (cstrategy_semantic_preservation _ _ H)).
Qed.



(** * Correctness of the CompCert compiler *)

(** Combining the results above, we obtain semantic preservation for two
  usage scenarios of CompCert: compilation of a single monolithic program,
  and separate compilation of multiple source files followed by linking.

  In the monolithic case, we have a whole C program [p] that is
  compiled in one run of CompCert to a whole Asm program [tp].
  Then, [tp] preserves the semantics of [p], in the sense that there
  exists a backward simulation of the dynamic semantics of [p]
  by the dynamic semantics of [tp]. *)

Theorem transf_c_program_correct:
  forall p tp,
    transf_c_program p = OK tp ->
    let init_stk := mk_init_stk tp in
  backward_simulation (Csem.semantics (fn_stack_requirements tp) p) (Asm_old.semantics tp init_stk).
Proof.
  intros. apply c_semantic_preservation. apply transf_c_program_match; auto.
Qed.



(** Here is the separate compilation case.  Consider a nonempty list [c_units]
  of C source files (compilation units), [C1 ,,, Cn].  Assume that every
  C compilation unit [Ci] is successfully compiled by CompCert, obtaining
  an Asm compilation unit [Ai].  Let [asm_unit] be the nonempty list
  [A1 ... An].  Further assume that the C units [C1 ... Cn] can be linked
  together to produce a whole C program [c_program].  Then, the generated
  Asm units can be linked together, producing a whole Asm program
  [asm_program].  Moreover, [asm_program] preserves the semantics of
  [c_program], in the sense that there exists a backward simulation of
  the dynamic semantics of [asm_program] by the dynamic semantics of [c_program].
*)

Theorem separate_transf_c_program_correct:
  forall c_units asm_units c_program,
  nlist_forall2 (fun cu tcu => transf_c_program cu = OK tcu) c_units asm_units ->
  link_list c_units = Some c_program ->
  exists asm_program, 
      link_list asm_units = Some asm_program
      /\
      let init_stk := mk_init_stk asm_program in
      backward_simulation (Csem.semantics (fn_stack_requirements asm_program) c_program) (Asm_old.semantics asm_program init_stk).
Proof.
  intros. 
  assert (nlist_forall2 match_prog c_units asm_units).
  { eapply nlist_forall2_imply. eauto. simpl; intros. apply transf_c_program_match; auto. }
  assert (exists asm_program, link_list asm_units = Some asm_program /\ match_prog c_program asm_program).
  { eapply link_list_compose_passes; eauto. }
  destruct H2 as (asm_program & P & Q).
  exists asm_program; split; auto. apply c_semantic_preservation; auto.
Qed.



End WITHEXTERNALCALLS.

