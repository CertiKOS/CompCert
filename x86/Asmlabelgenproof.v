(* *******************  *)


(* *******************  *)




Require Import Coqlib Errors.
Require Import Integers Floats AST Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Op Locations Mach Conventions Asm RealAsm.
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
|match_states_intro m rs:
   match_states (Asm.State rs m) (Asm.State rs m).

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

Lemma app_cons_comm: forall (A:Type) (l1:list A) a l2,
    (l1 ++ [a]) ++ l2 = l1 ++ a :: l2.
Proof.
  induction l1; intros. 
  - simpl. auto.
  - simpl. f_equal. apply IHl1.
Qed.


Lemma transf_symbol_refl: forall id,
    (Genv.symbol_address tge id Ptrofs.zero) = (Genv.symbol_address ge id Ptrofs.zero).
Proof.
  intros id.
  unfold Genv.symbol_address.
  red in TRANSF.
  unfold ge, tge.
  rewrite (Genv.find_symbol_transf_partial TRANSF id). auto.
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
