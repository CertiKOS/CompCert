Require compcert.cfrontend.ClightBigstep.
Require EventsX.

Import Coqlib.
Import AST.
Import Globalenvs.
Import EventsX.
Import Ctypes.
Import Clight.
Export ClightBigstep.

Require Import ClightX.

Section WITHCONFIG.
Context `{external_calls_prf: ExternalCalls}.

Variable fn_stack_requirements: ident -> Z.

Inductive bigstep_function_terminates' function_entry p i sg vargs (m: mem) t : Values.val * mem -> Prop :=
  | bigstep_function_terminates_intro b f targs tres cc vres m' m'':
      let ge := Clight.globalenv p in
      Genv.find_symbol ge i = Some b ->
      Genv.find_funct_ptr ge b = Some f ->
      type_of_fundef f = Tfunction targs tres cc ->
      sg = signature_of_type targs tres cc ->
      eval_funcall fn_stack_requirements ge function_entry (Memtype.Mem.push_new_stage m) f vargs t m' vres (fn_stack_requirements i) ->
      Memtype.Mem.unrecord_stack_block m' = Some m'' ->
      bigstep_function_terminates' function_entry p i sg vargs m t (vres,  m'').

Definition bigstep_function_terminates2 := bigstep_function_terminates' function_entry2.

Inductive bigstep_function_diverges' function_entry (p: program) i sg vargs m: traceinf -> Prop :=
  | bigstep_function_diverges_intro: forall b f targs tres cc t,
      let ge := globalenv p in
      Genv.find_symbol ge i = Some b ->
      Genv.find_funct_ptr ge b = Some f ->
      type_of_fundef f = Tfunction targs tres cc ->
      sg = signature_of_type targs tres cc ->
      evalinf_funcall fn_stack_requirements ge function_entry (Memtype.Mem.push_new_stage m) f vargs t (fn_stack_requirements i)->
      bigstep_function_diverges' function_entry p i sg vargs m t.

Definition bigstep_function_diverges2 := bigstep_function_diverges' function_entry2.

Definition bigstep_function_semantics2 (p: program) i sg vargs m :=
  Smallstep.Bigstep_semantics
    (bigstep_function_terminates2 p i sg vargs m)
    (bigstep_function_diverges2 p i sg vargs m).

Theorem bigstep_function_semantics_sound prog i (sg: AST.signature) (vargs: list Values.val) m:
  Smallstep.bigstep_sound
    (bigstep_function_semantics2 prog i sg vargs m)
    (ClightX.semantics fn_stack_requirements prog i m sg vargs).
Proof.
  constructor; simpl; intros.
(* termination *)
  inv H. econstructor; econstructor.
  split. econstructor; eauto.
  split. eapply eval_funcall_steps. eauto. red; auto.
  econstructor. eauto.
(* divergence *)
  inv H. econstructor.
  split. econstructor; eauto.
  eapply Smallstep.forever_N_forever with (order := order).
  red; intros. constructor; intros. red in H. elim H.
  eapply evalinf_funcall_forever; eauto.
Qed.


End WITHCONFIG.
