(* *******************  *)
(* Author: Yuting Wang  *)
(* Date:   Dec 2, 2019 *)
(* *******************  *)

Require Import Coqlib Errors.
Require Import Integers Floats AST Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Op Locations Mach Conventions Asm RealAsm.
Require Import PadInitData.
Import ListNotations.
Require AsmFacts.

Lemma transf_globdef_pres_id : forall def,
    fst def = fst (transf_globdef def).
Proof.
  unfold transf_globdef. destruct def. cbn. auto.
Qed.

Lemma genv_symb_pres: forall defs (ge1 ge2: Genv.t fundef unit),
    Genv.genv_next ge1 = Genv.genv_next ge2 ->
    Genv.genv_symb ge1 = Genv.genv_symb ge2 ->
    Genv.genv_symb (fold_left (Genv.add_global (V:=unit)) (map transf_globdef defs) ge1) =
    Genv.genv_symb (fold_left (Genv.add_global (V:=unit)) defs ge2).
Proof.
  induction defs as [| def defs].
  - intros ge1 ge2 GN GS.
    cbn. auto.
  - intros ge1 ge2 GN GS.
    cbn. apply IHdefs.
    + unfold Genv.add_global; cbn.
      congruence.
    + unfold Genv.add_global; cbn.    
      rewrite <- transf_globdef_pres_id. 
      congruence.
Qed.


Lemma genv_find_funct_ptr_add_global_pres: forall def ge1 ge2 b,
  Genv.find_funct_ptr ge1 b = Genv.find_funct_ptr ge2 b ->
  Genv.find_funct_ptr (Genv.add_global ge1 (transf_globdef def)) b =
  Genv.find_funct_ptr (Genv.add_global ge2 def) b.
Proof.
  intros def ge1 ge2 b FPTR.
  Admitted.


Lemma genv_find_funct_ptr_pres: forall defs (ge1 ge2: Genv.t fundef unit) b,
    Genv.find_funct_ptr ge1 b = Genv.find_funct_ptr ge2 b ->
    Genv.find_funct_ptr (fold_left (Genv.add_global (V:=unit)) (map transf_globdef defs) ge1) b =
    Genv.find_funct_ptr (fold_left (Genv.add_global (V:=unit)) defs ge2) b.
Proof.
  induction defs as [| def defs].
  - intros ge1 ge2 b FPTR.
    cbn. congruence.
  - intros ge1 ge2 b FPTR.
    cbn. apply IHdefs.
    apply genv_find_funct_ptr_add_global_pres; auto.
Qed.




Definition match_prog (p tp:Asm.program) :=
  tp = transf_program p.

Lemma transf_program_match:
  forall p tp, transf_program p = tp -> match_prog p tp.
Proof.
  intros. subst. red. 
  auto.
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
|match_states_intro m m' rs:
   Mem.extends m m' ->
   match_states (Asm.State rs m) (Asm.State rs m').

Lemma find_symbol_transf: forall s,
    Genv.find_symbol tge s =
    Genv.find_symbol ge s.
Proof.
  red in TRANSF. unfold transf_program in TRANSF.
  subst. cbn.
  unfold Genv.globalenv, Genv.add_globals.
  unfold Genv.find_symbol. 
  intros. f_equal.
  apply genv_symb_pres.
  reflexivity.
  reflexivity.
Qed.

Lemma find_funct_ptr_transf: forall b,
    Genv.find_funct_ptr tge b =
    Genv.find_funct_ptr ge b.
Proof.
  red in TRANSF. unfold transf_program in TRANSF.
  subst. cbn.
  intros. unfold ge. unfold Genv.globalenv.
  unfold Genv.add_globals.
  apply genv_find_funct_ptr_pres.
  reflexivity.
Qed.

Lemma senv_equiv: Senv.equiv ge tge.
Proof.
  red in TRANSF. unfold ge, tge.
  subst.
  red. split; cbn.
Admitted.

Lemma init_mem_transf: forall m,
    Genv.init_mem prog = Some m ->
    exists m', Genv.init_mem tprog = Some m' /\ Mem.extends m m'.
Admitted.

Lemma initial_state_extends: forall m m' rs st prog prog',
    (forall b, Genv.find_symbol (Genv.globalenv prog) b = Genv.find_symbol (Genv.globalenv prog') b) ->
    Mem.extends m m' ->
    initial_state_gen prog rs m st ->
    exists st', initial_state_gen prog' rs m' st' /\ match_states st st'.
Admitted.

Theorem step_simulation:
  forall S1 t S2, step ge S1 t S2 ->
                  forall S1' (MS: match_states S1 S1'),
                    (exists S2', step tge S1' t S2' /\ match_states S2 S2').
Proof.
Admitted.

Lemma transf_initial_states:
  forall st1 rs, initial_state prog rs st1 ->
         exists st2, initial_state tprog rs st2 /\ match_states st1 st2.
Proof.
  intros st1 rs HInit.
  inv HInit.
  generalize (init_mem_transf _ H).
  intros (m' & INIT & EXT).
  assert (exists st', initial_state_gen tprog rs m' st' /\ match_states st1 st') as IS.
  { apply initial_state_extends with m prog; eauto.
    intros. rewrite find_symbol_transf. auto. 
  }
  destruct IS as (st1' & IS & MS).
  exists st1'. split; eauto.
  econstructor; eauto.
Qed.


Lemma transf_final_states:
  forall st1 st2 r,
  match_states st1 st2 -> final_state st1 r -> final_state st2 r.
Proof.
  intros st1 st2 r MS HFinal.
  inv HFinal.
  inv MS.
  econstructor; eauto.
Qed.


Lemma transf_program_correct:
  forall rs, forward_simulation (semantics prog rs) (semantics tprog rs).
Proof.
  intro rs.
  apply forward_simulation_step with match_states.
  + intros id. unfold match_prog in TRANSF.
    generalize senv_equiv. intros SENV_EQ.
    red in SENV_EQ.
    destruct SENV_EQ as (S1 & S2 & S3 & S4). auto.
  + simpl. intros s1 Hinit.
    exploit transf_initial_states; eauto.
  + simpl. intros s1 s2 r MS HFinal. eapply transf_final_states; eauto.
  + simpl. intros s1 t s1' STEP s2 MS.
    edestruct step_simulation as (STEP' & MS' ); eauto.
Qed.
  

End PRESERVATION.
