(* *******************  *)
(* Author: Yuting Wang  *)
(* Date:   Oct 30, 2019 *)
(* *******************  *)

(** * Preservation of semantics under the permutation of definitions for RealAsm *)
Require Import Coqlib Errors.
Require Import Integers Floats AST.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import LocalLib.
Require Import Permutation.
Require Import Asm RealAsm.
Require Import AsmInject.

(** matching modulo the permutation of definitions *)

Definition match_prog {F V} (p tp: AST.program F V) :=
  Permutation (prog_defs p) (prog_defs tp) 
  /\ prog_main p = prog_main tp
  /\ prog_public p = prog_public tp.

Lemma transf_program_match:
  forall F V (p: AST.program F V), match_prog p p.
Proof.
  intros. red. 
  repeat (split; auto).
Qed.

(** Preservation of semantics under permutation *)
Section PRESERVATION.

Existing Instance inject_perm_all.
Context `{external_calls_prf: ExternalCalls}.

Local Existing Instance mem_accessors_default.


Variable prog: Asm.program.
Variable tprog: Asm.program.
Hypothesis TRANSF: match_prog prog tprog.

Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.


Record match_inj (j: meminj) : Type :=
  {
    (** Preservation of finding of global symbols *)
    agree_find_symbol:
      forall id b,
        Genv.find_symbol ge id = Some b ->
        exists b', Genv.find_symbol tge id = Some b' /\
              j b = Some (b', 0);

    (** Preservation of finding of external functions *)
    agree_find_funct_ptr:
      forall b f ofs b',
        Genv.find_funct_ptr ge b = Some f ->
        j b = Some (b', ofs) ->
        Genv.find_funct_ptr tge b' = Some f;
  }.

Inductive match_states : Asm.state -> Asm.state -> Prop :=
|match_states_intro: forall j m m' rs rs'
   (MINJ: Mem.inject j (def_frame_inj m) m m')
   (RSINJ: regset_inject j rs rs')
   (MATCH_INJ: match_inj j) ,
   match_states (Asm.State rs m) (Asm.State rs' m').

Definition shift_inj n (j: positive -> option positive) : positive -> option positive :=
  fun b => 
    if Pos.leb b n then None
    else match j (Pos.sub b n) with
         | None => None
         | Some m => Some (Pos.add n m)
         end.

(* Eval compute in (Pos.sub 1%positive 3%positive). *)

(* Fixpoint perm_inj_match {A} (l1 l2: list A) (pm: Permutation l1 l2) (j: positive -> option positive) : Prop := *)
(*   match pm with *)
(*   | perm_nil => forall b, j b = Some b *)
(*   | perm_skip x l1' l2' pm' =>  *)
(*     exists j', perm_inj_match l1' l2' pm' j' /\ *)
(*           fun b => if zeq b 0 then 0 else  *)
(*             shift_inj 1 j' b *)
(*   | perm_swap x y l => *)
(*     fun b => if zeq b 0 then 1 *)
(*           else if zeq b 1 then 0 *)
(*                else b *)
(*   | perm_trans l l' l'' pm1 pm2 => *)
(*     let j1 := perm_inj_fun l l' pm1 in *)
(*     let j2 := perm_inj_fun l' l'' pm2 in *)
(*     fun b => j2 (j1 b) *)
(*   end. *)
    

Lemma find_symbol_pres_some: forall id b, 
    Genv.find_symbol ge id = Some b ->
    exists b', Genv.find_symbol tge id = Some b'.
Admitted.

Lemma find_symbol_pres_none: forall id, 
    Genv.find_symbol ge id = None ->
    Genv.find_symbol tge id = None.
Admitted.


Theorem step_simulation:
  forall S1 t S2, step ge S1 t S2 ->
                  forall S1' (MS: match_states S1 S1'),
                    (exists S2', step tge S1' t S2' /\ match_states S2 S2').
Proof.
(*   destruct 1; intros; inv MS. *)
  
(*   - (* Internal Step *) *)
(*     exploit exec_instr_simulation; eauto. *)
(*     intros (m2' & rs2' & EXEC & EXT & RS & STK). *)
(*     exists (State rs2' m2'). split; [|constructor; auto]. *)
(*     eapply exec_step_internal; eauto. *)
(*     red in H8. generalize (H8 PC). rewrite H. *)
(*     inversion 1. eauto. *)
(*     rewrite find_funct_ptr_transf. auto. *)
  
(*   - (* Builtin step *) *)
(*     exploit eval_builtin_args_lessdef''; eauto. *)
(*     intros (vargs' & EB & VLE). *)
(*     exploit external_call_mem_extends; eauto. *)
(*     intros (vres' & m2' & EC & VLER & EXT & UCHG). *)
(*     eexists. split. *)
(*     eapply exec_step_builtin; eauto. *)
(*     red in H10. generalize (H10 PC). *)
(*     rewrite H. inversion 1. eauto. *)
(*     rewrite find_funct_ptr_transf. auto. *)
(*     eapply eval_builtin_args_preserved with (ge1 := ge); eauto. *)
(*     intros. rewrite find_symbol_transf. auto. *)
(*     eapply external_call_symbols_preserved; eauto. exact senv_equiv. *)
(*     constructor; eauto. *)
(*     erewrite <- (external_call_stack_blocks _ _ _ m'0 _ _ m2'); eauto. *)
(*     erewrite <- (external_call_stack_blocks _ _ _ m _ _ m'); eauto. *)

(*   - (* External Step *) *)
(*     edestruct extcall_arguments_match as (args' & EXTARGS & VLE). *)
(*     Focus 3. exact H1. *)
(*     instantiate (1:= rs'0 # RSP <- (Val.offset_ptr (rs'0 RSP) (Ptrofs.repr (size_chunk Mptr)))). *)
(*     eapply regset_lessdef_pregset; eauto. *)
(*     eauto. *)
(*     exploit external_call_mem_extends; eauto. *)
(*     intros (vres' & m2' & EXTCALL & VLER & EXT2 & CHG). *)
(*     eexists. split. *)
(*     eapply exec_step_external; eauto. *)
(*     red in H9. generalize (H9 PC). rewrite H. *)
(*     inversion 1. eauto. *)
(*     rewrite find_funct_ptr_transf. auto. *)
(*     red in H9. generalize (H9 RSP). inversion 1; congruence. *)
(*     edestruct Mem.loadv_extends as (ra' & LV & VLRA).  *)
(*     exact H7. exact LOADRA. red in H9. eauto. *)
(*     inv VLRA; congruence. *)
(*     red in H9. generalize (H9 RSP). *)
(*     intros VLRSP. inv VLRSP; congruence. *)
(*     apply external_call_symbols_preserved with ge; eauto. *)
(*     exact senv_equiv. *)
(*     constructor; auto. *)
(*     erewrite <- (external_call_stack_blocks _ _ _ m'0 _ _ m2'); eauto. *)
(*     erewrite <- (external_call_stack_blocks _ _ _ m _ _ m'); eauto. *)
(*     (** Regset lessdef *) *)
(*     eapply regset_lessdef_pregset; eauto. *)
(*     eapply regset_lessdef_pregset; eauto. *)
(* Qed. *)
Admitted.


Lemma init_mem_transf: forall m,
    Genv.init_mem prog = Some m ->
    exists m' j, Genv.init_mem tprog = Some m' /\ Mem.inject j (def_frame_inj m) m m'.
Proof.
(*   unfold Genv.init_mem. *)
(*   intros m ALLOC. *)
(*   red in TRANSF. unfold transf_program in TRANSF. *)
(*   replace (prog_defs tprog) with (map transf_globdef (prog_defs prog)). *)
(*   Focus 2. rewrite TRANSF. cbn. auto. *)
(*   apply alloc_globals_extends with ge Mem.empty; eauto. *)
(*   intros. rewrite find_symbol_transf. auto. *)
(*   eapply Mem.extends_refl. *)
(* Qed. *)
Admitted.

(* Lemma initial_state_inject: forall m m' rs st prog prog', *)
(*     (forall b, Genv.find_symbol (Genv.globalenv prog) b = Genv.find_symbol (Genv.globalenv prog') b) -> *)
(*     prog_main prog = prog_main prog' -> *)
(*     Mem.stack m = nil -> *)
(*     Mem.stack m' = nil -> *)
(*     Mem.inject j m m' -> *)
(*     initial_state_gen prog rs m st -> *)
(*     exists st', initial_state_gen prog' rs m' st' /\ match_states st st'. *)
(* Proof. *)
(*   intros m m' rs st prog0 prog' FS MAIN ISNIL ISNIL' EXT IS. *)
(*   inv IS. *)
(*   assert (exists m1' : mem, Mem.alloc (Mem.push_new_stage m') 0  *)
(*                                  (Mem.stack_limit + align (size_chunk Mptr) 8) = (m1', bstack) *)
(*                        /\ Mem.extends m1 m1') as MALLOC'. *)
(*   { eapply Mem.alloc_extends; eauto. *)
(*     eapply Mem.extends_push; eauto.  *)
(*     omega. omega. *)
(*   } *)
(*   destruct MALLOC' as (m1' & MALLOC' & EXT1). *)
(*   generalize (Mem.alloc_stack_blocks _ _ _ _ _ MALLOC). *)
(*   intros ISNIL1.  *)
(*   rewrite Mem.push_new_stage_stack in ISNIL1. *)
(*   rewrite ISNIL in ISNIL1. *)
(*   generalize (Mem.alloc_stack_blocks _ _ _ _ _ MALLOC'). *)
(*   intros ISNIL1'.  *)
(*   rewrite Mem.push_new_stage_stack in ISNIL1'. *)
(*   rewrite ISNIL' in ISNIL1'. *)
(*   assert (inject_perm_condition Freeable) as IPF. *)
(*   { red. cbn. auto. } *)
(*   generalize (Mem.drop_extends _ _ _ _ _ _ _ EXT1 IPF MDROP). *)
(*   intros (m2' & MDROP' & EXT2). *)
(*   generalize (Mem.drop_perm_stack _ _ _ _ _ _ MDROP). *)
(*   intros ISNIL2. rewrite ISNIL1 in ISNIL2. *)
(*   generalize (Mem.drop_perm_stack _ _ _ _ _ _ MDROP'). *)
(*   intros ISNIL2'. rewrite ISNIL1' in ISNIL2'. *)
(*   assert (exists m3', Mem.record_stack_blocks  *)
(*                    m2' (make_singleton_frame_adt' bstack RawAsm.frame_info_mono 0) = Some m3' /\ Mem.extends m3 m3')  *)
(*     as MRSB'. *)
(*   {  *)
(*     eapply Mem.record_stack_blocks_extends; eauto. *)
(*     * rewrite ISNIL2'. auto. *)
(*     * red. unfold make_singleton_frame_adt'. simpl. *)
(*       intros b fi o k p BEQ PERM. inv BEQ; try contradiction. *)
(*       inv H0. unfold RawAsm.frame_info_mono. simpl. *)
(*       erewrite drop_perm_perm in PERM; eauto. destruct PERM. *)
(*       eapply Mem.perm_alloc_3; eauto. *)
(*     * red. repeat rewrite_stack_blocks. constructor. auto. *)
(*     * repeat rewrite_stack_blocks. *)
(*       rewrite ISNIL, ISNIL'. omega. *)
(*   }  *)
(*   destruct MRSB' as (m3' & MRSB' & EXT3). *)
(*   generalize (Mem.record_stack_blocks_stack _ _ _ _ _ MRSB ISNIL2). *)
(*   intros ISNIL3. *)
(*   generalize (Mem.record_stack_blocks_stack _ _ _ _ _ MRSB' ISNIL2'). *)
(*   intros ISNIL3'. *)

(*   assert (exists m4', Mem.storev Mptr m3'  *)
(*                            (Vptr bstack (Ptrofs.repr (Mem.stack_limit + align (size_chunk Mptr) 8 - size_chunk Mptr))) Vnullptr = Some m4'  *)
(*                 /\ Mem.extends m4 m4') as STORE_RETADDR'. *)
(*   { eapply Mem.storev_extends; eauto. } *)
(*   destruct STORE_RETADDR' as (m4' & STORE_RETADDR' & EXT4). *)
(*   generalize (Mem.storev_stack _ _ _ _ _ STORE_RETADDR). *)
(*   intros ISNIL4. rewrite ISNIL3 in ISNIL4. *)
(*   generalize (Mem.storev_stack _ _ _ _ _ STORE_RETADDR'). *)
(*   intros ISNIL4'. rewrite ISNIL3' in ISNIL4'. *)
(*   exists (State rs0 m4'). split. *)
(*   - econstructor; eauto. *)
(*     rewrite <- FS. rewrite <- MAIN. auto. *)
(*   - eapply match_states_intro; eauto. congruence. *)
(*     apply regset_lessdef_refl. *)
(* Qed. *)

Lemma transf_initial_states:
  forall st1 rs, initial_state prog rs st1 ->
         exists st2, initial_state tprog rs st2 /\ match_states st1 st2.
Proof.
(*   intros st1 rs HInit. *)
(*   inv HInit. *)
(*   generalize (init_mem_transf _ H). *)
(*   intros (m' & j & INIT & MINJ). *)
(*   assert (exists st', initial_state_gen tprog rs m' st' /\ match_states st1 st') as IS. *)
(*   { apply initial_state_extends with m prog; eauto. *)
(*     intros. rewrite find_symbol_transf. auto. *)
(*     rewrite prog_main_eq. auto. *)
(*     erewrite Genv.init_mem_stack; eauto. *)
(*     erewrite Genv.init_mem_stack; eauto. *)
(*   } *)
(*   destruct IS as (st1' & IS & MS). *)
(*   exists st1'. split; eauto. *)
(*   econstructor; eauto. *)
(* Qed. *)
Admitted.


Lemma transf_final_states:
  forall st1 st2 r,
  match_states st1 st2 -> final_state st1 r -> final_state st2 r.
Proof.
  intros st1 st2 r MS HFinal.
  inv HFinal.
  inv MS.
  econstructor; eauto.
  red in RSINJ. generalize (RSINJ PC).
  rewrite H. inversion 1. auto.
  red in RSINJ. generalize (RSINJ RAX).
  rewrite H0. inversion 1. subst. auto.
Qed.



Theorem transf_program_correct: forall rs,
  forward_simulation (RealAsm.semantics prog rs)
                     (RealAsm.semantics tprog rs).
Proof.
  intro rs.
  apply forward_simulation_step with match_states.
  - intros id. unfold match_prog in TRANSF.
    decompose [and] TRANSF.
    cbn.
    unfold Genv.public_symbol.
    symmetry.
    destr.
    + exploit find_symbol_pres_some; eauto.
      intros (b' & FSYM).
      unfold tge in FSYM.
      rewrite FSYM. 
      unfold Genv.globalenv.
      repeat rewrite Genv.genv_public_add_globals. 
      rewrite <- H2. auto.
    + exploit find_symbol_pres_none; eauto.
      intros FSYM. 
      unfold tge in FSYM. rewrite FSYM. auto.
  - simpl. intros s1 Hinit.
    exploit transf_initial_states; eauto.
  - simpl. intros s1 s2 r MS HFinal. eapply transf_final_states; eauto.
  - simpl. intros s1 t s1' STEP s2 MS.
    edestruct step_simulation as (STEP' & MS' ); eauto.
Qed.
  


End PRESERVATION.
