Require Import LogicalRelations.
Require Import Linking.
Require Import GameSemantics.
Require Import Composition.
Require Import Values.
Require Import LanguageInterface.
Require Import AST.
Require Import Globalenvs.
Require Import Asm.
Require Import RTS.
Require Import ModuleSemantics.
Require Import Smallstep.

Definition asm p : modsem (li_asm -o li_asm) :=
  Behavior.of (Asm.semantics p).

Require Import Maps.
Require Import List.

Section HCOMP.
  Context (p1 p2 p: Asm.program) (Hp: link p1 p2 = Some p).
  Let L1 := Asm.semantics p1.
  Let L2 := Asm.semantics p2.
  Let L := Asm.semantics p.
  Let L12 := HComp.semantics (symbolenv L) L1 L2.

  Inductive res_state_rel {A B} (R : rel A B) : rel (@Res.state A) (@Res.state B) :=
    | res_running_rel:
        Monotonic Res.running (R ++> res_state_rel R)
    | res_resumed_rel:
        Monotonic Res.resumed (set_le R ++> res_state_rel R).

  Inductive match_fc_states : rel FComp.state (state L) :=
    | match_fc_states_l s1 :
        match_fc_states
          (FComp.running (inl s1) (FComp.inrk (initial_state L2)))
          s1
    | match_fc_states_r s2 :
        match_fc_states
          (FComp.running (inr s2) (FComp.inlk (initial_state L1)))
          s2.

  Inductive match_states : rel (state L12) (state L) :=
    | match_states_running s s' :
        match_fc_states s s' ->
        match_states (Res.running s) s'
    | match_states_resumed (S: FComp.state -> Prop) s' :
        (forall s, S s -> match_fc_states s s') ->
        match_states (Res.resumed S) s'.

  Inductive link_cases : bool -> bool -> bool -> Prop :=
    | lc_none : link_cases false false false
    | lc_left : link_cases true false true
    | lc_right : link_cases false true true.

  Lemma query_is_internal_cases q:
    link_cases
      (query_is_internal li_asm (Genv.globalenv p1) q)
      (query_is_internal li_asm (Genv.globalenv p2) q)
      (query_is_internal li_asm (Genv.globalenv p) q).
  Proof.
  Admitted.

  Lemma internal_hcomp_l q :
    query_is_internal li_asm (Genv.globalenv p1) q = true ->
    query_is_internal li_asm (Genv.globalenv p) q = true.
  Admitted.

  Lemma internal_hcomp_r q :
    query_is_internal li_asm (Genv.globalenv p2) q = true ->
    query_is_internal li_asm (Genv.globalenv p) q = true.
  Admitted.

  Lemma internal_hcomp_inv q :
    query_is_internal li_asm (Genv.globalenv p) q = true ->
    query_is_internal li_asm (Genv.globalenv p2) q = true \/
    query_is_internal li_asm (Genv.globalenv p2) q = true.
  Admitted.

  Lemma asm_hcomp_fsim_cont_l :
    fsim_match_cont cc_id (fun _ => match_states) tt
      (Res.liftk (FComp.liftk (FComp.inlk (initial_state L1))
                              (FComp.inrk (initial_state L2))))
      (simple_initial_state Asm.initial_state (Genv.globalenv p)).
  Proof.
    intros [] [[] | q] _ [].
    unfold Res.liftk, FComp.liftk, FComp.inlk, FComp.inrk.
    cbn -[query_is_internal]. unfold simple_dom.
    destruct (query_is_internal_cases q); constructor;
    intros _ [_ [s Hs]]; inversion Hs as [x]; clear Hs; subst;
    exists x; split; auto; repeat constructor.
  Qed.

  Lemma asm_hcomp_fsim_cont_r :
    fsim_match_cont cc_id (fun _ => match_states) tt
      (Res.liftk (FComp.liftk (FComp.inrk (initial_state L2))
                              (FComp.inlk (initial_state L1))))
      (simple_initial_state Asm.initial_state (Genv.globalenv p)).
  Proof.
    intros [] [[] | q] _ [].
    unfold Res.liftk, FComp.liftk, FComp.inlk, FComp.inrk.
    cbn -[query_is_internal]. unfold simple_dom.
    destruct (query_is_internal_cases q); constructor;
    intros _ [_ [s Hs]]; inversion Hs as [x]; clear Hs; subst;
    exists x; split; auto; repeat constructor.
  Qed.

  Axiom external_call_empty :
    forall ef ge vargs m t vres m',
      ~ Events.external_call ef ge vargs m t vres m'.

  Lemma asm_hcomp_fsim :
    forward_simulation cc_id (HComp.semantics (symbolenv L) L1 L2) L.
  Proof.
    apply forward_simulation_step with (fun _ => match_states); simpl.
    - reflexivity.
    - apply asm_hcomp_fsim_cont_l.
    - intros _ s12 s r12 k12 Hs H;
      destruct H as  [s12 r12 k12 Hk12 Hr];
      destruct Hk12 as [si r ki kj Hki | si r ki kj Hki];
      destruct Hki as [si Hsi];
      inversion Hs; clear Hs; subst;
      inversion H0; clear H0; subst;
      exists tt, (inl s), (simple_initial_state Asm.initial_state (Genv.globalenv p));
      intuition auto using asm_hcomp_fsim_cont_l, asm_hcomp_fsim_cont_r;
      constructor;
      simpl in Hr; unfold FComp.liftk, FComp.inlk, FComp.inrk in Hr;
      unfold simple_initial_state, simple_dom in Hr;
      destruct (query_is_internal_cases s); simpl in Hr; try congruence.
    - intros _ s12 t s12' Hs12' s Hs.
      destruct Hs12' as [s12 t s12' Hs12' | s12 r12 k12 S12 Hk12 Hq | ].
      + (* internal step *)
        destruct Hs12' as  [si t si' kj Hsi' | si t si' kj Hsi']; simpl in *.
      * inversion Hs; clear Hs; subst.
        destruct Hsi'.
        -- admit.
        -- admit.
        -- eelim external_call_empty; eauto.
      * admit.
      + (* internal switching *) 
        simpl in *.
        destruct Hk12 as [si r ki k' Hki | si r ki k' Hki]; simpl in *.
      * destruct Hki as [si Hsi]; cbn -[li_asm] in Hq.
        inversion Hs; clear Hs; subst.
        inversion H0; clear H0; subst.
        unfold FComp.liftk in Hq.
        unfold FComp.inlk at 1, FComp.inrk at 1 3 in Hq.
        unfold simple_initial_state at 1 2 4, simple_dom in Hq.
        destruct (query_is_internal_cases s); simpl in Hq; try congruence.
        inversion Hq; clear Hq; subst.
        exists s. split.
        -- admit. (* measured simulation *)
        -- constructor.
           intros x [y [z Hz]].
           destruct Hz.
           constructor.
      * admit.
      + (* resuming after internal switching *)
        inversion Hs; clear Hs; subst.
        specialize (H1 s0 H).
        exists s. split.
        -- admit. (* measured simulation *)
        -- constructor; auto.
        (* Need measured simulation -- can use whether internal matches
                  currently executing component as measure *)
  Admitted.
End HCOMP.
