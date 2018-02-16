(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Tools for small-step operational semantics *)

(** This module defines generic operations and theorems over
  the one-step transition relations that are used to specify
  operational semantics in small-step style. *)

Require Import Relations.
Require Import Wellfounded.
Require Import Coqlib.
Require Import Events.
Require Import Globalenvs.
Require Import Integers.
Require Export LanguageInterface.

Set Implicit Arguments.

(** * Closures of transitions relations *)

Section CLOSURES.

Variable genv: Type.
Variable state: Type.

(** A one-step transition relation has the following signature.
  It is parameterized by a global environment, which does not
  change during the transition.  It relates the initial state
  of the transition with its final state.  The [trace] parameter
  captures the observable events possibly generated during the
  transition. *)

Variable step: genv -> state -> trace -> state -> Prop.

(** No transitions: stuck state *)

Definition nostep (ge: genv) (s: state) : Prop :=
  forall t s', ~(step ge s t s').

(** Zero, one or several transitions.  Also known as Kleene closure,
    or reflexive transitive closure. *)

Inductive star (ge: genv): state -> trace -> state -> Prop :=
  | star_refl: forall s,
      star ge s E0 s
  | star_step: forall s1 t1 s2 t2 s3 t,
      step ge s1 t1 s2 -> star ge s2 t2 s3 -> t = t1 ** t2 ->
      star ge s1 t s3.

Lemma star_one:
  forall ge s1 t s2, step ge s1 t s2 -> star ge s1 t s2.
Proof.
  intros. eapply star_step; eauto. apply star_refl. traceEq.
Qed.

Lemma star_two:
  forall ge s1 t1 s2 t2 s3 t,
  step ge s1 t1 s2 -> step ge s2 t2 s3 -> t = t1 ** t2 ->
  star ge s1 t s3.
Proof.
  intros. eapply star_step; eauto. apply star_one; auto.
Qed.

Lemma star_three:
  forall ge s1 t1 s2 t2 s3 t3 s4 t,
  step ge s1 t1 s2 -> step ge s2 t2 s3 -> step ge s3 t3 s4 -> t = t1 ** t2 ** t3 ->
  star ge s1 t s4.
Proof.
  intros. eapply star_step; eauto. eapply star_two; eauto.
Qed.

Lemma star_four:
  forall ge s1 t1 s2 t2 s3 t3 s4 t4 s5 t,
  step ge s1 t1 s2 -> step ge s2 t2 s3 ->
  step ge s3 t3 s4 -> step ge s4 t4 s5 -> t = t1 ** t2 ** t3 ** t4 ->
  star ge s1 t s5.
Proof.
  intros. eapply star_step; eauto. eapply star_three; eauto.
Qed.

Lemma star_trans:
  forall ge s1 t1 s2, star ge s1 t1 s2 ->
  forall t2 s3 t, star ge s2 t2 s3 -> t = t1 ** t2 -> star ge s1 t s3.
Proof.
  induction 1; intros.
  rewrite H0. simpl. auto.
  eapply star_step; eauto. traceEq.
Qed.

Lemma star_left:
  forall ge s1 t1 s2 t2 s3 t,
  step ge s1 t1 s2 -> star ge s2 t2 s3 -> t = t1 ** t2 ->
  star ge s1 t s3.
Proof star_step.

Lemma star_right:
  forall ge s1 t1 s2 t2 s3 t,
  star ge s1 t1 s2 -> step ge s2 t2 s3 -> t = t1 ** t2 ->
  star ge s1 t s3.
Proof.
  intros. eapply star_trans. eauto. apply star_one. eauto. auto.
Qed.

Lemma star_E0_ind:
  forall ge (P: state -> state -> Prop),
  (forall s, P s s) ->
  (forall s1 s2 s3, step ge s1 E0 s2 -> P s2 s3 -> P s1 s3) ->
  forall s1 s2, star ge s1 E0 s2 -> P s1 s2.
Proof.
  intros ge P BASE REC.
  assert (forall s1 t s2, star ge s1 t s2 -> t = E0 -> P s1 s2).
    induction 1; intros; subst.
    auto.
    destruct (Eapp_E0_inv _ _ H2). subst. eauto.
  eauto.
Qed.

(** One or several transitions.  Also known as the transitive closure. *)

Inductive plus (ge: genv): state -> trace -> state -> Prop :=
  | plus_left: forall s1 t1 s2 t2 s3 t,
      step ge s1 t1 s2 -> star ge s2 t2 s3 -> t = t1 ** t2 ->
      plus ge s1 t s3.

Lemma plus_one:
  forall ge s1 t s2,
  step ge s1 t s2 -> plus ge s1 t s2.
Proof.
  intros. econstructor; eauto. apply star_refl. traceEq.
Qed.

Lemma plus_two:
  forall ge s1 t1 s2 t2 s3 t,
  step ge s1 t1 s2 -> step ge s2 t2 s3 -> t = t1 ** t2 ->
  plus ge s1 t s3.
Proof.
  intros. eapply plus_left; eauto. apply star_one; auto.
Qed.

Lemma plus_three:
  forall ge s1 t1 s2 t2 s3 t3 s4 t,
  step ge s1 t1 s2 -> step ge s2 t2 s3 -> step ge s3 t3 s4 -> t = t1 ** t2 ** t3 ->
  plus ge s1 t s4.
Proof.
  intros. eapply plus_left; eauto. eapply star_two; eauto.
Qed.

Lemma plus_four:
  forall ge s1 t1 s2 t2 s3 t3 s4 t4 s5 t,
  step ge s1 t1 s2 -> step ge s2 t2 s3 ->
  step ge s3 t3 s4 -> step ge s4 t4 s5 -> t = t1 ** t2 ** t3 ** t4 ->
  plus ge s1 t s5.
Proof.
  intros. eapply plus_left; eauto. eapply star_three; eauto.
Qed.

Lemma plus_star:
  forall ge s1 t s2, plus ge s1 t s2 -> star ge s1 t s2.
Proof.
  intros. inversion H; subst.
  eapply star_step; eauto.
Qed.

Lemma plus_right:
  forall ge s1 t1 s2 t2 s3 t,
  star ge s1 t1 s2 -> step ge s2 t2 s3 -> t = t1 ** t2 ->
  plus ge s1 t s3.
Proof.
  intros. inversion H; subst. simpl. apply plus_one. auto.
  rewrite Eapp_assoc. eapply plus_left; eauto.
  eapply star_right; eauto.
Qed.

Lemma plus_left':
  forall ge s1 t1 s2 t2 s3 t,
  step ge s1 t1 s2 -> plus ge s2 t2 s3 -> t = t1 ** t2 ->
  plus ge s1 t s3.
Proof.
  intros. eapply plus_left; eauto. apply plus_star; auto.
Qed.

Lemma plus_right':
  forall ge s1 t1 s2 t2 s3 t,
  plus ge s1 t1 s2 -> step ge s2 t2 s3 -> t = t1 ** t2 ->
  plus ge s1 t s3.
Proof.
  intros. eapply plus_right; eauto. apply plus_star; auto.
Qed.

Lemma plus_star_trans:
  forall ge s1 t1 s2 t2 s3 t,
  plus ge s1 t1 s2 -> star ge s2 t2 s3 -> t = t1 ** t2 -> plus ge s1 t s3.
Proof.
  intros. inversion H; subst.
  econstructor; eauto. eapply star_trans; eauto.
  traceEq.
Qed.

Lemma star_plus_trans:
  forall ge s1 t1 s2 t2 s3 t,
  star ge s1 t1 s2 -> plus ge s2 t2 s3 -> t = t1 ** t2 -> plus ge s1 t s3.
Proof.
  intros. inversion H; subst.
  simpl; auto.
  rewrite Eapp_assoc.
  econstructor. eauto. eapply star_trans. eauto.
  apply plus_star. eauto. eauto. auto.
Qed.

Lemma plus_trans:
  forall ge s1 t1 s2 t2 s3 t,
  plus ge s1 t1 s2 -> plus ge s2 t2 s3 -> t = t1 ** t2 -> plus ge s1 t s3.
Proof.
  intros. eapply plus_star_trans. eauto. apply plus_star. eauto. auto.
Qed.

Lemma plus_inv:
  forall ge s1 t s2,
  plus ge s1 t s2 ->
  step ge s1 t s2 \/ exists s', exists t1, exists t2, step ge s1 t1 s' /\ plus ge s' t2 s2 /\ t = t1 ** t2.
Proof.
  intros. inversion H; subst. inversion H1; subst.
  left. rewrite E0_right. auto.
  right. exists s3; exists t1; exists (t0 ** t3); split. auto.
  split. econstructor; eauto. auto.
Qed.

Lemma star_inv:
  forall ge s1 t s2,
  star ge s1 t s2 ->
  (s2 = s1 /\ t = E0) \/ plus ge s1 t s2.
Proof.
  intros. inv H. left; auto. right; econstructor; eauto.
Qed.

Lemma plus_ind2:
  forall ge (P: state -> trace -> state -> Prop),
  (forall s1 t s2, step ge s1 t s2 -> P s1 t s2) ->
  (forall s1 t1 s2 t2 s3 t,
   step ge s1 t1 s2 -> plus ge s2 t2 s3 -> P s2 t2 s3 -> t = t1 ** t2 ->
   P s1 t s3) ->
  forall s1 t s2, plus ge s1 t s2 -> P s1 t s2.
Proof.
  intros ge P BASE IND.
  assert (forall s1 t s2, star ge s1 t s2 ->
         forall s0 t0, step ge s0 t0 s1 ->
         P s0 (t0 ** t) s2).
  induction 1; intros.
  rewrite E0_right. apply BASE; auto.
  eapply IND. eauto. econstructor; eauto. subst t. eapply IHstar; eauto. auto.

  intros. inv H0. eauto.
Qed.

Lemma plus_E0_ind:
  forall ge (P: state -> state -> Prop),
  (forall s1 s2 s3, step ge s1 E0 s2 -> star ge s2 E0 s3 -> P s1 s3) ->
  forall s1 s2, plus ge s1 E0 s2 -> P s1 s2.
Proof.
  intros. inv H0. exploit Eapp_E0_inv; eauto. intros [A B]; subst. eauto.
Qed.

(** Counted sequences of transitions *)

Inductive starN (ge: genv): nat -> state -> trace -> state -> Prop :=
  | starN_refl: forall s,
      starN ge O s E0 s
  | starN_step: forall n s t t1 s' t2 s'',
      step ge s t1 s' -> starN ge n s' t2 s'' -> t = t1 ** t2 ->
      starN ge (S n) s t s''.

Remark starN_star:
  forall ge n s t s', starN ge n s t s' -> star ge s t s'.
Proof.
  induction 1; econstructor; eauto.
Qed.

Remark star_starN:
  forall ge s t s', star ge s t s' -> exists n, starN ge n s t s'.
Proof.
  induction 1.
  exists O; constructor.
  destruct IHstar as [n P]. exists (S n); econstructor; eauto.
Qed.

(** Infinitely many transitions *)

CoInductive forever (ge: genv): state -> traceinf -> Prop :=
  | forever_intro: forall s1 t s2 T,
      step ge s1 t s2 -> forever ge s2 T ->
      forever ge s1 (t *** T).

Lemma star_forever:
  forall ge s1 t s2, star ge s1 t s2 ->
  forall T, forever ge s2 T ->
  forever ge s1 (t *** T).
Proof.
  induction 1; intros. simpl. auto.
  subst t. rewrite Eappinf_assoc.
  econstructor; eauto.
Qed.

(** An alternate, equivalent definition of [forever] that is useful
    for coinductive reasoning. *)

Variable A: Type.
Variable order: A -> A -> Prop.

CoInductive forever_N (ge: genv) : A -> state -> traceinf -> Prop :=
  | forever_N_star: forall s1 t s2 a1 a2 T1 T2,
      star ge s1 t s2 ->
      order a2 a1 ->
      forever_N ge a2 s2 T2 ->
      T1 = t *** T2 ->
      forever_N ge a1 s1 T1
  | forever_N_plus: forall s1 t s2 a1 a2 T1 T2,
      plus ge s1 t s2 ->
      forever_N ge a2 s2 T2 ->
      T1 = t *** T2 ->
      forever_N ge a1 s1 T1.

Hypothesis order_wf: well_founded order.

Lemma forever_N_inv:
  forall ge a s T,
  forever_N ge a s T ->
  exists t, exists s', exists a', exists li,
  step ge s t s' /\ forever_N ge a' s' li /\ T = t *** li.
Proof.
  intros ge a0. pattern a0. apply (well_founded_ind order_wf).
  intros. inv H0.
  (* star case *)
  inv H1.
  (* no transition *)
  change (E0 *** T2) with T2. apply H with a2. auto. auto.
  (* at least one transition *)
  exists t1; exists s0; exists x; exists (t2 *** T2).
  split. auto. split. eapply forever_N_star; eauto.
  apply Eappinf_assoc.
  (* plus case *)
  inv H1.
  exists t1; exists s0; exists a2; exists (t2 *** T2).
  split. auto.
  split. inv H3. auto.
  eapply forever_N_plus. econstructor; eauto. eauto. auto.
  apply Eappinf_assoc.
Qed.

Lemma forever_N_forever:
  forall ge a s T, forever_N ge a s T -> forever ge s T.
Proof.
  cofix COINDHYP; intros.
  destruct (forever_N_inv H) as [t [s' [a' [li [P [Q R]]]]]].
  rewrite R. apply forever_intro with s'. auto.
  apply COINDHYP with a'; auto.
Qed.

(** Yet another alternative definition of [forever]. *)

CoInductive forever_plus (ge: genv) : state -> traceinf -> Prop :=
  | forever_plus_intro: forall s1 t s2 T1 T2,
      plus ge s1 t s2 ->
      forever_plus ge s2 T2 ->
      T1 = t *** T2 ->
      forever_plus ge s1 T1.

Lemma forever_plus_inv:
  forall ge s T,
  forever_plus ge s T ->
  exists s', exists t, exists li,
  step ge s t s' /\ forever_plus ge s' li /\ T = t *** li.
Proof.
  intros. inv H. inv H0. exists s0; exists t1; exists (t2 *** T2).
  split. auto.
  split. exploit star_inv; eauto. intros [[P Q] | R].
    subst. simpl. auto. econstructor; eauto.
  traceEq.
Qed.

Lemma forever_plus_forever:
  forall ge s T, forever_plus ge s T -> forever ge s T.
Proof.
  cofix COINDHYP; intros.
  destruct (forever_plus_inv H) as [s' [t [li [P [Q R]]]]].
  subst. econstructor; eauto.
Qed.

(** Infinitely many silent transitions *)

CoInductive forever_silent (ge: genv): state -> Prop :=
  | forever_silent_intro: forall s1 s2,
      step ge s1 E0 s2 -> forever_silent ge s2 ->
      forever_silent ge s1.

(** An alternate definition. *)

CoInductive forever_silent_N (ge: genv) : A -> state -> Prop :=
  | forever_silent_N_star: forall s1 s2 a1 a2,
      star ge s1 E0 s2 ->
      order a2 a1 ->
      forever_silent_N ge a2 s2 ->
      forever_silent_N ge a1 s1
  | forever_silent_N_plus: forall s1 s2 a1 a2,
      plus ge s1 E0 s2 ->
      forever_silent_N ge a2 s2 ->
      forever_silent_N ge a1 s1.

Lemma forever_silent_N_inv:
  forall ge a s,
  forever_silent_N ge a s ->
  exists s', exists a',
  step ge s E0 s' /\ forever_silent_N ge a' s'.
Proof.
  intros ge a0. pattern a0. apply (well_founded_ind order_wf).
  intros. inv H0.
  (* star case *)
  inv H1.
  (* no transition *)
  apply H with a2. auto. auto.
  (* at least one transition *)
  exploit Eapp_E0_inv; eauto. intros [P Q]. subst.
  exists s0; exists x.
  split. auto. eapply forever_silent_N_star; eauto.
  (* plus case *)
  inv H1. exploit Eapp_E0_inv; eauto. intros [P Q]. subst.
  exists s0; exists a2.
  split. auto. inv H3. auto.
  eapply forever_silent_N_plus. econstructor; eauto. eauto.
Qed.

Lemma forever_silent_N_forever:
  forall ge a s, forever_silent_N ge a s -> forever_silent ge s.
Proof.
  cofix COINDHYP; intros.
  destruct (forever_silent_N_inv H) as [s' [a' [P Q]]].
  apply forever_silent_intro with s'. auto.
  apply COINDHYP with a'; auto.
Qed.

(** Infinitely many non-silent transitions *)

CoInductive forever_reactive (ge: genv): state -> traceinf -> Prop :=
  | forever_reactive_intro: forall s1 s2 t T,
      star ge s1 t s2 -> t <> E0 -> forever_reactive ge s2 T ->
      forever_reactive ge s1 (t *** T).

Lemma star_forever_reactive:
  forall ge s1 t s2 T,
  star ge s1 t s2 -> forever_reactive ge s2 T ->
  forever_reactive ge s1 (t *** T).
Proof.
  intros. inv H0. rewrite <- Eappinf_assoc. econstructor.
  eapply star_trans; eauto.
  red; intro. exploit Eapp_E0_inv; eauto. intros [P Q]. contradiction.
  auto.
Qed.

End CLOSURES.

(** * Transition semantics *)

(** The general form of a transition semantics. *)

Record semantics liA liB: Type := Semantics_gen {
  state: Type;
  genvtype: Type;
  step : genvtype -> state -> trace -> state -> Prop;
  initial_state: query liB -> state -> Prop;
  external: state -> query liA -> (reply liA -> state -> Prop) -> Prop;
  final_state: state -> reply liB -> Prop;
  globalenv: genvtype;
  symbolenv: Senv.t
}.

(** In most cases, [external] can be defined through two, independent
  [at_external] and [after_external] predicates as follows. However,
  for defining [proj_semantics] below in such a way that we can
  transform forward simulations into backward simulations, we will the
  full generality of [external] to ensure that the worlds used to
  project the query and replies are consistent. *)

Section MAKE_EXTERNAL.
  Context {state: Type} {liA: language_interface}.
  Context (at_external: state -> query liA -> Prop).
  Context (after_external: state -> reply liA -> state -> Prop).

  Inductive make_external:
    state -> query liA -> (reply liA -> state -> Prop) -> Prop :=
      | make_external_intro s q:
          at_external s q ->
          make_external s q (after_external s).
End MAKE_EXTERNAL.

(** The form used in earlier CompCert versions, for backward compatibility. *)

Definition Semantics liA liB {state funtype vartype: Type}
    (step: Genv.t funtype vartype -> state -> trace -> state -> Prop)
    (initial_state: query liB -> state -> Prop)
    (at_external: state -> query liA -> Prop)
    (after_external: state -> reply liA -> state -> Prop)
    (final_state: state -> reply liB -> Prop)
    (globalenv: Genv.t funtype vartype) :=
  {| state := state;
     genvtype := Genv.t funtype vartype;
     step := step;
     initial_state := initial_state;
     final_state := final_state;
     external := make_external at_external after_external;
     globalenv := globalenv;
     symbolenv := Genv.to_senv globalenv |}.

(** Handy notations. *)

Notation Step L := (step L (globalenv L)).
Notation Star L := (star (step L) (globalenv L)).
Notation Plus L := (plus (step L) (globalenv L)).
Notation Forever_silent L := (forever_silent (step L) (globalenv L)).
Notation Forever_reactive L := (forever_reactive (step L) (globalenv L)).
Notation Nostep L := (nostep (step L) (globalenv L)).

(** * Forward simulations between two transition semantics. *)

(** The general form of a forward simulation. *)

Section FORWARD_SIMULATION.
Context {liA1 liB1 liA2 liB2: language_interface}.
Context (ccA: callconv liA1 liA2).
Context (ccB: callconv liB1 liB2).

Record fsim_properties (L1: semantics liA1 liB1) (L2: semantics liA2 liB2)
                       (index: Type) (order: index -> index -> Prop)
                       (match_states: world ccB -> index -> state L1 -> state L2 -> Prop) : Prop := {
    fsim_order_wf: well_founded order;
    fsim_match_initial_states:
      forall w q1 q2, match_query ccB w q1 q2 ->
      forall s1, initial_state L1 q1 s1 ->
      exists i s2,
        initial_state L2 q2 s2 /\
        match_states w i s1 s2;
    fsim_match_external:
      forall w i s1 s2, match_states w i s1 s2 ->
      forall q1 after_external1, external L1 s1 q1 after_external1 ->
      exists wA q2 after_external2,
        match_query ccA wA q1 q2 /\
        external L2 s2 q2 after_external2 /\
        forall r1 r2 s1',
          match_reply ccA wA r1 r2 ->
          after_external1 r1 s1' ->
          exists j s2',
            after_external2 r2 s2' /\
            match_states w j s1' s2';
    fsim_match_final_states:
      forall w i s1 s2 r1,
        match_states w i s1 s2 ->
        final_state L1 s1 r1 ->
        exists r2,
          match_reply ccB w r1 r2 /\
          final_state L2 s2 r2;
    fsim_simulation:
      forall w s1 t s1', Step L1 s1 t s1' ->
      forall i s2, match_states w i s1 s2 ->
      exists i', exists s2',
         (Plus L2 s2 t s2' \/ (Star L2 s2 t s2' /\ order i' i))
      /\ match_states w i' s1' s2';
    fsim_public_preserved:
      forall id, Senv.public_symbol (symbolenv L2) id = Senv.public_symbol (symbolenv L1) id
  }.

Arguments fsim_properties: clear implicits.

Inductive forward_simulation (L1 L2: semantics _ _) : Prop :=
  Forward_simulation (index: Type)
                     (order: index -> index -> Prop)
                     (match_states: world ccB -> index -> state L1 -> state L2 -> Prop)
                     (props: fsim_properties L1 L2 index order match_states).

Arguments Forward_simulation {L1 L2 index} order match_states props.

(** An alternate form of the simulation diagram *)

Lemma fsim_simulation':
  forall L1 L2 index order match_states, fsim_properties L1 L2 index order match_states ->
  forall w i s1 t s1', Step L1 s1 t s1' ->
  forall s2, match_states w i s1 s2 ->
  (exists i', exists s2', Plus L2 s2 t s2' /\ match_states w i' s1' s2')
  \/ (exists i', order i' i /\ t = E0 /\ match_states w i' s1' s2).
Proof.
  intros. exploit fsim_simulation; eauto.
  intros [i' [s2' [A B]]]. intuition.
  left; exists i'; exists s2'; auto.
  inv H3.
  right; exists i'; auto.
  left; exists i'; exists s2'; split; auto. econstructor; eauto.
Qed.

(** ** Forward simulation diagrams. *)

(** Various simulation diagrams that imply forward simulation *)

Section FORWARD_SIMU_DIAGRAMS.

Variable L1: semantics liA1 liB1.
Variable L2: semantics liA2 liB2.

Hypothesis public_preserved:
  forall id, Senv.public_symbol (symbolenv L2) id = Senv.public_symbol (symbolenv L1) id.

Variable match_states: world ccB -> state L1 -> state L2 -> Prop.

Hypothesis match_initial_states:
  forall w q1 q2, match_query ccB w q1 q2 ->
  forall s1, initial_state L1 q1 s1 ->
  exists s2,
    initial_state L2 q2 s2 /\
    match_states w s1 s2.

Hypothesis match_external:
  forall w s1 s2 q1 after_external1,
  match_states w s1 s2 ->
  external L1 s1 q1 after_external1 ->
  exists wA q2 after_external2,
    match_query ccA wA q1 q2 /\
    external L2 s2 q2 after_external2 /\
    forall r1 r2 s1',
      match_reply ccA wA r1 r2 ->
      after_external1 r1 s1' ->
      exists s2',
        after_external2 r2 s2' /\
        match_states w s1' s2'.

Hypothesis match_final_states:
  forall w s1 s2 r1,
  match_states w s1 s2 ->
  final_state L1 s1 r1 ->
  exists r2,
    match_reply ccB w r1 r2 /\
    final_state L2 s2 r2.

(** Simulation when one transition in the first program
    corresponds to zero, one or several transitions in the second program.
    However, there is no stuttering: infinitely many transitions
    in the source program must correspond to infinitely many
    transitions in the second program. *)

Section SIMULATION_STAR_WF.

(** [order] is a well-founded ordering associated with states
  of the first semantics.  Stuttering steps must correspond
  to states that decrease w.r.t. [order]. *)

Variable order: state L1 -> state L1 -> Prop.
Hypothesis order_wf: well_founded order.

Hypothesis simulation:
  forall w s1 t s1', Step L1 s1 t s1' ->
  forall s2, match_states w s1 s2 ->
  exists s2',
  (Plus L2 s2 t s2' \/ (Star L2 s2 t s2' /\ order s1' s1))
  /\ match_states w s1' s2'.

Lemma forward_simulation_star_wf: forward_simulation L1 L2.
Proof.
  apply Forward_simulation with order (fun w idx s1 s2 => idx = s1 /\ match_states w s1 s2);
  constructor.
- auto.
- intros. exploit match_initial_states; eauto.
  intros [s2 [A B]].
  exists s1; exists s2; auto.
- intros. destruct H.
  edestruct match_external as (wA & q2 & ae2 & Hq & Hs2 & Hresume); eauto.
  exists wA, q2, ae2; intuition.
  edestruct Hresume as (s2' & Hs2' & Hs'); eauto.
- intros. destruct H.
  edestruct match_final_states as (r2 & Hr & Hs2); eauto.
- intros. destruct H0. subst i. exploit simulation; eauto. intros [s2' [A B]].
  exists s1'; exists s2'; intuition auto.
- auto.
Qed.

End SIMULATION_STAR_WF.

Section SIMULATION_STAR.

(** We now consider the case where we have a nonnegative integer measure
  associated with states of the first semantics.  It must decrease when we take
  a stuttering step. *)

Variable measure: state L1 -> nat.

Hypothesis simulation:
  forall w s1 t s1', Step L1 s1 t s1' ->
  forall s2, match_states w s1 s2 ->
  (exists s2', Plus L2 s2 t s2' /\ match_states w s1' s2')
  \/ (measure s1' < measure s1 /\ t = E0 /\ match_states w s1' s2)%nat.

Lemma forward_simulation_star: forward_simulation L1 L2.
Proof.
  apply forward_simulation_star_wf with (ltof _ measure).
  apply well_founded_ltof.
  intros. exploit simulation; eauto. intros [[s2' [A B]] | [A [B C]]].
  exists s2'; auto.
  exists s2; split. right; split. rewrite B. apply star_refl. auto. auto.
Qed.

End SIMULATION_STAR.

(** Simulation when one transition in the first program corresponds
    to one or several transitions in the second program. *)

Section SIMULATION_PLUS.

Hypothesis simulation:
  forall w s1 t s1', Step L1 s1 t s1' ->
  forall s2, match_states w s1 s2 ->
  exists s2', Plus L2 s2 t s2' /\ match_states w s1' s2'.

Lemma forward_simulation_plus: forward_simulation L1 L2.
Proof.
  apply forward_simulation_star with (measure := fun _ => O).
  intros. exploit simulation; eauto.
Qed.

End SIMULATION_PLUS.

(** Lock-step simulation: each transition in the first semantics
    corresponds to exactly one transition in the second semantics. *)

Section SIMULATION_STEP.

Hypothesis simulation:
  forall w s1 t s1', Step L1 s1 t s1' ->
  forall s2, match_states w s1 s2 ->
  exists s2', Step L2 s2 t s2' /\ match_states w s1' s2'.

Lemma forward_simulation_step: forward_simulation L1 L2.
Proof.
  apply forward_simulation_plus.
  intros. exploit simulation; eauto. intros [s2' [A B]].
  exists s2'; split; auto. apply plus_one; auto.
Qed.

End SIMULATION_STEP.

(** Simulation when one transition in the first program
    corresponds to zero or one transitions in the second program.
    However, there is no stuttering: infinitely many transitions
    in the source program must correspond to infinitely many
    transitions in the second program. *)

Section SIMULATION_OPT.

Variable measure: state L1 -> nat.

Hypothesis simulation:
  forall w s1 t s1', Step L1 s1 t s1' ->
  forall s2, match_states w s1 s2 ->
  (exists s2', Step L2 s2 t s2' /\ match_states w s1' s2')
  \/ (measure s1' < measure s1 /\ t = E0 /\ match_states w s1' s2)%nat.

Lemma forward_simulation_opt: forward_simulation L1 L2.
Proof.
  apply forward_simulation_star with measure.
  intros. exploit simulation; eauto. intros [[s2' [A B]] | [A [B C]]].
  left; exists s2'; split; auto. apply plus_one; auto.
  right; auto.
Qed.

End SIMULATION_OPT.

End FORWARD_SIMU_DIAGRAMS.

(** ** Forward simulation of transition sequences *)

Section SIMULATION_SEQUENCES.

Context {li1 li2} (cc: callconv li1 li2).
Context L1 L2 index order match_states (S: fsim_properties L1 L2 index order match_states).

Lemma simulation_star:
  forall w s1 t s1', Star L1 s1 t s1' ->
  forall i s2, match_states w i s1 s2 ->
  exists i', exists s2', Star L2 s2 t s2' /\ match_states w i' s1' s2'.
Proof.
  induction 1; intros.
  exists i; exists s2; split; auto. apply star_refl.
  exploit fsim_simulation; eauto. intros [i' [s2' [A B]]].
  exploit IHstar; eauto. intros [i'' [s2'' [C D]]].
  exists i''; exists s2''; split; auto. eapply star_trans; eauto.
  intuition auto. apply plus_star; auto.
Qed.

Lemma simulation_plus:
  forall w s1 t s1', Plus L1 s1 t s1' ->
  forall i s2, match_states w i s1 s2 ->
  (exists i', exists s2', Plus L2 s2 t s2' /\ match_states w i' s1' s2')
  \/ (exists i', clos_trans _ order i' i /\ t = E0 /\ match_states w i' s1' s2).
Proof.
  induction 1 using plus_ind2; intros.
(* base case *)
  exploit fsim_simulation'; eauto. intros [A | [i' A]].
  left; auto.
  right; exists i'; intuition.
(* inductive case *)
  exploit fsim_simulation'; eauto. intros [[i' [s2' [A B]]] | [i' [A [B C]]]].
  exploit simulation_star. apply plus_star; eauto. eauto.
  intros [i'' [s2'' [P Q]]].
  left; exists i''; exists s2''; split; auto. eapply plus_star_trans; eauto.
  exploit IHplus; eauto. intros [[i'' [s2'' [P Q]]] | [i'' [P [Q R]]]].
  subst. simpl. left; exists i''; exists s2''; auto.
  subst. simpl. right; exists i''; intuition auto.
  eapply t_trans; eauto. eapply t_step; eauto.
Qed.

Lemma simulation_forever_silent:
  forall w i s1 s2,
  Forever_silent L1 s1 -> match_states w i s1 s2 ->
  Forever_silent L2 s2.
Proof.
  assert (forall w i s1 s2,
          Forever_silent L1 s1 -> match_states w i s1 s2 ->
          forever_silent_N (step L2) order (globalenv L2) i s2).
    cofix COINDHYP; intros.
    inv H. destruct (fsim_simulation S _ _ _ _ H1 _ _ H0) as [i' [s2' [A B]]].
    destruct A as [C | [C D]].
    eapply forever_silent_N_plus; eauto.
    eapply forever_silent_N_star; eauto.
  intros. eapply forever_silent_N_forever; eauto. eapply fsim_order_wf; eauto.
Qed.

Lemma simulation_forever_reactive:
  forall w i s1 s2 T,
  Forever_reactive L1 s1 T -> match_states w i s1 s2 ->
  Forever_reactive L2 s2 T.
Proof.
  cofix COINDHYP; intros.
  inv H.
  edestruct simulation_star as [i' [st2' [A B]]]; eauto.
  econstructor; eauto.
Qed.

End SIMULATION_SEQUENCES.

End FORWARD_SIMULATION.

Arguments fsim_properties {liA1 liB1 liA2 liB2}.

(** ** Composing two forward simulations *)

Lemma compose_forward_simulations:
  forall {liA1 liB1 liA2 liB2 liA3 liB3},
  forall {ccA12 ccB12 ccA23 ccB23},
  forall L1 L2 L3,
    @forward_simulation liA1 liB1 liA2 liB2 ccA12 ccB12 L1 L2 ->
    @forward_simulation liA2 liB2 liA3 liB3 ccA23 ccB23 L2 L3 ->
    forward_simulation (cc_compose ccA12 ccA23) (cc_compose ccB12 ccB23) L1 L3.
Proof.
  intros until ccB23.
  intros L1 L2 L3 S12 S23.
  destruct S12 as [index order match_states props].
  destruct S23 as [index' order' match_states' props'].

  set (ff_index := (index' * index)%type).
  set (ff_order := lex_ord (clos_trans _ order') order).
  set (ff_match_states := fun w (i: ff_index) (s1: state L1) (s3: state L3) =>
                             exists s2, match_states (comp_fst w) (snd i) s1 s2 /\ match_states' (comp_snd w) (fst i) s2 s3).
  apply Forward_simulation with _ ff_order ff_match_states; constructor.
- (* well founded *)
  unfold ff_order. apply wf_lex_ord. apply wf_clos_trans.
  eapply fsim_order_wf; eauto. eapply fsim_order_wf; eauto.
- (* initial states *)
  subst ff_match_states. simpl.
  inv_compose_query.
  intros. subst.
  exploit (fsim_match_initial_states props); eauto. intros [i [s2 [A B]]].
  exploit (fsim_match_initial_states props'); eauto. intros [i' [s3 [C D]]].
  exists (i', i); exists s3; split; auto. exists s2; auto.
- (* external call *)
  intros. destruct H as [s3 [A B]].
  edestruct (fsim_match_external props) as (? & ? & ? & ? & ? & Hr); eauto.
  edestruct (fsim_match_external props') as (? & ? & ? & ? & ? & Hr'); eauto.
  edestruct (match_cc_compose ccA12 ccA23) as (w' & Hq & Hr12); eauto.
  eexists _, _, _. intuition; eauto.
  edestruct Hr12 as (r3 & ? & ?); eauto.
  edestruct Hr as (j & s2' & Hs2' & Hs12'); eauto.
  edestruct Hr' as (j' & s3' & Hs3' & Hs23'); eauto.
  exists (j', j), s3'. intuition.
  red. eauto.
- (* final states *)
  intros. destruct H as [s3 [A B]].
  edestruct (fsim_match_final_states props) as (r2 & ? & ?); eauto.
  edestruct (fsim_match_final_states props') as (r3 & ? & ?); eauto.
  eexists; split; eauto.
  eapply match_reply_cc_compose; eauto.
- (* simulation *)
  intros. destruct H0 as [s3 [A B]]. destruct i as [i2 i1]; simpl in *.
  exploit (fsim_simulation' props); eauto. intros [[i1' [s3' [C D]]] | [i1' [C [D E]]]].
+ (* L2 makes one or several steps. *)
  exploit (simulation_plus props'); eauto. intros [[i2' [s2' [P Q]]] | [i2' [P [Q R]]]].
* (* L3 makes one or several steps *)
  exists (i2', i1'); exists s2'; split. auto. exists s3'; auto.
* (* L3 makes no step *)
  exists (i2', i1'); exists s2; split.
  right; split. subst t; apply star_refl. red. left. auto.
  exists s3'; auto.
+ (* L2 makes no step *)
  exists (i2, i1'); exists s2; split.
  right; split. subst t; apply star_refl. red. right. auto.
  exists s3; auto.
- (* symbols *)
  intros. transitivity (Senv.public_symbol (symbolenv L2) id); eapply fsim_public_preserved; eauto.
Qed.

(** * Receptiveness and determinacy *)

Definition single_events {liA liB} (L: semantics liA liB) : Prop :=
  forall s t s', Step L s t s' -> (length t <= 1)%nat.

Record receptive {liA liB} (L: semantics liA liB) : Prop :=
  Receptive {
    sr_receptive: forall s t1 s1 t2,
      Step L s t1 s1 -> match_traces (symbolenv L) t1 t2 -> exists s2, Step L s t2 s2;
    sr_traces:
      single_events L
  }.

(** XXX: need to add external *)
Record determinate {liA liB} (L: semantics liA liB) : Prop :=
  Determinate {
    sd_determ: forall s t1 s1 t2 s2,
      Step L s t1 s1 -> Step L s t2 s2 ->
      match_traces (symbolenv L) t1 t2 /\ (t1 = t2 -> s1 = s2);
    sd_traces:
      single_events L;
    sd_initial_determ: forall q s1 s2,
      initial_state L q s1 -> initial_state L q s2 -> s1 = s2;
    sd_external_nostep: forall s q ae,
      external L s q ae -> Nostep L s;
    sd_external_determ: forall s q1 ae1 q2 ae2,
      external L s q1 ae1 ->
      external L s q2 ae2 ->
      q1 = q2 (* /\
      forall r, ae1 r s1 -> ae2 r s2 -> s1 = s2 *);
    sd_external_nofinal: forall s q ae r,
      external L s q ae ->
      ~ final_state L s r;
    sd_final_nostep: forall s r,
      final_state L s r -> Nostep L s;
    sd_final_determ: forall s r1 r2,
      final_state L s r1 -> final_state L s r2 -> r1 = r2
  }.

Section DETERMINACY.

Variable liA liB: language_interface.
Variable L: semantics liA liB.
Hypothesis DET: determinate L.

Lemma sd_determ_1:
  forall s t1 s1 t2 s2,
  Step L s t1 s1 -> Step L s t2 s2 -> match_traces (symbolenv L) t1 t2.
Proof.
  intros. eapply sd_determ; eauto.
Qed.

Lemma sd_determ_2:
  forall s t s1 s2,
  Step L s t s1 -> Step L s t s2 -> s1 = s2.
Proof.
  intros. eapply sd_determ; eauto.
Qed.

Lemma star_determinacy:
  forall s t s', Star L s t s' ->
  forall s'', Star L s t s'' -> Star L s' E0 s'' \/ Star L s'' E0 s'.
Proof.
  induction 1; intros.
  auto.
  inv H2.
  right. eapply star_step; eauto.
  exploit sd_determ_1. eexact H. eexact H3. intros MT.
  exploit (sd_traces DET). eexact H. intros L1.
  exploit (sd_traces DET). eexact H3. intros L2.
  assert (t1 = t0 /\ t2 = t3).
    destruct t1. inv MT. auto.
    destruct t1; simpl in L1; try omegaContradiction.
    destruct t0. inv MT. destruct t0; simpl in L2; try omegaContradiction.
    simpl in H5. split. congruence. congruence.
  destruct H1; subst.
  assert (s2 = s4) by (eapply sd_determ_2; eauto). subst s4.
  auto.
Qed.

End DETERMINACY.

(** * Projecting a transition semantics by a calling convention *)

Section PROJ.

Context {liA1 liA2} (ccA: callconv liA1 liA2).
Context {liB1 liB2} (ccB: callconv liB1 liB2).
Context (L: semantics liA1 liB1).

Definition proj_state: Type := world ccB * state L.

Inductive proj_step: genvtype L -> proj_state -> trace -> proj_state -> Prop :=
  proj_step_intro ge w s t s':
    step L ge s t s' ->
    proj_step ge (w, s) t (w, s').

Inductive proj_initial_state: query liB2 -> proj_state -> Prop :=
  proj_initial_state_intro w q1 q2 s:
    match_query ccB w q1 q2 ->
    initial_state L q1 s ->
    proj_initial_state q2 (w, s).

Inductive proj_after_external wA after_external: reply liA2 -> proj_state -> Prop :=
  proj_after_external_intro s' r1 r2 w:
    after_external r1 s' ->
    match_reply ccA wA r1 r2 ->
    proj_after_external wA after_external r2 (w, s').

Inductive proj_external: proj_state -> query liA2 -> (reply liA2 -> proj_state -> Prop) -> Prop :=
  proj_at_external_intro wA q1 q2 ae1 w s:
    match_query ccA wA q1 q2 ->
    external L s q1 ae1 ->
    proj_external (w, s) q2 (proj_after_external wA ae1).

Inductive proj_final_state: proj_state -> reply liB2 -> Prop :=
  proj_final_state_intro w s r1 r2:
    final_state L s r1 ->
    match_reply ccB w r1 r2 ->
    proj_final_state (w, s) r2.

Definition proj_semantics :=
  {|
    state := proj_state;
    genvtype := genvtype L;
    step := proj_step;
    initial_state := proj_initial_state;
    external := proj_external;
    final_state := proj_final_state;
    globalenv := globalenv L;
    symbolenv := symbolenv L;
  |}.

End PROJ.

Arguments proj_step {liA1 liB1 liB2}.
Arguments proj_initial_state {liA1 liB1 liB2}.
Arguments proj_after_external {liA1 liA2} ccA {liB1 liB2}.
Arguments proj_external {liA1 liA2} ccA {liB1 liB2}.
Arguments proj_final_state {liA1 liB1 liB2}.

(** * Backward simulations between two transition semantics. *)

Definition safe {liA liB} (L: semantics liA liB) (s: state L) : Prop :=
  forall s',
  Star L s E0 s' ->
  (exists r, final_state L s' r)
  \/ (exists q ae, external L s' q ae)
  \/ (exists t, exists s'', Step L s' t s'').

Lemma star_safe:
  forall {liA liB} (L: semantics liA liB) s s',
  Star L s E0 s' -> safe L s -> safe L s'.
Proof.
  intros; red; intros. apply H0. eapply star_trans; eauto.
Qed.

(** The general form of a backward simulation. *)

Record bsim_properties {liA liB} (L1 L2: semantics liA liB) (index: Type)
                       (order: index -> index -> Prop)
                       (match_states: index -> state L1 -> state L2 -> Prop) : Prop := {
    bsim_order_wf: well_founded order;
    bsim_initial_states_exist:
      forall q s1, initial_state L1 q s1 -> exists s2, initial_state L2 q s2;
    bsim_match_initial_states:
      forall q s1 s2, initial_state L1 q s1 -> initial_state L2 q s2 ->
      exists i, exists s1', initial_state L1 q s1' /\ match_states i s1' s2;
    bsim_match_external:
      forall i s1 s2, match_states i s1 s2 -> safe L1 s1 ->
      forall q after_external2, external L2 s2 q after_external2 ->
      exists s1' after_external1,
        Star L1 s1 E0 s1' /\
        external L1 s1' q after_external1 /\
        forall r s1'',
          after_external1 r s1'' ->
          exists j s2',
            after_external2 r s2' /\
            match_states j s1'' s2';
    bsim_match_final_states:
      forall i s1 s2 r,
      match_states i s1 s2 -> safe L1 s1 -> final_state L2 s2 r ->
      exists s1', Star L1 s1 E0 s1' /\ final_state L1 s1' r;
    bsim_progress:
      forall i s1 s2,
      match_states i s1 s2 -> safe L1 s1 ->
      (exists r, final_state L2 s2 r) \/
      (exists q ae, external L2 s2 q ae) \/
      (exists t, exists s2', Step L2 s2 t s2');
    bsim_simulation:
      forall s2 t s2', Step L2 s2 t s2' ->
      forall i s1, match_states i s1 s2 -> safe L1 s1 ->
      exists i', exists s1',
         (Plus L1 s1 t s1' \/ (Star L1 s1 t s1' /\ order i' i))
      /\ match_states i' s1' s2';
    bsim_public_preserved:
      forall id, Senv.public_symbol (symbolenv L2) id = Senv.public_symbol (symbolenv L1) id
  }.

Arguments bsim_properties {liA liB}.

Inductive backward_simulation {liA liB} (L1 L2: semantics liA liB) : Prop :=
  Backward_simulation (index: Type)
                      (order: index -> index -> Prop)
                      (match_states: index -> state L1 -> state L2 -> Prop)
                      (props: bsim_properties L1 L2 index order match_states).

Arguments Backward_simulation {liA liB L1 L2 index} order match_states props.

(** An alternate form of the simulation diagram *)

Lemma bsim_simulation':
  forall {liA liB} (L1 L2: semantics liA liB) index order match_states,
  bsim_properties L1 L2 index order match_states ->
  forall i s2 t s2', Step L2 s2 t s2' ->
  forall s1, match_states i s1 s2 -> safe L1 s1 ->
  (exists i', exists s1', Plus L1 s1 t s1' /\ match_states i' s1' s2')
  \/ (exists i', order i' i /\ t = E0 /\ match_states i' s1 s2').
Proof.
  intros. exploit @bsim_simulation; eauto.
  intros [i' [s1' [A B]]]. intuition.
  left; exists i'; exists s1'; auto.
  inv H4.
  right; exists i'; auto.
  left; exists i'; exists s1'; split; auto. econstructor; eauto.
Qed.

(** ** Backward simulation diagrams. *)

(** Various simulation diagrams that imply backward simulation. *)

Section BACKWARD_SIMU_DIAGRAMS.

Context {liA liB: language_interface}.
Variable L1: semantics liA liB.
Variable L2: semantics liA liB.

Hypothesis public_preserved:
  forall id, Senv.public_symbol (symbolenv L2) id = Senv.public_symbol (symbolenv L1) id.

Variable match_states: state L1 -> state L2 -> Prop.

Hypothesis initial_states_exist:
  forall q s1, initial_state L1 q s1 -> exists s2, initial_state L2 q s2.

Hypothesis match_initial_states:
  forall q s1 s2, initial_state L1 q s1 -> initial_state L2 q s2 ->
  exists s1', initial_state L1 q s1' /\ match_states s1' s2.

Hypothesis match_external:
  forall s1 s2, match_states s1 s2 ->
  forall q after_external2, external L2 s2 q after_external2 ->
  exists after_external1, external L1 s1 q after_external1 /\
  forall r s1', after_external1 r s1' ->
  exists s2', after_external2 r s2' /\ match_states s1' s2'.

Hypothesis match_final_states:
  forall s1 s2 r,
  match_states s1 s2 -> final_state L2 s2 r -> final_state L1 s1 r.

Hypothesis progress:
  forall s1 s2,
  match_states s1 s2 -> safe L1 s1 ->
  (exists r, final_state L2 s2 r) \/
  (exists t, exists s2', Step L2 s2 t s2').

Section BACKWARD_SIMULATION_PLUS.

Hypothesis simulation:
  forall s2 t s2', Step L2 s2 t s2' ->
  forall s1, match_states s1 s2 -> safe L1 s1 ->
  exists s1', Plus L1 s1 t s1' /\ match_states s1' s2'.

Lemma backward_simulation_plus: backward_simulation L1 L2.
Proof.
  apply Backward_simulation with
    (fun (x y: unit) => False)
    (fun (i: unit) s1 s2 => match_states s1 s2);
  constructor; auto.
- red; intros; constructor; intros. contradiction.
- intros. exists tt; eauto.
- intros. edestruct match_external as (ae1 & Hae1 & Hr); eauto.
  exists s1, ae1; eauto using star_refl.
- intros. exists s1; split. apply star_refl. eauto.
- intros. exploit simulation; eauto. intros [s1' [A B]].
  exists tt; exists s1'; auto.
Qed.

End BACKWARD_SIMULATION_PLUS.

End BACKWARD_SIMU_DIAGRAMS.

(** ** Backward simulation of transition sequences *)

Section BACKWARD_SIMULATION_SEQUENCES.

Context {liA liB} (L1 L2: semantics liA liB).
Context index order match_states (S: bsim_properties L1 L2 index order match_states).

Lemma bsim_E0_star:
  forall s2 s2', Star L2 s2 E0 s2' ->
  forall i s1, match_states i s1 s2 -> safe L1 s1 ->
  exists i', exists s1', Star L1 s1 E0 s1' /\ match_states i' s1' s2'.
Proof.
  intros s20 s20' STAR0. pattern s20, s20'. eapply star_E0_ind; eauto.
- (* base case *)
  intros. exists i; exists s1; split; auto. apply star_refl.
- (* inductive case *)
  intros. exploit @bsim_simulation; eauto. intros [i' [s1' [A B]]].
  assert (Star L1 s0 E0 s1'). intuition. apply plus_star; auto.
  exploit H0. eauto. eapply star_safe; eauto. intros [i'' [s1'' [C D]]].
  exists i''; exists s1''; split; auto. eapply star_trans; eauto.
Qed.

Lemma bsim_safe:
  forall i s1 s2,
  match_states i s1 s2 -> safe L1 s1 -> safe L2 s2.
Proof.
  intros; red; intros.
  exploit bsim_E0_star; eauto. intros [i' [s1' [A B]]].
  eapply bsim_progress; eauto. eapply star_safe; eauto.
Qed.

Lemma bsim_E0_plus:
  forall s2 t s2', Plus L2 s2 t s2' -> t = E0 ->
  forall i s1, match_states i s1 s2 -> safe L1 s1 ->
     (exists i', exists s1', Plus L1 s1 E0 s1' /\ match_states i' s1' s2')
  \/ (exists i', clos_trans _ order i' i /\ match_states i' s1 s2').
Proof.
  induction 1 using plus_ind2; intros; subst t.
- (* base case *)
  exploit @bsim_simulation'; eauto. intros [[i' [s1' [A B]]] | [i' [A [B C]]]].
+ left; exists i'; exists s1'; auto.
+ right; exists i'; intuition.
- (* inductive case *)
  exploit Eapp_E0_inv; eauto. intros [EQ1 EQ2]; subst.
  exploit @bsim_simulation'; eauto. intros [[i' [s1' [A B]]] | [i' [A [B C]]]].
+ exploit bsim_E0_star. apply plus_star; eauto. eauto. eapply star_safe; eauto. apply plus_star; auto.
  intros [i'' [s1'' [P Q]]].
  left; exists i''; exists s1''; intuition. eapply plus_star_trans; eauto.
+ exploit IHplus; eauto. intros [P | [i'' [P Q]]].
  left; auto.
  right; exists i''; intuition. eapply t_trans; eauto. apply t_step; auto.
Qed.

Lemma star_non_E0_split:
  forall s2 t s2', Star L2 s2 t s2' -> (length t = 1)%nat ->
  exists s2x, exists s2y, Star L2 s2 E0 s2x /\ Step L2 s2x t s2y /\ Star L2 s2y E0 s2'.
Proof.
  induction 1; intros.
  simpl in H; discriminate.
  subst t.
  assert (EITHER: t1 = E0 \/ t2 = E0).
    unfold Eapp in H2; rewrite app_length in H2.
    destruct t1; auto. destruct t2; auto. simpl in H2; omegaContradiction.
  destruct EITHER; subst.
  exploit IHstar; eauto. intros [s2x [s2y [A [B C]]]].
  exists s2x; exists s2y; intuition. eapply star_left; eauto.
  rewrite E0_right. exists s1; exists s2; intuition. apply star_refl.
Qed.

End BACKWARD_SIMULATION_SEQUENCES.

(** ** Composing two backward simulations *)

Section COMPOSE_BACKWARD_SIMULATIONS.

Context {liA liB: language_interface}.
Variable L1: semantics liA liB.
Variable L2: semantics liA liB.
Variable L3: semantics liA liB.
Hypothesis L3_single_events: single_events L3.
Context index order match_states (S12: bsim_properties L1 L2 index order match_states).
Context index' order' match_states' (S23: bsim_properties L2 L3 index' order' match_states').

Let bb_index : Type := (index * index')%type.

Definition bb_order : bb_index -> bb_index -> Prop := lex_ord (clos_trans _ order) order'.

Inductive bb_match_states: bb_index -> state L1 -> state L3 -> Prop :=
  | bb_match_later: forall i1 i2 s1 s3 s2x s2y,
      match_states i1 s1 s2x -> Star L2 s2x E0 s2y -> match_states' i2 s2y s3 ->
      bb_match_states (i1, i2) s1 s3.

Lemma bb_match_at: forall i1 i2 s1 s3 s2,
  match_states i1 s1 s2 -> match_states' i2 s2 s3 ->
  bb_match_states (i1, i2) s1 s3.
Proof.
  intros. econstructor; eauto. apply star_refl.
Qed.

Lemma bb_simulation_base:
  forall s3 t s3', Step L3 s3 t s3' ->
  forall i1 s1 i2 s2, match_states i1 s1 s2 -> match_states' i2 s2 s3 -> safe L1 s1 ->
  exists i', exists s1',
    (Plus L1 s1 t s1' \/ (Star L1 s1 t s1' /\ bb_order i' (i1, i2)))
    /\ bb_match_states i' s1' s3'.
Proof.
  intros.
  exploit (bsim_simulation' S23); eauto. eapply bsim_safe; eauto.
  intros [ [i2' [s2' [PLUS2 MATCH2]]] | [i2' [ORD2 [EQ MATCH2]]]].
- (* 1 L2 makes one or several transitions *)
  assert (EITHER: t = E0 \/ (length t = 1)%nat).
  { exploit L3_single_events; eauto.
    destruct t; auto. destruct t; auto. simpl. intros. omegaContradiction. }
  destruct EITHER.
+ (* 1.1 these are silent transitions *)
  subst t. exploit (bsim_E0_plus S12); eauto.
  intros [ [i1' [s1' [PLUS1 MATCH1]]] | [i1' [ORD1 MATCH1]]].
* (* 1.1.1 L1 makes one or several transitions *)
  exists (i1', i2'); exists s1'; split. auto. eapply bb_match_at; eauto.
* (* 1.1.2 L1 makes no transitions *)
  exists (i1', i2'); exists s1; split.
  right; split. apply star_refl. left; auto.
  eapply bb_match_at; eauto.
+ (* 1.2 non-silent transitions *)
  exploit @star_non_E0_split. apply plus_star; eauto. auto.
  intros [s2x [s2y [P [Q R]]]].
  exploit (bsim_E0_star S12). eexact P. eauto. auto. intros [i1' [s1x [X Y]]].
  exploit (bsim_simulation' S12). eexact Q. eauto. eapply star_safe; eauto.
  intros [[i1'' [s1y [U V]]] | [i1'' [U [V W]]]]; try (subst t; discriminate).
  exists (i1'', i2'); exists s1y; split.
  left. eapply star_plus_trans; eauto. eapply bb_match_later; eauto.
- (* 2. L2 makes no transitions *)
  subst. exists (i1, i2'); exists s1; split.
  right; split. apply star_refl. right; auto.
  eapply bb_match_at; eauto.
Qed.

Lemma bb_simulation:
  forall s3 t s3', Step L3 s3 t s3' ->
  forall i s1, bb_match_states i s1 s3 -> safe L1 s1 ->
  exists i', exists s1',
    (Plus L1 s1 t s1' \/ (Star L1 s1 t s1' /\ bb_order i' i))
    /\ bb_match_states i' s1' s3'.
Proof.
  intros. inv H0.
  exploit star_inv; eauto. intros [[EQ1 EQ2] | PLUS].
- (* 1. match at *)
  subst. eapply bb_simulation_base; eauto.
- (* 2. match later *)
  exploit (bsim_E0_plus S12); eauto.
  intros [[i1' [s1' [A B]]] | [i1' [A B]]].
+ (* 2.1 one or several silent transitions *)
  exploit bb_simulation_base. eauto. auto. eexact B. eauto.
    eapply star_safe; eauto. eapply plus_star; eauto.
  intros [i'' [s1'' [C D]]].
  exists i''; exists s1''; split; auto.
  left. eapply plus_star_trans; eauto.
  destruct C as [P | [P Q]]. apply plus_star; eauto. eauto.
  traceEq.
+ (* 2.2 no silent transition *)
  exploit bb_simulation_base. eauto. auto. eexact B. eauto. auto.
  intros [i'' [s1'' [C D]]].
  exists i''; exists s1''; split; auto.
  intuition. right; intuition.
  inv H6. left. eapply t_trans; eauto. left; auto.
Qed.

End COMPOSE_BACKWARD_SIMULATIONS.

Lemma compose_backward_simulation:
  forall {liA liB} (L1 L2 L3: semantics liA liB),
  single_events L3 -> backward_simulation L1 L2 -> backward_simulation L2 L3 ->
  backward_simulation L1 L3.
Proof.
  intros liA liB L1 L2 L3 L3single S12 S23.
  destruct S12 as [index order match_states props].
  destruct S23 as [index' order' match_states' props'].
  apply Backward_simulation with (bb_order order order') (bb_match_states L1 L2 L3 match_states match_states');
  constructor.
- (* well founded *)
  unfold bb_order. apply wf_lex_ord. apply wf_clos_trans. eapply bsim_order_wf; eauto. eapply bsim_order_wf; eauto.
- (* initial states exist *)
  intros. exploit (bsim_initial_states_exist props); eauto. intros [s2 A].
  eapply (bsim_initial_states_exist props'); eauto.
- (* match initial states *)
  intros q s1 s3 INIT1 INIT3.
  exploit (bsim_initial_states_exist props); eauto. intros [s2 INIT2].
  exploit (bsim_match_initial_states props'); eauto. intros [i2 [s2' [INIT2' M2]]].
  exploit (bsim_match_initial_states props); eauto. intros [i1 [s1' [INIT1' M1]]].
  exists (i1, i2); exists s1'; intuition auto. eapply bb_match_at; eauto.
- (* match external states *)
  intros i s1 s3 MS SAFE1 q ae3 EXT3. inv MS.
  exploit (bsim_match_external props'); eauto.
    eapply star_safe; eauto. eapply bsim_safe; eauto.
  intros (s2' & ae2 & STAR2 & EXT2 & Hr23).
  exploit (bsim_E0_star props). eapply star_trans. eexact H0. eexact STAR2. eauto. eauto. auto.
  intros (i' & s1' & STAR1 & Hs12').
  exploit (bsim_match_external props); eauto.
    eapply star_safe; eauto.
  intros (s1'' & ae1 & STAR1' & EXT1 & Hr12).
  exists s1'', ae1; split; eauto.
  eapply star_trans; eauto.
  split; eauto.
  intros r s1''0 Hae1.
  edestruct Hr12 as (j & s2'' & AE2 & Hs12). eauto.
  edestruct Hr23 as (j' & s3'' & AE3 & Hs23). eauto.
  exists (j,j'), s3''; split; eauto.
  econstructor; eauto.
  apply star_refl.
- (* match final states *)
  intros i s1 s3 r MS SAFE FIN. inv MS.
  exploit (bsim_match_final_states props'); eauto.
    eapply star_safe; eauto. eapply bsim_safe; eauto.
  intros [s2' [A B]].
  exploit (bsim_E0_star props). eapply star_trans. eexact H0. eexact A. auto. eauto. auto.
  intros [i1' [s1' [C D]]].
  exploit (bsim_match_final_states props); eauto. eapply star_safe; eauto.
  intros [s1'' [P Q]].
  exists s1''; split; auto. eapply star_trans; eauto.
- (* progress *)
  intros i s1 s3 MS SAFE. inv MS.
  eapply (bsim_progress props'). eauto. eapply star_safe; eauto. eapply bsim_safe; eauto.
- (* simulation *)
  apply bb_simulation; auto.
- (* symbols *)
  intros. transitivity (Senv.public_symbol (symbolenv L2) id); eapply bsim_public_preserved; eauto.
Qed.

(** ** Converting a forward simulation to a backward simulation *)

Section FORWARD_TO_BACKWARD.

Context {liA1 liA2} (ccA: callconv liA1 liA2).
Context {liB1 liB2} (ccB: callconv liB1 liB2).

Context (L1: semantics liA1 liB1) (L2: semantics liA2 liB2)
        index order match_states (FS: fsim_properties ccA ccB L1 L2 index order match_states).
Hypothesis L1_receptive: receptive L1.
Hypothesis L2_determinate: determinate L2.

(** Exploiting forward simulation *)

Inductive f2b_transitions: proj_state ccB L1 -> state L2 -> Prop :=
  | f2b_trans_final: forall s1 s2 s1' r,
      Star (proj_semantics ccA ccB L1) s1 E0 s1' ->
      proj_final_state ccB L1 s1' r ->
      final_state L2 s2 r ->
      f2b_transitions s1 s2
  | f2b_trans_step: forall wB s1 s2 s1' t s1'' s2' i' i'',
      Star L1 s1 E0 s1' ->
      Step L1 s1' t s1'' ->
      Plus L2 s2 t s2' ->
      match_states wB i' s1' s2 ->
      match_states wB i'' s1'' s2' ->
      f2b_transitions (wB,s1) s2.

Lemma f2b_progress:
  forall i wB s1 s2, match_states wB i s1 s2 -> safe L1 s1 -> f2b_transitions (wB,s1) s2.
Proof.
  intros i0; pattern i0. apply well_founded_ind with (R := order).
  eapply fsim_order_wf; eauto.
  intros i REC wB s1 s2 MATCH SAFE.
  destruct (SAFE s1) as [[r FINAL] | [t [s1' STEP1]]]. apply star_refl.
- (* final state reached *)
  edestruct @fsim_match_final_states as (r2 & Hr & Hfinal); eauto.
  eapply f2b_trans_final; eauto.
  apply star_refl.
  econstructor; eauto.
- (* L1 can make one step *)
  exploit (fsim_simulation FS); eauto. intros [i' [s2' [A MATCH']]].
  assert (B: Plus L2 s2 t s2' \/ (s2' = s2 /\ t = E0 /\ order i' i)).
    intuition auto.
    destruct (star_inv H0); intuition auto.
  clear A. destruct B as [PLUS2 | [EQ1 [EQ2 ORDER]]].
+ eapply f2b_trans_step; eauto. apply star_refl.
+ subst. exploit REC; eauto. eapply star_safe; eauto. apply star_one; auto.
  intros TRANS; inv TRANS.
* eapply f2b_trans_final; eauto. eapply star_left; eauto.
  econstructor; eauto. auto.
* eapply f2b_trans_step; eauto. eapply star_left; eauto.
Qed.

Lemma fsim_simulation_not_E0:
  forall s1 t s1', Step L1 s1 t s1' -> t <> E0 ->
  forall i wB s2, match_states wB i s1 s2 ->
  exists i', exists s2', Plus L2 s2 t s2' /\ match_states wB i' s1' s2'.
Proof.
  intros. exploit (fsim_simulation FS); eauto. intros [i' [s2' [A B]]].
  exists i'; exists s2'; split; auto.
  destruct A. auto. destruct H2. exploit star_inv; eauto. intros [[EQ1 EQ2] | P]; auto.
  congruence.
Qed.

(** Exploiting determinacy *)

Remark silent_or_not_silent:
  forall t, t = E0 \/ t <> E0.
Proof.
  intros; unfold E0; destruct t; auto; right; congruence.
Qed.

Remark not_silent_length:
  forall t1 t2, (length (t1 ** t2) <= 1)%nat -> t1 = E0 \/ t2 = E0.
Proof.
  unfold Eapp, E0; intros. rewrite app_length in H.
  destruct t1; destruct t2; auto. simpl in H. omegaContradiction.
Qed.

Lemma f2b_determinacy_inv:
  forall s2 t' s2' t'' s2'',
  Step L2 s2 t' s2' -> Step L2 s2 t'' s2'' ->
  (t' = E0 /\ t'' = E0 /\ s2' = s2'')
  \/ (t' <> E0 /\ t'' <> E0 /\ match_traces (symbolenv L1) t' t'').
Proof.
  intros.
  assert (match_traces (symbolenv L2) t' t'').
    eapply sd_determ_1; eauto.
  destruct (silent_or_not_silent t').
  subst. inv H1.
  left; intuition. eapply sd_determ_2; eauto.
  destruct (silent_or_not_silent t'').
  subst. inv H1. elim H2; auto.
  right; intuition.
  eapply match_traces_preserved with (ge1 := (symbolenv L2)); auto.
  intros; symmetry; apply (fsim_public_preserved FS).
Qed.

Lemma f2b_determinacy_star:
  forall s s1, Star L2 s E0 s1 ->
  forall t s2 s3,
  Step L2 s1 t s2 -> t <> E0 ->
  Star L2 s t s3 ->
  Star L2 s1 t s3.
Proof.
  intros s0 s01 ST0. pattern s0, s01. eapply star_E0_ind; eauto.
  intros. inv H3. congruence.
  exploit f2b_determinacy_inv. eexact H. eexact H4.
  intros [[EQ1 [EQ2 EQ3]] | [NEQ1 [NEQ2 MT]]].
  subst. simpl in *. eauto.
  congruence.
Qed.

(** Orders *)

Inductive f2b_index : Type :=
  | F2BI_before (n: nat)
  | F2BI_after (n: nat).

Inductive f2b_order: f2b_index -> f2b_index -> Prop :=
  | f2b_order_before: forall n n',
      (n' < n)%nat ->
      f2b_order (F2BI_before n') (F2BI_before n)
  | f2b_order_after: forall n n',
      (n' < n)%nat ->
      f2b_order (F2BI_after n') (F2BI_after n)
  | f2b_order_switch: forall n n',
      f2b_order (F2BI_before n') (F2BI_after n).

Lemma wf_f2b_order:
  well_founded f2b_order.
Proof.
  assert (ACC1: forall n, Acc f2b_order (F2BI_before n)).
    intros n0; pattern n0; apply lt_wf_ind; intros.
    constructor; intros. inv H0. auto.
  assert (ACC2: forall n, Acc f2b_order (F2BI_after n)).
    intros n0; pattern n0; apply lt_wf_ind; intros.
    constructor; intros. inv H0. auto. auto.
  red; intros. destruct a; auto.
Qed.

(** Constructing the backward simulation *)

Inductive f2b_match_states: f2b_index -> proj_state ccB L1 -> state L2 -> Prop :=
  | f2b_match_at: forall wB i s1 s2,
      match_states wB i s1 s2 ->
      f2b_match_states (F2BI_after O) (wB,s1) s2
  | f2b_match_before: forall wB s1 t s1' s2b s2 n s2a i,
      Step L1 s1 t s1' ->  t <> E0 ->
      Star L2 s2b E0 s2 ->
      starN (step L2) (globalenv L2) n s2 t s2a ->
      match_states wB i s1 s2b ->
      f2b_match_states (F2BI_before n) (wB,s1) s2
  | f2b_match_after: forall wB n s2 s2a s1 i,
      starN (step L2) (globalenv L2) (S n) s2 E0 s2a ->
      match_states wB i s1 s2a ->
      f2b_match_states (F2BI_after (S n)) (wB,s1) s2.

Remark f2b_match_after':
  forall wB n s2 s2a s1 i,
  starN (step L2) (globalenv L2) n s2 E0 s2a ->
  match_states wB i s1 s2a ->
  f2b_match_states (F2BI_after n) (wB,s1) s2.
Proof.
  intros. inv H.
  econstructor; eauto.
  econstructor; eauto. econstructor; eauto.
Qed.

(** Backward simulation of L2 steps *)

Lemma proj_safe:
  forall w s,
    safe (proj_semantics ccA ccB L1) (w,s) ->
    safe L1 s.
Proof.
  intros w s SAFE s' STAR.
  revert STAR SAFE.
  remember E0 as t. intro STAR; revert t STAR Heqt.
  induction 1; simpl; intros.
  - edestruct (SAFE (w,s)).
    + apply star_refl.
    + destruct H as (r & FINAL).
      inv FINAL.
      left; eauto.
    + destruct H as (t & s'' & STEP).
      inv STEP.
      right; eauto.
  - subst. apply Eapp_E0_inv in Heqt. destruct Heqt; subst.
    apply IHSTAR. auto.
    eapply star_safe; eauto.
    eapply star_one. constructor; eauto.
Qed.

Lemma f2b_simulation_step:
  forall s2 t s2', Step L2 s2 t s2' ->
  forall i wB s1, f2b_match_states i (wB,s1) s2 -> safe L1 s1 ->
  exists i', exists s1',
    (Plus L1 s1 t s1' \/ (Star L1 s1 t s1' /\ f2b_order i' i))
     /\ f2b_match_states i' (wB,s1') s2'.
Proof.
  intros s2 t s2' STEP2 i wB s1 MATCH SAFE.
  inv MATCH.
- (* 1. At matching states *)
  exploit f2b_progress; eauto. intros TRANS; inv TRANS.
+ (* 1.1  L1 can reach final state and L2 is at final state: impossible! *)
  exploit (sd_final_nostep L2_determinate); eauto. contradiction.
+ (* 1.2  L1 can make 0 or several steps; L2 can make 1 or several matching steps. *)
  inv H4.
  exploit f2b_determinacy_inv. eexact H. eexact STEP2.
  intros [[EQ1 [EQ2 EQ3]] | [NOT1 [NOT2 MT]]].
* (* 1.2.1  L2 makes a silent transition *)
  destruct (silent_or_not_silent t2).
  (* 1.2.1.1  L1 makes a silent transition too: perform transition now and go to "after" state *)
  subst. simpl in *. destruct (star_starN H0) as [n STEPS2].
  exists (F2BI_after n); exists s1''; split.
  left. eapply plus_right; eauto.
  eapply f2b_match_after'; eauto.
  (* 1.2.1.2 L1 makes a non-silent transition: keep it for later and go to "before" state *)
  subst. simpl in *. destruct (star_starN H0) as [n STEPS2].
  exists (F2BI_before n); exists s1'; split.
  right; split. auto. constructor.
  econstructor. eauto. auto. apply star_one; eauto. eauto. eauto.
* (* 1.2.2 L2 makes a non-silent transition, and so does L1 *)
  exploit not_silent_length. eapply (sr_traces L1_receptive); eauto. intros [EQ | EQ].
  congruence.
  subst t2. rewrite E0_right in H2.
  (* Use receptiveness to equate the traces *)
  exploit (sr_receptive L1_receptive); eauto. intros [s1''' STEP1].
  exploit fsim_simulation_not_E0. eexact STEP1. auto. eauto.
  intros [i''' [s2''' [P Q]]]. inv P.
  (* Exploit determinacy *)
  exploit not_silent_length. eapply (sr_traces L1_receptive); eauto. intros [EQ | EQ].
  subst t0. simpl in *. exploit sd_determ_1. eauto. eexact STEP2. eassumption.
  intros. elim NOT2. inv H8. auto.
  subst t2. rewrite E0_right in *.
  assert (s4 = s2'). eapply sd_determ_2; eauto. subst s4.
  (* Perform transition now and go to "after" state *)
  destruct (star_starN H6) as [n STEPS2]. exists (F2BI_after n); exists s1'''; split.
  left. eapply plus_right; eauto.
  eapply f2b_match_after'; eauto.

- (* 2. Before *)
  inv H5. congruence.
  exploit f2b_determinacy_inv. eexact H. eexact STEP2.
  intros [[EQ1 [EQ2 EQ3]] | [NOT1 [NOT2 MT]]].
+ (* 2.1 L2 makes a silent transition: remain in "before" state *)
  subst. simpl in *. exists (F2BI_before n0); exists s1; split.
  right; split. apply star_refl. constructor. omega.
  econstructor; eauto. eapply star_right; eauto.
+ (* 2.2 L2 make a non-silent transition *)
  exploit not_silent_length. eapply (sr_traces L1_receptive); eauto. intros [EQ | EQ].
  congruence.
  subst. rewrite E0_right in *.
  (* Use receptiveness to equate the traces *)
  exploit (sr_receptive L1_receptive); eauto. intros [s1''' STEP1].
  exploit fsim_simulation_not_E0. eexact STEP1. auto. eauto.
  intros [i''' [s2''' [P Q]]].
  (* Exploit determinacy *)
  exploit f2b_determinacy_star. eauto. eexact STEP2. auto. apply plus_star; eauto.
  intro R. inv R. congruence.
  exploit not_silent_length. eapply (sr_traces L1_receptive); eauto. intros [EQ | EQ].
  subst. simpl in *. exploit sd_determ_1. eauto. eexact STEP2. eassumption.
  intros. elim NOT2. inv H6; auto.
  subst. rewrite E0_right in *.
  assert (s3 = s2'). eapply sd_determ_2; eauto. subst s3.
  (* Perform transition now and go to "after" state *)
  destruct (star_starN H5) as [n STEPS2]. exists (F2BI_after n); exists s1'''; split.
  left. apply plus_one; auto.
  eapply f2b_match_after'; eauto.

- (* 3. After *)
  inv H2. exploit Eapp_E0_inv; eauto. intros [EQ1 EQ2]; subst.
  exploit f2b_determinacy_inv. eexact H0. eexact STEP2.
  intros [[EQ1 [EQ2 EQ3]] | [NOT1 [NOT2 MT]]].
  subst. exists (F2BI_after n); exists s1; split.
  right; split. apply star_refl. constructor; omega.
  eapply f2b_match_after'; eauto.
  congruence.
Qed.

Let PL1 := proj_semantics ccA ccB L1.

Lemma proj_star_step:
  forall w s t s',
    Star L1 s t s' ->
    Star PL1 (w,s) t (w,s').
Proof.
  induction 1; simpl; intros; econstructor; eauto; constructor; eauto.
Qed.

Lemma proj_plus_step:
  forall w s t s',
    Plus L1 s t s' ->
    Plus PL1 (w,s) t (w,s').
Proof.
  destruct 1.
  econstructor; eauto.
  constructor; eauto.
  apply proj_star_step; eauto.
Qed.

Lemma f2b_simulation_step':
  forall s2 t s2', Step L2 s2 t s2' ->
  forall i s1, f2b_match_states i s1 s2 -> safe PL1 s1 ->
  exists i', exists s1',
    (Plus PL1 s1 t s1' \/ (Star PL1 s1 t s1' /\ f2b_order i' i))
     /\ f2b_match_states i' s1' s2'.
Proof.
  intros s2 t s2' STEP i s1 MS SAFE.
  destruct s1 as [w s1].
  apply proj_safe in SAFE.
  edestruct (f2b_simulation_step) as (i' & s1' & STEPS & MATCH); eauto.
  exists i', (w,s1'); split; eauto. 
  intuition eauto using proj_star_step, proj_plus_step.
Qed.

End FORWARD_TO_BACKWARD.

(** The backward simulation *)

Lemma forward_to_backward_simulation:
  forall {liA1 liA2} (ccA: callconv liA1 liA2)
         {liB1 liB2} (ccB: callconv liB1 liB2)
         (L1: semantics liA1 liB1) (L2: semantics liA2 liB2),
  forward_simulation ccA ccB L1 L2 -> receptive L1 -> determinate L2 ->
  backward_simulation (proj_semantics ccA ccB L1) L2.
Proof.
  intros liA1 liA2 ccA liB1 liB2 ccB.
  intros L1 L2 FS L1_receptive L2_determinate.
  destruct FS as [index order match_states FS].
  apply Backward_simulation with f2b_order (f2b_match_states L2 match_states); constructor.
- (* well founded *)
  apply wf_f2b_order.
- (* initial states exist *)
  intros. inv H.
  exploit (fsim_match_initial_states FS); eauto. intros [i [s2 [A B]]].
  exists s2; auto.
- (* initial states *)
  intros. inv H. exploit (fsim_match_initial_states FS); eauto. intros [i [s2' [A B]]].
  assert (s2 = s2') by (eapply sd_initial_determ; eauto). subst s2'.
  exists (F2BI_after O); exists (w,s); split; auto. econstructor; eauto.
  econstructor; eauto.
- (* external *)
  intros. destruct s1 as [w s1]. apply proj_safe in H0. inv H.
  exploit @f2b_progress; eauto. intros TRANS; inv TRANS.
  eelim sd_external_nofinal; eauto.
  inv H5. exploit (sd_external_nostep L2_determinate); eauto. contradiction.
  inv H8. congruence. exploit (sd_external_nostep L2_determinate); eauto. contradiction.
  inv H5. exploit (sd_external_nostep L2_determinate); eauto. contradiction.
- (* final states *)
  intros. destruct s1 as [w s1]. apply proj_safe in H0. inv H.
  exploit @f2b_progress; eauto. intros TRANS; inv TRANS.
  assert (r0 = r) by (eapply (sd_final_determ L2_determinate); eauto). subst r0.
  exists s1'; auto.
  inv H5. exploit (sd_final_nostep L2_determinate); eauto. contradiction.
  inv H8. congruence. exploit (sd_final_nostep L2_determinate); eauto. contradiction.
  inv H5. exploit (sd_final_nostep L2_determinate); eauto. contradiction.
- (* progress *)
  intros. destruct s1 as [w s1]. apply proj_safe in H0. inv H.
  exploit @f2b_progress; eauto. intros TRANS; inv TRANS.
  left; exists r; auto.
  inv H4. right; econstructor; econstructor; eauto.
  inv H7. congruence. right; econstructor; econstructor; eauto.
  inv H4. right; econstructor; econstructor; eauto.
- (* simulation *)
  eapply f2b_simulation_step'; eauto.
- (* symbols preserved *)
  exact (fsim_public_preserved FS).
Qed.

(** * Transforming a semantics into a single-event, equivalent semantics *)

Definition well_behaved_traces (L: semantics) : Prop :=
  forall s t s', Step L s t s' ->
  match t with nil => True | ev :: t' => output_trace t' end.

Section ATOMIC.

Variable L: semantics.

Hypothesis Lwb: well_behaved_traces L.

Inductive atomic_step (ge: genvtype L): (trace * state L) -> trace -> (trace * state L) -> Prop :=
  | atomic_step_silent: forall s s',
      Step L s E0 s' ->
      atomic_step ge (E0, s) E0 (E0, s')
  | atomic_step_start: forall s ev t s',
      Step L s (ev :: t) s' ->
      atomic_step ge (E0, s) (ev :: nil) (t, s')
  | atomic_step_continue: forall ev t s,
      output_trace (ev :: t) ->
      atomic_step ge (ev :: t, s) (ev :: nil) (t, s).

Definition atomic : semantics := {|
  state := (trace * state L)%type;
  genvtype := genvtype L;
  step := atomic_step;
  initial_state := fun s => initial_state L (snd s) /\ fst s = E0;
  final_state := fun s r => final_state L (snd s) r /\ fst s = E0;
  globalenv := globalenv L;
  symbolenv := symbolenv L
|}.

End ATOMIC.

(** A forward simulation from a semantics [L1] to a single-event semantics [L2]
  can be "factored" into a forward simulation from [atomic L1] to [L2]. *)

Section FACTOR_FORWARD_SIMULATION.

Variable L1: semantics.
Variable L2: semantics.
Context index order match_states (sim: fsim_properties L1 L2 index order match_states).
Hypothesis L2single: single_events L2.

Inductive ffs_match: index -> (trace * state L1) -> state L2 -> Prop :=
  | ffs_match_at: forall i s1 s2,
      match_states i s1 s2 ->
      ffs_match i (E0, s1) s2
  | ffs_match_buffer: forall i ev t s1 s2 s2',
      Star L2 s2 (ev :: t) s2' -> match_states i s1 s2' ->
      ffs_match i (ev :: t, s1) s2.

Lemma star_non_E0_split':
  forall s2 t s2', Star L2 s2 t s2' ->
  match t with
  | nil => True
  | ev :: t' => exists s2x, Plus L2 s2 (ev :: nil) s2x /\ Star L2 s2x t' s2'
  end.
Proof.
  induction 1. simpl. auto.
  exploit L2single; eauto. intros LEN.
  destruct t1. simpl in *. subst. destruct t2. auto.
  destruct IHstar as [s2x [A B]]. exists s2x; split; auto.
  eapply plus_left. eauto. apply plus_star; eauto. auto.
  destruct t1. simpl in *. subst t. exists s2; split; auto. apply plus_one; auto.
  simpl in LEN. omegaContradiction.
Qed.

Lemma ffs_simulation:
  forall s1 t s1', Step (atomic L1) s1 t s1' ->
  forall i s2, ffs_match i s1 s2 ->
  exists i', exists s2',
     (Plus L2 s2 t s2' \/ (Star L2 s2 t s2') /\ order i' i)
  /\ ffs_match i' s1' s2'.
Proof.
  induction 1; intros.
- (* silent step *)
  inv H0.
  exploit (fsim_simulation sim); eauto.
  intros [i' [s2' [A B]]].
  exists i'; exists s2'; split. auto. constructor; auto.
- (* start step *)
  inv H0.
  exploit (fsim_simulation sim); eauto.
  intros [i' [s2' [A B]]].
  destruct t as [ | ev' t].
+ (* single event *)
  exists i'; exists s2'; split. auto. constructor; auto.
+ (* multiple events *)
  assert (C: Star L2 s2 (ev :: ev' :: t) s2'). intuition. apply plus_star; auto.
  exploit star_non_E0_split'. eauto. simpl. intros [s2x [P Q]].
  exists i'; exists s2x; split. auto. econstructor; eauto.
- (* continue step *)
  inv H0.
  exploit star_non_E0_split'. eauto. simpl. intros [s2x [P Q]].
  destruct t.
  exists i; exists s2'; split. left. eapply plus_star_trans; eauto. constructor; auto.
  exists i; exists s2x; split. auto. econstructor; eauto.
Qed.

End FACTOR_FORWARD_SIMULATION.

Theorem factor_forward_simulation:
  forall L1 L2,
  forward_simulation L1 L2 -> single_events L2 ->
  forward_simulation (atomic L1) L2.
Proof.
  intros L1 L2 FS L2single.
  destruct FS as [index order match_states sim].
  apply Forward_simulation with order (ffs_match L1 L2 match_states); constructor.
- (* wf *)
  eapply fsim_order_wf; eauto.
- (* initial states *)
  intros. destruct s1 as [t1 s1]. simpl in H. destruct H. subst.
  exploit (fsim_match_initial_states sim); eauto. intros [i [s2 [A B]]].
  exists i; exists s2; split; auto. constructor; auto.
- (* final states *)
  intros. destruct s1 as [t1 s1]. simpl in H0; destruct H0; subst. inv H.
  eapply (fsim_match_final_states sim); eauto.
- (* simulation *)
  eapply ffs_simulation; eauto.
- (* symbols preserved *)
  simpl. exact (fsim_public_preserved sim).
Qed.

(** Likewise, a backward simulation from a single-event semantics [L1] to a semantics [L2]
  can be "factored" as a backward simulation from [L1] to [atomic L2]. *)

Section FACTOR_BACKWARD_SIMULATION.

Variable L1: semantics.
Variable L2: semantics.
Context index order match_states (sim: bsim_properties L1 L2 index order match_states).
Hypothesis L1single: single_events L1.
Hypothesis L2wb: well_behaved_traces L2.

Inductive fbs_match: index -> state L1 -> (trace * state L2) -> Prop :=
  | fbs_match_intro: forall i s1 t s2 s1',
      Star L1 s1 t s1' -> match_states i s1' s2 ->
      t = E0 \/ output_trace t ->
      fbs_match i s1 (t, s2).

Lemma fbs_simulation:
  forall s2 t s2', Step (atomic L2) s2 t s2' ->
  forall i s1, fbs_match i s1 s2 -> safe L1 s1 ->
  exists i', exists s1',
     (Plus L1 s1 t s1' \/ (Star L1 s1 t s1' /\ order i' i))
     /\ fbs_match i' s1' s2'.
Proof.
  induction 1; intros.
- (* silent step *)
  inv H0.
  exploit (bsim_simulation sim); eauto. eapply star_safe; eauto.
  intros [i' [s1'' [A B]]].
  exists i'; exists s1''; split.
  destruct A as [P | [P Q]]. left. eapply star_plus_trans; eauto. right; split; auto. eapply star_trans; eauto.
  econstructor. apply star_refl. auto. auto.
- (* start step *)
  inv H0.
  exploit (bsim_simulation sim); eauto. eapply star_safe; eauto.
  intros [i' [s1'' [A B]]].
  assert (C: Star L1 s1 (ev :: t) s1'').
    eapply star_trans. eauto. destruct A as [P | [P Q]]. apply plus_star; eauto. eauto. auto.
  exploit star_non_E0_split'; eauto. simpl. intros [s1x [P Q]].
  exists i'; exists s1x; split.
  left; auto.
  econstructor; eauto.
  exploit L2wb; eauto.
- (* continue step *)
  inv H0. unfold E0 in H8; destruct H8; try congruence.
  exploit star_non_E0_split'; eauto. simpl. intros [s1x [P Q]].
  exists i; exists s1x; split. left; auto. econstructor; eauto. simpl in H0; tauto.
Qed.

Lemma fbs_progress:
  forall i s1 s2,
  fbs_match i s1 s2 -> safe L1 s1 ->
  (exists r, final_state (atomic L2) s2 r) \/
  (exists t, exists s2', Step (atomic L2) s2 t s2').
Proof.
  intros. inv H. destruct t.
- (* 1. no buffered events *)
  exploit (bsim_progress sim); eauto. eapply star_safe; eauto.
  intros [[r A] | [t [s2' A]]].
+ (* final state *)
  left; exists r; simpl; auto.
+ (* L2 can step *)
  destruct t.
  right; exists E0; exists (nil, s2'). constructor. auto.
  right; exists (e :: nil); exists (t, s2'). constructor. auto.
- (* 2. some buffered events *)
  unfold E0 in H3; destruct H3. congruence.
  right; exists (e :: nil); exists (t, s3). constructor. auto.
Qed.

End FACTOR_BACKWARD_SIMULATION.

Theorem factor_backward_simulation:
  forall L1 L2,
  backward_simulation L1 L2 -> single_events L1 -> well_behaved_traces L2 ->
  backward_simulation L1 (atomic L2).
Proof.
  intros L1 L2 BS L1single L2wb.
  destruct BS as [index order match_states sim].
  apply Backward_simulation with order (fbs_match L1 L2 match_states); constructor.
- (* wf *)
  eapply bsim_order_wf; eauto.
- (* initial states exist *)
  intros. exploit (bsim_initial_states_exist sim); eauto. intros [s2 A].
  exists (E0, s2). simpl; auto.
- (* initial states match *)
  intros. destruct s2 as [t s2]; simpl in H0; destruct H0; subst.
  exploit (bsim_match_initial_states sim); eauto. intros [i [s1' [A B]]].
  exists i; exists s1'; split. auto. econstructor. apply star_refl. auto. auto.
- (* final states match *)
  intros. destruct s2 as [t s2]; simpl in H1; destruct H1; subst.
  inv H. exploit (bsim_match_final_states sim); eauto. eapply star_safe; eauto.
  intros [s1'' [A B]]. exists s1''; split; auto. eapply star_trans; eauto.
- (* progress *)
  eapply fbs_progress; eauto.
- (* simulation *)
  eapply fbs_simulation; eauto.
- (* symbols *)
  simpl. exact (bsim_public_preserved sim).
Qed.

(** Receptiveness of [atomic L]. *)

Record strongly_receptive (L: semantics) : Prop :=
  Strongly_receptive {
    ssr_receptive: forall s ev1 t1 s1 ev2,
      Step L s (ev1 :: t1) s1 ->
      match_traces (symbolenv L) (ev1 :: nil) (ev2 :: nil) ->
      exists s2, exists t2, Step L s (ev2 :: t2) s2;
    ssr_well_behaved:
      well_behaved_traces L
  }.

Theorem atomic_receptive:
  forall L, strongly_receptive L -> receptive (atomic L).
Proof.
  intros. constructor; intros.
(* receptive *)
  inv H0.
  (* silent step *)
  inv H1. exists (E0, s'). constructor; auto.
  (* start step *)
  assert (exists ev2, t2 = ev2 :: nil). inv H1; econstructor; eauto.
  destruct H0 as [ev2 EQ]; subst t2.
  exploit ssr_receptive; eauto. intros [s2 [t2 P]].
  exploit ssr_well_behaved. eauto. eexact P. simpl; intros Q.
  exists (t2, s2). constructor; auto.
  (* continue step *)
  simpl in H2; destruct H2.
  assert (t2 = ev :: nil). inv H1; simpl in H0; tauto.
  subst t2. exists (t, s0). constructor; auto. simpl; auto.
(* single-event *)
  red. intros. inv H0; simpl; omega.
Qed.

(** * Connections with big-step semantics *)

(** The general form of a big-step semantics *)

Record bigstep_semantics li : Type :=
  Bigstep_semantics {
    bigstep_terminates: query li -> trace -> reply li -> Prop;
    bigstep_diverges: query li -> traceinf -> Prop
  }.

(** Soundness with respect to a small-step semantics *)

Record bigstep_sound {li} (B: bigstep_semantics li) (L: semantics li) : Prop :=
  Bigstep_sound {
    bigstep_terminates_sound:
      forall k q t r,
      bigstep_terminates B q t r ->
      exists s1 s2, initial_state L k q s1 /\ Star L q s1 t s2 /\ final_state L q s2 r;
    bigstep_diverges_sound:
      forall k q T,
      bigstep_diverges B q T ->
      exists s1, initial_state L k q s1 /\ forever (step L q) (globalenv L) s1 T
}.

*)

