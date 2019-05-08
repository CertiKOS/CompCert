Require Import LogicalRelations.
Require Import KLR.
Require Import Axioms.
Require Import LanguageInterface.
Require Import Events.
Require Import Smallstep.
Require Import IntmDef.
Require Import IntmTactics.
Require Import IntmIter.
Require Import IntmDecomp.
Require Import IntmAbs.
Require Import Behaviors.

Import IntmDef.Behavior.
Import IntmIter.Behavior.
Import IntmAbs.Behavior.


(** * Languages *)

Definition sem li :=
  query li -> beh (query li) (reply li) (reply li).

Bind Scope behavior_scope with sem.

Class Semof (li : language_interface) (P : Type) :=
  {
    semof : P -> sem li;
  }.

Notation "〚 p 〛" := (semof p).


(** * Embedding small-step semantics *)

Section EMBEDDING.
  Context {li} (L : Smallstep.semantics li).

  Program Definition assert {M N} (P : Prop) : t M N unit :=
    {| has t := P -> t = val tt |}.
  Next Obligation.
    rewrite H in H0; eauto. inversion H0; congruence.
  Qed.

  Definition pick {M N A} (P : A -> Prop) : t M N A :=
    _ <- assert (ex P); choose P.

  Definition istep (s : state L) : beh (query li) (reply li) (state L) :=
    _ <- assert (safe L s);
    (choose (step L (globalenv L) s E0) \/
     (q <- choose (at_external L s);
      r <- interact q;
      pick (after_external L s r))).

  Lemma assert_true {M N} (P : Prop) :
    P -> @assert M N P = ret tt.
  Proof.
    intros; apply antisymmetry; firstorder.
  Qed.

  Lemma assert_false {M N} P :
    ~ P -> @assert M N P = top.
  Proof.
    intros; apply antisymmetry; firstorder.
  Qed.

  Lemma assert_min {M N} P :
    ref (ret tt) (@assert M N P).
  Proof.
    firstorder.
  Qed.

  Lemma unsafe_istep s :
    ~ safe L s -> repeat istep s = top.
  Proof.
    intros. rewrite repeat_unfold_l. unfold istep at 3.
    setoid_rewrite assert_false; auto. monad.
  Qed.

  Lemma choose_val {M N A} {P : A -> Prop} (a : A) :
    P a -> @ref M N A (ret a) (choose P).
  Proof.
    firstorder.
  Qed.

  Lemma star_star s s' :
    Star L s E0 s' ->
    ref (ret s') (star istep s).
  Proof.
    revert s s'. eapply star_E0_ind; eauto.
    - intros s.
      rewrite star_unfold_l, <- join_ub_l.
      cbn. auto.
    - intros s s' s'' Hs' Hs''.
      rewrite star_unfold_l, <- join_ub_r.
      unfold istep at 2. rewrite <- assert_min. monad.
      rewrite <- (choose_val s') by eauto. monad.
  Qed.

  Require Import Classical.

  Global Instance pick_sim {W} :
    Monotonic
      (@pick)
      (forallr RM, forallr RN, forallr R,
        bsim_match_cont R --> sim (W:=W) RM RN (flip R)).
  Proof.
    intros M1 M2 RM N1 N2 RN A B R x y [He Hm].
    unfold pick.
    destruct (classic (ex y)) as [[s Hs] | Hns].
    - rewrite !assert_true by eauto. monad.
      rstep. clear - Hm Hs. firstorder.
    - rewrite (assert_false (ex y)) by eauto. monad.
      red. rewrite pull_top. monad.
  Qed.

  Lemma join_top_l {M N A} (x : beh M N A) :
    join top x = top.
  Proof.
    apply antisymmetry; auto using top_ref, join_ub_l.
  Qed.

  Lemma choose_as_sup {M N A} P :
    @choose M N A P = sup (fun p : sig P => ret (proj1_sig p)).
  Proof.
    apply antisymmetry; red; cbn.
    - intros t (a & Ha & Ht). subst. exists (exist P a Ha). auto.
    - intros t ([a Ha] & Ht). subst. eauto.
  Qed.

  Lemma choose_lub {M N A} (P : A -> Prop) (x : t M N A) :
    (forall a, P a -> ref (ret a) x) ->
    ref (choose P) x.
  Proof.
    intros H t (a & Ha & Ht). subst. eapply H; eauto.
  Qed.

  Lemma diverges_forever_silent s :
    diverges istep s <-> (safe L s -> Forever_silent L s).
  Proof.
    split.
    - revert s. cofix IH.
      intros s [s' Hs' Hd] Hs. cbn in Hs'.
      destruct Hs' as (t & Ht & Hts'). specialize (Ht Hs). subst.
      inversion Hts'; clear Hts'; subst.
      cbn in H0. destruct H0 as [(xs' & Hs' & Hxs') | H].
      + inversion Hxs'; clear Hxs'; subst.
        econstructor; eauto. eapply IH; eauto.
        red. intros. eapply Hs. eauto using star_step.
      + clear Hd IH.
        firstorder. subst. inversion H0; clear H0; subst.
        firstorder; subst; inversion H1.
    - destruct (classic (safe L s)) as [Hs|Hs].
      + intros Hd. apply Hd in Hs. clear Hd. revert s Hs. cofix IH.
        intros _ [s s' Hs' Hd].
        econstructor; eauto. clear - Hs'.
        unfold istep. rewrite <- assert_min. monad.
      + intros _. cofix IH.
        econstructor; eauto.
        unfold istep. rewrite assert_false by auto. monad.
  Qed.

  Lemma safe_star s s' :
    safe L s ->
    Star L s E0 s' ->
    safe L s'.
  Proof.
    intros Hs Hs'. red. intros.
    eauto using star_trans.
  Qed.

End EMBEDDING.

Hint Rewrite @assert_true @assert_false using eauto : monad.
Hint Immediate safe_star.

Global Instance smallstep_semof li : Semof li (semantics li) :=
  {
    semof L q :=
      (s <- pick (initial_state L q);
       z <- repeat (istep L) s;
       _ <- assert (safe L z);
       choose (final_state L z))%beh
  }.

Section STAR.

  Lemma star_ub {M N A} (k : nat) (f : A -> t M N A) (a : A) :
    ref (pow f k a) (star f a).
  Proof.
    apply (sup_ub (fun i => pow f i a)).
  Qed.

  Global Instance star_sim {W} :
    Monotonic
      (@star)
      (forallr RM : klr W, forallr RN : klr W, forallr RX : rel,
        (RX ++> sim RM RN RX) ++> RX ++> sim RM RN RX).
  Proof.
    intros M1 M2 RM N1 N2 RN X1 X2 RX f1 f2 Hf a1 a2 Ha.
    apply sup_sim. intros n. revert a1 a2 Ha.
    induction n; cbn; intros; repeat rstep. eauto.
  Qed.

  Lemma bind_star_star {M N A} (f : A -> t M N A) (a : A) :
    (f^* a >>= f^* = f^* a)%beh.
  Proof.
    clear.
    unfold star. setoid_rewrite Behavior.bind_sup.
    apply antisymmetry.
    - apply sup_lub. intros n. monad.
      apply sup_lub. intros n'. eapply sup_at.
      rewrite <- pow_plus. reflexivity.
    - apply sup_lub. intros n.
      apply (sup_at _ _ 0). cbn. rewrite ret_bind. monad.
  Qed.

  Hint Rewrite @bind_star_star : monad.

  Lemma bind_repeat_star {M N A} (f : A -> t M N A) (a : A) :
    (f^∞ a >>= f^* = f^∞ a)%beh.
  Proof.
    unfold repeat. monad.
  Qed.

  Lemma star_idemp {M N A} (f : A -> t M N A) :
    star (star f) = star f.
  Proof.
    apply functional_extensionality. intros a.
    apply antisymmetry.
    - rewrite <- bind_ret at 1. revert a.
      eapply star_ind_l; intro a; monad.
      apply (star_ub 0).
    - rewrite <- (star_ub 1 (f^*)%beh).
      cbn. monad.
  Qed.

  Lemma repeat_ind_sim {W M1 M2 RM N1 N2 RN A1 A2 RA} f g :
    (RA ++> sim RM RN RA)%rel f (star g) ->
    (RA ++> sim RM RN RA)%rel (divs f) (divs g) ->
    (RA ++> @sim W M1 M2 RM N1 N2 RN A1 A2 RA)%rel (f^∞)%beh (g^∞)%beh.
  Proof.
    intros Hfg Hdivs a1 a2 Ha. unfold repeat.
    rewrite <- (star_idemp g). rauto.
  Qed.

End STAR.

Section SOUNDNESS.
  Context {li1 li2} (cc : callconv li1 li2).
  Context (L1 : semantics li1).
  Context (L2 : semantics li2).
  Context {index ord} R (HR : bsim_properties cc L1 L2 index ord R).

  Require Import Classical.

  Definition srel w s2 s1 :=
    exists i, R w i s1 s2.

  Definition xrel s1 s2 w q2 q1 :=
    exists w',
      match_query cc w' q1 q2 /\
      forall r1 r2,
        match_reply cc w' r1 r2 ->
        bsim_match_cont (rexists i, R w i)
          (after_external L1 s1 r1)
          (after_external L2 s2 r2).

  Notation SIM :=
    (sim (k1 flip (match_query cc)) (k1 flip (match_reply cc))).

  Instance bind_proper M N A B:
    Proper
      (pointwise_relation A (flip ref) ==> flip ref ==> flip ref)
      (@bind M N A B).
  Proof.
    clear. red. rauto.
  Qed.

  Lemma istep_sim :
    Related (istep L2) (star (istep L1)) (|= srel ++> k1 SIM srel).
  Proof.
    intros w s2 s1 [i Hs]. red.
    destruct (classic (safe L1 s1)).
    - unfold istep at 1.
      rewrite assert_true by eauto using bsim_safe. monad.
      apply join_lub.
      + apply choose_lub.
        intros s2' Hs2'.
        edestruct @bsim_simulation as (i' & s1' & Hs1' & Hs'); eauto.
        assert (HH : Star L1 s1 E0 s1') by intuition eauto using plus_star.
        clear - HH Hs'. simpl.
        rewrite <- star_star by eauto.
        apply ret_sim. red. eauto.
      + rewrite choose_as_sup. mnorm.
        apply sup_lub. intros [q2 Hq2]. cbn.
        edestruct @bsim_match_external as (w' & s1' & q1 & Hs1' & Hq1 & Hq & H');
          eauto.
        rewrite star_unfold_r, <- join_ub_r.
        rewrite <- star_star by eauto. monad. unfold istep. monad.
        rewrite <- join_ub_r, <- (choose_val q1) by eauto. monad.
        eapply bind_sim; [ | eapply interact_sim; eauto ].
        intros r2 r1 Hr. apply pick_sim. eapply H'; eauto.
    - rewrite star_unfold_l. unfold istep at 3. monad.
      red. rewrite <- join_pull, pull_top. monad.
  Qed.

  Definition ccsim : rel (sem li2) (sem li1) :=
    |= k1 flip (match_query cc) ++> k1 SIM (k1 flip (match_reply cc)).

  Lemma soundness :
    Related (semof L2) (semof L1) ccsim.
  Proof.
    intros w q1 q2 Hq. cbn.
    rstep. rstep; [ | repeat (rstep; eauto using @bsim_initial_states) ].
    intros s2 s1 Hs. do 2 red in Hq.
    rewrite <- (bind_repeat_star (istep L1)). mnorm.
    rstep.
    - instantiate (1 := srel w). clear s1 s2 Hs q1 q2 Hq.
      intros s2 s1 [i Hs].
      destruct (classic (safe L1 s1)); monad.
      + assert (safe L2 s2) by eauto using @bsim_safe. monad.
        apply choose_lub. intros r2 Hr2.
        edestruct @bsim_match_final_states as (s1' & r1 & Hs1'& Hr & Hr1); eauto.
        rewrite <- star_star by eauto. monad.
        rewrite <- choose_val by eauto. monad.
        apply ret_sim; eauto.
      + rewrite <- (star_ub 0). cbn. monad.
        red. rewrite pull_top. monad.
    - revert s2 s1 Hs. eapply repeat_ind_sim.
      + apply istep_sim.
      + intros s2 s1 [i Hs].
        intros t [Ht ?]. subst. cbn. constructor. cbn. intuition.
        apply diverges_forever_silent. intro.
        apply diverges_forever_silent in H; eauto using bsim_safe.
        eauto using backward_simulation_forever_silent.
  Qed.

End SOUNDNESS.
