Require Import LogicalRelations.
Require Import KLR.
Require Import Axioms.
Require Import Errors.
Require Import LanguageInterface.
Require Import Smallstep.
Require Import SmallstepInteraction.
Require Import Clight.
Require Import Asm.
Require Import Compiler.
Require Import IntmDef.
Require Import IntmTactics.
Require Import IntmIter.
Require Import IntmDecomp.
Require Import IntmAbs.

Import IntmDef.Behavior.
Import IntmIter.Behavior.
Import IntmAbs.Behavior.


(** * Semantic domains *)

Definition zero {li} : sem li :=
  fun q => bot.

Definition plus {li} (σ1 σ2 : sem li) : sem li :=
  fun q => join (σ1 q) (σ2 q).

Lemma plus_assoc {li} (σ1 σ2 σ3 : sem li) :
  plus (plus σ1 σ2) σ3 = plus σ1 (plus σ2 σ3).
Proof.
  apply functional_extensionality.
  unfold plus. monad.
Qed.

Lemma plus_comm {li} (σ1 σ2 : sem li) :
  plus σ1 σ2 = plus σ2 σ1.
Proof.
  apply functional_extensionality.
  unfold plus. monad.
Qed.

Lemma plus_zero_l {li} (σ : sem li) :
  plus zero σ = σ.
Proof.
  apply functional_extensionality.
  unfold plus, zero. monad.
Qed.

Lemma plus_zero_r {li} (σ : sem li) :
  plus σ zero = σ.
Proof.
  apply functional_extensionality.
  unfold plus, zero. monad.
Qed.

Infix "+" := plus : behavior_scope.
Notation "0" := zero : behavior_scope.

Global Instance plus_ccsim :
  Monotonic
    (@plus)
    (forallr cc : flip callconv, ccsim cc ++> ccsim cc ++> ccsim cc).
Proof.
  unfold plus, ccsim.
  repeat rstep.
  - eapply H; eauto.
  - eapply H0; eauto.
Qed.


(** * CompCert compilation unit semantics *)

Global Instance clight_sem : Semof li_c Clight.program :=
  {
    semof p := 〚Clight.semantics2 p〛;
  }.

Global Instance asm_sem : Semof li_asm Asm.program :=
  {
    semof p := 〚Asm.semantics p〛;
  }.

Lemma compcert_correct (p : Clight.program) (tp : Asm.program) :
  transf_clight_program p = OK tp ->
  ccsim cc_compcert 〚tp〛 〚p〛.
Proof.
  intros H.
  apply transf_clight_program_correct in H.
  destruct H.
  eapply soundness; eauto.
Qed.


(** * Multi-module semantics *)

Require Import List.
Local Open Scope behavior_scope.

(** ** Definition *)

Global Instance mmsem `(Semof) : Semof li (list P) :=
  {
    semof :=
      fold_right (fun p x => 〚p〛 + x) 0;
  }.

Lemma mmsem_app `{Semof} (p1 p2 : list P) :
  〚p1 ++ p2〛 = 〚p1〛 + 〚p2〛.
Proof.
  induction p1; eauto.
  - cbn.
    rewrite plus_zero_l.
    reflexivity.
  - cbn in *.
    rewrite IHp1, plus_assoc.
    reflexivity.
Qed.

(** ** Multi-module compiler *)

Definition mmcompcert : list Clight.program -> res (list Asm.program) :=
  fold_right
    (fun p r =>
       match r, transf_clight_program p with
         | OK ltp, OK tp => OK (tp :: ltp)
         | Error msg, _ => Error msg
         | _, Error msg => Error msg
       end)
    (OK nil).

Lemma mmcompcert_correct lp ltp :
  mmcompcert lp = OK ltp ->
  ccsim cc_compcert 〚ltp〛 〚lp〛.
Proof.
  revert ltp. induction lp as [ | p lp IHlp].
  - inversion 1; clear H; subst. cbn.
    unfold ccsim, zero, sim. repeat rstep. monad.
  - intros ltp Hltp.
    cbn in *.
    destruct mmcompcert as [xltp|msg] eqn:Hxltp; try congruence.
    destruct transf_clight_program as [tp|msg] eqn:Htp; try congruence.
    inversion Hltp; clear Hltp; subst. cbn.
    unfold ccsim, plus. do 5 rstep.
    + apply compcert_correct; eauto.
    + apply IHlp; eauto.
Qed.
