Require Import LogicalRelations.
Require Import Axioms.
Require Import IntmDef.
Require Import IntmTactics.
Require Import IntmIter.
Require Import IntmDecomp.

Local Obligation Tactic := cbn; eauto.

Module Behavior.
  Import IntmDef.Behavior.
  Import IntmTactics.Behavior.
  Import IntmIter.Behavior.
  Import IntmDecomp.Behavior.

  (** *** Substitution *)

  Definition subst_step {M N P Q A} (f : M -> t P Q N) (x : t M N A) :=
    mu x >>= fun m => f m >>= fun n => ret (delta x m n).

  Definition subst {M N P Q A} (f : M -> t P Q N) (x : t M N A) :=
    repeat (subst_step f) x >>= fun y => (rho y \/ omega y)%beh.

  Lemma eta {A B} (f : A -> B) :
    (fun a => f a) = f.
  Proof.
    reflexivity.
  Qed.

  Hint Rewrite @eta : monad.
  Ltac monad := repeat mnorm; auto with monad.

  Lemma divs_flat {M N P Q A B} f :
    @divs M N P Q A B f = @divs M N P Q A B (fun a => rho (f a)).
  Proof.
    apply functional_extensionality. intro a.
    apply antisymmetry.
    - intros t [Ht Ha]. subst. split; auto. clear - Ha.
      revert a Ha. cofix IH.
      intros a [a' Ha' ?].
      eapply diverges_val; cbn; eauto.
    - intros t [Ht Ha]. subst. split; auto. clear - Ha.
      revert a Ha. cofix IH.
      intros a [a' Ha' ?].
      cbn in Ha'. destruct Ha' as [(v & Hfav & Hv) | Hu].
      + inversion Hv; clear Hv; subst. eapply diverges_val; cbn; eauto.
      + cofix IHa. exists a; eauto using closed.
  Qed.

  Lemma subst_interact {M N A} (x : t M N A) :
    subst interact x = x.
  Proof.
    eapply antisymmetry.
    - unfold subst.
      change x with ((fun x => x) x) at 2. revert x.
      apply repeat_ind_l; intros.
      + unfold subst_step.
        rewrite (decompose a) at 2.
        monad.
      + auto using rho_decr, omega_decr with monad.
      + unfold subst_step.
        rewrite divs_flat.
        repeat mnorm.
        intros t Ht. destruct Ht as [Ht Hd]. subst.
        destruct Hd; cbn in *; eauto using closed.
    - intros t Ht. unfold subst, repeat.
      rewrite bind_bind. revert x Ht.
      induction t; intros; cbn.
      + exists (val x). split; eauto 20. exists 0; auto.
      + exists (val x). split; eauto 20. exists 0; auto.
      + exists (val x). split; eauto 20. exists 0; auto.
      + exists (move m). split; eauto 20. exists 1; eauto 20.
      + specialize (IHt (delta x m n)). simpl in IHt.
        destruct IHt as (s & (k & Hs) & Hst); auto.
        exists (tcons m n s). split; eauto.
        exists (S k). cbn [pow].
        exists (tcons m n (val (delta x m n))). split; eauto 10.
        exists (val m). eauto 20 using closed.
  Qed.


  Lemma div_subst_step_ret {K L M N P Q A B} (f : M -> t P Q N) (a : A) :
    divs (subst_step f) (ret a) = @bot K L B.
  Proof.
    apply antisymmetry; auto using bot_ref.
    intros t [Ht H]. subst. exfalso.
    destruct H as [a' Ha' H].
    cbn in Ha'. clear H. firstorder congruence.
  Qed.

  Lemma div_subst_step_interact {K L M N P Q B} (f : M -> t P Q N) m :
    ref (divs (subst_step f) (interact m)) (@ups _ _ K L _ B (f m)).
  Proof.
    intros t [Ht H]. subst. cbn.
    destruct H as [a' Ha' H].
    revert Ha'. unfold subst_step. repeat mnorm. cbn.
    intros (s & Hs & Hsa').
    inversion Hsa'; clear Hsa'; subst; auto.
    cbn in *. inversion H0; clear H0; subst.
    assert (has (divs (subst_step f) (ret a)) (@div M N B)) by (cbn; eauto).
    rewrite div_subst_step_ret in H0. elim H0.
  Qed.

  Lemma subst_step_ret {M N P Q A} (f : M -> t P Q N) (a : A) :
    repeat (subst_step f) (ret a) = ret (ret a).
  Proof.
    rewrite repeat_unfold_l.
    rewrite div_subst_step_ret.
    unfold subst_step at 2.
    monad.
  Qed.

  Hint Rewrite @subst_step_ret : monad.

  Lemma pow_star {M N A} (n : nat) (f : A -> t M N A) (a : A) :
    ref (pow f n a) (star f a).
  Proof.
    firstorder.
  Qed.

  Hint Resolve pow_star : monad.

  Lemma interact_subst {M N P Q} (f : M -> t P Q N) (m : M) :
    subst f (interact m) = f m.
  Proof.
    apply antisymmetry.
    - unfold subst.
      rewrite repeat_unfold_l.
      rewrite !bind_join.
      repeat apply join_lub.
      + monad.
      + rewrite div_subst_step_interact.
        monad.
      + unfold subst_step at 2.
        set (resid := fun y => (@rho M N P Q N y \/ @omega M N P Q N N y)%beh).
        mnorm. subst resid. simpl. monad.
    - unfold subst, repeat.
      rewrite <- (pow_star 1). cbn.
      unfold subst_step. monad.
  Qed.

Lemma ref_ups_mu {M N P Q A} (x : t M N A) :
  @ref P Q _ (ups x) (mu x).
Proof.
  firstorder.
Qed.

Lemma mu_assoc {M N P Q R S A} (x : t M N A) (f : M -> t P Q N) :
  @mu P Q R S N (mu x >>= f) =
  mu x >>= (fun m => mu (f m)).
Proof.
  mnorm.
  apply antisymmetry; monad.
  apply join_lub; eauto.
  rewrite <- ref_ups_mu. monad.
Qed.

Lemma mu_divs {M N P Q R S A B} f a :
  @mu P Q R S B (@divs M N P Q A B f a) = bot.
Proof.
  apply antisymmetry; auto using bot_ref.
  intros t [(m & [Hm _] & Ht) | [Hu _]]; congruence.
Qed.

Hint Rewrite @mu_divs : monad.

Lemma join_idemp {M N A} (x : t M N A) :
  join x x = x.
Proof.
  monad.
Qed.

Hint Rewrite @join_idemp : monad.

Lemma mu_subst {M N P Q R S A} (x : t M N A) (f : M -> t P Q N) :
  @ref R S _ (mu x >>= fun m => mu (f m)) (mu (subst f x)).
Proof.
  unfold subst. rewrite repeat_unfold_l. mnorm.
  unfold subst_step at 1. mnorm.
  rewrite bind_plus. monad.
Qed.

  Lemma subst_subst {M N P Q R S A} (x: t M N A) (f: M -> t P Q N) (g: P -> t R S Q):
    subst (fun a => subst g (f a)) x = subst g (subst f x).
  Proof.
    apply antisymmetry.
    - unfold subst at 1 3.
      change (subst g (subst f x)) with ((fun x => subst g (subst f x)) x).
      revert x.
      apply repeat_ind_l.
      + intros x.
  Abort.

End Behavior.
