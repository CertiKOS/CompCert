Require Import LogicalRelations.
Require Import IntmDef.
Require Import IntmTactics.

Local Obligation Tactic := cbn; eauto.

Module Behavior.
  Import IntmDef.Behavior.
  Import IntmTactics.Behavior.

  (** *** Decomposition *)

  Program Definition rho {M N P Q A} (x : t M N A) : t P Q A :=
    {|
      has t := (exists v, has x (val v) /\ t = val v) \/ has x undef;
    |}.
  Next Obligation.
    firstorder. subst. inversion H0. eauto.
  Qed.

  Program Definition mu {M N P Q A} (x : t M N A) : t P Q M :=
    {|
      has t := (exists m, has x (move m) /\ t = val m) \/ has x undef;
    |}.
  Next Obligation.
    firstorder. subst. inversion H0. eauto.
  Qed.

  Program Definition omega {M N P Q A B} (x : t M N A) : t P Q B :=
    {|
      has t := (has x div /\ t = div) \/ has x undef;
    |}.
  Next Obligation.
    firstorder. subst. inversion H0. eauto.
  Qed.

  Program Definition ups {M N P Q A B} (x : t M N A) : t P Q B :=
    {|
      has t := has x undef;
    |}.

  Program Definition delta {M N A} (x : t M N A) (m : M) (n : N) : t M N A :=
    {| has t := has x (tcons m n t) |}.
  Next Obligation.
    eauto using closed.
  Qed.

  (** *** Relational properties *)

  Global Instance rho_ref :
    Monotonic
      (@rho)
      (forallr -, forallr -, forallr -, forallr -, forallr -, ref ++> ref).
  Proof.
    firstorder.
  Qed.

  Global Instance mu_ref :
    Monotonic
      (@mu)
      (forallr -, forallr -, forallr -, forallr -, forallr -, ref ++> ref).
  Proof.
    firstorder.
  Qed.

  Global Instance omega_ref :
    Monotonic
      (@omega)
      (forallr -, forallr -, forallr -, forallr -, forallr -, forallr -,
        ref ++> ref).
  Proof.
    firstorder.
  Qed.

  Global Instance ups_ref :
    Monotonic
      (@ups)
      (forallr -, forallr -, forallr -, forallr -, forallr -, forallr -,
        ref ++> ref).
  Proof.
    firstorder.
  Qed.

  Global Instance delta_ref :
    Monotonic
      (@delta)
      (forallr -,forallr -,forallr -, ref ++> eq ==> eq ==> ref).
  Proof.
    repeat rstep; subst; firstorder.
  Qed.

  (** *** Various properties *)

  Lemma rho_decr {M N A} (x : t M N A) :
    ref (rho x) x.
  Proof.
    destruct 1; firstorder subst; eauto using closed.
  Qed.

  Lemma omega_decr {M N A} (x : t M N A) :
    ref (omega x) x.
  Proof.
    destruct 1; firstorder subst; eauto using closed.
  Qed.

  Lemma decompose {M N A} (x : t M N A) :
    x = (rho x \/
         omega x \/
         mu x >>= fun m => interact m >>= delta x m)%beh.
  Proof.
    apply antisymmetry.
    - intros t Ht. simpl.
      destruct t; eauto 20.
      + right. right. exists (val m). intuition eauto.
        constructor. simpl. eauto.
      + right. right. exists (val m). intuition eauto using closed.
        constructor. simpl. eauto.
        exists (tcons m n (val n)). intuition eauto.
    - repeat apply join_lub.
      + apply rho_decr.
      + apply omega_decr.
      + intros t (s & [(m & Hm & Hs) | H] & Hst); subst; eauto using closed.
        inversion Hst; clear Hst; subst. simpl in H0.
        destruct H0 as (? & [? | (? & ?)] & Hst); subst.
        * inversion Hst; auto.
        * inversion Hst; clear Hst; subst.
          inversion H3; clear H3; subst.
          simpl in H0. auto.
  Qed.

  (** *** Components of various constructions *)

  (** [ret] *)

  Lemma rho_ret {M N P Q A} (v : A) :
    rho (@ret M N A v) = @ret P Q A v.
  Proof.
    apply antisymmetry; red; cbn; firstorder (subst; eauto; try congruence).
  Qed.

  Lemma mu_ret {M N P Q A} (v : A) :
    @mu M N P Q A (ret v) = bot.
  Proof.
    apply antisymmetry; red; cbn; firstorder congruence.
  Qed.

  Lemma omega_ret {M N P Q A B} (v : A) :
    @omega M N P Q A B (ret v) = bot.
  Proof.
    apply antisymmetry; red; cbn; firstorder congruence.
  Qed.

  Lemma ups_ret {M N P Q A B} (v : A) :
    @ups M N P Q A B (ret v) = bot.
  Proof.
    apply antisymmetry; red; cbn; firstorder congruence.
  Qed.

  Lemma delta_ret {M N A} (v : A) (m : M) (n : N) :
    delta (ret v) m n = bot.
  Proof.
    apply antisymmetry; firstorder congruence.
  Qed.

  Hint Rewrite @rho_ret @mu_ret @omega_ret @ups_ret @delta_ret : monad.

  (** [bind] *)

  Hint Extern 1 (has _ _) => progress cbn.

  Lemma rho_bind {M N P Q A B} (x : t M N A) (f : A -> t M N B) :
    rho (P:=P) (Q:=Q) (x >>= f) = rho x >>= fun a => rho (f a).
  Proof.
    apply antisymmetry.
    - intros t Ht. cbn in *.
      destruct Ht as [(v & (s & Hs & Hsv) & Ht) | (s & Hs & Hsv)]; subst;
      inversion Hsv; clear Hsv; subst; eauto 20.
    - intros t (s & [(v & Hv & Hsv) | H] & Hst); subst; cbn; eauto.
      inversion Hst; clear Hst; subst; cbn in *. firstorder.
  Qed.

  Lemma mu_bind {M N P Q A B} (x : t M N A) (f : A -> t M N B) :
    mu (P:=P) (Q:=Q) (x >>= f) =
    join (mu x) (rho x >>= fun a => mu (f a)).
  Proof.
    apply antisymmetry.
    - intros t [(m & (s & Hs & Hst) & Ht) | (s & Hs & Hst)]; subst;
      inversion Hst; clear Hst; subst; eauto 20.
    - apply join_lub.
      + intros t [(m & Hm & Ht) | H]; subst; cbn; eauto 10.
      + intros t (s & [(v & Hv & Ht) | H] & Hst); subst; eauto 10.
        inversion Hst; clear Hst; subst. firstorder.
  Qed.

  Lemma omega_bind {M N P Q A B C} (x : t M N A) (f : A -> t M N B) :
    omega (P:=P) (Q:=Q) (B:=C) (x >>= f) =
    join (omega x) (rho x >>= fun a => omega (f a)).
  Proof.
    apply antisymmetry.
    - intros t. firstorder subst. inversion H1; clear H1; subst; eauto 20.
      inversion H0; clear H0; subst; firstorder eauto 10.
    - intros t. firstorder subst; eauto 10.
      inversion H0; clear H0; subst. firstorder.
  Qed.

  Lemma ups_bind {M N P Q A B C} (x : t M N A) (f : A -> t M N B) :
    @ups M N P Q B C (x >>= f) =
    join (ups x) (rho x >>= fun a => ups (f a)).
  Proof.
    apply antisymmetry.
    - intro t. firstorder subst. inversion H0; clear H0; subst; eauto 20.
    - intro t. firstorder subst; eauto 20. inversion H0; clear H0; subst; eauto.
  Qed.

  Lemma delta_bind {M N A B} (x : t M N A) (f : A -> t M N B) m n :
    delta (x >>= f) m n =
    join (delta x m n >>= f) (rho x >>= fun a => delta (f a) m n).
  Proof.
    apply antisymmetry.
    - intros t (s & Hs & Hst).
      destruct s; inversion Hst; clear Hst; subst; cbn; eauto 10.
    - intros t [(s & Hs & Hst) | (s & Hs & Hst)]; cbn in *; firstorder.
      subst. inversion Hst; clear Hst; subst. cbn in *. eauto.
  Qed.

  Hint Rewrite @rho_bind @mu_bind @omega_bind @ups_bind @delta_bind : monad.

  (** [interact] *)

  Lemma rho_interact {M N P Q} m :
    @rho M N P Q N (interact m) = bot.
  Proof.
    apply antisymmetry; firstorder congruence.
  Qed.

  Lemma mu_interact {M N P Q} m :
    @mu M N P Q N (interact m) = ret m.
  Proof.
    apply antisymmetry; try firstorder congruence.
    intros _ [ ]. eauto 10.
  Qed.

  Lemma omega_interact {M N P Q A} m :
    @omega M N P Q N A (interact m) = bot.
  Proof.
    apply antisymmetry; firstorder congruence.
  Qed.

  Lemma ups_interact {M N P Q A} m :
    @ups M N P Q N A (interact m) = bot.
  Proof.
    apply antisymmetry; firstorder congruence.
  Qed.

  Lemma delta_interact {M N} (m m' : M) (n : N) :
    delta (interact m) m' n = guard (m = m') >>= fun _ => ret n.
  Proof.
    apply antisymmetry.
    - intros t [Htm | (n' & Htmn)].
      + congruence.
      + inversion Htmn; clear Htmn; subst. eauto 10.
    - intros t (s & [Hm Hs] & Hst). subst.
      inversion Hst; clear Hst; subst.
      destruct H0. eauto.
  Qed.

  Hint Rewrite
    @rho_interact
    @mu_interact
    @omega_interact
    @ups_interact
    @delta_interact
    : monad.

  (** [join] *)

  Lemma rho_join {M N P Q A} (x y : t M N A) :
    @rho M N P Q A (join x y) = join (rho x) (rho y).
  Proof.
    apply antisymmetry; firstorder.
  Qed.

  Lemma mu_join {M N P Q A} (x y : t M N A) :
    @mu M N P Q A (join x y) = join (mu x) (mu y).
  Proof.
    apply antisymmetry; firstorder.
  Qed.

  Lemma omega_join {M N P Q A B} (x y : t M N A) :
    @omega M N P Q A B (join x y) = join (omega x) (omega y).
  Proof.
    apply antisymmetry; firstorder.
  Qed.

  Lemma ups_join {M N P Q A B} (x y : t M N A) :
    @ups M N P Q A B (join x y) = join (ups x) (ups y).
  Proof.
    apply antisymmetry; firstorder.
  Qed.

  Lemma delta_join {M N A} (x y : t M N A) m n :
    @delta M N A (join x y) m n = join (delta x m n) (delta y m n).
  Proof.
    apply antisymmetry; firstorder.
  Qed.

  Hint Rewrite @rho_join @mu_join @omega_join @ups_join @delta_join : monad.

  (** [rho] *)

  Lemma rho_rho {M N P Q R S A} (x : t M N A) :
    @rho P Q R S A (@rho M N P Q A x) = @rho M N R S A x.
  Proof.
    apply antisymmetry; firstorder congruence.
  Qed.

  Lemma mu_rho {M N P Q R S A} (x : t M N A) :
    @mu P Q R S A (@rho M N P Q A x) = ups x.
  Proof.
    apply antisymmetry; firstorder congruence.
  Qed.

  Lemma omega_rho {M N P Q R S A B} (x : t M N A) :
    @omega P Q R S A B (@rho M N P Q A x) = ups x.
  Proof.
    apply antisymmetry; firstorder congruence.
  Qed.

  Lemma ups_rho {M N P Q R S A B} (x : t M N A) :
    @ups P Q R S A B (@rho M N P Q A x) = ups x.
  Proof.
    apply antisymmetry; firstorder congruence.
  Qed.

  Lemma delta_rho {M N P Q A} (x : t M N A) m n :
    delta (@rho M N P Q A x) m n = ups x.
  Proof.
    apply antisymmetry; firstorder congruence.
  Qed.

  Hint Rewrite @rho_rho @mu_rho @omega_rho @ups_rho @delta_rho : monad.

  (** [mu] *)

  Lemma rho_mu {M N P Q R S A} (x : t M N A) :
    @rho P Q R S M (@mu M N P Q A x) = mu x.
  Proof.
    apply antisymmetry; firstorder congruence.
  Qed.

  Lemma mu_mu {M N P Q R S A} (x : t M N A) :
    @mu P Q R S M (@mu M N P Q A x) = ups x.
  Proof.
    apply antisymmetry; firstorder congruence.
  Qed.

  Lemma omega_mu {M N P Q R S A B} (x : t M N A) :
    @omega P Q R S M B (@mu M N P Q A x) = ups x.
  Proof.
    apply antisymmetry; firstorder congruence.
  Qed.

  Lemma ups_mu {M N P Q R S A} (x : t M N A) :
    @ups P Q R S M A (@mu M N P Q A x) = ups x.
  Proof.
    apply antisymmetry; firstorder congruence.
  Qed.

  Lemma delta_mu {M N P Q A} x m n :
    delta (@mu M N P Q A x) m n = ups x.
  Proof.
    apply antisymmetry; firstorder congruence.
  Qed.

  Hint Rewrite @rho_mu @mu_mu @omega_mu @ups_mu @delta_mu : monad.

  (** [omega] *)

  Lemma rho_omega {M N P Q R S A B} (x : t M N A) :
    @rho P Q R S B (@omega M N P Q A B x) = ups x.
  Proof.
    apply antisymmetry; firstorder congruence.
  Qed.

  Lemma mu_omega {M N P Q R S A B} (x : t M N A) :
    @mu P Q R S B (@omega M N P Q A B x) = ups x.
  Proof.
    apply antisymmetry; firstorder congruence.
  Qed.

  Lemma omega_omega {M N P Q R S A B C} (x : t M N A) :
    @omega P Q R S B C (@omega M N P Q A B x) = omega x.
  Proof.
    apply antisymmetry; firstorder congruence.
  Qed.

  Lemma ups_omega {M N P Q R S A B C} (x : t M N A) :
    @ups P Q R S B C (@omega M N P Q A B x) = ups x.
  Proof.
    apply antisymmetry; firstorder congruence.
  Qed.

  Lemma delta_omega {M N P Q A B} x m n :
    delta (@omega M N P Q A B x) m n = ups x.
  Proof.
    apply antisymmetry; firstorder congruence.
  Qed.

  Hint Rewrite @rho_omega @mu_omega @omega_omega @ups_omega @delta_omega : monad.




  (** Bind and bot *)

  Lemma bind_mu_bot {M N P Q A B} x :
    (@mu M N P Q A x >>= fun _ => @bot P Q B) = ups x.
  Proof.
    apply antisymmetry; intro; firstorder subst.
    - inversion H0; contradiction.
    - cbn in *. eauto.
  Qed.

  Hint Rewrite @bind_mu_bot : monad.

Global Instance subrel_subrelation {A} (R R' : relation A) :
  RAuto (subrel R R') -> subrelation R R'.
Proof.
  firstorder.
Qed.


  Lemma bind_ups {M N P Q A B C} (x : t M N A) (f : B -> t P Q C) :
    ups x >>= f = ups x.
  Proof.
    apply antisymmetry; firstorder eauto 10.
  Qed.

  Hint Rewrite @bind_ups : monad.

  Lemma ups_decr {M N A} (x : t M N A) :
    ref (ups x) x.
  Proof.
    red. cbn. eauto using closed.
  Qed.

  Hint Resolve ups_decr : monad.

End Behavior.
