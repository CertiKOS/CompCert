Require Import ATS.
Require Import MultiChannel.
Require Import KLR.
Require Import List.
Require FComp.


(** * Resolution operator *)

(** The resolution operator allows a component to interact with itself
  by feeding back its own questions to it whenever possible. To make
  sure we can direct back the reply to the right component, we keep a
  stack of booleans indicating for each expected reply of the original
  transition system, whether it will answer its own question or that
  of the opponent. *)

Section ATS.
  Context {G S K} (α : ats G G S K).

  Definition state : Type := list player * S.
  Definition cont : Type := list player * K.

  Inductive step : state -> option state -> Prop :=
    | step_int s s' stk :
        ATS.step α s s' ->
        step (stk, s) (option_map (pair stk) s')
    | step_q (m : question G) s k s' stk :
        ATS.suspend α s (pq m, k) ->
        ATS.resume α k (oq m) s' ->
        step (stk, s) (option_map (pair (P :: stk)) s')
    | step_a (m : answer G) s k s' stk :
        ATS.suspend α s (pa m, k) ->
        ATS.resume α k (oa m) s' ->
        step (P :: stk, s) (option_map (pair stk) s').

  Inductive suspend : state -> pmove G G * cont -> Prop :=
    | suspend_q (m : question G) s k stk :
        ATS.suspend α s (pq m, k) ->
        ATS.refuse α k m ->
        suspend (stk, s) (pq m, (stk, k))
    | suspend_a (m : answer G) s k stk :
        ATS.suspend α s (pa m, k) ->
        suspend (O :: stk, s) (pa m, (stk, k)).

  Inductive resume : cont -> omove G G -> option state -> Prop :=
    | resume_q m k s stk :
        ATS.resume α k (oq m) s ->
        resume (stk, k) (oq m) (option_map (pair (O :: stk)) s)
    | resume_a m k s stk :
        ATS.resume α k (oa m) s ->
        resume (stk, k) (oa m) (option_map (pair stk) s).

  Inductive refuse : cont -> oqmove G G -> Prop :=
    | refuse_intro k m stk :
        ATS.refuse α k m ->
        refuse (stk, k) m.

  Definition of :=
    ATS.Build_ats G G state cont step suspend resume refuse.

End ATS.

Arguments state : clear implicits.
Arguments cont : clear implicits.

Section SIM.
  Context {G1 G2} (GR : grel G1 G2).
  Context {S1 S2} (RS : klr (gworld GR GR) S1 S2).
  Context {K1 K2} (RK : klr (gworld GR GR) K1 K2).

  Inductive extw : bool -> list player -> gworld GR GR -> gworld GR GR -> Prop :=
    | extw_nil pp :
        extw false pp nil nil
    | extw_ext pp w ws ws' :
        extw false pp ws ws' ->
        extw true (O::pp) (inr w :: ws) (inr w :: ws')
    | extw_int pp w ws ws' :
        extw true pp ws ws' ->
        extw true (P::pp) (inr w :: inl w :: ws) ws'
    | extw_dom b pp w ws ws' :
        extw (negb b) pp ws ws' ->
        extw b pp (inl w :: ws) (inl w :: ws').

  Inductive state_rel : klr (gworld GR GR) (state S1) (state S2) :=
    state_rel_intro pp ws ws' s1 s2 :
      extw true pp ws ws' ->
      RS ws s1 s2 ->
      state_rel ws' (pp, s1) (pp, s2).

  Inductive cont_rel : klr (gworld GR GR) (cont K1) (cont K2) :=
    cont_rel_intro pp ws ws' k1 k2 :
      extw false pp ws ws' ->
      RK ws k1 k2 ->
      cont_rel ws' (pp, k1) (pp, k2).
End SIM.

Global Instance step_sim :
  Monotonic
    (@step)
    (forallr GR, forallr RS, forallr RK,
      ATS.sim GR GR RS RK ++>
      |= state_rel GR RS ++> k1 set_le (k1 option_ge (state_rel GR RS))).
Proof.
  intros G1 G2 GR S1 S2 RS K1 K2 RK.
  intros α1 α2 Hα ws s1 s2 Hs s1' Hs1'.
  destruct Hs1' as
    [s1 s1' stk Hs1' | q1 s1 k1 s1' stk Hk1 Hs1' | a1 s1 k1 s1' stk Hk1 Hs1'];
  inversion Hs; clear Hs; subst.
  - (* internal step *)
    edestruct @ATS.sim_step as (s2' & Hs2' & Hs'); eauto.
    eexists. split.
    + constructor; eauto.
    + repeat rstep. econstructor; eauto.
  - (* internal question *)
    edestruct @ATS.sim_suspend as ([m2 k2] & Hqk2 & Hqk); eauto.
    destruct Hqk as (ws'' & Hq & Hk).
    apply FComp.gacc_inv_pq in Hq as (w & q2 & Hm2 & Hq & Hws''); subst.
    inversion Hm2; clear Hm2; subst.
    edestruct @ATS.sim_resume as (s2 & Hs2 & Hs); eauto.
    + instantiate (1 := inr w :: inl w :: ws0).
      instantiate (1 := oq q2).
      repeat econstructor; auto.
    + exists (option_map (pair (P :: stk)) s2). split.
      * econstructor; eauto.
      * repeat rstep. repeat econstructor; eauto.
  - (* internal answer *)
    edestruct @ATS.sim_suspend as ([m2 k2] & Hqk2 & Hqk); eauto.
    destruct Hqk as (ws'' & Hq & Hk).
    apply FComp.gacc_inv_pa in Hq as (w & a2 & Hm2 & Ha & Hws''); subst.
    inversion Hm2; clear Hm2; subst.
    inversion H2; clear H2; subst.
    edestruct @ATS.sim_resume as (s2 & Hs2 & Hs); eauto.
    + instantiate (1 := ws0).
      instantiate (1 := oa a2).
      repeat constructor; auto.
    + exists (option_map (pair stk) s2). split.
      * econstructor; eauto.
      * repeat rstep; repeat econstructor; eauto.
Qed.

Global Instance suspend_sim :
  Monotonic
    (@suspend)
    (forallr GR, forallr RS, forallr RK,
      ATS.sim GR GR RS RK ++>
      |= state_rel GR RS ++> k1 set_le (<> * cont_rel GR RK)).
Proof.
  intros G1 G2 GR S1 S2 RS K1 K2 RK α1 α2 Hα.
  intros ws s1 s2 Hs km1 Hkm1.
  destruct Hkm1 as [m1 s1 k1 stk Hsk1 Hkm1 | m1 s1 k1 stk Hmk1];
  inversion Hs; clear Hs; subst.
  - (* external P question *)
    edestruct @ATS.sim_suspend as ([m2 k2] & Hkm2 & Hkm); eauto.
    destruct Hkm as (ws'' & Hws'' & Hkm).
    apply FComp.gacc_inv_pq in Hws'' as (w & q2 & Hm2 & Hq & Hws''); subst.
    inversion Hm2; clear Hm2; subst.
    exists (pq q2, (stk, k2)). split.
    + constructor; auto.
      eapply ATS.sim_refuse; eauto.
      repeat econstructor; eauto.
    + exists (inl w :: ws). split.
      * repeat constructor; auto.
      * repeat econstructor; eauto.
  - (* external P answer *)
    edestruct @ATS.sim_suspend as ([m2 k2] & Hkm2 & Hkm); eauto.
    destruct Hkm as (ws'' & Hws'' & Hkm).
    apply FComp.gacc_inv_pa in Hws'' as (w & a2 & Hm2 & Ha & Hws''); subst.
    inversion Hm2; clear Hm2; subst.
    inversion H2; clear H2; subst.
    exists (pa a2, (stk, k2)). split.
    + constructor; auto.
    + exists ws'. split.
      * repeat constructor; auto.
      * repeat econstructor; eauto.
Qed.

Global Instance resume_sim :
  Monotonic
    (@resume)
    (forallr GR, forallr RS, forallr RK,
     ATS.sim GR GR RS RK ++>
     |= cont_rel GR RK ++> ([] -> k1 set_le (k1 option_ge (state_rel GR RS)))).
Proof.
  intros G1 G2 GR S1 S2 RS K1 K2 RK.
  intros α1 α2 Hα ws k1 k2 Hk m1 m2 ws' Hm s1 Hs1.
  destruct Hs1 as [q1 k1 s1 stk Hs1 | a1 k1 s1 stk Hs1];
  inversion Hk; clear Hk; subst;
  inversion Hm; clear Hm; subst.
  - (* external O question *)
    inversion H5; clear H5; subst.
    edestruct @ATS.sim_resume as (s2 & Hs2 & Hs); eauto.
    + instantiate (1 := inr w0 :: ws0).
      instantiate (1 := oq m0).
      repeat constructor; auto.
    + exists (option_map (pair (O :: stk)) s2). split.
      * constructor; auto.
      * repeat rstep. repeat econstructor; eauto.
  - inversion H5.
  - inversion H5.
  - (* external O answer *)
    inversion H5; clear H5; subst.
    inversion H2; clear H2; subst.
    edestruct @ATS.sim_resume as (s2 & Hs2 & Hs); eauto.
    + instantiate (1 := ws).
      instantiate (1 := oa m0).
      repeat constructor; auto.
    + exists (option_map (pair stk) s2). split.
      * constructor; auto.
      * repeat rstep. repeat econstructor; eauto.
Qed.

Global Instance refuse_sim :
  Monotonic
    (@refuse)
    (forallr GR, forallr RS, forallr RK,
     ATS.sim GR GR RS RK ++>
     |= cont_rel GR RK ++> ([] -> k impl)).
Proof.
  intros G1 G2 GR S1 S2 RS K1 K2 RK.
  intros α1 α2 Hα ws k1 k2 Hk m1 m2 ws' Hm Hm1.
  destruct Hm1;
  inversion Hk; clear Hk; subst;
  inversion Hm; clear Hm; subst;
  inversion H6; clear H6; subst.
  constructor.
  eapply ATS.sim_refuse, H; eauto.
  instantiate (1 := inr w0 :: ws0).
  repeat constructor; auto.
Qed.

Global Instance of_sim :
  Monotonic
    (@of)
    (forallr GR, forallr RS, forallr RK,
     ATS.sim GR GR RS RK ++>
     ATS.sim GR GR (state_rel GR RS) (cont_rel GR RK)).
Proof.
  intros G1 G2 GR S1 S2 RS K1 K2 RK α1 α2 H.
  split; simpl; rauto.
Qed.
