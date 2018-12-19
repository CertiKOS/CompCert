Require Import ATS.
Require Import MultiChannel.
Require Import KLR.
Require Import List.


(** * Flat composition *)

(** The flat composition of a family of alternating transition systems
  switches between them with each opponent question, allowing one
  component to proceed when all the others refuse. To match incoming
  answers with the right component, we keep a stack of ids which
  remembers what component asked what pending question. *)

(** ** Definition *)

Section ATS.
  Context {GA GB : game} {I S K} (α : ats (GA ^ I) (GB ^ I) S K).

  Definition state : Type := list I * S.
  Definition cont : Type := list I * K.

  Inductive step : state -> option state -> Prop :=
    | step_intro s s' stk :
        ATS.step α s s' ->
        step (stk, s) (option_map (pair stk) s').

  Inductive suspend : state -> pmove GA GB * cont -> Prop :=
    | suspend_q (m : question GA) i s k stk :
        ATS.suspend α s (Pow.mkp i (pq m), k) ->
        suspend (stk, s) (pq m, (i :: stk, k))
    | suspend_a (m : answer GB) i s k stk :
        ATS.suspend α s (Pow.mkp i (pa m), k) ->
        suspend (stk, s) (pa m, (stk, k)).

  Inductive resume : cont -> omove GA GB -> option state -> Prop :=
    | resume_q (m : question GB) i s k stk :
        (forall j, i <> j -> ATS.refuse α k (j, m)) ->
        ATS.resume α k (Pow.mko i (oq m)) s ->
        resume (stk, k) (oq m) (option_map (pair stk) s)
    | resume_a (m : answer GA) i s k stk :
        ATS.resume α k (Pow.mko i (oa m)) s ->
        resume (i :: stk, k) (oa m) (option_map (pair stk) s).

  Inductive refuse : cont -> oqmove GA GB -> Prop :=
    | refuse_intro (m : question GB) k stk :
        (forall i, ATS.refuse α k (i, m)) ->
        refuse (stk, k) m.

  Definition of :=
    ATS.Build_ats GA GB state cont step suspend resume refuse.

End ATS.

Arguments state : clear implicits.
Arguments cont : clear implicits.

Definition strat {GA GB I} (σ : strat (GA ^ I) (GB ^ I)) :=
  ATS.Build_strat GA GB _ _ (of (ATS.transitions σ)) (nil, ATS.init_cont σ).

(** ** Monotonicity *)

Section SIMREL.
  Context {I : Type}.
  Context {GA1 GB1 : game} {S1 K1} (α1 : ats (GA1 ^ I) (GB1 ^ I) S1 K1).
  Context {GA2 GB2 : game} {S2 K2} (α2 : ats (GA2 ^ I) (GB2 ^ I) S2 K2).
  Context {GRA : grel GA1 GA2} {GRB : grel GB1 GB2}.

  Fixpoint wstack (ws : gworld (GRA ^ I) (GRB ^ I)) : list I :=
    match ws with
      | inl w :: ws => fst w :: wstack ws
      | inr w :: ws => wstack ws
      | nil => nil
    end.

  Fixpoint wproj (ws : gworld (GRA ^ I) (GRB ^ I)) : gworld GRA GRB :=
    match ws with
      | inl w :: ws => inl (snd w) :: wproj ws
      | inr w :: ws => inr (snd w) :: wproj ws
      | nil => nil
    end.

  Inductive state_rel (RS : klr _ S1 S2) : klr _ (state I S1) (state I S2) :=
    state_rel_intro ws s1 s2 :
      RS ws s1 s2 ->
      state_rel RS (wproj ws) (wstack ws, s1) (wstack ws, s2).

  Inductive cont_rel (RK : klr _ K1 K2) : klr _ (cont I K1) (cont I K2) :=
    cont_rel_intro ws k1 k2 :
      RK ws k1 k2 ->
      cont_rel RK (wproj ws) (wstack ws, k1) (wstack ws, k2).
End SIMREL.

Global Instance step_sim :
  Monotonic
    (@step)
    (forallr GRA, forallr GRB, forallr - @ I, forallr RS, forallr RK,
      ATS.sim (GRA ^ I) (GRB ^ I) RS RK ++>
      |= state_rel RS ++> k1 set_le (k1 option_ge (state_rel RS))).
Proof.
  intros GA1 GA2 GRA GB1 GB2 GRB I S1 S2 RS K1 K2 RK.
  intros α1 α2 Hα ws s1 s2 Hs s1' Hs1'.
  destruct Hs1' as [s1 s1' stk Hs1'].
  inversion Hs as [iws xs1 xs2]; clear Hs; subst.
  edestruct @ATS.sim_step as (s2' & Hs2' & Hs'); eauto.
  exists (option_map (pair (wstack iws)) s2'). intuition idtac.
  - constructor; auto.
  - repeat rstep. constructor; auto.
Qed.

Lemma gacc_inv_pq {GA1 GA2} GRA {GB1 GB2} GRB q1 m2 ws ws' :
  @gacc GA1 GA2 GRA GB1 GB2 GRB (pm (pq q1), m2) ws ws' ->
  exists w q2,
    m2 = pm (pq q2) /\
    question_rel GRA w q1 q2 /\
    ws' = inl w :: ws.
Proof.
  intros H.
  inversion H; clear H; subst;
  inversion H4; clear H4; subst.
  eauto.
Qed.

Lemma gacc_inv_pa {GA1 GA2} GRA {GB1 GB2} GRB a1 m2 ws ws' :
  @gacc GA1 GA2 GRA GB1 GB2 GRB (pm (pa a1), m2) ws ws' ->
  exists w a2,
    m2 = pm (pa a2) /\
    answer_rel GRB w a1 a2 /\
    ws = inr w :: ws'.
Proof.
  intros H.
  inversion H; clear H; subst;
  inversion H4; clear H4; subst.
  eauto.
Qed.

Global Instance suspend_sim :
  Monotonic
    (@suspend)
    (forallr GRA, forallr GRB, forallr - @ I, forallr RS, forallr RK,
      ATS.sim (GRA ^ I) (GRB ^ I) RS RK ++>
      |= state_rel RS ++> k1 set_le (<> * cont_rel RK)).
Proof.
  intros GA1 GA2 GRA GB1 GB2 GRB I S1 S2 RS K1 K2 RK.
  intros α1 α2 Hα ws mk1 mk2 Hmk mk1' Hmk1'.
  destruct Hmk1' as [q1 i1 s1 k1 stk H1 | a1 i1 s1 k1 stk H1];
  inversion Hmk; clear Hmk; subst.
  - edestruct @ATS.sim_suspend as ([m2 k2] & Hmk2 & Hmk); eauto.
    destruct Hmk as (ws' & Hws' & Hk). simpl in Hws'. 
    apply gacc_inv_pq in Hws' as (w & q2 & Hm2 & Hq & Hws'). subst.
    inversion Hm2; clear Hm2; subst.
    simpl in Hq. destruct w as [i w].
    rinversion Hq; clear Hq. destruct H. inversion Hql; clear Hql; subst.
    eexists (pq b2, (_, k2)). split.
    + constructor; eauto.
    + red. eexists (wproj (inl (i1, w) :: ws0)). split.
      * constructor. constructor. auto.
      * constructor. auto.
  - edestruct @ATS.sim_suspend as ([m2 k2] & Hmk2 & Hmk); eauto.
    destruct Hmk as (ws' & Hws' & Hk). simpl in Hws'. 
    apply gacc_inv_pa in Hws' as (w & a2 & Hm2 & Ha & Hws). subst.
    inversion Hm2; clear Hm2; subst.
    simpl in Ha. destruct w as [i w].
    rinversion Ha; clear Ha. destruct H. inversion Hal; clear Hal; subst.
    eexists (pa b2, (_, k2)). split.
    + econstructor; eauto.
    + eexists (wproj ws'). split.
      * constructor. constructor. auto.
      * simpl. constructor. auto.
Qed.

Global Instance resume_sim :
  Monotonic
    (@resume)
    (forallr GRA, forallr GRB, forallr - @ I, forallr RS, forallr RK,
     ATS.sim (GRA ^ I) (GRB ^ I) RS RK ++>
     |= cont_rel RK ++> ([] -> k1 set_le (k1 option_ge (state_rel RS)))).
Proof.
  intros GA1 GA2 GRA GB1 GB2 GRB I S1 S2 RS K1 K2 RK.
  intros α1 α2 Hα ws k1 k2 Hk m1 m2 ws' Hm s1 Hs1.
  destruct Hs1 as [q1 i1 s1 k1 stk Hr1 Hs1 | a1 i1 s1 k1 stk Hs1];
  inversion Hk; clear Hk; subst;
  inversion Hm; clear Hm; subst.
  - inversion H4; clear H4; subst.
    edestruct @ATS.sim_resume as (s2 & Hs2 & Hs); eauto.
    + instantiate (1 := inr (i1, w0) :: ws0).
      instantiate (1 := Pow.mko i1 (oq m0)).
      repeat constructor. simpl. auto.
    + exists (option_map (pair (wstack ws0)) s2). split.
      * econstructor; eauto.
        intros j Hj. eapply ATS.sim_refuse, Hr1; eauto.
        instantiate (1 := inr (j, w0) :: ws0).
        repeat constructor; eauto.
      * change (_ :: _) with (wproj (inr (i1, w0) :: ws0)).
        change (wstack ws0) with (wstack (inr (i1, w0) :: ws0)).
        repeat rstep. constructor; auto.
  - inversion H4.
  - inversion H5.
  - inversion H5; clear H5; subst.
    destruct ws0 as [ | [w|w] ws]; inversion H4; clear H4; subst.
    simpl in H. inversion H; clear H; subst.
    destruct w as [i w]; cbv [fst snd] in *.
    edestruct @ATS.sim_resume as (s2 & Hs2 & Hs); eauto.
    + instantiate (1 := ws).
      instantiate (1 := Pow.mko i (oa m0)).
      repeat constructor. simpl. auto.
    + exists (option_map (pair (wstack ws)) s2). split.
      * constructor; auto.
      * repeat rstep. constructor; auto.
Qed.

Global Instance refuse_sim :
  Monotonic
    (@refuse)
    (forallr GRA, forallr GRB, forallr - @ I, forallr RS, forallr RK,
     ATS.sim (GRA ^ I) (GRB ^ I) RS RK ++>
     |= cont_rel RK ++> ([] -> k impl)).
Proof.
  intros GA1 GA2 GRA GB1 GB2 GRB I S1 S2 RS K1 K2 RK.
  intros α1 α2 Hα ws k1 k2 Hk m1 m2 ws' Hm Hm1.
  destruct Hm1;
  inversion Hk; clear Hk; subst;
  inversion Hm; clear Hm; subst;
  inversion H5; clear H5; subst.
  constructor. intro i.
  eapply ATS.sim_refuse, H; eauto.
  instantiate (1 := inr (i, w0) :: ws0).
  instantiate (1 := i).
  repeat constructor; auto.
Qed.

Global Instance of_sim :
  Monotonic
    (@of)
    (forallr GRA, forallr GRB, forallr - @ I, forallr RS, forallr RK,
     ATS.sim (GRA ^ I) (GRB ^ I) RS RK ++>
     ATS.sim GRA GRB (state_rel RS) (cont_rel RK)).
Proof.
  intros GA1 GA2 GRA GB1 GB2 GRB I S1 S2 RS K1 K2 RK α1 α2 H.
  split; simpl; try rauto.
Qed.

Global Instance strat_sim :
  Monotonic
    (@strat)
    (forallr GRA, forallr GRB, forallr - @ I,
     ATS.ref (GRA ^ I) (GRB ^ I) ++> ATS.ref GRA GRB).
Proof.
  intros GA1 GA2 GRA GB1 GB2 GRB I σ1 σ2 Hσ.
  destruct Hσ as (RS & RK & Hσ & Hk0).
  eexists _, _. simpl. split.
  - rauto.
  - apply cont_rel_intro with (ws := nil); auto.
Qed.

(** ** Properties *)

(** *** Singleton flattening *)

(** The flat composition of a single strategy leaves it unchanged. *)

Fixpoint outls {A B} (ws : list (A + B)) : list A :=
  match ws with
    | nil => nil
    | inl a :: ws' => a :: outls ws'
    | inr b :: ws' => outls ws'
  end.

Module Singl.
  Section SINGL.
    Context {GA GB} (σ : ATS.strat GA GB).

    Let Fσ := strat (Pow.strat (fun i : unit => σ)).

    Inductive state_rel : klr _ (ATS.state Fσ) (ATS.state σ) :=
      state_rel_intro ws k s :
        pworld (@grel_id GA) (@grel_id GB) ws ->
        state_rel ws (outls ws, Pow.st k tt s) s.

    Inductive cont_rel : klr _ (ATS.cont Fσ) (ATS.cont σ) :=
      cont_rel_intro ws k :
        oworld (@grel_id GA) (@grel_id GB) ws ->
        cont_rel ws (outls ws, k) (k tt).

    Lemma le :
      ATS.ref grel_id grel_id Fσ σ.
    Proof.
      exists state_rel, cont_rel. split.
      - split; simpl in *.
        + intros _ _ _ [ws k s Hws] fs' Hfs'.
          inversion Hfs' as [? ps' ? Hps']; clear Hfs'; subst. simpl in Hps'.
          inversion Hps' as [? ? s' ? Hs']; clear Hps'; subst.
          eexists s'. intuition auto.
          destruct s' as [s' | ]; repeat (constructor; auto).
        + intros _ _ _ [ws k s Hws] fmk Hfmk.
          inversion Hfmk as [q ? ? pk ? Hpmk | a ? ? pk ? Hpmk]; clear Hfmk; subst;
          inversion Hpmk as [? ? ? ? ki k' Hk' _ Hki]; clear Hpmk; subst;
          destruct m; inversion H2; clear H2; subst.
          * exists (pq q, pk tt). intuition auto.
            exists (inl tt :: ws). repeat (constructor; auto).
          * exists (pa a, pk tt). intuition auto.
            destruct Hws as [w ws Hws].
            exists ws. simpl. repeat (constructor; auto).
        + intros _ _ _ [ws k Hws] m1 m2 ws' Hm fs Hfs.
          inversion Hfs as [q ? ps ? ? _ Hps | a ? ps ? ? Hps]; clear Hfs; subst;
          inversion Hps as [? ? ? s Hs]; clear Hps; subst.
          * destruct i, m; inversion H0; clear H0; subst.
            inversion Hm; clear Hm; subst;
            inversion H3; clear H3; subst. destruct H2.
            exists s. repeat (constructor; auto).
            change (outls ws) with (outls (inr w0 :: ws)).
            destruct s; repeat (constructor; auto).
          * destruct i, m; inversion H1; clear H1; subst.
            inversion Hm; clear Hm; subst;
            inversion H4; clear H4; subst. destruct H3.
            exists s. repeat (constructor; auto).
            inversion H; clear H; subst.
            destruct s; repeat (constructor; auto).
            inversion Hws; auto.
        + intros _ _ _ [ws k Hws] m1 m2 ws' Hm Hfref.
          inversion Hfref as [q ? ? Hpref]; clear Hfref; subst.
          specialize (Hpref tt).
          inversion Hpref as [? ? ? Href]; clear Hpref; subst.
          inversion Hm; clear Hm; subst;
          inversion H3; clear H3; subst. destruct H2.
          auto.
      - repeat constructor.
    Qed.

    Lemma ge :
      ATS.ref grel_id grel_id σ Fσ.
    Proof.
      exists (k1 flip state_rel), (k1 flip cont_rel). split.
      - split; simpl in *.
        + intros _ _ _ [ws k s Hws] s' Hs'.
          eexists. split; repeat (constructor; eauto).
          destruct s' as [s' | ]; repeat (constructor; auto).
        + intros _ _ _ [ws k s Hws] [[q|r] k'] Hk'.
          * exists (pq q, (outls (inl tt :: ws), fun 'tt => k')).
            split; repeat (econstructor; eauto). intros [ ]. congruence.
          * destruct Hws as [w ws Hws].
            exists (pa r, (outls ws, fun 'tt => k')). split.
            -- repeat (econstructor; eauto). intros [ ]. congruence.
            -- exists ws. repeat (constructor; auto).
        + intros _ _ _ [ws k Hws] m1 m2 ws' Hm s Hs.
          inversion Hm; clear Hm; subst;
          inversion H3; clear H3; subst; destruct H2.
          * eexists (option_map (pair (outls (inr _ :: ws))) (option_map _ s)).
            repeat (econstructor; eauto).
            -- destruct j. congruence.
            -- destruct s; repeat (constructor; auto).
          * destruct w0.
            eexists (option_map (pair _) (option_map _ s)).
            repeat (econstructor; eauto).
            destruct s; repeat (constructor; auto).
            inversion Hws; auto.
        + intros _ _ _ [ws k Hws] m1 m2 ws' Hm Href.
          inversion Hm; clear Hm; subst;
          inversion H3; clear H3; subst; destruct H2.
          constructor. intros [ ]. constructor. auto.
      - constructor. constructor.
    Qed.
  End SINGL.
End Singl.
