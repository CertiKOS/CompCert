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

Module FComp.

  (** ** Definition *)

  Section ATS.
    Context {GA GB : game} {I S K} (α : ats (GA ^ I) (GB ^ I) S K).

    Definition state : Type := S * list I.
    Definition cont : Type := K * list I.

    Inductive step : state -> state -> Prop :=
      | step_intro s s' stk :
          ATS.step α s s' ->
          step (s, stk) (s', stk).

    Inductive suspend : state -> pmove GA GB * cont -> Prop :=
      | suspend_q (m : question GA) i s k stk :
          ATS.suspend α s (Pow.mkp i (pq m), k) ->
          suspend (s, stk) (pq m, (k, i :: stk))
      | suspend_a (m : answer GB) i s k stk :
          ATS.suspend α s (Pow.mkp i (pa m), k) ->
          suspend (s, stk) (pa m, (k, stk)).

    Inductive resume : cont -> omove GA GB -> state -> Prop :=
      | resume_q (m : question GB) i s k stk :
          (forall j, ATS.refuse α k (j, m)) ->
          ATS.resume α k (Pow.mko i (oq m)) s ->
          resume (k, stk) (oq m) (s, stk)
      | resume_a (m : answer GA) i s k stk :
          ATS.resume α k (Pow.mko i (oa m)) s ->
          resume (k, i :: stk) (oa m) (s, stk).

    Inductive refuse : cont -> oqmove GA GB -> Prop :=
      | refuse_intro (m : question GB) k stk :
          (forall i, ATS.refuse α k (i, m)) ->
          refuse (k, stk) m.

    Definition of :=
      ATS.Build_ats GA GB state cont step suspend resume refuse.

  End ATS.

  Arguments state : clear implicits.
  Arguments cont : clear implicits.

  (** ** Monotonicity *)

  Section SIMREL.
    Context {I : Type}.
    Context {GA1 GB1 : game} {S1 K1} (α1 : ats (GA1 ^ I) (GB1 ^ I) S1 K1).
    Context {GA2 GB2 : game} {S2 K2} (α2 : ats (GA2 ^ I) (GB2 ^ I) S2 K2).
    Context {GRA : grel GA1 GA2} {GRB : grel GB1 GB2}.

    Definition sum_map {A1 A2} f {B1 B2} g : A1 + B1 -> A2 + B2 :=
      fun x =>
        match x with
          | inl a => inl (f a)
          | inr b => inr (g b)
        end.

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
        state_rel RS (wproj ws) (s1, wstack ws) (s2, wstack ws).

    Inductive cont_rel (RK : klr _ K1 K2) : klr _ (cont I K1) (cont I K2) :=
      cont_rel_intro ws k1 k2 :
        RK ws k1 k2 ->
        cont_rel RK (wproj ws) (k1, wstack ws) (k2, wstack ws).
  End SIMREL.

  Global Instance step_sim :
    Monotonic
      (@step)
      (forallr GRA, forallr GRB, forallr - @ I, forallr RS, forallr RK,
        ATS.sim (GRA ^ I) (GRB ^ I) RS RK ++>
        |= state_rel RS ++> k1 set_le (state_rel RS)).
  Proof.
    intros GA1 GA2 GRA GB1 GB2 GRB I S1 S2 RS K1 K2 RK.
    intros α1 α2 Hα ws s1 s2 Hs s1' Hs1'.
    destruct Hs1' as [s1 s1' stk Hs1'].
    inversion Hs as [iws xs1 xs2]; clear Hs; subst.
    edestruct @ATS.sim_step as (s2' & Hs2' & Hs'); eauto.
    exists (s2', wstack iws). intuition idtac.
    - constructor; auto.
    - constructor; auto.
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
      eexists (pq b2, (k2, _)). split.
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
      eexists (pa b2, (k2, _)). split.
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
       |= cont_rel RK ++> ([] -> k1 set_le (state_rel RS))).
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
      + exists (s2, wstack ws0). split.
        * econstructor; eauto.
          intro j. eapply ATS.sim_refuse, Hr1; eauto.
          instantiate (1 := inr (j, w0) :: ws0).
          instantiate (1 := j). simpl.
          repeat constructor; eauto.
        * change (_ :: _) with (wproj (inr (i1, w0) :: ws0)).
          change (wstack ws0) with (wstack (inr (i1, w0) :: ws0)).
          constructor; auto.
    - inversion H4.
    - inversion H5.
    - inversion H5; clear H5; subst.
      destruct ws0 as [ | [w|w] ws]; inversion H4; clear H4; subst.
      simpl in H2. inversion H2; clear H2; subst.
      destruct w as [i w]; cbv [fst snd] in *.
      edestruct @ATS.sim_resume as (s2 & Hs2 & Hs); eauto.
      + instantiate (1 := ws).
        instantiate (1 := Pow.mko i (oa m0)).
        repeat constructor. simpl. auto.
      + exists (s2, wstack ws). split.
        * constructor; auto.
        * constructor; auto.
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

End FComp.

(** The resolution operator allows a component to interact with itself
  by feeding back its own questions to it whenever possible. To make
  sure we can direct back the reply to the right component, we keep a
  stack of booleans indicating for each expected reply of the original
  transition system, whether it will answer its own question or that
  of the opponent. *)

Module Res.
  Section ATS.
    Context {G S K} (α : ats G G S K).

    Definition state : Type := S * list bool.
    Definition cont : Type := K * list bool.

    Inductive step : state -> state -> Prop :=
      | step_int s s' stk :
          ATS.step α s s' ->
          step (s, stk) (s', stk)
      | step_q (m : question G) s k s' stk :
          ATS.suspend α s (pq m, k) ->
          ATS.resume α k (oq m) s' ->
          step (s, stk) (s', true :: stk)
      | step_a (m : answer G) s k s' stk :
          ATS.suspend α s (pa m, k) ->
          ATS.resume α k (oa m) s' ->
          step (s, true :: stk) (s', stk).

    Inductive suspend : state -> pmove G G * cont -> Prop :=
      | suspend_q (m : question G) s k stk :
          ATS.suspend α s (pq m, k) ->
          ATS.refuse α k m ->
          suspend (s, stk) (pq m, (k, stk))
      | suspend_a (m : answer G) s k stk :
          ATS.suspend α s (pa m, k) ->
          suspend (s, false :: stk) (pa m, (k, stk)).

    Inductive resume : cont -> omove G G -> state -> Prop :=
      | resume_q m k s stk :
          ATS.resume α k (oq m) s ->
          resume (k, stk) (oq m) (s, false :: stk)
      | resume_a m k s stk :
          ATS.resume α k (oa m) s ->
          resume (k, stk) (oa m) (s, stk).

    Inductive refuse : cont -> oqmove G G -> Prop :=
      | refuse_intro k m stk :
          ATS.refuse α k m ->
          refuse (k, stk) m.

    Definition of :=
      ATS.Build_ats G G state cont step suspend resume refuse.

  End ATS.
End Res.
