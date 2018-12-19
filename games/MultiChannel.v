Require Import LogicalRelations.
Require Import KLR.
Require Import List.
Require Import Classical.
Require Import ClassicalChoice.
Require Import DecidableClass.
Require Import ATS.


(** * Side-by-side composition *)

Module Pow.

  (** ** Game *)

  Canonical Structure g G I :=
    {|
      question := I * question G;
      answer := I * answer G;
    |}.

  Definition r {G1 G2} (GR : grel G1 G2) (I : Type) :=
    Build_grel (g G1 I) (g G2 I)
      (I * grel_world GR)
      (fun '(i, w) => req i * question_rel GR w)%rel
      (fun '(i, w) => req i * answer_rel GR w)%rel.

  Infix "^" := g : game_scope.
  Infix "^" := r : grel_scope.

  Definition mko {GA GB I} (i : I) (m : omove GA GB) : omove (GA ^ I) (GB ^ I) :=
    match m with
      | oa ma => oa (i, ma)
      | oq mq => oq (i, mq)
    end.

  Definition mkp {GA GB I} (i : I) (m : pmove GA GB) : pmove (GA ^ I) (GB ^ I) :=
    match m with
      | pq mq => pq (i, mq)
      | pa ma => pa (i, ma)
    end.

  (** ** Transition system *)

  Section ATS.
    Context {GA GB I} {S K : I -> Type} (α : forall i, ats GA GB (S i) (K i)).

    Inductive state :=
      st (k : forall j, K j) (i : I) (s : S i).

    Definition cont :=
      forall i : I, K i.

    Inductive step : state -> option state -> Prop :=
      step_intro i s s' k :
        ATS.step (α i) s s' ->
        step (st k i s) (option_map (st k i) s').

    Inductive suspend : state -> pmove (GA ^ I) (GB ^ I) * cont -> Prop :=
      suspend_intro i s k m ki k' :
        ATS.suspend (α i) s (m, ki) ->
        (forall j, i <> j -> k' j = k j) ->
        k' i = ki ->
        suspend (st k i s) (mkp i m, k').

    Inductive resume : cont -> omove (GA ^ I) (GB ^ I) -> option state -> Prop :=
      resume_intro i k m s :
        ATS.resume (α i) (k i) m s ->
        resume k (mko i m) (option_map (st k i) s).

    Inductive refuse : cont -> question (GB ^ I) -> Prop :=
      refuse_intro i k m :
        ATS.refuse (α i) (k i) m ->
        refuse k (i, m).

    Definition of :=
      ATS.Build_ats (GA ^ I) (GB ^ I) state cont step suspend resume refuse.

  End ATS.

  Arguments state {I} S K.
  Arguments cont {I} K.

  Definition strat {GA GB I} (σ : I -> strat GA GB) : strat (GA ^ I) (GB ^ I) :=
    {|
      ATS.transitions := of (fun i => ATS.transitions (σ i));
      ATS.init_cont := fun i => ATS.init_cont (σ i);
    |}.

  (** ** Monotonicity *)

  (** We can build KLRs for these two kinds of maps. *)

  Section REL.
    Context {GA1 GA2} (GRA : grel GA1 GA2).
    Context {GB1 GB2} (GRB : grel GB1 GB2).
    Context (I : Type) `{forall i j : I, Decidable (i = j)}.
    Context {S1 S2} (RS : forall i:I, klr (gworld GRA GRB) (S1 i) (S2 i)).
    Context {K1 K2} (RK : forall i:I, klr (gworld GRA GRB) (K1 i) (K2 i)).

    Definition sum_map {A1 A2} (f : A1 -> A2) {B1 B2} (g : B1 -> B2) :=
      fun x : A1 + B1 =>
        match x with
          | inl a1 => inl (f a1)
          | inr b1 => inr (g b1)
        end.

    Inductive wfw : option I -> gworld (GRA ^ I) (GRB ^ I) -> Prop :=
      | wfw_nil :
          wfw None nil
      | wfw_oq i w ws :
          wfw None ws ->
          wfw (Some i) (inr (i, w) :: ws)
      | wfw_pq i w ws :
          wfw (Some i) ws ->
          wfw None (inl (i, w) :: ws).

    Fixpoint wproj i (ws : gworld (GRA ^ I) (GRB ^ I)) : gworld GRA GRB :=
      match ws with
        | nil => nil
        | inl (j, w) :: ws' =>
          if decide (j = i) then inl w :: wproj i ws' else wproj i ws'
        | inr (j, w) :: ws' =>
          if decide (j = i) then inr w :: wproj i ws' else wproj i ws'
      end.

    Inductive state_rel ws : rel (state S1 K1) (state S2 K2) :=
      state_rel_intro i s1 s2 k1 k2 :
        wfw (Some i) ws ->
        RS i (wproj i ws) s1 s2 ->
        (forall j, i <> j -> RK j (wproj j ws) (k1 j) (k2 j)) ->
        state_rel ws (st k1 i s1) (st k2 i s2).

    Definition cont_rel : klr (gworld (GRA^I) (GRB^I)) (cont K1) (cont K2) :=
      fun ws k1 k2 =>
        wfw None ws /\
        forall i, RK i (wproj i ws) (k1 i) (k2 i).

    Lemma wproj_acc_o i mo1 m2 ws ws' :
      wfw None ws ->
      gacc (GRA ^ I) (GRB ^ I) (om (mko i mo1), m2) ws ws' ->
      exists mo2,
        m2 = om (mko i mo2) /\
        wfw (Some i) ws' /\
        gacc GRA GRB (om mo1, om mo2) (wproj i ws) (wproj i ws') /\
        forall j, i <> j -> wproj j ws' = wproj j ws.
    Proof.
      intros Hws Hws'.
      inversion Hws'; clear Hws'; subst.
      - (* OQ *)
        inversion H4; clear H4; subst.
        destruct w0 as [j w], m1, m0. simpl in H2. destruct H2 as [His Hm].
        simpl in His. destruct His. destruct mo1; inversion H0; clear H0; subst.
        exists (oq q0). simpl in *. intuition auto.
        + constructor; auto.
        + rewrite Decidable_complete by auto.
          repeat constructor; auto.
        + rewrite Decidable_sound_alt by auto.
          reflexivity.
      - (* OA *)
        inversion H4; clear H4; subst.
        destruct w0 as [j w], m1, m0. simpl in H2. destruct H2 as [His Hm].
        simpl in His. destruct His. destruct mo1; inversion H0; clear H0; subst.
        exists (oa a0). simpl in *. intuition auto.
        + inversion Hws; clear Hws; subst. auto.
        + rewrite Decidable_complete by auto.
          repeat constructor; auto.
        + rewrite Decidable_sound_alt by auto.
          reflexivity.
    Qed.        
  End REL.

  Global Instance step_sim :
    Monotonic
      (@step)
      (forallr GRA, forallr GRB, forallr - @ I,
       rforall Idec : (forall i j : I, Decidable (i = j)),
       forallr RS : fun S1 S2 => forall i, klr _ (S1 i) (S2 i),
       forallr RK : fun K1 K2 => forall i, klr _ (K1 i) (K2 i),
       (forallr - @ i, ATS.sim GRA GRB (RS i) (RK i)) ++>
       |=  state_rel GRA GRB I RS RK ++>
           k1 set_le (k1 option_ge (state_rel GRA GRB I RS RK))).
  Proof.
    intros GA1 GA2 GRA GB1 GB2 GRB I Idec S1 S2 RS K1 K2 RK.
    intros α β Hαβ ws x1 x2 Hx x1' Hx1'. destruct Hx1' as [i s1 s1' k1 Hs1'].
    inversion Hx; clear Hx. apply inj_pair2 in H1. subst.
    edestruct @ATS.sim_step as (s2' & Hs2' & Hs'); eauto.
    eexists. split.
    - econstructor; eauto.
    - repeat rstep. econstructor; eauto.
  Qed.

  Axiom proof_irrelevance : forall (P:Prop) (p1 p2:P), p1 = p2.

  Lemma update_contmap {I K} {Idec : forall i j : I, Decidable (i = j)} :
    forall i ki (k : forall j:I, K j),
      exists k' : (forall i:I, K i),
        k' i = ki /\ forall j, i <> j -> k' j = k j.
  Proof.
    intros.
    assert (Hchoi: ChoiceFacts.DependentFunctionalChoice_on K).
    {
      apply ChoiceFacts.non_dep_dep_functional_choice.
      intros. intro. apply choice.
    }
    red in Hchoi.
    destruct
      (Hchoi (fun j k'j =>
                (forall Hj, k'j = eq_rect i K ki j Hj) /\
                (i <> j -> k'j = k j))) as
      (k' & Hk').
    {
      clear. intros j. destruct (classic (i = j)).
      - destruct H. exists ki. split; try congruence.
        intros Hi. rewrite <- eq_rect_eq. reflexivity.
      - exists (k j). split; congruence.
    }
    exists k'. split.
    - specialize (Hk' i) as [H _]. specialize (H eq_refl). simpl in H. auto.
    - intros j Hj. specialize (Hk' j) as [_ H]. specialize (H Hj). auto.
  Qed.

  (* TODO: split out wproj_acc_p as appropriate *)
  Global Instance suspend_sim :
    Monotonic
      (@suspend)
      (forallr GRA, forallr GRB, forallr - @ I,
       rforall Idec : (forall i j : I, Decidable (i = j)),
       forallr RS : fun S1 S2 => forall i, klr _ (S1 i) (S2 i),
       forallr RK : fun K1 K2 => forall i, klr _ (K1 i) (K2 i),
       (forallr - @ i, ATS.sim GRA GRB (RS i) (RK i)) ++>
       |=  state_rel GRA GRB I RS RK ++>
           k1 set_le (<> * cont_rel GRA GRB I RK)).
  Proof.
    intros GA1 GA2 GRA GB1 GB2 GRB I Idec S1 S2 RS K1 K2 RK.
    intros α β Hαβ ws x1 x2 Hx x1' Hx1'.
    destruct Hx1' as [i s1 k1 m1 ki1 k1' Hki1 Hk1' Hki1'].
    inversion Hx; clear Hx. apply inj_pair2 in H1. subst.
    edestruct @ATS.sim_suspend as ([m2 k2i'] & Hmk2 & Hmk); eauto.
    destruct Hmk as (wi' & Hm & Hk).
    destruct (update_contmap i k2i' k2) as (k2' & Hk2'i & Hk2'j).
    exists (Pow.mkp i m2, k2'). split.
    - econstructor; eauto.
    - inversion Hm; clear Hm; subst.
      + inversion H6; clear H6; subst.
        exists (inl (i, w0) :: ws). split.
        * repeat constructor; auto.
        * split. { constructor. auto. }
          intros j. simpl. destruct decide eqn:Hdec.
          -- apply Decidable_sound in Hdec. subst. auto.
          -- apply Decidable_complete_alt in Hdec.
             assert (Hij : i <> j) by congruence.
             erewrite (Hk1' _ Hij), (Hk2'j _ Hij).
             auto.
      + inversion H6; clear H6; subst.
        inversion H2; clear H2; subst.
        simpl in H3. rewrite Decidable_complete in H3 by auto.
        inversion H3; clear H3; subst.
        * exists ws0. split.
          -- repeat constructor; auto.
          -- split; auto. intro j.
             specialize (H5 j). simpl wproj in H5.
             destruct decide eqn:Hj.
             ++ apply Decidable_sound in Hj. subst. auto.
             ++ apply Decidable_complete_alt in Hj.
                rewrite (Hk1' j Hj), (Hk2'j j Hj). auto.
  Qed.

  Global Instance resume_sim :
    Monotonic
      (@resume)
      (forallr GRA, forallr GRB, forallr - @ I,
       rforall Idec : (forall i j : I, Decidable (i = j)),
       forallr RS : fun S1 S2 => forall i, klr _ (S1 i) (S2 i),
       forallr RK : fun K1 K2 => forall i, klr _ (K1 i) (K2 i),
       (forallr - @ i, ATS.sim GRA GRB (RS i) (RK i)) ++>
       |=  cont_rel GRA GRB I RK ++> [] ->
           k1 set_le (k1 option_ge (state_rel GRA GRB I RS RK))).
  Proof.
    intros GA1 GA2 GRA GB1 GB2 GRB I Idec S1 S2 RS K1 K2 RK.
    intros α β Hαβ ws k1 k2 Hk m1 m2 ws' Hm s1 Hs1.
    destruct Hs1 as [i k1 m1 s1 Hs1].
    destruct Hk as [Hws Hk].
    eapply wproj_acc_o in Hm as (mo2 & Hm2 & Hws' & Hm & Hws'j); eauto.
    inversion Hm2; clear Hm2; subst.
    edestruct @ATS.sim_resume as (s2 & Hs2 & Hs); eauto. { eapply Hm. }
    exists (option_map (st k2 i) s2). split.
    - constructor; auto.
    - repeat rstep. constructor; auto.
      intros. rewrite Hws'j by auto. auto.
  Qed.

  Global Instance refuse_sim :
    Monotonic
      (@refuse)
      (forallr GRA, forallr GRB, forallr - @ I,
       rforall Idec : (forall i j : I, Decidable (i = j)),
       forallr RS : fun S1 S2 => forall i, klr _ (S1 i) (S2 i),
       forallr RK : fun K1 K2 => forall i, klr _ (K1 i) (K2 i),
       (forallr - @ i, ATS.sim GRA GRB (RS i) (RK i)) ++>
       |=  cont_rel GRA GRB I RK ++> [] -> k impl).
  Proof.
    intros GA1 GA2 GRA GB1 GB2 GRB I Idec S1 S2 RS K1 K2 RK.
    intros α β Hαβ ws k1 k2 [Hws Hk] m1 m2 ws' Hm Hm1.
    destruct Hm1 as [i k1 m1 Hm1].
    apply (wproj_acc_o GRA GRB I i (oq m1)) in Hm; auto.
    destruct Hm as (mo2 & Hm2 & Hws' & Hm & Hws'j).
    destruct mo2; inversion Hm2; clear Hm2; subst.
    constructor.
    eapply @ATS.sim_refuse; eauto. apply Hm.
  Qed.

  Global Instance of_sim :
    Monotonic
      (@of)
      (forallr GRA, forallr GRB, forallr - @ I,
       rforall Idec : (forall i j : I, Decidable (i = j)),
       forallr RS : fun S1 S2 => forall i, klr _ (S1 i) (S2 i),
       forallr RK : fun K1 K2 => forall i, klr _ (K1 i) (K2 i),
       (forallr - @ i, ATS.sim GRA GRB (RS i) (RK i)) ++>
       ATS.sim (GRA^I) (GRB^I) (state_rel GRA GRB I RS RK) (cont_rel GRA GRB I RK)).
  Proof.
    split; simpl; rauto.
  Qed.

End Pow.

Infix "^" := Pow.g : game_scope.
Infix "^" := Pow.r : grel_scope.
