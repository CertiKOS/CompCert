Require Import ATS.
Require Import KLR.
Require Import Classical.

Module Obs.

  (** ** Definition *)

  Section ATS.
    Context {GA GB : game} {S K} (α : ats GA GB S K).

    Inductive state := st (mk : pmove GA GB * K) | div.

    Inductive reachable : rel (option S) (option _) :=
      | reachable_suspend s mk :
          ATS.suspend α s mk ->
          reachable (Some s) (Some (st mk))
      | reachable_none :
          reachable None None
      | reachable_step s s' s'' :
          ATS.step α s s' ->
          reachable s' s'' ->
          reachable (Some s) s''.

    CoInductive diverges (s : S) : Prop :=
      | forever_internal_intro s' :
          ATS.step α s (Some s') ->
          diverges s' ->
          diverges s.

    Inductive step : state -> option state -> Prop :=
      | step_intro : step div (Some div).

    Inductive suspend : state -> pmove GA GB * K -> Prop :=
      | suspend_intro mk : suspend (st mk) mk.

    Inductive resume : K -> omove GA GB -> option state -> Prop :=
      | resume_reachable k m s s' :
          ATS.resume α k m s ->
          reachable s s' ->
          resume k m s'
      | resume_diverges k m s :
          ATS.resume α k m (Some s) ->
          diverges s ->
          resume k m (Some div).

    Definition of :=
      ATS.Build_ats GA GB state K step suspend resume (ATS.refuse α).
  End ATS.

  Arguments state : clear implicits.

  Definition strat {GA GB} (σ : strat GA GB) :=
    {|
      ATS.transitions := of (ATS.transitions σ);
      ATS.init_cont := ATS.init_cont σ;
    |}.

  (** ** Monotonicity *)

  Section SIM.
    Context {GA1 GA2} (GRA : grel GA1 GA2).
    Context {GB1 GB2} (GRB : grel GB1 GB2).
    Context {S1 S2} (RS : klr (gworld GRA GRB) S1 S2).
    Context {K1 K2} (RK : klr (gworld GRA GRB) K1 K2).

    Inductive state_rel : klr _ (state GA1 GB1 K1) (state GA2 GB2 K2) :=
      | st_rel :
          (|= (<> * RK) ++> state_rel)%rel st st
      | div_rel :
          (|= state_rel)%rel div div.

    Lemma reachable_sim :
      Monotonic reachable
        (ATS.sim GRA GRB RS RK ++>
         |= k1 option_ge RS ++> k1 set_le (k1 option_ge state_rel)).
    Proof.
      intros α1 α2 Hα w s1 s2 Hs s1' Hs1'. revert s2 Hs.
      induction Hs1' as [s1 mk1 Hmk1 | | s1 s1' s1'' Hs1' Hs1'' IHs1'']; intros;
      inversion Hs; clear Hs; subst;
      try solve [exists None; repeat constructor; auto].
      - edestruct @ATS.sim_suspend as (mk2 & Hmk2 & Hmk); eauto.
        exists (Some (st mk2)). repeat constructor; auto.
      - edestruct @ATS.sim_step as (s2' & Hs2' & Hs'); eauto.
        edestruct IHs1'' as (s2'' & Hs2'' & Hs''); eauto.
        exists s2''; split; auto.
        eapply reachable_step; eauto.
    Qed.

    Lemma diverges_sim α1 α2 w s1 s2 :
      ATS.sim GRA GRB RS RK α1 α2 ->
      RS w s1 s2 ->
      diverges α1 s1 ->
      diverges α2 s2 \/ reachable α2 (Some s2) None.
    Proof.
      intros Hα Hs Hs1.
      destruct (classic (reachable α2 (Some s2) None)) as [ | Hsafe]; auto. left.
      revert s1 s2 Hsafe Hs Hs1. cofix IH. intros.
      destruct Hs1 as [s1' Hs1' Hs1'd].
      edestruct @ATS.sim_step as (os2' & Hs2' & Hos'); [ eauto .. | ].
      inversion Hos' as [xs1' s2' Hs' | xs1']; clear Hos'; subst.
      - econstructor; eauto.
        eapply IH; eauto.
        intros Hs2'safe. apply Hsafe. econstructor; eauto.
      - elim Hsafe. repeat econstructor; eauto.
    Qed.

    Lemma step_sim :
      Monotonic step (|= state_rel ++> k1 set_le (k1 option_ge state_rel)).
    Proof.
      intros w s1 s2 Hs s1' Hs1'.
      destruct Hs1'; inversion Hs; subst.
      exists (Some div); repeat constructor.
    Qed.

    Lemma suspend_sim :
      Monotonic suspend (|= state_rel ++> k1 set_le (<> * RK)).
    Proof.
      intros w s1 s2 Hs mk1 Hmk1. destruct Hmk1 as [mk1].
      inversion Hs as [xw xmk1 mk2 Hmk | ]; clear Hs; subst.
      exists mk2; repeat constructor; auto.
    Qed.

    Lemma resume_sim :
      Monotonic resume
        (ATS.sim GRA GRB RS RK ++>
         |= RK ++> [] -> k1 set_le (k1 option_ge state_rel)).
    Proof.
      intros α1 α2 Hα w k1 k2 Hk m1 m2 w' Hm s1 Hs1.
      destruct Hs1 as [k1 m1 s1 s1' Hs1 Hs1' | k1 m1 s1 Hs1 Hd].
      - edestruct @ATS.sim_resume as (s2 & Hs2 & Hs); eauto.
        edestruct @reachable_sim as (s2' & Hs2' & Hs'); eauto.
        exists s2'; split.
        + eauto using resume_reachable.
        + rauto.
      - edestruct @ATS.sim_resume as (os2 & Hs2 & Hos); eauto.
        inversion Hos as [xs1 s2 Hs | xs1]; clear Hos; subst.
        + edestruct diverges_sim as [Hs2d | Hs2c]; eauto.
          * exists (Some div). repeat constructor; auto.
            eapply resume_diverges; eauto.
          * exists None. repeat constructor; auto.
            eapply resume_reachable; eauto.
        + exists None. repeat constructor; auto.
          eapply resume_reachable; eauto. constructor.
    Qed.
  End SIM.

  Global Instance of_sim :
    Monotonic
      (@of)
      (forallr GRA, forallr GRB, forallr RS, forallr RK,
       ATS.sim GRA GRB RS RK ++> ATS.sim GRA GRB (state_rel GRA GRB RK) RK).
  Proof.
    split; simpl; repeat rstep.
    - eapply step_sim; eauto.
    - eapply suspend_sim; eauto.
    - eapply resume_sim; eauto.
  Qed.

End Obs.
