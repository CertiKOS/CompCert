Require Import ATS.
Require Import KLR.



Module Obs.

  (** ** Definition *)

  Section ATS.
    Context {GA GB : game} {S K} (α : ats GA GB S K).

    Inductive reachable : relation S :=
      | reachable_refl s mk :
          ATS.suspend α s mk ->
          reachable s s
      | reachable_step s s' s'' :
          ATS.step α s s' ->
          reachable s' s'' ->
          reachable s s''.

    CoInductive diverges (s : S) : Prop :=
      | forever_internal_intro s' :
          ATS.step α s s' ->
          diverges s' ->
          diverges s.

    Inductive step : option S -> option S -> Prop :=
      | step_intro : step None None.

    Inductive suspend : option S -> pmove GA GB * K -> Prop :=
      | suspend_intro s mk :
          ATS.suspend α s mk ->
          suspend (Some s) mk.

    Inductive resume : K -> omove GA GB -> option S -> Prop :=
      | resume_reachable k m s s' :
          ATS.resume α k m s ->
          reachable s s' ->
          resume k m (Some s')
      | resume_diverges k m s :
          ATS.resume α k m s ->
          diverges s ->
          resume k m None.

    Definition of :=
      ATS.Build_ats GA GB (option S) K step suspend resume (ATS.refuse α).
  End ATS.

  (** ** Monotonicity *)

  Global Instance reachable_sim :
    Monotonic
      (@reachable)
      (forallr GRA, forallr GRB, forallr RS, forallr RK,
       ATS.sim GRA GRB RS RK ++> |= RS ++> k1 set_le RS).
  Proof.
    intros GA1 GA2 GRA GB1 GB2 GRB S1 S2 RS K1 K2 RK α1 α2 Hα w.
    intros s1 s2 Hs s1' Hs1'. revert s2 Hs.
    induction Hs1' as [s1 mk1 H1 | s1 s1' s1'' Hs1' Hs1'' IHs1'']; intros.
    - edestruct @ATS.sim_suspend as (mk2 & Hmk2 & Hmk); eauto.
      eauto using reachable_refl.
    - edestruct @ATS.sim_step as (s2' & Hs2' & Hs'); eauto.
      edestruct IHs1'' as (s2'' & Hs2'' & Hs''); eauto.
      eauto using reachable_step.
  Qed.

  Global Instance diverges_sim :
    Monotonic
      (@diverges)
      (forallr GRA, forallr GRB, forallr RS, forallr RK,
       ATS.sim GRA GRB RS RK ++> |= RS ++> k impl).
  Proof.
    intros GA1 GA2 GRA GB1 GB2 GRB S1 S2 RS K1 K2 RK α1 α2 Hα w.
    cofix IH.
    intros s1 s2 Hs Hs1.
    destruct Hs1 as [s1' Hs1' Hs1'd].
    edestruct @ATS.sim_step as (s2' & Hs2' & Hs'); [ eauto .. | ].
    econstructor; eauto.
    eapply IH; eauto.
  Qed.

  Global Instance step_sim :
    Monotonic
      (@step)
      (forallr RS, option_rel RS ++> set_le (option_rel RS)).
  Proof.
    intros S1 S2 RS s1 s2 Hs s1' Hs1'.
    destruct Hs1'; inversion Hs; subst.
    exists None; repeat constructor.
  Qed.

  Global Instance suspend_sim :
    Monotonic
      (@suspend)
      (forallr GRA, forallr GRB, forallr RS, forallr RK,
       ATS.sim GRA GRB RS RK ++>
       |= k1 option_rel RS ++> k1 set_le (<> * RK)).
  Proof.
    intros GA1 GA2 GRA GB1 GB2 GRB S1 S2 RS K1 K2 RK α1 α2 Hα w.
    intros s1 s2 Hs mk1 Hmk1.
    destruct Hmk1 as [s1 mk1 Hmk1]; inversion Hs; clear Hs; subst.
    edestruct @ATS.sim_suspend as (mk2 & Hmk2 & Hmk); eauto.
    exists mk2; intuition auto.
    constructor; auto.
  Qed.

  Global Instance resume_sim :
    Monotonic
      (@resume)
      (forallr GRA, forallr GRB, forallr RS, forallr RK,
       ATS.sim GRA GRB RS RK ++>
       |= RK ++> [] -> k1 set_le (k1 option_rel RS)).
  Proof.
    intros GA1 GA2 GRA GB1 GB2 GRB S1 S2 RS K1 K2 RK α1 α2 Hα w.
    intros k1 k2 Hk m1 m2 w' Hm s1 Hs1.
    destruct Hs1 as [k1 m1 s1 s1' Hs1 Hs1' | k1 m1 s1 Hs1 Hd].
    - edestruct @ATS.sim_resume as (s2 & Hs2 & Hs); eauto.
      edestruct @reachable_sim as (s2' & Hs2' & Hs'); eauto.
      exists (Some s2'); split.
      + eauto using resume_reachable.
      + rauto.
    - edestruct @ATS.sim_resume as (s2 & Hs2 & Hs); eauto.
      exists None; split.
      + eapply resume_diverges; eauto.
        eapply diverges_sim; eauto.
      + rauto.
  Qed.

  Global Instance of_sim :
    Monotonic
      (@of)
      (forallr GRA, forallr GRB, forallr RS, forallr RK,
       ATS.sim GRA GRB RS RK ++> ATS.sim GRA GRB (k1 option_rel RS) RK).
  Proof.
    split; simpl; rauto.
  Qed.

End Obs.
