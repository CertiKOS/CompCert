Require Export LogicalRelations.
Require Export OptionRel.
Require Export Games.
Require Import KLR.
Require Import List.


(** * Alternating transition systems *)

Module ATS.

  (** ** Definition *)

  Record ats {GA GB S K} :=
    {
      step : S -> option S -> Prop;
      suspend : S -> pmove GA GB * K -> Prop;
      resume : K -> omove GA GB -> option S -> Prop;
      refuse : K -> question GB -> Prop;
    }.

  Arguments ats : clear implicits.

  Record strat {GA GB} :=
    {
      state : Type;
      cont : Type;
      transitions :> ats GA GB state cont;
      init_cont : cont;
    }.

  Arguments strat : clear implicits.

  (** ** Simulations *)

  Section SIM.
    Context {GA1 GA2} (GRA : grel GA1 GA2).
    Context {GB1 GB2} (GRB : grel GB1 GB2).
    Context {S1 S2} (RS : klr (gworld GRA GRB) S1 S2).
    Context {K1 K2} (RK : klr (gworld GRA GRB) K1 K2).

    Record sim (α1 : ats GA1 GB1 S1 K1) (α2 : ats GA2 GB2 S2 K2) :=
      {
        sim_step :
          (|= RS ++> k1 set_le (k1 option_ge RS))%rel (step α1) (step α2);
        sim_suspend :
          (|= RS ++> k1 set_le (<> * RK))%rel (suspend α1) (suspend α2);
        sim_resume :
          (|= RK ++> [] -> k1 set_le (k1 option_ge RS))%rel (resume α1) (resume α2);
        sim_refuse :
          (|= RK ++> [] -> k impl)%rel (refuse α1) (refuse α2);
      }.
  End SIM.

  Global Instance step_sim :
    Monotonic
      (@step)
      (forallr GRA, forallr GRB, forallr RS, forallr RK,
       sim GRA GRB RS RK ++> |= RS ++> k1 set_le (k1 option_ge RS)).
  Proof.
    firstorder.
  Qed.

  Global Instance suspend_sim :
    Monotonic
      (@suspend)
      (forallr GRA, forallr GRB, forallr RS, forallr RK,
       sim GRA GRB RS RK ++> |= RS ++> k1 set_le (<> * RK)).
  Proof.
    firstorder.
  Qed.

  Global Instance resume_sim :
    Monotonic
      (@resume)
      (forallr GRA, forallr GRB, forallr RS, forallr RK,
       sim GRA GRB RS RK ++> |= RK ++> [] -> k1 set_le (k1 option_ge RS)).
  Proof.
    repeat intro. eapply sim_resume; eauto.
  Qed.

  Global Instance refuse_sim :
    Monotonic
      (@refuse)
      (forallr GRA, forallr GRB, forallr RS, forallr RK,
       sim GRA GRB RS RK ++> |= RK ++> [] -> k impl).
  Proof.
    firstorder.
  Qed.

  (** Identity and composition *)

  Global Instance sim_id G S K :
    Reflexive (sim (@grel_id G) (@grel_id G) (k (@eq S)) (k (@eq K))).
  Proof.
    split.
    - intros w s _ [ ]. rstep. reflexivity || admit.
    - intros w s _ [ ]. rstep. reflexivity || admit.
    - intros w k _ [ ]. reflexivity || admit.
    - intros w k _ [ ]. reflexivity || admit.
  Admitted.

  (* some version of:
  Global Instance sim_compose {GA GB GC GRAB GRBC A B C RAB RBC RAC} :
    (forall wab wbc, RDecompose (RAB wab) (RBC wbc) (RAC (wab, wbc))) ->
    (forall wab wbc, RCompose (RAB wab) (RBC wbc) (RAC (wab, wbc))) ->
    @RCompose (ats GA A) (ats GB B) (ats GC C)
      (sim GRAB RAB)
      (sim GRBC RBC)
      (sim (grel_compose GRAB GRBC) RAC).
   *)

  (** ** Refinement *)

  Definition ref {GA1 GA2 GRA GB1 GB2 GRB} {σ1: strat GA1 GB1} {σ2: strat GA2 GB2} :=
    exists RS RK,
      sim GRA GRB RS RK σ1 σ2 /\
      RK nil (init_cont σ1) (init_cont σ2).

  Arguments ref {GA1 GA2} GRA {GB1 GB2} GRB σ1 σ2.

  Global Instance ref_id G :
    Reflexive (ref (@grel_id G) (@grel_id G)).
  Proof.
    intros σ.
    eexists _, _. split.
    - apply sim_id.
    - reflexivity.
  Qed.

  (** ** Nonbranching *)

  


  (** ** Traces *)

  Inductive strace {GA GB S K} (α : ats GA GB S K) : option S -> play GA GB -> Prop :=
    | strace_step s s' t :
        step α s s' ->
        strace α s' t ->
        strace α (Some s) (tau :: t)
    | strace_suspend s m k t :
        suspend α s (m, k) ->
        ktrace α k t ->
        strace α (Some s) (ext (pm m) :: t)
    | strace_crash :
        strace α None (crash :: nil)
  with ktrace {GA GB S K} (α : ats GA GB S K) : K -> play GA GB -> Prop :=
    | ktrace_nil k :
        ktrace α k nil
    | ktrace_omove k m :
        ktrace α k (ext (om m) :: nil)
    | ktrace_resume k m s t :
        resume α k m s ->
        strace α s t ->
        ktrace α k (ext (om m) :: t)
    | ktrace_refuse k m :
        refuse α k m ->
        ktrace α k (ext (oq m) :: refused :: nil).

  Definition traces {GA GB} (σ : strat GA GB) : play GA GB -> Prop :=
    ktrace σ (init_cont σ).

End ATS.

Notation ats := ATS.ats.
Notation strat := ATS.strat.
