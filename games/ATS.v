Require Import LogicalRelations.
Require Import KLR.
Require Import List.
Require Import Games.

(** ** Alternating transition systems *)

Record ats {GA GB S K} :=
  {
    step : S -> S -> Prop;
    suspend : S -> pmove GA GB * K -> Prop;
    resume : K -> omove GA GB -> S -> Prop;
    refuse : K -> question GB -> Prop;
  }.

Arguments ats : clear implicits.

Section SIM.
  Context {GA1 GA2} (GRA : grel GA1 GA2).
  Context {GB1 GB2} (GRB : grel GB1 GB2).
  Context {S1 S2} (RS : klr (gworld GRA GRB) S1 S2).
  Context {K1 K2} (RK : klr (gworld GRA GRB) K1 K2).

  Record sim (α1 : ats GA1 GB1 S1 K1) (α2 : ats GA2 GB2 S2 K2) :=
    {
      step_sim :
        (|= RS ++> k1 set_le RS)%rel (step α1) (step α2);
      suspend_sim :
        (|= RS ++> k1 set_le (<> * RK))%rel (suspend α1) (suspend α2);
      resume_sim :
        (|= RK ++> [] -> k1 set_le RS)%rel (resume α1) (resume α2);
      refuse_sim :
        (|= RK ++> [] -> k impl)%rel (refuse α1) (refuse α2);
    }.
End SIM.

(** ** Strategies *)

Record strategy {GA GB : game} :=
  {
    state : Type;
    cont : Type;
    transitions :> ats GA GB state cont;
    init_cont : cont;
  }.

Record ref {GA1 GA2} (GRA: grel GA1 GA2) {GB1 GB2} (GRB: grel GB1 GB2) σ1 σ2 :=
  {
    state_rel : klr (gworld GRA GRB) (state σ1) (state σ2);
    cont_rel : klr (gworld GRA GRB) (cont σ1) (cont σ2);
    ref_transitions : sim GRA GRB state_rel cont_rel σ1 σ2;
    ref_init_cont : cont_rel nil (init_cont σ1) (init_cont σ2);
  }.

(** ** Traces *)

Inductive strace {GA GB S K} (α : ats GA GB S K) : S -> play GA GB -> Prop :=
  | strace_step s s' t :
      step α s s' ->
      strace α s' t ->
      strace α s (tau :: t)
  | strace_suspend s m k t :
      suspend α s (m, k) ->
      ktrace α k t ->
      strace α s (ext (pm m) :: t)
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
