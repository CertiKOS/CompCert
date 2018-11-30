Require Import ATS.
Require Import MultiChannel.
Require Import List.


(** The flat composition of a family of alternating transition systems
  switches between them with each opponent question, allowing one
  component to proceed when all the others refuse. To match incoming
  answers with the right component, we keep a stack of ids which
  remembers what component asked what pending question. *)

Module FComp.
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
          ATS.suspend α s (Pow.mkp i (inl m), k) ->
          suspend (s, stk) (inl m, (k, i :: stk))
      | suspend_a (m : answer GB) i s k stk :
          ATS.suspend α s (Pow.mkp i (inr m), k) ->
          suspend (s, stk) (inr m, (k, stk)).

    Inductive resume : cont -> omove GA GB -> state -> Prop :=
      | resume_q (m : question GB) i s k stk :
          (forall j, ATS.refuse α k (j, m)) ->
          ATS.resume α k (Pow.mko i (inr m)) s ->
          resume (k, stk) (inr m) (s, stk)
      | resume_a (m : answer GA) i s k stk :
          ATS.resume α k (Pow.mko i (inl m)) s ->
          resume (k, i :: stk) (inl m) (s, stk).

    Inductive refuse : cont -> oqmove GA GB -> Prop :=
      | refuse_intro (m : question GB) k stk :
          (forall i, ATS.refuse α k (i, m)) ->
          refuse (k, stk) m.

    Definition of :=
      ATS.Build_ats GA GB state cont step suspend resume refuse.

  End ATS.
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
          ATS.suspend α s (inl m, k) ->
          ATS.resume α k (inr m) s' ->
          step (s, stk) (s', true :: stk)
      | step_a (m : answer G) s k s' stk :
          ATS.suspend α s (inr m, k) ->
          ATS.resume α k (inl m) s' ->
          step (s, true :: stk) (s', stk).

    Inductive suspend : state -> pmove G G * cont -> Prop :=
      | suspend_q (m : question G) s k stk :
          ATS.suspend α s (inl m, k) ->
          ATS.refuse α k m ->
          suspend (s, stk) (inl m, (k, stk))
      | suspend_a (m : answer G) s k stk :
          ATS.suspend α s (inr m, k) ->
          suspend (s, false :: stk) (inr m, (k, stk)).

    Inductive resume : cont -> omove G G -> state -> Prop :=
      | resume_q m k s stk :
          ATS.resume α k (inr m) s ->
          resume (k, stk) (inr m) (s, false :: stk)
      | resume_a m k s stk :
          ATS.resume α k (inl m) s ->
          resume (k, stk) (inl m) (s, stk).

    Inductive refuse : cont -> oqmove G G -> Prop :=
      | refuse_intro k m stk :
          ATS.refuse α k m ->
          refuse (k, stk) m.

    Definition of :=
      ATS.Build_ats G G state cont step suspend resume refuse.

  End ATS.
End Res.
