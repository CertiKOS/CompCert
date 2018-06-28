
Require Import Relations.
Require Import Wellfounded.
Require Import Coqlib.
Require Import Events.
Require Import Globalenvs.
Require Import Integers.
Require Import Smallstep.

Definition cont {li} (L: semantics li) := query li -> state L -> Prop.

Inductive apply_cont {li} L (k: @cont li L) q: option (state L) -> Prop :=
  | apply_cont_some s :
      k q s -> apply_cont L k q (Some s)
  | apply_cont_none :
      (forall s, ~ k q s) -> apply_cont L k q None.

(** * Flat composition *)

(** The flat composition of transition systems essentially corresponds
  to the union of strategies: if component [i] handles a given query,
  then the flat composition will handle it in a similar way. However,
  the components cannot call each other. *)

Module FComp.
  Section FLATCOMP.
    Context (ge: Senv.t).
    Context {li I} (L: I -> semantics li).

    Definition genv := forall i, genvtype (L i).

    Definition state := { i : I & state (L i) }.

    Inductive liftk {i} (k: cont (L i)) q: state -> Prop :=
      | lift_intro s: k q s -> liftk k q (existT _ i s).

    Inductive step (ge: genv): state -> trace -> state -> Prop :=
      | step_intro i s t s':
          Smallstep.step (L i) (ge i) s t s' ->
          step ge (existT _ i s) t (existT _ i s').

    Inductive initial_state (q: query li): state -> Prop :=
      | initial_state_intro i s:
          Smallstep.initial_state (L i) q s ->
          initial_state q (existT _ i s).

    Inductive final_state: state -> reply li -> (query li -> state -> Prop) -> Prop :=
      | final_state_intro i s r k:
          Smallstep.final_state (L i) s r k ->
          final_state (existT _ i s) r (liftk k).

    Definition semantics :=
      {|
        Smallstep.genvtype := genv;
        Smallstep.state := state;
        Smallstep.step := step;
        Smallstep.initial_state := initial_state;
        Smallstep.final_state := final_state;
        Smallstep.globalenv := fun i => Smallstep.globalenv (L i);
        Smallstep.symbolenv := ge;
      |}.
    End FLATCOMP.
End FComp.

(** * Resolution operator *)

(** To go from the flat composition to horizontal composition, we
  introduce the following resolution operator. [Res] eliminates
  external calls to internal functions by replacing them with a nested
  execution of the transition system. Each [Res.state] is a stack of
  states of [L]: normal execution operates on the topmost state;
  a recursive call into [L] pushes the nested initial state on the
  stack; reaching a final state causes the topmost state to be popped
  and the caller to be resumed, or returns to the environment when
  we reach the last one. *)

Module Res.
  Section RESOLVE.
    Context {li} (L: Smallstep.semantics (li -o li)).
    Context (dom : query li -> bool).

    Definition state: Type := option (Smallstep.state L) * list (cont L).

    Definition observable (x: reply (li -o li)) (stk: list (cont L)) :=
      match x with
        | inl q => dom q = false (*forall s, ~ Smallstep.initial_state L (inr q) s*)
        | inr r => stk = nil
      end.

    Inductive liftk (k: cont L) stk: query (li -o li) -> state -> Prop :=
      | liftk_intro q s:
          k q s ->
          liftk k stk q (Some s, stk).

    Definition initial_state :=
      liftk (Smallstep.initial_state L) nil.

    Inductive final_state: state -> reply (li -o li) -> _ -> Prop :=
      | final_state_intro s r k stk:
          observable r stk ->
          Smallstep.final_state L s r k ->
          final_state (Some s, stk) r (liftk k stk).

    Inductive step ge : state -> trace -> state -> Prop :=
      | step_internal s t s' stk:
          Smallstep.step L ge s t s' ->
          step ge (Some s, stk) t (Some s', stk)
      | step_call s stk qi si k:
          dom qi = true ->
          Smallstep.final_state L s (inl qi) k ->
          apply_cont L (Smallstep.initial_state L) (inr qi) si ->
          step ge (Some s, stk) E0 (si, k :: stk)
      | step_return si ri ki (k: cont L) s stk:
          Smallstep.final_state L si (inr ri) ki ->
          apply_cont L k (inl ri) s ->
          step ge (Some si, k :: stk) E0 (s, stk).

    Definition semantics: Smallstep.semantics (li -o li) :=
      {|
        Smallstep.state := state;
        Smallstep.step := step;
        Smallstep.initial_state := initial_state;
        Smallstep.final_state := final_state;
        Smallstep.globalenv := globalenv L;
        Smallstep.symbolenv := symbolenv L;
      |}.
  End RESOLVE.
End Res.

(** * Horizontal composition *)

(** Applying the resolution operator to the flat composition of
  some transitions systems gives us horizontal composition. *)

Module HComp.
  Section HCOMP.
    Context (ge: Senv.t).
    Context {li I} (L: I -> semantics (li -o li)).

    Definition semantics :=
      Res.semantics (FComp.semantics ge L).
  End HCOMP.
End HComp.
