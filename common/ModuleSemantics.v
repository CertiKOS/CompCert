
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
    Context {li} (L1 L2: semantics li).

    Definition genv: Type := genvtype L1 * genvtype L2.

    Inductive state :=
      | state_l (s1: Smallstep.state L1) (k2: cont L2)
      | state_r (s2: Smallstep.state L2) (k1: cont L1).

    Definition liftk (k1: cont L1) (k2: cont L2) (q: query li) (s: state) :=
      match dom L1 q, dom L2 q, s with
        | true, false, state_l s1 k2' => k1 q s1 /\ k2' = k2
        | false, true, state_r s2 k1' => k2 q s2 /\ k1' = k1
        | _, _, _ => False
      end.

    Inductive step (ge: genv): state -> trace -> state -> Prop :=
      | step_l s t s' k:
          Smallstep.step L1 (fst ge) s t s' ->
          step ge (state_l s k) t (state_l s' k)
      | step_r s t s' k:
          Smallstep.step L2 (snd ge) s t s' ->
          step ge (state_r s k) t (state_r s' k).

    Inductive final_state: state -> reply li -> _ -> Prop :=
      | final_state_l s1 r1 k1 k2:
          Smallstep.final_state L1 s1 r1 k1 ->
          final_state (state_l s1 k2) r1 (liftk k1 k2)
      | final_state_r s2 r2 k2 k1:
          Smallstep.final_state L2 s2 r2 k2 ->
          final_state (state_r s2 k1) r2 (liftk k1 k2).

    Definition semantics :=
      {|
        Smallstep.genvtype := genv;
        Smallstep.state := state;
        Smallstep.step := step;
        Smallstep.initial_state := liftk (initial_state L1) (initial_state L2);
        Smallstep.final_state := final_state;
        Smallstep.globalenv := (globalenv L1, globalenv L2);
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

    Definition sw (r : reply (li -o li)) : option (query (li -o li)) :=
      match r with
        | inl qA => if dom L (inr qA) then Some (inr qA) else None
        | inr rB => None
      end.

    Inductive state :=
      | running (s : Smallstep.state L)
      | resumed (k : Smallstep.state L -> Prop).

    Inductive step ge : state -> trace -> state -> Prop :=
      | step_internal s t s':
          Smallstep.step L ge s t s' ->
          step ge (running s) t (running s')
      | step_switch s r k q:
          Smallstep.final_state L s r k ->
          sw r = Some q ->
          step ge (running s) E0 (resumed (k q))
      | step_resume (k: Smallstep.state L -> Prop) s :
          k s ->
          step ge (resumed k) E0 (running s).

    Inductive liftr (k: Smallstep.state L -> Prop) : state -> Prop :=
      liftr_intro s :
        k s ->
        liftr k (running s).

    Definition liftk (k: cont L) (q: query (li -o li)) : state -> Prop :=
      liftr (k q).

    Inductive final_state : state -> reply (li -o li) -> _ -> Prop :=
      final_state_intro s r k :
        Smallstep.final_state L s r k ->
        sw r = None ->
        final_state (running s) r (liftk k).

    Definition semantics: Smallstep.semantics (li -o li) :=
      {|
        Smallstep.state := state;
        Smallstep.step := step;
        Smallstep.initial_state := liftk (initial_state L);
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
    Context {li} (L1 L2: semantics (li -o li)).

    Definition semantics :=
      Res.semantics (FComp.semantics ge L1 L2).
  End HCOMP.
End HComp.
