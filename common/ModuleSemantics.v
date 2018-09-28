
Require Import Relations.
Require Import Wellfounded.
Require Import Coqlib.
Require Import Events.
Require Import Globalenvs.
Require Import Integers.
Require Import Smallstep.
Require Import Sets.

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

    Inductive state {A B} :=
      | state_l (s1: A) (k2: cont li B)
      | state_r (s2: B) (k1: cont li A).

    Definition liftk {A B} (k1: cont li A) (k2: cont li B) (q: query li) :=
      match k1 q, k2 q with
        | Some S1, None => Some (set_map (fun s1 => state_l s1 k2) S1)
        | None, Some S2 => Some (set_map (fun s2 => state_r s2 k1) S2)
        | Some _, Some _ => Some (fun _ => False)
        | None, None => None
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
    Context {li} (sw: reply li -> query li) (L: Smallstep.semantics li).

    (** When switching occurs, we use an intermediate [resumed] state
      before starting up again. This is important for two reasons.
      First, in a nondeterministic transition system, a switching
      final state may coexist with other steps. If the switch results
      in a query that goes initially wrong, this behavior would be
      cancelled out by the alternative step, whereas the approach
      below allows us to first transition to the [resumed] step, then
      go wrong. Second, the strategy-level horizontal composition will
      also have such a step, introduced as the initial step of the
      embedding for the component being switched to, so that using the
      extra step allows the commutation proof between horizontal
      composition and embedding to be a simple lockstep simulation. *)

    Inductive state {A} :=
      | running (s : A)
      | resumed (S : A -> Prop).

    Inductive step ge : state -> trace -> state -> Prop :=
      | step_internal s t s':
          Smallstep.step L ge s t s' ->
          step ge (running s) t (running s')
      | step_switch s r k S:
          Smallstep.final_state L s r k ->
          k (sw r) = Some S ->
          step ge (running s) E0 (resumed S)
      | step_resume (S: Smallstep.state L -> Prop) s :
          S s ->
          step ge (resumed S) E0 (running s).

    Definition liftk {A} (k: cont li A) : cont li state :=
      fun q => option_map (set_map running) (k q).

    Inductive final_state : state -> reply li -> _ -> Prop :=
      final_state_intro s r k :
        Smallstep.final_state L s r k ->
        k (sw r) = None ->
        final_state (running s) r (liftk k).

    Definition semantics: Smallstep.semantics li :=
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

    Definition sw (r : reply (li -o li)) : query (li -o li) :=
      match r with
        | inl qA => inr qA
        | inr rB => inl rB
      end.

    Definition semantics :=
      Res.semantics sw (FComp.semantics ge L1 L2).
  End HCOMP.
End HComp.
